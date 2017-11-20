/*******************************************************************************
 *
 * Xilinx XDMA IP Core Linux Driver
 * Copyright(c) 2015 - 2017 Xilinx, Inc.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * The full GNU General Public License is included in this distribution in
 * the file called "LICENSE".
 *
 * Karen Xie <karen.xie@xilinx.com>
 *
 ******************************************************************************/

#define pr_fmt(fmt)     KBUILD_MODNAME ":%s: " fmt, __func__

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/string.h>
#include <linux/mm.h>
#include <linux/errno.h>
#include <linux/sched.h>
#include <linux/vmalloc.h>

#include "libxdma.h"
#include "libxdma_api.h"
#include "cdev_sgdma.h"

/* SECTION: Module licensing */

#ifdef __LIBXDMA_MOD__
#include "version.h"
#define DRV_MODULE_NAME		"libxdma"
#define DRV_MODULE_DESC		"Xilinx XDMA Base Driver"
#define DRV_MODULE_RELDATE	"Feb. 2017"

static char version[] =
        DRV_MODULE_DESC " " DRV_MODULE_NAME " v" DRV_MODULE_VERSION "\n";

MODULE_AUTHOR("Xilinx, Inc.");
MODULE_DESCRIPTION(DRV_MODULE_DESC);
MODULE_VERSION(DRV_MODULE_VERSION);
MODULE_LICENSE("GPL v2");
#endif

/* Module Parameters */
static unsigned int poll_mode;
module_param(poll_mode, uint, 0644);
MODULE_PARM_DESC(poll_mode, "Set 1 for hw polling, default is 0 (interrupts)");

static unsigned int interrupt_mode;
module_param(interrupt_mode, uint, 0644);
MODULE_PARM_DESC(interrupt_mode, "0 - MSI-x , 1 - MSI, 2 - Legacy");

static unsigned int enable_credit_mp;
module_param(enable_credit_mp, uint, 0644);
MODULE_PARM_DESC(enable_credit_mp, "Set 1 to enable creidt feature, default is 0 (no credit control)");

unsigned int desc_blen_max = XDMA_DESC_BLEN_MAX;
module_param(desc_blen_max, uint, 0644);
MODULE_PARM_DESC(desc_blen_max, "per descriptor max. buffer length, default is (1 << 28) - 1");

/*
 * xdma device management
 * maintains a list of the xdma devices
 */
static LIST_HEAD(xdev_list);
static DEFINE_MUTEX(xdev_mutex);

static LIST_HEAD(xdev_rcu_list);
static DEFINE_SPINLOCK(xdev_rcu_lock);

#ifndef list_last_entry
#define list_last_entry(ptr, type, member) \
		list_entry((ptr)->prev, type, member)
#endif

static inline void xdev_list_add(struct xdma_dev *xdev)
{
	mutex_lock(&xdev_mutex);
	if (list_empty(&xdev_list))
		xdev->idx = 0;
	else {
		struct xdma_dev *last;

		last = list_last_entry(&xdev_list, struct xdma_dev, list_head);
		xdev->idx = last->idx + 1;
	}
	list_add_tail(&xdev->list_head, &xdev_list);
	mutex_unlock(&xdev_mutex);

	dbg_init("dev %s, xdev 0x%p, xdma idx %d.\n",
		dev_name(&xdev->pdev->dev), xdev, xdev->idx);

	spin_lock(&xdev_rcu_lock);
	list_add_tail_rcu(&xdev->rcu_node, &xdev_rcu_list);
	spin_unlock(&xdev_rcu_lock);
}

#undef list_last_entry

static inline void xdev_list_remove(struct xdma_dev *xdev)
{
	mutex_lock(&xdev_mutex);
	list_del(&xdev->list_head);
	mutex_unlock(&xdev_mutex);

	spin_lock(&xdev_rcu_lock);
	list_del_rcu(&xdev->rcu_node);
	spin_unlock(&xdev_rcu_lock);
	synchronize_rcu();
}

struct xdma_dev *xdev_find_by_pdev(struct pci_dev *pdev)
{
        struct xdma_dev *xdev, *tmp;

        mutex_lock(&xdev_mutex);
        list_for_each_entry_safe(xdev, tmp, &xdev_list, list_head) {
                if (xdev->pdev == pdev) {
                        mutex_unlock(&xdev_mutex);
                        return xdev;
                }
        }
        mutex_unlock(&xdev_mutex);
        return NULL;
}
EXPORT_SYMBOL_GPL(xdev_find_by_pdev);

static inline int debug_check_dev_hndl(const char *fname, struct pci_dev *pdev,
				 void *hndl)
{
	struct xdma_dev *xdev;

	if (!pdev)
		return -EINVAL;

	xdev = xdev_find_by_pdev(pdev);
	if (!xdev) {
		pr_info("%s pdev 0x%p, hndl 0x%p, NO match found!\n",
			fname, pdev, hndl);
		return -EINVAL;
	}
	if (xdev != hndl) {
		pr_err("%s pdev 0x%p, hndl 0x%p != 0x%p!\n",
			fname, pdev, hndl, xdev);
		return -EINVAL;
	}

	return 0;
}

#ifdef __LIBXDMA_DEBUG__
/* SECTION: Function definitions */
inline void __write_register(const char *fn, u32 value, void *iomem, unsigned long off)
{
	pr_err("%s: w reg 0x%lx(0x%p), 0x%x.\n", fn, off, iomem, value);
	iowrite32(value, iomem);
}
#define write_register(v,mem,off) __write_register(__func__, v, mem, off)
#else
#define write_register(v,mem,off) iowrite32(v, mem)
#endif

inline u32 read_register(void *iomem)
{
	return ioread32(iomem);
}

static inline u32 build_u32(u32 hi, u32 lo)
{
	return ((hi & 0xFFFFUL) << 16) | (lo & 0xFFFFUL);
}

static inline u64 build_u64(u64 hi, u64 lo)
{
	return ((hi & 0xFFFFFFFULL) << 32) | (lo & 0xFFFFFFFFULL);
}

static void check_nonzero_interrupt_status(struct xdma_dev *xdev)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);
	u32 w;

	w = read_register(&reg->user_int_enable);
	if (w)
		pr_info("%s xdma%d user_int_enable = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);

	w = read_register(&reg->channel_int_enable);
	if (w)
	pr_info("%s xdma%d channel_int_enable = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);

	w = read_register(&reg->user_int_request);
	if (w)
		pr_info("%s xdma%d user_int_request = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);
	w = read_register(&reg->channel_int_request);
	if (w)
		pr_info("%s xdma%d channel_int_request = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);

	w = read_register(&reg->user_int_pending);
	if (w)
		pr_info("%s xdma%d user_int_pending = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);
	w = read_register(&reg->channel_int_pending);
	if (w)
		pr_info("%s xdma%d channel_int_pending = 0x%08x\n",
			dev_name(&xdev->pdev->dev), xdev->idx, w);
}

/* channel_interrupts_enable -- Enable interrupts we are interested in */
static void channel_interrupts_enable(struct xdma_dev *xdev, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->channel_int_enable_w1s, XDMA_OFS_INT_CTRL);
}

/* channel_interrupts_disable -- Disable interrupts we not interested in */
static void channel_interrupts_disable(struct xdma_dev *xdev, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->channel_int_enable_w1c, XDMA_OFS_INT_CTRL);
}

/* user_interrupts_enable -- Enable interrupts we are interested in */
static void user_interrupts_enable(struct xdma_dev *xdev, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->user_int_enable_w1s, XDMA_OFS_INT_CTRL);
}

/* user_interrupts_disable -- Disable interrupts we not interested in */
static void user_interrupts_disable(struct xdma_dev *xdev, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->user_int_enable_w1c, XDMA_OFS_INT_CTRL);
}

/* read_interrupts -- Print the interrupt controller status */
static u32 read_interrupts(struct xdma_dev *xdev)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(xdev->bar[xdev->config_bar_idx] + XDMA_OFS_INT_CTRL);
	u32 lo;
	u32 hi;

	/* extra debugging; inspect complete engine set of registers */
	hi = read_register(&reg->user_int_request);
	dbg_io("ioread32(0x%p) returned 0x%08x (user_int_request).\n",
		&reg->user_int_request, hi);
	lo = read_register(&reg->channel_int_request);
	dbg_io("ioread32(0x%p) returned 0x%08x (channel_int_request)\n",
		&reg->channel_int_request, lo);

	/* return interrupts: user in upper 16-bits, channel in lower 16-bits */
	return build_u32(hi, lo);
}

void enable_perf(struct xdma_engine *engine)
{
	u32 w;

	w = XDMA_PERF_CLEAR;
	write_register(w, &engine->regs->perf_ctrl,
			(unsigned long)(&engine->regs->perf_ctrl) -
			(unsigned long)(&engine->regs));
	read_register(&engine->regs->identifier);
	w = XDMA_PERF_AUTO | XDMA_PERF_RUN;
	write_register(w, &engine->regs->perf_ctrl,
			(unsigned long)(&engine->regs->perf_ctrl) -
			(unsigned long)(&engine->regs));
	read_register(&engine->regs->identifier);

	dbg_perf("IOCTL_XDMA_PERF_START\n");

}
EXPORT_SYMBOL_GPL(enable_perf);

void get_perf_stats(struct xdma_engine *engine)
{
	u32 hi;
	u32 lo;

	BUG_ON(!engine);

	if (!engine->xdma_perf) {
		pr_info("%s perf struct not set up.\n", engine->name);
		return;
	}

	hi = 0;
	lo = read_register(&engine->regs->completed_desc_count);
	engine->xdma_perf->iterations = build_u64(hi, lo);

	hi = read_register(&engine->regs->perf_cyc_hi);
	lo = read_register(&engine->regs->perf_cyc_lo);

	engine->xdma_perf->clock_cycle_count = build_u64(hi, lo);

	hi = read_register(&engine->regs->perf_dat_hi);
	lo = read_register(&engine->regs->perf_dat_lo);
	engine->xdma_perf->data_cycle_count = build_u64(hi, lo);

	hi = read_register(&engine->regs->perf_pnd_hi);
	lo = read_register(&engine->regs->perf_pnd_lo);
	engine->xdma_perf->pending_count = build_u64(hi, lo);
}
EXPORT_SYMBOL_GPL(get_perf_stats);

static void engine_reg_dump(struct xdma_engine *engine)
{
	u32 w;

	BUG_ON(!engine);

	w = read_register(&engine->regs->identifier);
	pr_info("%s: ioread32(0x%p) = 0x%08x (id).\n",
		engine->name, &engine->regs->identifier, w);
	w &= BLOCK_ID_MASK;
	if (w != BLOCK_ID_HEAD) {
		pr_info("%s: engine id missing, 0x%08x exp. & 0x%x = 0x%x\n",
			 engine->name, w, BLOCK_ID_MASK, BLOCK_ID_HEAD);
		return;
	}
	/* extra debugging; inspect complete engine set of registers */
	w = read_register(&engine->regs->status);
	pr_info("%s: ioread32(0x%p) = 0x%08x (status).\n",
		engine->name, &engine->regs->status, w);
	w = read_register(&engine->regs->control);
	pr_info("%s: ioread32(0x%p) = 0x%08x (control)\n",
		engine->name, &engine->regs->control, w);
	w = read_register(&engine->sgdma_regs->first_desc_lo);
	pr_info("%s: ioread32(0x%p) = 0x%08x (first_desc_lo)\n",
		engine->name, &engine->sgdma_regs->first_desc_lo, w);
	w = read_register(&engine->sgdma_regs->first_desc_hi);
	pr_info("%s: ioread32(0x%p) = 0x%08x (first_desc_hi)\n",
		engine->name, &engine->sgdma_regs->first_desc_hi, w);
	w = read_register(&engine->sgdma_regs->first_desc_adjacent);
	pr_info("%s: ioread32(0x%p) = 0x%08x (first_desc_adjacent).\n",
		engine->name, &engine->sgdma_regs->first_desc_adjacent, w);
	w = read_register(&engine->regs->completed_desc_count);
	pr_info("%s: ioread32(0x%p) = 0x%08x (completed_desc_count).\n",
		engine->name, &engine->regs->completed_desc_count, w);
	w = read_register(&engine->regs->interrupt_enable_mask);
	pr_info("%s: ioread32(0x%p) = 0x%08x (interrupt_enable_mask)\n",
		engine->name, &engine->regs->interrupt_enable_mask, w);
}

/**
 * engine_status_read() - read status of SG DMA engine (optionally reset)
 *
 * Stores status in engine->status.
 *
 * @return -1 on failure, status register otherwise
 */
static void engine_status_dump(struct xdma_engine *engine)
{
	u32 v = engine->status;
	char buffer[256];
	char *buf = buffer;
	int len = 0;

	len = sprintf(buf, "SG engine %s status: 0x%08x: ", engine->name, v);
	
	if ((v & XDMA_STAT_BUSY))
		len += sprintf(buf + len, "BUSY,");
	if ((v & XDMA_STAT_DESC_STOPPED))
		len += sprintf(buf + len, "DESC_STOPPED,");
	if ((v & XDMA_STAT_DESC_COMPLETED))
		len += sprintf(buf + len, "DESC_COMPL,");

	/* common H2C & C2H */	
 	if ((v & XDMA_STAT_COMMON_ERR_MASK)) {
		if ((v & XDMA_STAT_ALIGN_MISMATCH))
			len += sprintf(buf + len, "ALIGN_MISMATCH ");
		if ((v & XDMA_STAT_MAGIC_STOPPED))
			len += sprintf(buf + len, "MAGIC_STOPPED ");
		if ((v & XDMA_STAT_INVALID_LEN))
			len += sprintf(buf + len, "INVLIAD_LEN ");
		if ((v & XDMA_STAT_IDLE_STOPPED))
			len += sprintf(buf + len, "IDLE_STOPPED ");
		buf[len - 1] = ',';
	}

	if ((engine->dir == DMA_TO_DEVICE)) {
		/* H2C only */
		if ((v & XDMA_STAT_H2C_R_ERR_MASK)) {
			len += sprintf(buf + len, "R:");
			if ((v & XDMA_STAT_H2C_R_UNSUPP_REQ))
				len += sprintf(buf + len, "UNSUPP_REQ ");
			if ((v & XDMA_STAT_H2C_R_COMPL_ABORT))
				len += sprintf(buf + len, "COMPL_ABORT ");
			if ((v & XDMA_STAT_H2C_R_PARITY_ERR))
				len += sprintf(buf + len, "PARITY ");
			if ((v & XDMA_STAT_H2C_R_HEADER_EP))
				len += sprintf(buf + len, "HEADER_EP ");
			if ((v & XDMA_STAT_H2C_R_UNEXP_COMPL))
				len += sprintf(buf + len, "UNEXP_COMPL ");
			buf[len - 1] = ',';
		}

		if ((v & XDMA_STAT_H2C_W_ERR_MASK)) {
			len += sprintf(buf + len, "W:");
			if ((v & XDMA_STAT_H2C_W_DECODE_ERR))
				len += sprintf(buf + len, "DECODE_ERR ");
			if ((v & XDMA_STAT_H2C_W_SLAVE_ERR))
				len += sprintf(buf + len, "SLAVE_ERR ");
			buf[len - 1] = ',';
		}
		
	} else {
		/* C2H only */
		if ((v & XDMA_STAT_C2H_R_ERR_MASK)) {
			len += sprintf(buf + len, "R:");
			if ((v & XDMA_STAT_C2H_R_DECODE_ERR))
				len += sprintf(buf + len, "DECODE_ERR ");
			if ((v & XDMA_STAT_C2H_R_SLAVE_ERR))
				len += sprintf(buf + len, "SLAVE_ERR ");
			buf[len - 1] = ',';
		}
	}

	/* common H2C & C2H */	
 	if ((v & XDMA_STAT_DESC_ERR_MASK)) {
		len += sprintf(buf + len, "DESC_ERR:");
		if ((v & XDMA_STAT_DESC_UNSUPP_REQ))
			len += sprintf(buf + len, "UNSUPP_REQ ");
		if ((v & XDMA_STAT_DESC_COMPL_ABORT))
			len += sprintf(buf + len, "COMPL_ABORT ");
		if ((v & XDMA_STAT_DESC_PARITY_ERR))
			len += sprintf(buf + len, "PARITY ");
		if ((v & XDMA_STAT_DESC_HEADER_EP))
			len += sprintf(buf + len, "HEADER_EP ");
		if ((v & XDMA_STAT_DESC_UNEXP_COMPL))
			len += sprintf(buf + len, "UNEXP_COMPL ");
		buf[len - 1] = ',';
	}

	buf[len - 1] = '\0';
	pr_info("%s\n", buffer);
}

static u32 engine_status_read(struct xdma_engine *engine, bool clear, bool dump)
{
	u32 value;

	BUG_ON(!engine);

	if (dump)
		engine_reg_dump(engine);

	/* read status register */
	if (clear)
		value = engine->status =
			read_register(&engine->regs->status_rc);
	else
		value = engine->status = read_register(&engine->regs->status);

	if (dump)
		engine_status_dump(engine);

	return value;
}

/**
 * xdma_engine_stop() - stop an SG DMA engine
 *
 */
static void xdma_engine_stop(struct xdma_engine *engine)
{
	u32 w;

	BUG_ON(!engine);
	dbg_tfr("xdma_engine_stop(engine=%p)\n", engine);

	w = 0;
	w |= (u32)XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
	w |= (u32)XDMA_CTRL_IE_MAGIC_STOPPED;
	w |= (u32)XDMA_CTRL_IE_READ_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESC_ERROR;

	if (poll_mode) {
		w |= (u32) XDMA_CTRL_POLL_MODE_WB;
	} else {
		w |= (u32)XDMA_CTRL_IE_DESC_STOPPED;
		w |= (u32)XDMA_CTRL_IE_DESC_COMPLETED;

		/* Disable IDLE STOPPED for MM */
		if ((engine->streaming && (engine->dir == DMA_FROM_DEVICE)) ||
		    (engine->xdma_perf))
			w |= (u32)XDMA_CTRL_IE_IDLE_STOPPED;
	}

	dbg_tfr("Stopping SG DMA %s engine; writing 0x%08x to 0x%p.\n",
			engine->name, w, (u32 *)&engine->regs->control);
	write_register(w, &engine->regs->control,
			(unsigned long)(&engine->regs->control) -
			(unsigned long)(&engine->regs));
	/* dummy read of status register to flush all previous writes */
	dbg_tfr("xdma_engine_stop(%s) done\n", engine->name);
}

static void engine_start_mode_config(struct xdma_engine *engine)
{
	u32 w;

	BUG_ON(!engine);

	/* If a perf test is running, enable the engine interrupts */
	if (engine->xdma_perf) {
		w = XDMA_CTRL_IE_DESC_STOPPED;
		w |= XDMA_CTRL_IE_DESC_COMPLETED;
		w |= XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
		w |= XDMA_CTRL_IE_MAGIC_STOPPED;
		w |= XDMA_CTRL_IE_IDLE_STOPPED;
		w |= XDMA_CTRL_IE_READ_ERROR;
		w |= XDMA_CTRL_IE_DESC_ERROR;

		write_register(w, &engine->regs->interrupt_enable_mask,
			(unsigned long)(&engine->regs->interrupt_enable_mask) -
			(unsigned long)(&engine->regs));
	}

	/* write control register of SG DMA engine */
	w = (u32)XDMA_CTRL_RUN_STOP;
	w |= (u32)XDMA_CTRL_IE_READ_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESC_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
	w |= (u32)XDMA_CTRL_IE_MAGIC_STOPPED;

	if (poll_mode) {
		w |= (u32)XDMA_CTRL_POLL_MODE_WB;
	} else { 
		w |= (u32)XDMA_CTRL_IE_DESC_STOPPED;
		w |= (u32)XDMA_CTRL_IE_DESC_COMPLETED;

		if ((engine->streaming && (engine->dir == DMA_FROM_DEVICE)) ||
		    (engine->xdma_perf))
			w |= (u32)XDMA_CTRL_IE_IDLE_STOPPED;

		/* set non-incremental addressing mode */
		if (engine->non_incr_addr)
			w |= (u32)XDMA_CTRL_NON_INCR_ADDR;
	}

	dbg_tfr("iowrite32(0x%08x to 0x%p) (control)\n", w,
			(void *)&engine->regs->control);
	/* start the engine */
	write_register(w, &engine->regs->control,
			(unsigned long)(&engine->regs->control) -
			(unsigned long)(&engine->regs));

	/* dummy read of status register to flush all previous writes */
	w = read_register(&engine->regs->status);
	dbg_tfr("ioread32(0x%p) = 0x%08x (dummy read flushes writes).\n",
			&engine->regs->status, w);
}

/**
 * engine_start() - start an idle engine with its first transfer on queue
 *
 * The engine will run and process all transfers that are queued using
 * transfer_queue() and thus have their descriptor lists chained.
 *
 * During the run, new transfers will be processed if transfer_queue() has
 * chained the descriptors before the hardware fetches the last descriptor.
 * A transfer that was chained too late will invoke a new run of the engine
 * initiated from the engine_service() routine.
 *
 * The engine must be idle and at least one transfer must be queued.
 * This function does not take locks; the engine spinlock must already be
 * taken.
 *
 */
static struct xdma_transfer *engine_start(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer;
	u32 w;
	int extra_adj = 0;

	/* engine must be idle */
	BUG_ON(engine->running);
	/* engine transfer queue must not be empty */
	BUG_ON(list_empty(&engine->transfer_list));
	/* inspect first transfer queued on the engine */
	transfer = list_entry(engine->transfer_list.next, struct xdma_transfer,
				entry);
	BUG_ON(!transfer);

	/* engine is no longer shutdown */
	engine->shutdown = ENGINE_SHUTDOWN_NONE;

	dbg_tfr("engine_start(%s): transfer=0x%p.\n", engine->name, transfer);

	/* initialize number of descriptors of dequeued transfers */
	engine->desc_dequeued = 0;

	/* write lower 32-bit of bus address of transfer first descriptor */
	w = cpu_to_le32(PCI_DMA_L(transfer->desc_bus));
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_lo)\n", w,
			(void *)&engine->sgdma_regs->first_desc_lo);
	write_register(w, &engine->sgdma_regs->first_desc_lo,
			(unsigned long)(&engine->sgdma_regs->first_desc_lo) -
			(unsigned long)(&engine->sgdma_regs));
	/* write upper 32-bit of bus address of transfer first descriptor */
	w = cpu_to_le32(PCI_DMA_H(transfer->desc_bus));
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_hi)\n", w,
			(void *)&engine->sgdma_regs->first_desc_hi);
	write_register(w, &engine->sgdma_regs->first_desc_hi,
			(unsigned long)(&engine->sgdma_regs->first_desc_hi) -
			(unsigned long)(&engine->sgdma_regs));

	if (transfer->desc_adjacent > 0) {
		extra_adj = transfer->desc_adjacent - 1;
		if (extra_adj > MAX_EXTRA_ADJ)
			extra_adj = MAX_EXTRA_ADJ;
	}
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_adjacent)\n",
		extra_adj, (void *)&engine->sgdma_regs->first_desc_adjacent);
	write_register(extra_adj, &engine->sgdma_regs->first_desc_adjacent,
			(unsigned long)(&engine->sgdma_regs->first_desc_adjacent) -
			(unsigned long)(&engine->sgdma_regs));

	dbg_tfr("ioread32(0x%p) (dummy read flushes writes).\n",
		&engine->regs->status);
	mmiowb();

	engine_start_mode_config(engine);

	engine_status_read(engine, 0, 0);

	dbg_tfr("%s engine 0x%p now running\n", engine->name, engine);
	/* remember the engine is running */
	engine->running = 1;
	return transfer;
}

/**
 * engine_service() - service an SG DMA engine
 *
 * must be called with engine->lock already acquired
 *
 * @engine pointer to struct xdma_engine
 *
 */
static void engine_service_shutdown(struct xdma_engine *engine)
{
	/* if the engine stopped with RUN still asserted, de-assert RUN now */
	dbg_tfr("engine just went idle, resetting RUN_STOP.\n");
	xdma_engine_stop(engine);
	engine->running = 0;

	/* awake task on engine's shutdown wait queue */
	wake_up_interruptible(&engine->shutdown_wq);
}

struct xdma_transfer *engine_transfer_completion(struct xdma_engine *engine,
		struct xdma_transfer *transfer)
{
	BUG_ON(!engine);

	if (unlikely(!transfer)) {
		pr_info("%s: xfer empty.\n", engine->name);
		return NULL;
	}

	/* synchronous I/O? */
	/* awake task on transfer's wait queue */
	wake_up_interruptible(&transfer->wq);

	return transfer;
}

struct xdma_transfer *engine_service_transfer_list(struct xdma_engine *engine,
		struct xdma_transfer *transfer, u32 *pdesc_completed)
{
	BUG_ON(!engine);
	BUG_ON(!pdesc_completed);

	if (unlikely(!transfer)) {
		pr_info("%s xfer empty, pdesc completed %u.\n",
			engine->name, *pdesc_completed);
		return NULL;
	}

	/*
	 * iterate over all the transfers completed by the engine,
	 * except for the last (i.e. use > instead of >=).
	 */
	while (transfer && (!transfer->cyclic) &&
		(*pdesc_completed > transfer->desc_num)) {
		/* remove this transfer from pdesc_completed */
		*pdesc_completed -= transfer->desc_num;
		dbg_tfr("%s engine completed non-cyclic xfer 0x%p (%d desc)\n",
			engine->name, transfer, transfer->desc_num);
		/* remove completed transfer from list */
		list_del(engine->transfer_list.next);
		/* add to dequeued number of descriptors during this run */
		engine->desc_dequeued += transfer->desc_num;
		/* mark transfer as succesfully completed */
		transfer->state = TRANSFER_STATE_COMPLETED;

		/* Complete transfer - sets transfer to NULL if an async
		 * transfer has completed */
		transfer = engine_transfer_completion(engine, transfer);

		/* if exists, get the next transfer on the list */
		if (!list_empty(&engine->transfer_list)) {
			transfer = list_entry(engine->transfer_list.next,
					struct xdma_transfer, entry);
			dbg_tfr("Non-completed transfer %p\n", transfer);
		} else {
			/* no further transfers? */
			transfer = NULL;
		}
	}

	return transfer;
}

static void engine_err_handle(struct xdma_engine *engine,
		struct xdma_transfer *transfer, u32 desc_completed)
{
	u32 value;

	/*
	 * The BUSY bit is expected to be clear now but older HW has a race
	 * condition which could cause it to be still set.  If it's set, re-read
	 * and check again.  If it's still set, log the issue.
	 */
	if (engine->status & XDMA_STAT_BUSY) {
		value = read_register(&engine->regs->status);
		if ((value & XDMA_STAT_BUSY) && printk_ratelimit())
			pr_info("%s has errors but is still BUSY\n",
				engine->name);
	}

	if (printk_ratelimit()) {
		pr_info("%s, s 0x%x, aborted xfer 0x%p, cmpl %d/%d\n",
			engine->name, engine->status, transfer, desc_completed,
			transfer->desc_num);
	}
	
	/* mark transfer as failed */
	transfer->state = TRANSFER_STATE_FAILED;
	xdma_engine_stop(engine);
}

struct xdma_transfer *engine_service_final_transfer(struct xdma_engine *engine,
			struct xdma_transfer *transfer, u32 *pdesc_completed)
{
	BUG_ON(!engine);
	BUG_ON(!pdesc_completed);

	/* inspect the current transfer */
	if (unlikely(!transfer)) {
		pr_info("%s xfer empty, pdesc completed %u.\n",
			engine->name, *pdesc_completed);
		return NULL;
	} else {
		if (((engine->dir == DMA_FROM_DEVICE) &&
		     (engine->status & XDMA_STAT_C2H_ERR_MASK)) ||
		    ((engine->dir == DMA_TO_DEVICE) &&
		     (engine->status & XDMA_STAT_H2C_ERR_MASK))) {
			pr_info("engine %s, status error 0x%x.\n",
				engine->name, engine->status);
			engine_status_dump(engine);
			engine_err_handle(engine, transfer, *pdesc_completed);
			goto transfer_del;
		}

		if (engine->status & XDMA_STAT_BUSY)
			pr_debug("engine %s is unexpectedly busy - ignoring\n",
				engine->name);

		/* the engine stopped on current transfer? */
		if (*pdesc_completed < transfer->desc_num) {
			transfer->state = TRANSFER_STATE_FAILED;
			pr_info("%s, xfer 0x%p, stopped half-way, %d/%d.\n",
				engine->name, transfer, *pdesc_completed,
				transfer->desc_num);
		} else {
			dbg_tfr("engine %s completed transfer\n", engine->name);
			dbg_tfr("Completed transfer ID = 0x%p\n", transfer);
			dbg_tfr("*pdesc_completed=%d, transfer->desc_num=%d",
				*pdesc_completed, transfer->desc_num);

			if (!transfer->cyclic) {
				/*
				 * if the engine stopped on this transfer,
				 * it should be the last
				 */
				WARN_ON(*pdesc_completed > transfer->desc_num);
			}
			/* mark transfer as succesfully completed */
			transfer->state = TRANSFER_STATE_COMPLETED;
		}

transfer_del:
		/* remove completed transfer from list */
		list_del(engine->transfer_list.next);
		/* add to dequeued number of descriptors during this run */
		engine->desc_dequeued += transfer->desc_num;

		/*
		 * Complete transfer - sets transfer to NULL if an asynchronous
		 * transfer has completed
		 */
		transfer = engine_transfer_completion(engine, transfer);
	} 

	return transfer;
}

static void engine_service_perf(struct xdma_engine *engine, u32 desc_completed)
{
	BUG_ON(!engine);

	/* performance measurement is running? */
	if (engine->xdma_perf) {
		/* a descriptor was completed? */
		if (engine->status & XDMA_STAT_DESC_COMPLETED) {
			engine->xdma_perf->iterations = desc_completed;
			dbg_perf("transfer->xdma_perf->iterations=%d\n",
				engine->xdma_perf->iterations);
		}

		/* a descriptor stopped the engine? */
		if (engine->status & XDMA_STAT_DESC_STOPPED) {
			engine->xdma_perf->stopped = 1;
			/*
			 * wake any XDMA_PERF_IOCTL_STOP waiting for
			 * the performance run to finish
			 */
			wake_up_interruptible(&engine->xdma_perf_wq);
			dbg_perf("transfer->xdma_perf stopped\n");
		}
	}
}

static void engine_transfer_dequeue(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer;

	BUG_ON(!engine);

	/* pick first transfer on the queue (was submitted to the engine) */
	transfer = list_entry(engine->transfer_list.next, struct xdma_transfer,
		entry);
	if (!transfer || transfer != &engine->cyclic_req->xfer) {
		pr_info("%s, xfer 0x%p != 0x%p.\n",
			engine->name, transfer, &engine->cyclic_req->xfer);
		return;
	}
	dbg_tfr("%s engine completed cyclic transfer 0x%p (%d desc).\n",
		engine->name, transfer, transfer->desc_num);
	/* remove completed transfer from list */
	list_del(engine->transfer_list.next);
}

static int engine_ring_process(struct xdma_engine *engine)
{
	struct xdma_result *result;
	int start;
	int eop_count = 0;

	BUG_ON(!engine);
	result = engine->cyclic_result;
	BUG_ON(!result);

	/* where we start receiving in the ring buffer */
	start = engine->rx_tail;

	/* iterate through all newly received RX result descriptors */
	dbg_tfr("%s, result %d, 0x%x, len 0x%x.\n",
		engine->name, engine->rx_tail, result[engine->rx_tail].status,
		result[engine->rx_tail].length);
	while (result[engine->rx_tail].status && !engine->rx_overrun) {
		/* EOP bit set in result? */
		if (result[engine->rx_tail].status & RX_STATUS_EOP){
			eop_count++;
		}

		/* increment tail pointer */
		engine->rx_tail = (engine->rx_tail + 1) % CYCLIC_RX_PAGES_MAX;

		dbg_tfr("%s, head %d, tail %d, 0x%x, len 0x%x.\n",
			engine->name, engine->rx_head, engine->rx_tail,
			result[engine->rx_tail].status,
			result[engine->rx_tail].length);

		/* overrun? */
		if (engine->rx_tail == engine->rx_head) {
			dbg_tfr("%s: overrun\n", engine->name);
			/* flag to user space that overrun has occurred */
			engine->rx_overrun = 1;
		}
	}

	return eop_count;
}

static int engine_service_cyclic_polled(struct xdma_engine *engine)
{
	int eop_count = 0;
	int rc = 0;
	struct xdma_poll_wb *writeback_data;
	u32 sched_limit = 0;

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	writeback_data = (struct xdma_poll_wb *)engine->poll_mode_addr_virt;

	while (eop_count == 0) {
		if (sched_limit != 0) {
			if ((sched_limit % NUM_POLLS_PER_SCHED) == 0)
				schedule();
		}
		sched_limit++;

		/* Monitor descriptor writeback address for errors */
		if ((writeback_data->completed_desc_count) & WB_ERR_MASK) {
			rc = -1;
			break;
		}

		eop_count = engine_ring_process(engine);
	}

	if (eop_count == 0) {
		engine_status_read(engine, 1, 0);
		if ((engine->running) && !(engine->status & XDMA_STAT_BUSY)) {
			/* transfers on queue? */
			if (!list_empty(&engine->transfer_list))
				engine_transfer_dequeue(engine);

			engine_service_shutdown(engine);
		}
	}

	return rc;
}

static int engine_service_cyclic_interrupt(struct xdma_engine *engine)
{
	int eop_count = 0;
	struct xdma_transfer *xfer;

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	engine_status_read(engine, 1, 0);

	eop_count = engine_ring_process(engine);
	/*
	 * wake any reader on EOP, as one or more packets are now in
	 * the RX buffer
	 */
	xfer = &engine->cyclic_req->xfer;
	if(enable_credit_mp){
		if (eop_count > 0) {
			//engine->eop_found = 1;
		}
		wake_up_interruptible(&xfer->wq);
	}else{
		if (eop_count > 0) {
			/* awake task on transfer's wait queue */
			dbg_tfr("wake_up_interruptible() due to %d EOP's\n", eop_count);
			engine->eop_found = 1;
			wake_up_interruptible(&xfer->wq);
		}
	}

	/* engine was running but is no longer busy? */
	if ((engine->running) && !(engine->status & XDMA_STAT_BUSY)) {
		/* transfers on queue? */
		if (!list_empty(&engine->transfer_list))
			engine_transfer_dequeue(engine);

		engine_service_shutdown(engine);
	}

	return 0;
}

/* must be called with engine->lock already acquired */
static int engine_service_cyclic(struct xdma_engine *engine)
{
	int rc = 0;

	dbg_tfr("engine_service_cyclic()");

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	if (poll_mode)
		rc = engine_service_cyclic_polled(engine);
	else
		rc = engine_service_cyclic_interrupt(engine);

	return rc;
}


static void engine_service_resume(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer_started;

	BUG_ON(!engine);

	/* engine stopped? */
	if (!engine->running) {
		/* in the case of shutdown, let it finish what's in the Q */
		if (!list_empty(&engine->transfer_list)) {
			/* (re)start engine */
			transfer_started = engine_start(engine);
			pr_info("re-started %s engine with pending xfer 0x%p\n",
				engine->name, transfer_started);
		/* engine was requested to be shutdown? */
		} else if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
			engine->shutdown |= ENGINE_SHUTDOWN_IDLE;
			/* awake task on engine's shutdown wait queue */
			wake_up_interruptible(&engine->shutdown_wq);
		} else {
			dbg_tfr("no pending transfers, %s engine stays idle.\n",
				engine->name);
		}
	} else {
		/* engine is still running? */
		if (list_empty(&engine->transfer_list)) {
			pr_warn("no queued transfers but %s engine running!\n",
				engine->name);
			WARN_ON(1);
		}
	}
}

/**
 * engine_service() - service an SG DMA engine
 *
 * must be called with engine->lock already acquired
 *
 * @engine pointer to struct xdma_engine
 *
 */
static int engine_service(struct xdma_engine *engine, int desc_writeback)
{
	struct xdma_transfer *transfer = NULL;
	u32 desc_count = desc_writeback & WB_COUNT_MASK;
	u32 err_flag = desc_writeback & WB_ERR_MASK;
	int rv = 0;
	struct xdma_poll_wb *wb_data;

	BUG_ON(!engine);

	/* If polling detected an error, signal to the caller */
	if (err_flag)
		rv = -1;

	/* Service the engine */
	if (!engine->running) {
		dbg_tfr("Engine was not running!!! Clearing status\n");
		engine_status_read(engine, 1, 0);
		return 0;
	}

	/*
	 * If called by the ISR or polling detected an error, read and clear
	 * engine status. For polled mode descriptor completion, this read is
	 * unnecessary and is skipped to reduce latency
	 */
	if ((desc_count == 0) || (err_flag != 0))
		engine_status_read(engine, 1, 0);

	/*
	 * engine was running but is no longer busy, or writeback occurred,
	 * shut down
	 */
	if ((engine->running && !(engine->status & XDMA_STAT_BUSY)) ||
		(desc_count != 0))
		engine_service_shutdown(engine);

	/*
	 * If called from the ISR, or if an error occurred, the descriptor
	 * count will be zero.  In this scenario, read the descriptor count
	 * from HW.  In polled mode descriptor completion, this read is
	 * unnecessary and is skipped to reduce latency
	 */
	if (!desc_count)
		desc_count = read_register(&engine->regs->completed_desc_count);
	dbg_tfr("desc_count = %d\n", desc_count);

	/* transfers on queue? */
	if (!list_empty(&engine->transfer_list)) {
		/* pick first transfer on queue (was submitted to the engine) */
		transfer = list_entry(engine->transfer_list.next,
				struct xdma_transfer, entry);

		dbg_tfr("head of queue transfer 0x%p has %d descriptors\n",
			transfer, (int)transfer->desc_num);

		dbg_tfr("Engine completed %d desc, %d not yet dequeued\n",
			(int)desc_count,
			(int)desc_count - engine->desc_dequeued);

		engine_service_perf(engine, desc_count);
	}

	/* account for already dequeued transfers during this engine run */
	desc_count -= engine->desc_dequeued;

	/* Process all but the last transfer */
	transfer = engine_service_transfer_list(engine, transfer, &desc_count);

	/*
	 * Process final transfer - includes checks of number of descriptors to
	 * detect faulty completion
	 */
	transfer = engine_service_final_transfer(engine, transfer, &desc_count);

	/* Before starting engine again, clear the writeback data */
        if (poll_mode) {
		wb_data = (struct xdma_poll_wb *)engine->poll_mode_addr_virt;
		wb_data->completed_desc_count = 0;
	}

	/* Restart the engine following the servicing */
	engine_service_resume(engine);

	return 0;
}

/* engine_service_work */
static void engine_service_work(struct work_struct *work)
{
	struct xdma_engine *engine;
	unsigned long flags;

	engine = container_of(work, struct xdma_engine, work);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	/* lock the engine */
	spin_lock_irqsave(&engine->lock, flags);

	dbg_tfr("engine_service() for %s engine %p\n",
		engine->name, engine);
	if (engine->cyclic_req)
                engine_service_cyclic(engine);
	else
		engine_service(engine, 0);

	/* re-enable interrupts for this engine */
	if (engine->xdev->msix_enabled){
		write_register(engine->interrupt_enable_mask_value,
			       &engine->regs->interrupt_enable_mask_w1s,
			(unsigned long)(&engine->regs->interrupt_enable_mask_w1s) -
			(unsigned long)(&engine->regs));
	} else
		channel_interrupts_enable(engine->xdev, engine->irq_bitmask);
		
	/* unlock the engine */
	spin_unlock_irqrestore(&engine->lock, flags);
}

static u32 engine_service_wb_monitor(struct xdma_engine *engine,
	u32 expected_wb)
{
	struct xdma_poll_wb *wb_data;
	u32 desc_wb = 0;
	u32 sched_limit = 0;
	unsigned long timeout;

	BUG_ON(!engine);
	wb_data = (struct xdma_poll_wb *)engine->poll_mode_addr_virt;

	/*
 	 * Poll the writeback location for the expected number of
 	 * descriptors / error events This loop is skipped for cyclic mode,
 	 * where the expected_desc_count passed in is zero, since it cannot be
 	 * determined before the function is called
 	 */

	timeout = jiffies + (POLL_TIMEOUT_SECONDS * HZ);
	while (expected_wb != 0) {
		desc_wb = wb_data->completed_desc_count;

		if (desc_wb & WB_ERR_MASK)
			break;
		else if (desc_wb == expected_wb)
			break;
			
		/* RTO - prevent system from hanging in polled mode */
		if (time_after(jiffies, timeout)) {
			dbg_tfr("Polling timeout occurred");
			dbg_tfr("desc_wb = 0x%08x, expected 0x%08x\n", desc_wb,
				expected_wb);
			if ((desc_wb & WB_COUNT_MASK) > expected_wb)
				desc_wb = expected_wb | WB_ERR_MASK;

			break;
		}

		/*
 		 * Define NUM_POLLS_PER_SCHED to limit how much time is spent
 		 * in the scheduler
 		 */

		if (sched_limit != 0) {
			if ((sched_limit % NUM_POLLS_PER_SCHED) == 0)
				schedule();
		}
		sched_limit++;
	}

	return desc_wb;
}

static int engine_service_poll(struct xdma_engine *engine,
                u32 expected_desc_count)
{
	struct xdma_poll_wb *writeback_data;
	u32 desc_wb = 0;
	unsigned long flags;
	int rv = 0;

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	writeback_data = (struct xdma_poll_wb *)engine->poll_mode_addr_virt;

	if ((expected_desc_count & WB_COUNT_MASK) != expected_desc_count) {
		dbg_tfr("Queued descriptor count is larger than supported\n");
		return -1;
	}

	/*
 	 * Poll the writeback location for the expected number of
 	 * descriptors / error events This loop is skipped for cyclic mode,
 	 * where the expected_desc_count passed in is zero, since it cannot be
 	 * determined before the function is called
 	 */

	desc_wb = engine_service_wb_monitor(engine, expected_desc_count);

	spin_lock_irqsave(&engine->lock, flags);
	dbg_tfr("%s service.\n", engine->name);
	if (engine->cyclic_req) {
		rv = engine_service_cyclic(engine);
	} else {
		rv = engine_service(engine, desc_wb);
	}
	spin_unlock_irqrestore(&engine->lock, flags);

	return rv;
}

static irqreturn_t user_irq_service(int irq, struct xdma_user_irq *user_irq)
{
	unsigned long flags;

	BUG_ON(!user_irq);

	if (user_irq->handler)
		return user_irq->handler(user_irq->user_idx, user_irq->dev);

	spin_lock_irqsave(&(user_irq->events_lock), flags);
	if (!user_irq->events_irq) {
		user_irq->events_irq = 1;
		wake_up_interruptible(&(user_irq->events_wq));
	}
	spin_unlock_irqrestore(&(user_irq->events_lock), flags);

	return IRQ_HANDLED;
}

/*
 * xdma_isr() - Interrupt handler
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_isr(int irq, void *dev_id)
{
	u32 ch_irq;
	u32 user_irq;
	u32 mask;
	struct xdma_dev *xdev;
	struct interrupt_regs *irq_regs;

	dbg_irq("(irq=%d, dev 0x%p) <<<< ISR.\n", irq, dev_id);
	BUG_ON(!dev_id);
	xdev = (struct xdma_dev *)dev_id;

	if (!xdev) {
		WARN_ON(!xdev);
		dbg_irq("xdma_isr(irq=%d) xdev=%p ??\n", irq, xdev);
		return IRQ_NONE;
	}

	irq_regs = (struct interrupt_regs *)(xdev->bar[xdev->config_bar_idx] +
			XDMA_OFS_INT_CTRL);

	/* read channel interrupt requests */
	ch_irq = read_register(&irq_regs->channel_int_request);
	dbg_irq("ch_irq = 0x%08x\n", ch_irq);

	/*
	 * disable all interrupts that fired; these are re-enabled individually
	 * after the causing module has been fully serviced.
	 */
	if (ch_irq)
		channel_interrupts_disable(xdev, ch_irq);

	/* read user interrupts - this read also flushes the above write */
	user_irq = read_register(&irq_regs->user_int_request);
	dbg_irq("user_irq = 0x%08x\n", user_irq);

	if (user_irq) {
		int user = 0;
                u32 mask = 1;
		int max = xdev->h2c_channel_max;

		for (; user < max && user_irq; user++, mask <<= 1) {
			if (user_irq & mask) {
				user_irq &= ~mask;
				user_irq_service(irq, &xdev->user_irq[user]);
			}
		}
	}

	mask = ch_irq & xdev->mask_irq_h2c;
	if (mask) {
		int channel = 0;
		int max = xdev->h2c_channel_max;

		/* iterate over H2C (PCIe read) */
		for (channel = 0; channel < max && mask; channel++) {
			struct xdma_engine *engine = &xdev->engine_h2c[channel];

			/* engine present and its interrupt fired? */
			if((engine->irq_bitmask & mask) &&
			   (engine->magic == MAGIC_ENGINE)) {
				mask &= ~engine->irq_bitmask;
				dbg_tfr("schedule_work, %s.\n", engine->name);
				schedule_work(&engine->work);
			}
		}
	}

	mask = ch_irq & xdev->mask_irq_c2h;
	if (mask) {
		int channel = 0;
		int max = xdev->c2h_channel_max;

		/* iterate over C2H (PCIe write) */
		for (channel = 0; channel < max && mask; channel++) {
			struct xdma_engine *engine = &xdev->engine_c2h[channel];

			/* engine present and its interrupt fired? */
			if((engine->irq_bitmask & mask) &&
			   (engine->magic == MAGIC_ENGINE)) {
				mask &= ~engine->irq_bitmask;
				dbg_tfr("schedule_work, %s.\n", engine->name);
				schedule_work(&engine->work);
			}
		}
	}

	xdev->irq_count++;
	return IRQ_HANDLED;
}

/*
 * xdma_user_irq() - Interrupt handler for user interrupts in MSI-X mode
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_user_irq(int irq, void *dev_id)
{
	struct xdma_user_irq *user_irq;

	dbg_irq("(irq=%d) <<<< INTERRUPT SERVICE ROUTINE\n", irq);

	BUG_ON(!dev_id);
	user_irq = (struct xdma_user_irq *)dev_id;

	return  user_irq_service(irq, user_irq);
}

/*
 * xdma_channel_irq() - Interrupt handler for channel interrupts in MSI-X mode
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_channel_irq(int irq, void *dev_id)
{
	struct xdma_dev *xdev;
	struct xdma_engine *engine;
	struct interrupt_regs *irq_regs;

	dbg_irq("(irq=%d) <<<< INTERRUPT service ROUTINE\n", irq);
	BUG_ON(!dev_id);

	engine = (struct xdma_engine *)dev_id;
	xdev = engine->xdev;

	if (!xdev) {
		WARN_ON(!xdev);
		dbg_irq("xdma_channel_irq(irq=%d) xdev=%p ??\n", irq, xdev);
		return IRQ_NONE;
	}

	irq_regs = (struct interrupt_regs *)(xdev->bar[xdev->config_bar_idx] +
			XDMA_OFS_INT_CTRL);

	/* Disable the interrupt for this engine */
	write_register(engine->interrupt_enable_mask_value,
			&engine->regs->interrupt_enable_mask_w1c,
			(unsigned long)
			(&engine->regs->interrupt_enable_mask_w1c) -
			(unsigned long)(&engine->regs));
	/* Dummy read to flush the above write */
	read_register(&irq_regs->channel_int_pending);
	/* Schedule the bottom half */
	schedule_work(&engine->work);

	/*
	 * RTO - need to protect access here if multiple MSI-X are used for
	 * user interrupts
	 */
	xdev->irq_count++;
	return IRQ_HANDLED;
}

/*
 * Unmap the BAR regions that had been mapped earlier using map_bars()
 */
static void unmap_bars(struct xdma_dev *xdev, struct pci_dev *dev)
{
	int i;

	for (i = 0; i < XDMA_BAR_NUM; i++) {
		/* is this BAR mapped? */
		if (xdev->bar[i]) {
			/* unmap BAR */
			pci_iounmap(dev, xdev->bar[i]);
			/* mark as unmapped */
			xdev->bar[i] = NULL;
		}
	}
}

static int map_single_bar(struct xdma_dev *xdev, struct pci_dev *dev, int idx)
{
	resource_size_t bar_start;
	resource_size_t bar_len;
	resource_size_t map_len;

	bar_start = pci_resource_start(dev, idx);
	bar_len = pci_resource_len(dev, idx);
	map_len = bar_len;

	xdev->bar[idx] = NULL;

	/* do not map BARs with length 0. Note that start MAY be 0! */
	if (!bar_len) {
		//pr_info("BAR #%d is not present - skipping\n", idx);
		return 0;
	}

	/* BAR size exceeds maximum desired mapping? */
	if (bar_len > INT_MAX) {
		pr_info("Limit BAR %d mapping from %llu to %d bytes\n", idx,
			(u64)bar_len, INT_MAX);
		map_len = (resource_size_t)INT_MAX;
	}
	/*
	 * map the full device memory or IO region into kernel virtual
	 * address space
	 */
	dbg_init("BAR%d: %llu bytes to be mapped.\n", idx, (u64)map_len);
	xdev->bar[idx] = pci_iomap(dev, idx, map_len);

	if (!xdev->bar[idx]) {
		pr_info("Could not map BAR %d.\n", idx);
		return -1;
	}

	pr_info("BAR%d at 0x%llx mapped at 0x%p, length=%llu(/%llu)\n", idx,
		(u64)bar_start, xdev->bar[idx], (u64)map_len, (u64)bar_len);

	return (int)map_len;
}

static int is_config_bar(struct xdma_dev *xdev, int idx)
{
	u32 irq_id = 0;
	u32 cfg_id = 0;
	int flag = 0;
	u32 mask = 0xffff0000; /* Compare only XDMA ID's not Version number */
	struct interrupt_regs *irq_regs =
		(struct interrupt_regs *) (xdev->bar[idx] + XDMA_OFS_INT_CTRL);
	struct config_regs *cfg_regs =
		(struct config_regs *)(xdev->bar[idx] + XDMA_OFS_CONFIG);

	irq_id = read_register(&irq_regs->identifier);
	cfg_id = read_register(&cfg_regs->identifier);

	if (((irq_id & mask)== IRQ_BLOCK_ID) &&
	    ((cfg_id & mask)== CONFIG_BLOCK_ID)) {
		dbg_init("BAR %d is the XDMA config BAR\n", idx);
		flag = 1;
	} else {
		dbg_init("BAR %d is NOT the XDMA config BAR: 0x%x, 0x%x.\n",
			idx, irq_id, cfg_id);
		flag = 0;
	}

	return flag;
}

static void identify_bars(struct xdma_dev *xdev, int *bar_id_list, int num_bars,
			int config_bar_pos)
{
	/*
	 * The following logic identifies which BARs contain what functionality
	 * based on the position of the XDMA config BAR and the number of BARs
	 * detected. The rules are that the user logic and bypass logic BARs
	 * are optional.  When both are present, the XDMA config BAR will be the
	 * 2nd BAR detected (config_bar_pos = 1), with the user logic being
	 * detected first and the bypass being detected last. When one is
	 * omitted, the type of BAR present can be identified by whether the
	 * XDMA config BAR is detected first or last.  When both are omitted,
	 * only the XDMA config BAR is present.  This somewhat convoluted
	 * approach is used instead of relying on BAR numbers in order to work
	 * correctly with both 32-bit and 64-bit BARs.
	 */

	BUG_ON(!xdev);
	BUG_ON(!bar_id_list);

	dbg_init("xdev 0x%p, bars %d, config at %d.\n",
		xdev, num_bars, config_bar_pos);

	switch (num_bars) {
	case 1:
		/* Only one BAR present - no extra work necessary */
		break;

	case 2:
		if (config_bar_pos == 0) {
			xdev->bypass_bar_idx = bar_id_list[1];
		} else if (config_bar_pos == 1) {
			xdev->user_bar_idx = bar_id_list[0];
		} else {
			pr_info("2, XDMA config BAR unexpected %d.\n",
				config_bar_pos);
		}
		break;

	case 3:
	case 4:
		if ((config_bar_pos == 1) || (config_bar_pos == 2)) {
			/* user bar at bar #0 */
			xdev->user_bar_idx = bar_id_list[0];
			/* bypass bar at the last bar */
			xdev->bypass_bar_idx = bar_id_list[num_bars - 1];
		} else {
			pr_info("3/4, XDMA config BAR unexpected %d.\n",
				config_bar_pos);
		}
		break;

	default:
		/* Should not occur - warn user but safe to continue */
		pr_info("Unexpected # BARs (%d), XDMA config BAR only.\n",
			num_bars);
		break;

	}
	pr_info("%d BARs: config %d, user %d, bypass %d.\n",
		num_bars, config_bar_pos, xdev->user_bar_idx,
		xdev->bypass_bar_idx);
}

/* map_bars() -- map device regions into kernel virtual address space
 *
 * Map the device memory regions into kernel virtual address space after
 * verifying their sizes respect the minimum sizes needed
 */
static int map_bars(struct xdma_dev *xdev, struct pci_dev *dev)
{
	int rv;
	int i;
	int bar_id_list[XDMA_BAR_NUM];
	int bar_id_idx = 0;
	int config_bar_pos = 0;

	/* iterate through all the BARs */
	for (i = 0; i < XDMA_BAR_NUM; i++) {
		int bar_len;

		bar_len = map_single_bar(xdev, dev, i);
		if (bar_len == 0) {
			continue;
		} else if (bar_len < 0) {
			rv = -EINVAL;
			goto fail;
		}

		/* Try to identify BAR as XDMA control BAR */
		if ((bar_len >= XDMA_BAR_SIZE) && (xdev->config_bar_idx < 0)) {

			if (is_config_bar(xdev, i)) {
				xdev->config_bar_idx = i;
				config_bar_pos = bar_id_idx;
				pr_info("config bar %d, pos %d.\n",
					xdev->config_bar_idx, config_bar_pos);
			}
		}

		bar_id_list[bar_id_idx] = i;
		bar_id_idx++;
	}

	/* The XDMA config BAR must always be present */
	if (xdev->config_bar_idx < 0) {
		pr_info("Failed to detect XDMA config BAR\n");
		rv = -EINVAL;
		goto fail;
	}

	identify_bars(xdev, bar_id_list, bar_id_idx, config_bar_pos);

	/* successfully mapped all required BAR regions */
	return 0;

fail:
	/* unwind; unmap any BARs that we did map */
	unmap_bars(xdev, dev);
	return rv;
}

/*
 * MSI-X interrupt: 
 *	<h2c+c2h channel_max> vectors, followed by <user_max> vectors
 */

/*
 * RTO - code to detect if MSI/MSI-X capability exists is derived
 * from linux/pci/msi.c - pci_msi_check_device
 */

#ifndef arch_msi_check_device
int arch_msi_check_device(struct pci_dev *dev, int nvec, int type)
{
	return 0;
}
#endif

/* type = PCI_CAP_ID_MSI or PCI_CAP_ID_MSIX */
static int msi_msix_capable(struct pci_dev *dev, int type)
{
	struct pci_bus *bus;
	int ret;

	if (!dev || dev->no_msi)
		return 0;

	for (bus = dev->bus; bus; bus = bus->parent)
		if (bus->bus_flags & PCI_BUS_FLAGS_NO_MSI)
			return 0;

	ret = arch_msi_check_device(dev, 1, type);
	if (ret)
		return 0;

	if (!pci_find_capability(dev, type))
		return 0;

	return 1;
}

static void disable_msi_msix(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	if (xdev->msix_enabled) {
		pci_disable_msix(pdev);
		xdev->msix_enabled = 0;
	} else if (xdev->msi_enabled) {
		pci_disable_msi(pdev);
		xdev->msi_enabled = 0;
	}
}

static int enable_msi_msix(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	int rv = 0;

	BUG_ON(!xdev);
	BUG_ON(!pdev);

	if (!interrupt_mode && msi_msix_capable(pdev, PCI_CAP_ID_MSIX)) {
		int req_nvec = xdev->c2h_channel_max + xdev->h2c_channel_max +
				 xdev->user_max;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
		dbg_init("Enabling MSI-X\n");
		rv = pci_alloc_irq_vectors(pdev, req_nvec, req_nvec,
					PCI_IRQ_MSIX);
#else
		int i;

		dbg_init("Enabling MSI-X\n");
		for (i = 0; i < req_nvec; i++)
			xdev->entry[i].entry = i;

		rv = pci_enable_msix(pdev, xdev->entry, req_nvec);
#endif
		if (rv < 0)
			dbg_init("Couldn't enable MSI-X mode: %d\n", rv);

		xdev->msix_enabled = 1;

	} else if (interrupt_mode == 1 &&
		   msi_msix_capable(pdev, PCI_CAP_ID_MSI)) {
		/* enable message signalled interrupts */
		dbg_init("pci_enable_msi()\n");
		rv = pci_enable_msi(pdev);
		if (rv < 0)
			dbg_init("Couldn't enable MSI mode: %d\n", rv);
		xdev->msi_enabled = 1;

	} else {
		dbg_init("MSI/MSI-X not detected - using legacy interrupts\n");
	}

	return rv;
}

static void pci_check_intr_pend(struct pci_dev *pdev)
{
	u16 v;

	pci_read_config_word(pdev, PCI_STATUS, &v);
	if (v & PCI_STATUS_INTERRUPT) {
		pr_info("%s PCI STATUS Interrupt pending 0x%x.\n",
                        dev_name(&pdev->dev), v);
		pci_write_config_word(pdev, PCI_STATUS, PCI_STATUS_INTERRUPT);
	}
}

static void pci_keep_intx_enabled(struct pci_dev *pdev)
{
	/* workaround to a h/w bug:
	 * when msix/msi become unavaile, default to legacy.
	 * However the legacy enable was not checked.
	 * If the legacy was disabled, no ack then everything stuck
	 */
	u16 pcmd, pcmd_new;

	pci_read_config_word(pdev, PCI_COMMAND, &pcmd);
	pcmd_new = pcmd & ~PCI_COMMAND_INTX_DISABLE;
	if (pcmd_new != pcmd) {
		pr_info("%s: clear INTX_DISABLE, 0x%x -> 0x%x.\n",
			dev_name(&pdev->dev), pcmd, pcmd_new);
		pci_write_config_word(pdev, PCI_COMMAND, pcmd_new);
	}
}

static void prog_irq_msix_user(struct xdma_dev *xdev, bool clear)
{
	/* user */
	struct interrupt_regs *int_regs = (struct interrupt_regs *)
					(xdev->bar[xdev->config_bar_idx] +
					 XDMA_OFS_INT_CTRL);
	u32 i = xdev->c2h_channel_max + xdev->h2c_channel_max;
	u32 max = i + xdev->user_max;
	int j;

	for (j = 0; i < max; j++) {
		u32 val = 0;
		int k;
		int shift = 0;

		if (clear)
			i += 4;
		else
			for (k = 0; k < 4 && i < max; i++, k++, shift += 8)
				val |= (i & 0x1f) << shift;
		
		write_register(val, &int_regs->user_msi_vector[j],
			XDMA_OFS_INT_CTRL +
			((unsigned long)&int_regs->user_msi_vector[j] -
			 (unsigned long)int_regs));

		dbg_init("vector %d, 0x%x.\n", j, val);
	}
}

static void prog_irq_msix_channel(struct xdma_dev *xdev, bool clear) 
{
	struct interrupt_regs *int_regs = (struct interrupt_regs *)
					(xdev->bar[xdev->config_bar_idx] +
					 XDMA_OFS_INT_CTRL);
	u32 max = xdev->c2h_channel_max + xdev->h2c_channel_max;
	u32 i;
	int j;

	/* engine */
	for (i = 0, j = 0; i < max; j++) {
		u32 val = 0;
		int k;
		int shift = 0;

		if (clear)
			i += 4;
		else
			for (k = 0; k < 4 && i < max; i++, k++, shift += 8)
				val |= (i & 0x1f) << shift;
		
		write_register(val, &int_regs->channel_msi_vector[j],
			XDMA_OFS_INT_CTRL +
			((unsigned long)&int_regs->channel_msi_vector[j] -
			 (unsigned long)int_regs));
		dbg_init("vector %d, 0x%x.\n", j, val);
	}
}

static void irq_msix_channel_teardown(struct xdma_dev *xdev)
{
	struct xdma_engine *engine;
	int j = 0;
	int i = 0;

	if (!xdev->msix_enabled)
		return;

	prog_irq_msix_channel(xdev, 1);

 	engine = xdev->engine_h2c;
	for (i = 0; i < xdev->h2c_channel_max; i++, j++, engine++) {
		if (!engine->msix_irq_line)
			break;
		dbg_sg("Release IRQ#%d for engine %p\n", engine->msix_irq_line,
			engine);
		free_irq(engine->msix_irq_line, engine);
	}

 	engine = xdev->engine_c2h;
	for (i = 0; i < xdev->c2h_channel_max; i++, j++, engine++) {
		if (!engine->msix_irq_line)
			break;
		dbg_sg("Release IRQ#%d for engine %p\n", engine->msix_irq_line,
			engine);
		free_irq(engine->msix_irq_line, engine);
	}
}

static int irq_msix_channel_setup(struct xdma_dev *xdev)
{
	int i;
	int j = xdev->h2c_channel_max;
	int rv = 0;
	u32 vector;
	struct xdma_engine *engine;

	BUG_ON(!xdev);
	if (!xdev->msix_enabled)
		return 0;

	engine = xdev->engine_h2c;
	for (i = 0; i < xdev->h2c_channel_max; i++, engine++) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
		vector = pci_irq_vector(xdev->pdev, i);
#else
		vector = xdev->entry[i].vector;
#endif
		rv = request_irq(vector, xdma_channel_irq, 0, xdev->mod_name,
				 engine);
		if (rv) {
			pr_info("requesti irq#%d failed %d, engine %s.\n",
				vector, rv, engine->name);
			return rv;
		}
		pr_info("engine %s, irq#%d.\n", engine->name, vector);
		engine->msix_irq_line = vector;
	}

	engine = xdev->engine_c2h;
	for (i = 0; i < xdev->c2h_channel_max; i++, j++, engine++) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
		vector = pci_irq_vector(xdev->pdev, j);
#else
		vector = xdev->entry[j].vector;
#endif
		rv = request_irq(vector, xdma_channel_irq, 0, xdev->mod_name,
				 engine);
		if (rv) {
			pr_info("requesti irq#%d failed %d, engine %s.\n",
				vector, rv, engine->name);
			return rv;
		}
		pr_info("engine %s, irq#%d.\n", engine->name, vector);
		engine->msix_irq_line = vector;
	}

	return 0;
}

static void irq_msix_user_teardown(struct xdma_dev *xdev)
{
	int i;
	int j = xdev->h2c_channel_max + xdev->c2h_channel_max;

	BUG_ON(!xdev);

	if (!xdev->msix_enabled)
		return;

	prog_irq_msix_user(xdev, 1);

	for (i = 0; i < xdev->user_max; i++, j++) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
		u32 vector = pci_irq_vector(xdev->pdev, j);
#else
		u32 vector = xdev->entry[j].vector;
#endif
		dbg_init("user %d, releasing IRQ#%d\n", i, vector);
		free_irq(vector, &xdev->user_irq[i]);
	}
}

static int irq_msix_user_setup(struct xdma_dev *xdev)
{
	int i;
	int j = xdev->h2c_channel_max + xdev->c2h_channel_max;
	int rv = 0;	

	/* vectors set in probe_scan_for_msi() */
	for (i = 0; i < xdev->user_max; i++, j++) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
		u32 vector = pci_irq_vector(xdev->pdev, j);
#else
		u32 vector = xdev->entry[j].vector;
#endif
		rv = request_irq(vector, xdma_user_irq, 0, xdev->mod_name,
				&xdev->user_irq[i]);
		if (rv) {
			pr_info("user %d couldn't use IRQ#%d, %d\n",
				i, vector, rv);
			break;
		}
		pr_info("%d-USR-%d, IRQ#%d with 0x%p\n", xdev->idx, i, vector,
			&xdev->user_irq[i]);
        }

	/* If any errors occur, free IRQs that were successfully requested */
	if (rv) {
		for (i--, j--; i >= 0; i--, j--) {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,12,0)
			u32 vector = pci_irq_vector(xdev->pdev, j);
#else
			u32 vector = xdev->entry[j].vector;
#endif
			free_irq(vector, &xdev->user_irq[i]);
		}
	}

	return rv;
}

static int irq_msi_setup(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	int rv;

	xdev->irq_line = (int)pdev->irq;
	rv = request_irq(pdev->irq, xdma_isr, 0, xdev->mod_name, xdev);
	if (rv)
		dbg_init("Couldn't use IRQ#%d, %d\n", pdev->irq, rv);
	else
		dbg_init("Using IRQ#%d with 0x%p\n", pdev->irq, xdev);

	return rv;
}

static int irq_legacy_setup(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	u32 w;
	u8 val;
	void *reg;
	int rv;

	pci_read_config_byte(pdev, PCI_INTERRUPT_PIN, &val);
	dbg_init("Legacy Interrupt register value = %d\n", val);
	if (val > 1) {
		val--;
		w = (val<<24) | (val<<16) | (val<<8)| val;
		/* Program IRQ Block Channel vactor and IRQ Block User vector
		 * with Legacy interrupt value */
		reg = xdev->bar[xdev->config_bar_idx] + 0x2080;   // IRQ user
		write_register(w, reg, 0x2080);
		write_register(w, reg+0x4, 0x2084);
		write_register(w, reg+0x8, 0x2088);
		write_register(w, reg+0xC, 0x208C);
		reg = xdev->bar[xdev->config_bar_idx] + 0x20A0;   // IRQ Block
		write_register(w, reg, 0x20A0);
		write_register(w, reg+0x4, 0x20A4);
	}

	xdev->irq_line = (int)pdev->irq;
	rv = request_irq(pdev->irq, xdma_isr, IRQF_SHARED, xdev->mod_name,
			xdev);
	if (rv)
		dbg_init("Couldn't use IRQ#%d, %d\n", pdev->irq, rv);
	else
		dbg_init("Using IRQ#%d with 0x%p\n", pdev->irq, xdev);

	return rv;
}

static void irq_teardown(struct xdma_dev *xdev)
{
	if (xdev->msix_enabled) {
		irq_msix_channel_teardown(xdev);
		irq_msix_user_teardown(xdev);
	} else if (xdev->irq_line != -1) {
		dbg_init("Releasing IRQ#%d\n", xdev->irq_line);
		free_irq(xdev->irq_line, xdev);
	}
}

static int irq_setup(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	pci_keep_intx_enabled(pdev);

	if (xdev->msix_enabled) {
		int rv = irq_msix_channel_setup(xdev);
		if (rv)
			return rv;
		rv = irq_msix_user_setup(xdev);
		if (rv)
			return rv;
		prog_irq_msix_channel(xdev, 0);
		prog_irq_msix_user(xdev, 0);

		return 0;
	} else if (xdev->msi_enabled)
		return irq_msi_setup(xdev, pdev);

	return irq_legacy_setup(xdev, pdev);
}

#ifdef __LIBXDMA_DEBUG__
static void dump_desc(struct xdma_desc *desc_virt)
{
	int j;
	u32 *p = (u32 *)desc_virt;
	static char * const field_name[] = {
		"magic|extra_adjacent|control", "bytes", "src_addr_lo",
		"src_addr_hi", "dst_addr_lo", "dst_addr_hi", "next_addr",
		"next_addr_pad"};
	char *dummy;

	/* remove warning about unused variable when debug printing is off */
	dummy = field_name[0];

	for (j = 0; j < 8; j += 1) {
		pr_info("0x%08lx/0x%02lx: 0x%08x 0x%08x %s\n",
			 (uintptr_t)p, (uintptr_t)p & 15, (int)*p,
			 le32_to_cpu(*p), field_name[j]);
		p++;
	}
	pr_info("\n");
}

static void transfer_dump(struct xdma_transfer *transfer)
{
	int i;
	struct xdma_desc *desc_virt = transfer->desc_virt;

	pr_info("xfer 0x%p, state 0x%x, f 0x%x, dir %d, len %u, last %d.\n",
		transfer, transfer->state, transfer->flags, transfer->dir,
		transfer->len, transfer->last_in_request);

	pr_info("transfer 0x%p, desc %d, bus 0x%llx, adj %d.\n",
		transfer, transfer->desc_num, (u64)transfer->desc_bus,
		transfer->desc_adjacent);
	for (i = 0; i < transfer->desc_num; i += 1)
		dump_desc(desc_virt + i);
}
#endif /* __LIBXDMA_DEBUG__ */

/* xdma_desc_alloc() - Allocate cache-coherent array of N descriptors.
 *
 * Allocates an array of 'number' descriptors in contiguous PCI bus addressable
 * memory. Chains the descriptors as a singly-linked list; the descriptor's
 * next * pointer specifies the bus address of the next descriptor.
 *
 *
 * @dev Pointer to pci_dev
 * @number Number of descriptors to be allocated
 * @desc_bus_p Pointer where to store the first descriptor bus address
 *
 * @return Virtual address of the first descriptor
 *
 */
static void transfer_desc_init(struct xdma_transfer *transfer, int count)
{
	struct xdma_desc *desc_virt = transfer->desc_virt;
	dma_addr_t desc_bus = transfer->desc_bus;
	int i;
	int adj = count - 1;
	int extra_adj;
	u32 temp_control;

	BUG_ON(count > XDMA_TRANSFER_MAX_DESC);

	/* create singly-linked list for SG DMA controller */
	for (i = 0; i < count - 1; i++) {
		/* increment bus address to next in array */
		desc_bus += sizeof(struct xdma_desc);

		/* singly-linked list uses bus addresses */
		desc_virt[i].next_lo = cpu_to_le32(PCI_DMA_L(desc_bus));
		desc_virt[i].next_hi = cpu_to_le32(PCI_DMA_H(desc_bus));
		desc_virt[i].bytes = cpu_to_le32(0);

		/* any adjacent descriptors? */
		if (adj > 0) {
			extra_adj = adj - 1;
			if (extra_adj > MAX_EXTRA_ADJ)
				extra_adj = MAX_EXTRA_ADJ;

			adj--;
		} else {
			extra_adj = 0;
		}

		temp_control = DESC_MAGIC | (extra_adj << 8);

		desc_virt[i].control = cpu_to_le32(temp_control);
	}
	/* { i = number - 1 } */
	/* zero the last descriptor next pointer */
	desc_virt[i].next_lo = cpu_to_le32(0);
	desc_virt[i].next_hi = cpu_to_le32(0);
	desc_virt[i].bytes = cpu_to_le32(0);

	temp_control = DESC_MAGIC;

	desc_virt[i].control = cpu_to_le32(temp_control);
}

/* xdma_desc_link() - Link two descriptors
 *
 * Link the first descriptor to a second descriptor, or terminate the first.
 *
 * @first first descriptor
 * @second second descriptor, or NULL if first descriptor must be set as last.
 * @second_bus bus address of second descriptor
 */
static void xdma_desc_link(struct xdma_desc *first, struct xdma_desc *second,
		dma_addr_t second_bus)
{
	/*
	 * remember reserved control in first descriptor, but zero
	 * extra_adjacent!
	 */
	 /* RTO - what's this about?  Shouldn't it be 0x0000c0ffUL? */
	u32 control = le32_to_cpu(first->control) & 0x0000f0ffUL;
	/* second descriptor given? */
	if (second) {
		/*
		 * link last descriptor of 1st array to first descriptor of
		 * 2nd array
		 */
		first->next_lo = cpu_to_le32(PCI_DMA_L(second_bus));
		first->next_hi = cpu_to_le32(PCI_DMA_H(second_bus));
		WARN_ON(first->next_hi);
		/* no second descriptor given */
	} else {
		/* first descriptor is the last */
		first->next_lo = 0;
		first->next_hi = 0;
	}
	/* merge magic, extra_adjacent and control field */
	control |= DESC_MAGIC;

	/* write bytes and next_num */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_adjacent -- Set how many descriptors are adjacent to this one */
static void xdma_desc_adjacent(struct xdma_desc *desc, int next_adjacent)
{
	int extra_adj = 0;
	/* remember reserved and control bits */
	u32 control = le32_to_cpu(desc->control) & 0x0000f0ffUL;
	u32 max_adj_4k = 0;

	if (next_adjacent > 0) {
		extra_adj =  next_adjacent - 1;
		if (extra_adj > MAX_EXTRA_ADJ){
			extra_adj = MAX_EXTRA_ADJ;
		}
		max_adj_4k = (0x1000 - ((le32_to_cpu(desc->next_lo))&0xFFF))/32 - 1;
		if (extra_adj>max_adj_4k) {
			extra_adj = max_adj_4k;
		}
		if(extra_adj<0){
			printk("Warning: extra_adj<0, converting it to 0\n");
			extra_adj = 0;
		}
	}
	/* merge adjacent and control field */
	control |= 0xAD4B0000UL | (extra_adj << 8);
	/* write control and next_adjacent */
	desc->control = cpu_to_le32(control);
}

/* xdma_desc_control -- Set complete control field of a descriptor. */
static void xdma_desc_control_set(struct xdma_desc *first, u32 control_field)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control) & ~(LS_BYTE_MASK);

	BUG_ON(control_field & ~(LS_BYTE_MASK));
	/* merge adjacent and control field */
	control |= control_field;
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_clear -- Clear bits in control field of a descriptor. */
static void xdma_desc_control_clear(struct xdma_desc *first, u32 clear_mask)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control);

	BUG_ON(clear_mask & ~(LS_BYTE_MASK));

	/* merge adjacent and control field */
	control &= (~clear_mask);
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_done - recycle cache-coherent linked list of descriptors.
 *
 * @dev Pointer to pci_dev
 * @number Number of descriptors to be allocated
 * @desc_virt Pointer to (i.e. virtual address of) first descriptor in list
 * @desc_bus Bus address of first descriptor in list
 */
static inline void xdma_desc_done(struct xdma_desc *desc_virt)
{
	memset(desc_virt, 0, XDMA_TRANSFER_MAX_DESC * sizeof(struct xdma_desc));
}

/* xdma_desc() - Fill a descriptor with the transfer details
 *
 * @desc pointer to descriptor to be filled
 * @addr root complex address
 * @ep_addr end point address
 * @len number of bytes, must be a (non-negative) multiple of 4.
 * @dir, dma direction
 * is the end point address. If zero, vice versa.
 *
 * Does not modify the next pointer
 */
static void xdma_desc_set(struct xdma_desc *desc, dma_addr_t rc_bus_addr,
		u64 ep_addr, int len, int dir)
{
	/* transfer length */
	desc->bytes = cpu_to_le32(len);
	if (dir == DMA_TO_DEVICE) {
		/* read from root complex memory (source address) */
		desc->src_addr_lo = cpu_to_le32(PCI_DMA_L(rc_bus_addr));
		desc->src_addr_hi = cpu_to_le32(PCI_DMA_H(rc_bus_addr));
		/* write to end point address (destination address) */
		desc->dst_addr_lo = cpu_to_le32(PCI_DMA_L(ep_addr));
		desc->dst_addr_hi = cpu_to_le32(PCI_DMA_H(ep_addr));
	} else {
		/* read from end point address (source address) */
		desc->src_addr_lo = cpu_to_le32(PCI_DMA_L(ep_addr));
		desc->src_addr_hi = cpu_to_le32(PCI_DMA_H(ep_addr));
		/* write to root complex memory (destination address) */
		desc->dst_addr_lo = cpu_to_le32(PCI_DMA_L(rc_bus_addr));
		desc->dst_addr_hi = cpu_to_le32(PCI_DMA_H(rc_bus_addr));
	}
}

/*
 * should hold the engine->lock;
 */
static void transfer_abort(struct xdma_engine *engine,
			struct xdma_transfer *transfer)
{
	struct xdma_transfer *head;

	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(transfer->desc_num == 0);

	pr_info("abort transfer 0x%p, desc %d, engine desc queued %d.\n",
		transfer, transfer->desc_num, engine->desc_dequeued);

	head = list_entry(engine->transfer_list.next, struct xdma_transfer,
			entry);
	if (head == transfer)
		list_del(engine->transfer_list.next);
        else
		pr_info("engine %s, transfer 0x%p NOT found, 0x%p.\n",
			engine->name, transfer, head);

	if (transfer->state == TRANSFER_STATE_SUBMITTED)
		transfer->state = TRANSFER_STATE_ABORTED;
}

/* transfer_queue() - Queue a DMA transfer on the engine
 *
 * @engine DMA engine doing the transfer
 * @transfer DMA transfer submitted to the engine
 *
 * Takes and releases the engine spinlock
 */
static int transfer_queue(struct xdma_engine *engine,
		struct xdma_transfer *transfer)
{
	int rv = 0;
	struct xdma_transfer *transfer_started;
	struct xdma_dev *xdev;
	unsigned long flags;

	BUG_ON(!engine);
	BUG_ON(!engine->xdev);
	BUG_ON(!transfer);
	BUG_ON(transfer->desc_num == 0);
	dbg_tfr("transfer_queue(transfer=0x%p).\n", transfer);

	xdev = engine->xdev;
	if (xdma_device_flag_check(xdev, XDEV_FLAG_OFFLINE)) {
		pr_info("dev 0x%p offline, transfer 0x%p not queued.\n",
			xdev, transfer);
		return -EBUSY;
	}

	/* lock the engine state */
	spin_lock_irqsave(&engine->lock, flags);

	engine->prev_cpu = get_cpu();
	put_cpu();

	/* engine is being shutdown; do not accept new transfers */
	if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
		pr_info("engine %s offline, transfer 0x%p not queued.\n",
			engine->name, transfer);
		rv = -EBUSY;
		goto shutdown;
	}

	/* mark the transfer as submitted */
	transfer->state = TRANSFER_STATE_SUBMITTED;
	/* add transfer to the tail of the engine transfer queue */
	list_add_tail(&transfer->entry, &engine->transfer_list);

	/* engine is idle? */
	if (!engine->running) {
		/* start engine */
		dbg_tfr("transfer_queue(): starting %s engine.\n",
			engine->name);
		transfer_started = engine_start(engine);
		dbg_tfr("transfer=0x%p started %s engine with transfer 0x%p.\n",
			transfer, engine->name, transfer_started);
	} else {
		dbg_tfr("transfer=0x%p queued, with %s engine running.\n",
			transfer, engine->name);
	}

shutdown:
	/* unlock the engine state */
	dbg_tfr("engine->running = %d\n", engine->running);
	spin_unlock_irqrestore(&engine->lock, flags);
	return rv;
}

static void engine_alignments(struct xdma_engine *engine)
{
	u32 w;
	u32 align_bytes;
	u32 granularity_bytes;
	u32 address_bits;

	w = read_register(&engine->regs->alignments);
	dbg_init("engine %p name %s alignments=0x%08x\n", engine,
		engine->name, (int)w);

	/* RTO  - add some macros to extract these fields */
	align_bytes = (w & 0x00ff0000U) >> 16;
	granularity_bytes = (w & 0x0000ff00U) >> 8;
	address_bits = (w & 0x000000ffU);

	dbg_init("align_bytes = %d\n", align_bytes);
	dbg_init("granularity_bytes = %d\n", granularity_bytes);
	dbg_init("address_bits = %d\n", address_bits);

	if (w) {
		engine->addr_align = align_bytes;
		engine->len_granularity = granularity_bytes;
		engine->addr_bits = address_bits;
	} else {
		/* Some default values if alignments are unspecified */
		engine->addr_align = 1;
		engine->len_granularity = 1;
		engine->addr_bits = 64;
	}
}

static void engine_free_resource(struct xdma_engine *engine)
{
	struct xdma_dev *xdev = engine->xdev;

	/* Release memory use for descriptor writebacks */
	if (engine->poll_mode_addr_virt) {
		dbg_sg("Releasing memory for descriptor writeback\n");
		dma_free_coherent(&xdev->pdev->dev,
				sizeof(struct xdma_poll_wb),
				engine->poll_mode_addr_virt,
				engine->poll_mode_bus);
		dbg_sg("Released memory for descriptor writeback\n");
		engine->poll_mode_addr_virt = NULL;
	}

	if (engine->desc) {
		dbg_init("device %s, engine %s pre-alloc desc 0x%p,0x%llx.\n",
			dev_name(&xdev->pdev->dev), engine->name,
			engine->desc, engine->desc_bus);
		dma_free_coherent(&xdev->pdev->dev,
			XDMA_TRANSFER_MAX_DESC * sizeof(struct xdma_desc),
			engine->desc, engine->desc_bus);
		engine->desc = NULL;
	}

	if (engine->cyclic_result) {
		dma_free_coherent(&xdev->pdev->dev,
			CYCLIC_RX_PAGES_MAX * sizeof(struct xdma_result),
			engine->cyclic_result, engine->cyclic_result_bus);
		engine->cyclic_result = NULL;
	}
}

static void engine_destroy(struct xdma_dev *xdev, struct xdma_engine *engine)
{
	BUG_ON(!xdev);
	BUG_ON(!engine);

	dbg_sg("Shutting down engine %s%d", engine->name, engine->channel);

	/* Disable interrupts to stop processing new events during shutdown */
	write_register(0x0, &engine->regs->interrupt_enable_mask,
			(unsigned long)(&engine->regs->interrupt_enable_mask) -
			(unsigned long)(&engine->regs));

	if (enable_credit_mp && engine->streaming &&
		engine->dir == DMA_FROM_DEVICE) {
		u32 reg_value = (0x1 << engine->channel) << 16;
		struct sgdma_common_regs *reg = (struct sgdma_common_regs *)
				(xdev->bar[xdev->config_bar_idx] +
				 (0x6*TARGET_SPACING));	
		write_register(reg_value, &reg->credit_mode_enable_w1c, 0);
	}

	/* Release memory use for descriptor writebacks */
	engine_free_resource(engine);

	memset(engine, 0, sizeof(struct xdma_engine));
	/* Decrement the number of engines available */
	xdev->engines_num--;
}

/**
 *engine_cyclic_stop() - stop a cyclic transfer running on an SG DMA engine
 *
 *engine->lock must be taken
 */
struct xdma_transfer *engine_cyclic_stop(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer = 0;

	/* transfers on queue? */
	if (!list_empty(&engine->transfer_list)) {
		/* pick first transfer on the queue (was submitted to engine) */
		transfer = list_entry(engine->transfer_list.next,
					struct xdma_transfer, entry);
		BUG_ON(!transfer);

		xdma_engine_stop(engine);

		if (transfer->cyclic) {
			if (engine->xdma_perf)
				dbg_perf("Stopping perf transfer on %s\n",
					engine->name);
			else
				dbg_perf("Stopping cyclic transfer on %s\n",
					engine->name);
			/* make sure the handler sees correct transfer state */
			transfer->cyclic = 1;
			/*
			* set STOP flag and interrupt on completion, on the
			* last descriptor
			*/
			xdma_desc_control_set(
				transfer->desc_virt + transfer->desc_num - 1,
				XDMA_DESC_COMPLETED | XDMA_DESC_STOPPED);
		} else {
			dbg_sg("(engine=%p) running transfer is not cyclic\n",
				engine);
		}
	} else {
		dbg_sg("(engine=%p) found not running transfer.\n", engine);
	}
	return transfer;
}
EXPORT_SYMBOL_GPL(engine_cyclic_stop);

static int engine_writeback_setup(struct xdma_engine *engine)
{
	u32 w;
	struct xdma_dev *xdev;
	struct xdma_poll_wb *writeback;

	BUG_ON(!engine);
	xdev = engine->xdev;
	BUG_ON(!xdev);

	/*
	 * RTO - doing the allocation per engine is wasteful since a full page
	 * is allocated each time - better to allocate one page for the whole
	 * device during probe() and set per-engine offsets here
	 */
	writeback = (struct xdma_poll_wb *)engine->poll_mode_addr_virt;
	writeback->completed_desc_count = 0;

	dbg_init("Setting writeback location to 0x%llx for engine %p",
		engine->poll_mode_bus, engine);
	w = cpu_to_le32(PCI_DMA_L(engine->poll_mode_bus));
	write_register(w, &engine->regs->poll_mode_wb_lo, 
			(unsigned long)(&engine->regs->poll_mode_wb_lo) - 
			(unsigned long)(&engine->regs));
	w = cpu_to_le32(PCI_DMA_H(engine->poll_mode_bus));
	write_register(w, &engine->regs->poll_mode_wb_hi, 
			(unsigned long)(&engine->regs->poll_mode_wb_hi) - 
			(unsigned long)(&engine->regs));

	return 0;
}


/* engine_create() - Create an SG DMA engine bookkeeping data structure
 *
 * An SG DMA engine consists of the resources for a single-direction transfer
 * queue; the SG DMA hardware, the software queue and interrupt handling.
 *
 * @dev Pointer to pci_dev
 * @offset byte address offset in BAR[xdev->config_bar_idx] resource for the
 * SG DMA * controller registers.
 * @dir: DMA_TO/FROM_DEVICE
 * @streaming Whether the engine is attached to AXI ST (rather than MM)
 */
static int engine_init_regs(struct xdma_engine *engine)
{
	u32 reg_value;
	int rv = 0;

	write_register(XDMA_CTRL_NON_INCR_ADDR, &engine->regs->control_w1c,
			(unsigned long)(&engine->regs->control_w1c) -
			(unsigned long)(&engine->regs));

	engine_alignments(engine);

	/* Configure error interrupts by default */
	reg_value = XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
	reg_value |= XDMA_CTRL_IE_MAGIC_STOPPED;
	reg_value |= XDMA_CTRL_IE_MAGIC_STOPPED;
	reg_value |= XDMA_CTRL_IE_READ_ERROR;
	reg_value |= XDMA_CTRL_IE_DESC_ERROR;

	/* if using polled mode, configure writeback address */
	if (poll_mode) {
		rv = engine_writeback_setup(engine);
		if (rv) {
			dbg_init("%s descr writeback setup failed.\n",
				engine->name);
			goto fail_wb;
		}
	} else {
		/* enable the relevant completion interrupts */
		reg_value |= XDMA_CTRL_IE_DESC_STOPPED;
		reg_value |= XDMA_CTRL_IE_DESC_COMPLETED;

		if (engine->streaming && engine->dir == DMA_FROM_DEVICE)
			reg_value |= XDMA_CTRL_IE_IDLE_STOPPED;
	}

	/* Apply engine configurations */
	write_register(reg_value, &engine->regs->interrupt_enable_mask,
			(unsigned long)(&engine->regs->interrupt_enable_mask) -
			(unsigned long)(&engine->regs));

	engine->interrupt_enable_mask_value = reg_value;

	/* only enable credit mode for AXI-ST C2H */
	if (enable_credit_mp && engine->streaming &&
		engine->dir == DMA_FROM_DEVICE) {

		struct xdma_dev *xdev = engine->xdev;
		u32 reg_value = (0x1 << engine->channel) << 16;
		struct sgdma_common_regs *reg = (struct sgdma_common_regs *)
				(xdev->bar[xdev->config_bar_idx] +
				 (0x6*TARGET_SPACING));	

		write_register(reg_value, &reg->credit_mode_enable_w1s, 0);
	}

	return 0;

fail_wb:
	return rv;
}

static int engine_alloc_resource(struct xdma_engine *engine)
{
	struct xdma_dev *xdev = engine->xdev;

	engine->desc = dma_alloc_coherent(&xdev->pdev->dev,
			XDMA_TRANSFER_MAX_DESC * sizeof(struct xdma_desc),
			&engine->desc_bus, GFP_KERNEL);
	if (!engine->desc) {
		pr_warn("dev %s, %s pre-alloc desc OOM.\n",
			dev_name(&xdev->pdev->dev), engine->name);
		goto err_out;
	}

	if (poll_mode) {
		engine->poll_mode_addr_virt = dma_alloc_coherent(
					&xdev->pdev->dev,
					sizeof(struct xdma_poll_wb),
					&engine->poll_mode_bus, GFP_KERNEL);
		if (!engine->poll_mode_addr_virt) {
                        pr_warn("%s, %s poll pre-alloc writeback OOM.\n",
				dev_name(&xdev->pdev->dev), engine->name);
			goto err_out;
		}
	}

	if (engine->streaming && engine->dir == DMA_FROM_DEVICE) {
		engine->cyclic_result = dma_alloc_coherent(&xdev->pdev->dev,
			CYCLIC_RX_PAGES_MAX * sizeof(struct xdma_result),
			&engine->cyclic_result_bus, GFP_KERNEL);

		if (!engine->cyclic_result) {
                        pr_warn("%s, %s pre-alloc result OOM.\n",
				dev_name(&xdev->pdev->dev), engine->name);
			goto err_out;
		}
	}

	return 0;

err_out:
	engine_free_resource(engine);
	return -ENOMEM;
}

static int engine_init(struct xdma_engine *engine, struct xdma_dev *xdev,
			int offset, enum dma_data_direction dir, int channel)
{
	int rv;
	u32 val;

	dbg_init("channel %d, offset 0x%x, dir %d.\n", channel, offset, dir);

	/* set magic */
	engine->magic = MAGIC_ENGINE;

	engine->channel = channel;

	/* engine interrupt request bit */
	engine->irq_bitmask = (1 << XDMA_ENG_IRQ_NUM) - 1;
	engine->irq_bitmask <<= (xdev->engines_num * XDMA_ENG_IRQ_NUM);
	engine->bypass_offset = xdev->engines_num * BYPASS_MODE_SPACING;

	/* parent */
	engine->xdev = xdev;
	/* register address */
	engine->regs = (xdev->bar[xdev->config_bar_idx] + offset);
	engine->sgdma_regs = xdev->bar[xdev->config_bar_idx] + offset +
				SGDMA_OFFSET_FROM_CHANNEL;
	val = read_register(&engine->regs->identifier);
        if (val & 0x8000U)
		engine->streaming = 1;

	/* remember SG DMA direction */
	engine->dir = dir;
	sprintf(engine->name, "%d-%s%d-%s", xdev->idx,
		(dir == DMA_TO_DEVICE) ? "H2C" : "C2H", channel,
		engine->streaming ? "ST" : "MM");

	dbg_init("engine %p name %s irq_bitmask=0x%08x\n", engine, engine->name,
		(int)engine->irq_bitmask);

	/* initialize the deferred work for transfer completion */
	INIT_WORK(&engine->work, engine_service_work);

	if (dir == DMA_TO_DEVICE)
		xdev->mask_irq_h2c |= engine->irq_bitmask;
	else
		xdev->mask_irq_c2h |= engine->irq_bitmask;
	xdev->engines_num++;

	rv = engine_alloc_resource(engine);
	if (rv)
		return rv;

	rv = engine_init_regs(engine);
	if (rv)
		return rv;

	return 0;
}

/* transfer_destroy() - free transfer */
static void transfer_destroy(struct xdma_dev *xdev, struct xdma_transfer *xfer)
{
	/* free descriptors */
	xdma_desc_done(xfer->desc_virt);

	if (xfer->last_in_request && (xfer->flags & XFER_FLAG_NEED_UNMAP)) {
        	struct sg_table *sgt = xfer->sgt;

		if (sgt->nents) {
			pci_unmap_sg(xdev->pdev, sgt->sgl, sgt->nents,
				xfer->dir);
			sgt->nents = 0;
		}
	}
}

static int transfer_build(struct xdma_engine *engine,
			struct xdma_request_cb *req, unsigned int desc_max)
{
	struct xdma_transfer *xfer = &req->xfer;
	struct sw_desc *sdesc = &(req->sdesc[req->sw_desc_idx]);
	int i = 0;
	int j = 0;

	for (; i < desc_max; i++, j++, sdesc++) {
		dbg_desc("sw desc %d/%u: 0x%llx, 0x%x, ep 0x%llx.\n",
			i + req->sw_desc_idx, req->sw_desc_cnt,
			sdesc->addr, sdesc->len, req->ep_addr);

		/* fill in descriptor entry j with transfer details */
		xdma_desc_set(xfer->desc_virt + j, sdesc->addr, req->ep_addr,
				 sdesc->len, xfer->dir);
		xfer->len += sdesc->len;

		/* for non-inc-add mode don't increment ep_addr */
		if (!engine->non_incr_addr)
			req->ep_addr += sdesc->len;
	}
	req->sw_desc_idx += desc_max; 
	return 0;
}

static int transfer_init(struct xdma_engine *engine, struct xdma_request_cb *req)
{
	struct xdma_transfer *xfer = &req->xfer;
	unsigned int desc_max = min_t(unsigned int,
				req->sw_desc_cnt - req->sw_desc_idx,
				XDMA_TRANSFER_MAX_DESC);
	int i = 0;
	int last = 0;
	u32 control;

	memset(xfer, 0, sizeof(*xfer));

	/* initialize wait queue */
	init_waitqueue_head(&xfer->wq);

	/* remember direction of transfer */
	xfer->dir = engine->dir;

	xfer->desc_virt = engine->desc;
	xfer->desc_bus = engine->desc_bus;

	transfer_desc_init(xfer, desc_max);
	
	dbg_sg("transfer->desc_bus = 0x%llx.\n", (u64)xfer->desc_bus);

	transfer_build(engine, req, desc_max);

	/* terminate last descriptor */
	last = desc_max - 1;
	xdma_desc_link(xfer->desc_virt + last, 0, 0);
	/* stop engine, EOP for AXI ST, req IRQ on last descriptor */
	control = XDMA_DESC_STOPPED;
	control |= XDMA_DESC_EOP;
	control |= XDMA_DESC_COMPLETED;
	xdma_desc_control_set(xfer->desc_virt + last, control);

	xfer->desc_num = xfer->desc_adjacent = desc_max;

	dbg_sg("transfer 0x%p has %d descriptors\n", xfer, xfer->desc_num);
	/* fill in adjacent numbers */
	for (i = 0; i < xfer->desc_num; i++)
		xdma_desc_adjacent(xfer->desc_virt + i, xfer->desc_num - i - 1);

	return 0;
}

#ifdef __LIBXDMA_DEBUG__
static void sgt_dump(struct sg_table *sgt)
{
	int i;
	struct scatterlist *sg = sgt->sgl;

	pr_info("sgt 0x%p, sgl 0x%p, nents %u/%u.\n",
		sgt, sgt->sgl, sgt->nents, sgt->orig_nents);

	for (i = 0; i < sgt->orig_nents; i++, sg = sg_next(sg))
		pr_info("%d, 0x%p, pg 0x%p,%u+%u, dma 0x%llx,%u.\n",
			i, sg, sg_page(sg), sg->offset, sg->length,
			sg_dma_address(sg), sg_dma_len(sg)); 
}

static void xdma_request_cb_dump(struct xdma_request_cb *req)
{
	int i;

	pr_info("request 0x%p, total %u, ep 0x%llx, sw_desc %u, sgt 0x%p.\n",
		req, req->total_len, req->ep_addr, req->sw_desc_cnt, req->sgt);
	sgt_dump(req->sgt);
	for (i = 0; i < req->sw_desc_cnt; i++)
		pr_info("%d/%u, 0x%llx, %u.\n",
			i, req->sw_desc_cnt, req->sdesc[i].addr,
			req->sdesc[i].len);
}
#endif

static void xdma_request_free(struct xdma_request_cb *req)
{
	if (((unsigned long)req) >= VMALLOC_START &&
	    ((unsigned long)req) < VMALLOC_END)
		vfree(req);
	else
		kfree(req);
}

static struct xdma_request_cb * xdma_request_alloc(unsigned int sdesc_nr)
{
	struct xdma_request_cb *req;
	unsigned int size = sizeof(struct xdma_request_cb) +
				sdesc_nr * sizeof(struct sw_desc);

	req = kzalloc(size, GFP_KERNEL);
	if (!req) {
		req = vmalloc(size);
		if (req)
			memset(req, 0, size);
	}
	if (!req) {
		pr_info("OOM, %u sw_desc, %u.\n", sdesc_nr, size);
		return NULL;
	}

	return req;
}

static struct xdma_request_cb * xdma_init_request(struct sg_table *sgt,
						u64 ep_addr)
{
	struct xdma_request_cb *req;
	struct scatterlist *sg = sgt->sgl;
	int max = sgt->nents;
	int extra = 0;
	int i, j = 0;

	for (i = 0;  i < max; i++, sg = sg_next(sg)) {
		unsigned int len = sg_dma_len(sg);

		if (unlikely(len > desc_blen_max))
			extra += (len + desc_blen_max - 1) / desc_blen_max;
	}

//pr_info("ep 0x%llx, desc %u+%u.\n", ep_addr, max, extra);

	max += extra;
	req = xdma_request_alloc(max);
	if (!req)
		return NULL;

	req->sgt = sgt;	
	req->ep_addr = ep_addr;

	for (i = 0, sg = sgt->sgl;  i < sgt->nents; i++, sg = sg_next(sg)) {
		unsigned int tlen = sg_dma_len(sg);
		dma_addr_t addr = sg_dma_address(sg);	

		req->total_len += tlen;
		while (tlen) {
			req->sdesc[j].addr = addr;
			if (tlen > desc_blen_max) {
				req->sdesc[j].len = desc_blen_max;
				addr += desc_blen_max;
				tlen -= desc_blen_max;	
			} else {
				req->sdesc[j].len = tlen;
				tlen = 0;
			}
			j++;
		}
	}
	BUG_ON(j > max);

	req->sw_desc_cnt = j;
#ifdef __LIBXDMA_DEBUG__
	xdma_request_cb_dump(req);
#endif
	return req;
}

ssize_t xdma_xfer_submit(void *dev_hndl, int channel, bool write, u64 ep_addr,
			struct sg_table *sgt, bool dma_mapped, int timeout_ms)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;
	struct xdma_engine *engine;
	int rv = 0;
	ssize_t done = 0;
	struct scatterlist *sg = sgt->sgl;
	int nents;
	enum dma_data_direction dir = write ? DMA_TO_DEVICE : DMA_FROM_DEVICE;
	struct xdma_request_cb *req = NULL;

	if (!dev_hndl)
		return -EINVAL;

	if (debug_check_dev_hndl(__func__, xdev->pdev, dev_hndl) < 0)
		return -EINVAL;

	if (write == 1) {
		if (channel >= xdev->h2c_channel_max) {
			pr_warn("H2C channel %d >= %d.\n",
				channel, xdev->h2c_channel_max);
			return -EINVAL;
		}
		engine = &xdev->engine_h2c[channel];
	} else if (write == 0) {
		if (channel >= xdev->c2h_channel_max) {
			pr_warn("C2H channel %d >= %d.\n",
				channel, xdev->c2h_channel_max);
			return -EINVAL;
		}
		engine = &xdev->engine_c2h[channel];
	} else {
		pr_warn("write %d, exp. 0|1.\n", write);
		return -EINVAL;
	}

        BUG_ON(!engine);
        BUG_ON(engine->magic != MAGIC_ENGINE);

	xdev = engine->xdev;
	if (xdma_device_flag_check(xdev, XDEV_FLAG_OFFLINE)) {
		pr_info("xdev 0x%p, offline.\n", xdev);
		return -EBUSY;
	}

	/* check the direction */
	if (engine->dir != dir) {
		pr_info("0x%p, %s, %d, W %d, 0x%x/0x%x mismatch.\n",
			engine, engine->name, channel, write, engine->dir, dir);
		return -EINVAL;
	}

	if (!dma_mapped) {
		nents = pci_map_sg(xdev->pdev, sg, sgt->orig_nents, dir);
		if (!nents) {
			pr_info("map sgl failed, sgt 0x%p.\n", sgt);
			return -EIO;
		}
		sgt->nents = nents;
	} else {
		BUG_ON(!sgt->nents);
	}

	req = xdma_init_request(sgt, ep_addr);
	if (!req) {
		rv = -ENOMEM;
		goto unmap_sgl;
	}

	dbg_tfr("%s, len %u sg cnt %u.\n",
		engine->name, req->total_len, req->sw_desc_cnt);

	sg = sgt->sgl;
	nents = req->sw_desc_cnt;
	while (nents) {
		unsigned long flags;
		struct xdma_transfer *xfer;

		/* one transfer at a time */
		spin_lock(&engine->desc_lock);

		/* build transfer */	
		rv = transfer_init(engine, req);
		if (rv < 0) {
			spin_unlock(&engine->desc_lock);
			goto unmap_sgl;
		}
		xfer = &req->xfer;

		if (!dma_mapped)
			xfer->flags = XFER_FLAG_NEED_UNMAP;

		/* last transfer for the given request? */
		nents -= xfer->desc_num;
		if (!nents) {
			xfer->last_in_request = 1;
			xfer->sgt = sgt;
		}

		dbg_tfr("xfer, %u, ep 0x%llx, done %lu, sg %u/%u.\n",
			xfer->len, req->ep_addr, done, req->sw_desc_idx,
			req->sw_desc_cnt);

#ifdef __LIBXDMA_DEBUG__
		transfer_dump(xfer);
#endif

		rv = transfer_queue(engine, xfer);
		if (rv < 0) {
			spin_unlock(&engine->desc_lock);
			pr_info("unable to submit %s, %d.\n", engine->name, rv);
			goto unmap_sgl;
		}

		/*
		 * When polling, determine how many descriptors have been queued		 * on the engine to determine the writeback value expected
		 */
		if (poll_mode) {
			unsigned int desc_count;

			spin_lock_irqsave(&engine->lock, flags);
                        desc_count = xfer->desc_num;
			spin_unlock_irqrestore(&engine->lock, flags);

                        dbg_tfr("%s poll desc_count=%d\n",
				engine->name, desc_count);
			rv = engine_service_poll(engine, desc_count);

		} else {
			rv = wait_event_interruptible_timeout(xfer->wq,
                	        (xfer->state != TRANSFER_STATE_SUBMITTED),
				msecs_to_jiffies(timeout_ms));
		}

		spin_lock_irqsave(&engine->lock, flags);

		switch(xfer->state) {
		case TRANSFER_STATE_COMPLETED:
			spin_unlock_irqrestore(&engine->lock, flags);

			dbg_tfr("transfer %p, %u, ep 0x%llx compl, +%lu.\n",
				xfer, xfer->len, req->ep_addr - xfer->len, done);
			done += xfer->len;
			rv = 0;
			break;
		case TRANSFER_STATE_FAILED:
			pr_info("xfer 0x%p,%u, failed, ep 0x%llx.\n",
				 xfer, xfer->len, req->ep_addr - xfer->len);
			spin_unlock_irqrestore(&engine->lock, flags);

#ifdef __LIBXDMA_DEBUG__
			transfer_dump(xfer);
			sgt_dump(sgt);
#endif
			rv = -EIO;
			break;
		default:
			/* transfer can still be in-flight */
			pr_info("xfer 0x%p,%u, s 0x%x timed out, ep 0x%llx.\n",
				 xfer, xfer->len, xfer->state, req->ep_addr);
			engine_status_read(engine, 0, 1);
			//engine_status_dump(engine);
			transfer_abort(engine, xfer);

			xdma_engine_stop(engine);
			spin_unlock_irqrestore(&engine->lock, flags);

#ifdef __LIBXDMA_DEBUG__
			transfer_dump(xfer);
			sgt_dump(sgt);
#endif
			rv = -ERESTARTSYS;
			break;
		}

		transfer_destroy(xdev, xfer);
		spin_unlock(&engine->desc_lock);

		if (rv < 0)
			goto unmap_sgl;
	} /* while (sg) */

unmap_sgl:
	if (!dma_mapped && sgt->nents) {
		pci_unmap_sg(xdev->pdev, sgt->sgl, sgt->orig_nents, dir);
		sgt->nents = 0;
	}

	if (req)
		xdma_request_free(req);

	if (rv < 0)
		return rv;

	return done;
}
EXPORT_SYMBOL_GPL(xdma_xfer_submit);

int xdma_performance_submit(struct xdma_dev *xdev, struct xdma_engine *engine)
{
	u8 *buffer_virt;
	u32 max_consistent_size = 128 * 32 * 1024; /* 1024 pages, 4MB */
	dma_addr_t buffer_bus;	/* bus address */
	struct xdma_transfer *transfer;
	u64 ep_addr = 0;
	int num_desc_in_a_loop = 128;
	int size_in_desc = engine->xdma_perf->transfer_size;
	int size = size_in_desc * num_desc_in_a_loop;
	int i;

	BUG_ON(size_in_desc > max_consistent_size);

	if (size > max_consistent_size) {
		size = max_consistent_size;
		num_desc_in_a_loop = size / size_in_desc;
	}

	buffer_virt = dma_alloc_coherent(&xdev->pdev->dev, size,
					&buffer_bus, GFP_KERNEL);

	/* allocate transfer data structure */
	transfer = kzalloc(sizeof(struct xdma_transfer), GFP_KERNEL);
	BUG_ON(!transfer);

	/* 0 = write engine (to_dev=0) , 1 = read engine (to_dev=1) */
	transfer->dir = engine->dir;
	/* set number of descriptors */
	transfer->desc_num = num_desc_in_a_loop;

	/* allocate descriptor list */
	if (!engine->desc) {
		engine->desc = dma_alloc_coherent(&xdev->pdev->dev,
			num_desc_in_a_loop * sizeof(struct xdma_desc),
			&engine->desc_bus, GFP_KERNEL);
		BUG_ON(!engine->desc);
		dbg_init("device %s, engine %s pre-alloc desc 0x%p,0x%llx.\n",
			dev_name(&xdev->pdev->dev), engine->name,
			engine->desc, engine->desc_bus);
	}
	transfer->desc_virt = engine->desc;
	transfer->desc_bus = engine->desc_bus;

	transfer_desc_init(transfer, transfer->desc_num);

	dbg_sg("transfer->desc_bus = 0x%llx.\n", (u64)transfer->desc_bus);

	for (i = 0; i < transfer->desc_num; i++) {
		struct xdma_desc *desc = transfer->desc_virt + i;
		dma_addr_t rc_bus_addr = buffer_bus + size_in_desc * i;

		/* fill in descriptor entry with transfer details */
		xdma_desc_set(desc, rc_bus_addr, ep_addr, size_in_desc,
			engine->dir);
	}

	/* stop engine and request interrupt on last descriptor */
	xdma_desc_control_set(transfer->desc_virt, 0);
	/* create a linked loop */
	xdma_desc_link(transfer->desc_virt + transfer->desc_num - 1,
		transfer->desc_virt, transfer->desc_bus);

	transfer->cyclic = 1;

	/* initialize wait queue */
	init_waitqueue_head(&transfer->wq);

	//printk("=== Descriptor print for PERF \n");
	//transfer_dump(transfer);

	dbg_perf("Queueing XDMA I/O %s request for performance measurement.\n",
		engine->dir ? "write (to dev)" : "read (from dev)");
	transfer_queue(engine, transfer);
	return 0;

}
EXPORT_SYMBOL_GPL(xdma_performance_submit);

static struct xdma_dev *alloc_dev_instance(struct pci_dev *pdev)
{
	int i;
	struct xdma_dev *xdev;
	struct xdma_engine *engine;

	BUG_ON(!pdev);

	/* allocate zeroed device book keeping structure */
	xdev = kzalloc(sizeof(struct xdma_dev), GFP_KERNEL);
	if (!xdev) {
		pr_info("OOM, xdma_dev.\n");
		return NULL;
	}
	spin_lock_init(&xdev->lock);

	xdev->magic = MAGIC_DEVICE;
	xdev->config_bar_idx = -1;
	xdev->user_bar_idx = -1;
	xdev->bypass_bar_idx = -1;
	xdev->irq_line = -1;

	/* create a driver to device reference */
	xdev->pdev = pdev;
	dbg_init("xdev = 0x%p\n", xdev);

	/* Set up data user IRQ data structures */
	for (i = 0; i < 16; i++) {
		xdev->user_irq[i].xdev = xdev;
		spin_lock_init(&xdev->user_irq[i].events_lock);
		init_waitqueue_head(&xdev->user_irq[i].events_wq);
		xdev->user_irq[i].handler = NULL;
		xdev->user_irq[i].user_idx = i; /* 0 based */
	}

	engine = xdev->engine_h2c;
	for (i = 0; i < XDMA_CHANNEL_NUM_MAX; i++, engine++) {
		spin_lock_init(&engine->lock);
		spin_lock_init(&engine->desc_lock);
		INIT_LIST_HEAD(&engine->transfer_list);
		init_waitqueue_head(&engine->shutdown_wq);
		init_waitqueue_head(&engine->xdma_perf_wq);
	}

	engine = xdev->engine_c2h;
	for (i = 0; i < XDMA_CHANNEL_NUM_MAX; i++, engine++) {
		spin_lock_init(&engine->lock);
		spin_lock_init(&engine->desc_lock);
		INIT_LIST_HEAD(&engine->transfer_list);
		init_waitqueue_head(&engine->shutdown_wq);
		init_waitqueue_head(&engine->xdma_perf_wq);
	}

	return xdev;
}

static int request_regions(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	int rv;

	BUG_ON(!xdev);
	BUG_ON(!pdev);

	dbg_init("pci_request_regions()\n");
	rv = pci_request_regions(pdev, xdev->mod_name);
	/* could not request all regions? */
	if (rv) {
		dbg_init("pci_request_regions() = %d, device in use?\n", rv);
		/* assume device is in use so do not disable it later */
		xdev->regions_in_use = 1;
	} else {
		xdev->got_regions = 1;
	}

	return rv;
}

static int set_dma_mask(struct pci_dev *pdev)
{
	BUG_ON(!pdev);

	dbg_init("sizeof(dma_addr_t) == %ld\n", sizeof(dma_addr_t));
	/* 64-bit addressing capability for XDMA? */
	if (!pci_set_dma_mask(pdev, DMA_BIT_MASK(64))) {
		/* query for DMA transfer */
		/* @see Documentation/DMA-mapping.txt */
		dbg_init("pci_set_dma_mask()\n");
		/* use 64-bit DMA */
		dbg_init("Using a 64-bit DMA mask.\n");
		/* use 32-bit DMA for descriptors */
		pci_set_consistent_dma_mask(pdev, DMA_BIT_MASK(32));
		/* use 64-bit DMA, 32-bit for consistent */
	} else if (!pci_set_dma_mask(pdev, DMA_BIT_MASK(32))) {
		dbg_init("Could not set 64-bit DMA mask.\n");
		pci_set_consistent_dma_mask(pdev, DMA_BIT_MASK(32));
		/* use 32-bit DMA */
		dbg_init("Using a 32-bit DMA mask.\n");
	} else {
		dbg_init("No suitable DMA possible.\n");
		return -EINVAL;
	}

	return 0;
}

static u32 get_engine_channel_id(struct engine_regs *regs)
{
	u32 value;

	BUG_ON(!regs);

	value = read_register(&regs->identifier);

	return (value & 0x00000f00U) >> 8;
}

static u32 get_engine_id(struct engine_regs *regs)
{
	u32 value;

	BUG_ON(!regs);

	value = read_register(&regs->identifier);
	return (value & 0xffff0000U) >> 16;
}

static void remove_engines(struct xdma_dev *xdev)
{
	struct xdma_engine *engine;
	int i;

	BUG_ON(!xdev);

	/* iterate over channels */
	for (i = 0; i < xdev->h2c_channel_max; i++) {
		engine = &xdev->engine_h2c[i];
		if (engine->magic == MAGIC_ENGINE) {
			dbg_sg("Remove %s, %d", engine->name, i);
			engine_destroy(xdev, engine);
			dbg_sg("%s, %d removed", engine->name, i);
		}
	}

	for (i = 0; i < xdev->c2h_channel_max; i++) {
		engine = &xdev->engine_c2h[i];
		if (engine->magic == MAGIC_ENGINE) {
			dbg_sg("Remove %s, %d", engine->name, i);
			engine_destroy(xdev, engine);
			dbg_sg("%s, %d removed", engine->name, i);
		}
	}
}

static int probe_for_engine(struct xdma_dev *xdev, enum dma_data_direction dir,
			int channel)
{
	struct engine_regs *regs;
	int offset = channel * CHANNEL_SPACING;
	u32 engine_id;
	u32 engine_id_expected;
	u32 channel_id;
	struct xdma_engine *engine;
	int rv;

	/* register offset for the engine */
	/* read channels at 0x0000, write channels at 0x1000,
	 * channels at 0x100 interval */
	if (dir == DMA_TO_DEVICE) {
		engine_id_expected = XDMA_ID_H2C;
		engine = &xdev->engine_h2c[channel];
	} else {
		offset += H2C_CHANNEL_OFFSET;
		engine_id_expected = XDMA_ID_C2H;
		engine = &xdev->engine_c2h[channel];
	}

	regs = xdev->bar[xdev->config_bar_idx] + offset;
	engine_id = get_engine_id(regs);
	channel_id = get_engine_channel_id(regs);

	if ((engine_id != engine_id_expected) || (channel_id != channel)) {
		dbg_init("%s %d engine, reg off 0x%x, id mismatch 0x%x,0x%x,"
			"exp 0x%x,0x%x, SKIP.\n",
		 	dir == DMA_TO_DEVICE ? "H2C" : "C2H",
			 channel, offset, engine_id, channel_id,
			engine_id_expected, channel_id != channel);
		return -EINVAL;
	}

	dbg_init("found AXI %s %d engine, reg. off 0x%x, id 0x%x,0x%x.\n",
		 dir == DMA_TO_DEVICE ? "H2C" : "C2H", channel,
		 offset, engine_id, channel_id);

	/* allocate and initialize engine */
	rv = engine_init(engine, xdev, offset, dir, channel);
	if (rv != 0) {
		pr_info("failed to create AXI %s %d engine.\n",
			dir == DMA_TO_DEVICE ? "H2C" : "C2H",
			channel);
		return rv;
	}

	return 0;
}

static int probe_engines(struct xdma_dev *xdev)
{
	int i;
	int rv = 0;

	BUG_ON(!xdev);

	/* iterate over channels */
	for (i = 0; i < xdev->h2c_channel_max; i++) {
		rv = probe_for_engine(xdev, DMA_TO_DEVICE, i);
		if (rv)
			break;
	}
	xdev->h2c_channel_max = i;

	for (i = 0; i < xdev->c2h_channel_max; i++) {
		rv = probe_for_engine(xdev, DMA_FROM_DEVICE, i);
		if (rv)
			break;
	}
	xdev->c2h_channel_max = i;

	return 0;
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(3,5,0)
static void pci_enable_relaxed_ordering(struct pci_dev *pdev)
{
	pcie_capability_set_word(pdev, PCI_EXP_DEVCTL, PCI_EXP_DEVCTL_RELAX_EN);
}
#else
static void pci_enable_relaxed_ordering(struct pci_dev *pdev)
{
	u16 v;
	int pos;

	pos = pci_pcie_cap(pdev);
	if (pos > 0) {
		pci_read_config_word(pdev, pos + PCI_EXP_DEVCTL, &v);
		v |= PCI_EXP_DEVCTL_RELAX_EN;
		pci_write_config_word(pdev, pos + PCI_EXP_DEVCTL, v);
	}
}
#endif

static void pci_check_extended_tag(struct xdma_dev *xdev, struct pci_dev *pdev)
{
	u16 cap;
	u32 v;
	void *__iomem reg;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(3,5,0)
	pcie_capability_read_word(pdev, PCI_EXP_DEVCTL, &cap);
#else
	int pos;

	pos = pci_pcie_cap(pdev);
	if (pos > 0)
		pci_read_config_word(pdev, pos + PCI_EXP_DEVCTL, &cap);
	else {
		pr_info("pdev 0x%p, unable to access pcie cap.\n", pdev);
		return;
	}
#endif

	if ((cap & PCI_EXP_DEVCTL_EXT_TAG))
		return;

	/* extended tag not enabled */
	pr_info("0x%p EXT_TAG disabled.\n", pdev);

	if (xdev->config_bar_idx < 0) {
		pr_info("pdev 0x%p, xdev 0x%p, config bar UNKNOWN.\n",
			pdev, xdev);
                return;
	}

	reg = xdev->bar[xdev->config_bar_idx] + XDMA_OFS_CONFIG + 0x4C;
	v =  read_register(reg);
	v = (v & 0xFF) | (((u32)32) << 8);
	write_register(v, reg, XDMA_OFS_CONFIG + 0x4C);
}

void *xdma_device_open(const char *mname, struct pci_dev *pdev, int *user_max,
			int *h2c_channel_max, int *c2h_channel_max)
{
	struct xdma_dev *xdev = NULL;
	int rv = 0;

	pr_info("%s device %s, 0x%p.\n", mname, dev_name(&pdev->dev), pdev);

	/* allocate zeroed device book keeping structure */
	xdev = alloc_dev_instance(pdev);
	if (!xdev)
		return NULL;
	xdev->mod_name = mname;
	xdev->user_max = *user_max;
	xdev->h2c_channel_max = *h2c_channel_max;
	xdev->c2h_channel_max = *c2h_channel_max;

	xdma_device_flag_set(xdev, XDEV_FLAG_OFFLINE);
	xdev_list_add(xdev);

	if (xdev->user_max == 0 || xdev->user_max > MAX_USER_IRQ)
		xdev->user_max = MAX_USER_IRQ;
	if (xdev->h2c_channel_max == 0 ||
	    xdev->h2c_channel_max > XDMA_CHANNEL_NUM_MAX) 
		xdev->h2c_channel_max = XDMA_CHANNEL_NUM_MAX;
	if (xdev->c2h_channel_max == 0 ||
	    xdev->c2h_channel_max > XDMA_CHANNEL_NUM_MAX) 
		xdev->c2h_channel_max = XDMA_CHANNEL_NUM_MAX;
		
	rv = pci_enable_device(pdev);
	if (rv) {
		dbg_init("pci_enable_device() failed, %d.\n", rv);
		goto err_enable;
	}

	/* keep INTx enabled */
	pci_check_intr_pend(pdev);

	/* enable relaxed ordering */
	pci_enable_relaxed_ordering(pdev);

	pci_check_extended_tag(xdev, pdev);

	/* force MRRS to be 512 */
	rv = pcie_set_readrq(pdev, 512);
	if (rv)
		pr_info("device %s, error set PCI_EXP_DEVCTL_READRQ: %d.\n",
			dev_name(&pdev->dev), rv);

	/* enable bus master capability */
	pci_set_master(pdev);

	rv = request_regions(xdev, pdev);
	if (rv)
		goto err_regions;

	rv = map_bars(xdev, pdev);
	if (rv)
		goto err_map;

	rv = set_dma_mask(pdev);
	if (rv)
		goto err_mask;

	check_nonzero_interrupt_status(xdev);
	/* explicitely zero all interrupt enable masks */
	channel_interrupts_disable(xdev, ~0);
	user_interrupts_disable(xdev, ~0);
	read_interrupts(xdev);

	rv = probe_engines(xdev);
	if (rv)
		goto err_engines;

	rv = enable_msi_msix(xdev, pdev);
	if (rv < 0)
		goto err_enable_msix;

	rv = irq_setup(xdev, pdev);
	if (rv < 0)
		goto err_interrupts;

	if (!poll_mode)
		channel_interrupts_enable(xdev, ~0);

	/* Flush writes */
	read_interrupts(xdev);

	*user_max = xdev->user_max;
	*h2c_channel_max = xdev->h2c_channel_max;
	*c2h_channel_max = xdev->c2h_channel_max;

	xdma_device_flag_clear(xdev, XDEV_FLAG_OFFLINE);
	return (void *)xdev;

err_interrupts:
	irq_teardown(xdev);
err_enable_msix:
	disable_msi_msix(xdev, pdev);
err_engines:
	remove_engines(xdev);
err_mask:
	unmap_bars(xdev, pdev);
err_map:
	if (xdev->got_regions)
		pci_release_regions(pdev);
err_regions:
	if (!xdev->regions_in_use)
		pci_disable_device(pdev);
err_enable:
	xdev_list_remove(xdev);
	kfree(xdev);
	return NULL;
}
EXPORT_SYMBOL_GPL(xdma_device_open);

void xdma_device_close(struct pci_dev *pdev, void *dev_hndl)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;

	dbg_init("pdev 0x%p, xdev 0x%p.\n", pdev, dev_hndl);

	if (!dev_hndl)
		return;

	if (debug_check_dev_hndl(__func__, pdev, dev_hndl) < 0)
		return;

	dbg_sg("remove(dev = 0x%p) where pdev->dev.driver_data = 0x%p\n",
		   pdev, xdev);
	if (xdev->pdev != pdev) {
		dbg_sg("pci_dev(0x%lx) != pdev(0x%lx)\n",
			(unsigned long)xdev->pdev, (unsigned long)pdev);
	}

	channel_interrupts_disable(xdev, ~0);
	user_interrupts_disable(xdev, ~0);
	read_interrupts(xdev);

	irq_teardown(xdev);
	disable_msi_msix(xdev, pdev);

	remove_engines(xdev);
	unmap_bars(xdev, pdev);

	if (xdev->got_regions) {
		dbg_init("pci_release_regions 0x%p.\n", pdev);
		pci_release_regions(pdev);
	}

	if (!xdev->regions_in_use) {
		dbg_init("pci_disable_device 0x%p.\n", pdev);
		pci_disable_device(pdev);
	}

	xdev_list_remove(xdev);

	kfree(xdev);
}
EXPORT_SYMBOL_GPL(xdma_device_close);

void xdma_device_offline(struct pci_dev *pdev, void *dev_hndl)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;
	struct xdma_engine *engine;
	int i;

	if (!dev_hndl)
		return;

	if (debug_check_dev_hndl(__func__, pdev, dev_hndl) < 0)
		return;

pr_info("pdev 0x%p, xdev 0x%p.\n", pdev, xdev);
	xdma_device_flag_set(xdev, XDEV_FLAG_OFFLINE);

	/* wait for all engines to be idle */
	for (i  = 0; i < xdev->h2c_channel_max; i++) {
		unsigned long flags;

		engine = &xdev->engine_h2c[i];
		
		if (engine->magic == MAGIC_ENGINE) {
			spin_lock_irqsave(&engine->lock, flags);
			engine->shutdown |= ENGINE_SHUTDOWN_REQUEST;

			xdma_engine_stop(engine);
			engine->running = 0;
			spin_unlock_irqrestore(&engine->lock, flags);
		}
	}

	for (i  = 0; i < xdev->c2h_channel_max; i++) {
		unsigned long flags;

		engine = &xdev->engine_c2h[i];
		if (engine->magic == MAGIC_ENGINE) {
			spin_lock_irqsave(&engine->lock, flags);
			engine->shutdown |= ENGINE_SHUTDOWN_REQUEST;

			xdma_engine_stop(engine);
			engine->running = 0;
			spin_unlock_irqrestore(&engine->lock, flags);
		}
	}

	/* turn off interrupts */
	channel_interrupts_disable(xdev, ~0);
	user_interrupts_disable(xdev, ~0);
	read_interrupts(xdev);
	irq_teardown(xdev);

	pr_info("xdev 0x%p, done.\n", xdev);
}
EXPORT_SYMBOL_GPL(xdma_device_offline);

void xdma_device_online(struct pci_dev *pdev, void *dev_hndl)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;
	struct xdma_engine *engine;
	unsigned long flags;
	int i;

	if (!dev_hndl)
		return;

	if (debug_check_dev_hndl(__func__, pdev, dev_hndl) < 0)
		return;

pr_info("pdev 0x%p, xdev 0x%p.\n", pdev, xdev);

	for (i  = 0; i < xdev->h2c_channel_max; i++) {
		engine = &xdev->engine_h2c[i];
		if (engine->magic == MAGIC_ENGINE) {
			engine_init_regs(engine);
			spin_lock_irqsave(&engine->lock, flags);
			engine->shutdown &= ~ENGINE_SHUTDOWN_REQUEST;
			spin_unlock_irqrestore(&engine->lock, flags);
		}
	}

	for (i  = 0; i < xdev->c2h_channel_max; i++) {
		engine = &xdev->engine_c2h[i];
		if (engine->magic == MAGIC_ENGINE) {
			engine_init_regs(engine);
			spin_lock_irqsave(&engine->lock, flags);
			engine->shutdown &= ~ENGINE_SHUTDOWN_REQUEST;
			spin_unlock_irqrestore(&engine->lock, flags);
		}
	}

	/* re-write the interrupt table */
	if (!poll_mode) {
		irq_setup(xdev, pdev);

		channel_interrupts_enable(xdev, ~0);
		user_interrupts_enable(xdev, xdev->mask_irq_user);
		read_interrupts(xdev);
	}
	
	xdma_device_flag_clear(xdev, XDEV_FLAG_OFFLINE);
pr_info("xdev 0x%p, done.\n", xdev);
}
EXPORT_SYMBOL_GPL(xdma_device_online);

int xdma_device_restart(struct pci_dev *pdev, void *dev_hndl)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;

	if (!dev_hndl)
		return -EINVAL;

	if (debug_check_dev_hndl(__func__, pdev, dev_hndl) < 0)
		return -EINVAL;

	pr_info("NOT implemented, 0x%p.\n", xdev);
	return -EINVAL;
}
EXPORT_SYMBOL_GPL(xdma_device_restart);

int xdma_user_isr_register(void *dev_hndl, unsigned int mask,
			irq_handler_t handler, void *dev)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;
	int i;

	if (!dev_hndl)
		return -EINVAL;

	if (debug_check_dev_hndl(__func__, xdev->pdev, dev_hndl) < 0)
		return -EINVAL;

	for (i = 0; i < xdev->user_max && mask; i++) {
		unsigned int bit = (1 << i);

		if ((bit & mask) == 0)
			continue;

		mask &= ~bit;
		xdev->user_irq[i].handler = handler;
		xdev->user_irq[i].dev = dev;
	}

	return 0;
}
EXPORT_SYMBOL_GPL(xdma_user_isr_register);

int xdma_user_isr_enable(void *dev_hndl, unsigned int mask)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;

	if (!dev_hndl)
		return -EINVAL;

	if (debug_check_dev_hndl(__func__, xdev->pdev, dev_hndl) < 0)
		return -EINVAL;

	xdev->mask_irq_user |= mask;
	/* enable user interrupts */
	user_interrupts_enable(xdev, mask);
	read_interrupts(xdev);

	return 0;
}
EXPORT_SYMBOL_GPL(xdma_user_isr_enable);

int xdma_user_isr_disable(void *dev_hndl, unsigned int mask)
{
	struct xdma_dev *xdev = (struct xdma_dev *)dev_hndl;

	if (!dev_hndl)
		return -EINVAL;

	if (debug_check_dev_hndl(__func__, xdev->pdev, dev_hndl) < 0)
		return -EINVAL;
	
	xdev->mask_irq_user &= ~mask;
	user_interrupts_disable(xdev, mask);
	read_interrupts(xdev);

	return 0;
}
EXPORT_SYMBOL_GPL(xdma_user_isr_disable);

#ifdef __LIBXDMA_MOD__
static int __init xdma_base_init(void)
{
	printk(KERN_INFO "%s", version);
	return 0;
}

static void __exit xdma_base_exit(void)
{
	return;
}

module_init(xdma_base_init);
module_exit(xdma_base_exit);
#endif
/* makes an existing transfer cyclic */
static void xdma_transfer_cyclic(struct xdma_transfer *transfer)
{
	/* link last descriptor to first descriptor */
	xdma_desc_link(transfer->desc_virt + transfer->desc_num - 1,
			transfer->desc_virt, transfer->desc_bus);
	/* remember transfer is cyclic */
	transfer->cyclic = 1;
}

static int transfer_monitor_cyclic(struct xdma_engine *engine,
			struct xdma_transfer *transfer, int timeout_ms)
{
	struct xdma_result *result;
	int rc = 0;

	BUG_ON(!engine);
	BUG_ON(!transfer);

	result = engine->cyclic_result;
	BUG_ON(!result);

	if (poll_mode) {
		int i ; 
		for (i = 0; i < 5; i++) {
			rc = engine_service_poll(engine, 0);
			if (rc) {
				pr_info("%s service_poll failed %d.\n",
					engine->name, rc);
				rc = -ERESTARTSYS;
			}
			if (result[engine->rx_head].status)
				return 0;
		}
	} else {
		if (enable_credit_mp){
			dbg_tfr("%s: rx_head=%d,rx_tail=%d, wait ...\n",
				engine->name, engine->rx_head, engine->rx_tail);
			rc = wait_event_interruptible_timeout( transfer->wq,
					(engine->rx_head!=engine->rx_tail ||
					 engine->rx_overrun),
					msecs_to_jiffies(timeout_ms));
			dbg_tfr("%s: wait returns %d, rx %d/%d, overrun %d.\n",
				 engine->name, rc, engine->rx_head,
				engine->rx_tail, engine->rx_overrun);
		} else {
			rc = wait_event_interruptible_timeout( transfer->wq,
					engine->eop_found,
					msecs_to_jiffies(timeout_ms));
			dbg_tfr("%s: wait returns %d, eop_found %d.\n",
				engine->name, rc, engine->eop_found);
		}
	}

	return 0;
}

struct scatterlist *sglist_index(struct sg_table *sgt, unsigned int idx)
{
	struct scatterlist *sg = sgt->sgl;
	int i;

	if (idx >= sgt->orig_nents)
		return NULL;

	if (!idx)
		return sg;

	for (i = 0; i < idx; i++, sg = sg_next(sg))
		;

	return sg;
}

static int copy_cyclic_to_user(struct xdma_engine *engine, int pkt_length,
				int head, char __user *buf, size_t count)
{
	struct scatterlist *sg;
	int more = pkt_length;

	BUG_ON(!engine);
	BUG_ON(!buf);

	dbg_tfr("%s, pkt_len %d, head %d, user buf idx %u.\n",
		engine->name, pkt_length, head, engine->user_buffer_index);

	sg = sglist_index(&engine->cyclic_sgt, head);
	if (!sg) {
		pr_info("%s, head %d OOR, sgl %u.\n",
			engine->name, head, engine->cyclic_sgt.orig_nents);
		return -EIO;
	}

	/* EOP found? Transfer anything from head to EOP */
	while (more) {
		unsigned int copy = more > PAGE_SIZE ? PAGE_SIZE : more; 
		unsigned int blen = count - engine->user_buffer_index;
		int rv;

		if (copy > blen)
			copy = blen;

		dbg_tfr("%s sg %d, 0x%p, copy %u to user %u.\n",
			engine->name, head, sg, copy,
			engine->user_buffer_index);

		rv = copy_to_user(&buf[engine->user_buffer_index],
			page_address(sg_page(sg)), copy);
		if (rv) {
			pr_info("%s copy_to_user %u failed %d\n",
				engine->name, copy, rv);
			return -EIO;
		}

		more -= copy;
		engine->user_buffer_index += copy;

		if (engine->user_buffer_index == count) {
			/* user buffer used up */
			break;
		}
		
		head++;
		if (head >= CYCLIC_RX_PAGES_MAX) {
			head = 0;
			sg = engine->cyclic_sgt.sgl;
		} else
			sg = sg_next(sg);
	}

	return pkt_length;
}

static int complete_cyclic(struct xdma_engine *engine, char __user *buf,
			   size_t count)
{
	struct xdma_result *result;
	int pkt_length = 0;
	int fault = 0;
	int eop = 0;
	int head;
	int rc = 0;
	int num_credit = 0;
	unsigned long flags;

	BUG_ON(!engine);
	result = engine->cyclic_result;
	BUG_ON(!result);

	spin_lock_irqsave(&engine->lock, flags);

	/* where the host currently is in the ring buffer */
	head = engine->rx_head;

	/* iterate over newly received results */
	while (engine->rx_head != engine->rx_tail||engine->rx_overrun) {

		WARN_ON(result[engine->rx_head].status==0);

		dbg_tfr("%s, result[%d].status = 0x%x length = 0x%x.\n",
			engine->name, engine->rx_head, 
			result[engine->rx_head].status,
			result[engine->rx_head].length);

		if ((result[engine->rx_head].status >> 16) != C2H_WB) {
			pr_info("%s, result[%d].status 0x%x, no magic.\n",
				engine->name, engine->rx_head,
				result[engine->rx_head].status);
			fault = 1;
		} else if (result[engine->rx_head].length > PAGE_SIZE) {
			pr_info("%s, result[%d].len 0x%x, > PAGE_SIZE 0x%lx.\n",
				engine->name, engine->rx_head,
				result[engine->rx_head].length, PAGE_SIZE);
			fault = 1;
		} else if (result[engine->rx_head].length == 0) {
			pr_info("%s, result[%d].length 0x%x.\n",
				engine->name, engine->rx_head,
				result[engine->rx_head].length);
			fault = 1;
			/* valid result */
		} else {
			pkt_length += result[engine->rx_head].length;
			num_credit++; 
			/* seen eop? */
			//if (result[engine->rx_head].status & RX_STATUS_EOP)
			if (result[engine->rx_head].status & RX_STATUS_EOP){
				eop = 1;
				engine->eop_found = 1;
			}

			dbg_tfr("%s, pkt_length=%d (%s)\n",
				engine->name, pkt_length,
				eop ? "with EOP" : "no EOP yet");
		}
		/* clear result */
		result[engine->rx_head].status = 0;
		result[engine->rx_head].length = 0;
		/* proceed head pointer so we make progress, even when fault */
		engine->rx_head = (engine->rx_head + 1) % CYCLIC_RX_PAGES_MAX;

		/* stop processing if a fault/eop was detected */
		if (fault || eop){
			break;
		}
	}

	spin_unlock_irqrestore(&engine->lock, flags);

	if (fault)
		return -EIO;
		
	rc = copy_cyclic_to_user(engine, pkt_length, head, buf, count);
	engine->rx_overrun = 0; 
	/* if copy is successful, release credits */
	if(rc > 0)
		write_register(num_credit,&engine->sgdma_regs->credits, 0);

	return rc;
}

ssize_t xdma_engine_read_cyclic(struct xdma_engine *engine, char __user *buf,
				size_t count, int timeout_ms)
{
	int i = 0;
	int rc = 0;
	int rc_len = 0;
	struct xdma_transfer *transfer;

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	transfer = &engine->cyclic_req->xfer;
	BUG_ON(!transfer);

        engine->user_buffer_index = 0;
        
	do {
		rc = transfer_monitor_cyclic(engine, transfer, timeout_ms);
		if (rc < 0)
			return rc;
		rc = complete_cyclic(engine, buf, count);
		if (rc < 0)
			return rc;
		rc_len += rc;

		i++;
		if (i > 10)
			break;
	} while (!engine->eop_found);

	if(enable_credit_mp)
		engine->eop_found = 0;

	return rc_len;
}

static void sgt_free_with_pages(struct sg_table *sgt, int dir,
				struct pci_dev *pdev)
{
	struct scatterlist *sg = sgt->sgl;
	int npages = sgt->orig_nents;
	int i;

	for (i = 0; i < npages; i++, sg = sg_next(sg)) {
		struct page *pg = sg_page(sg);
		dma_addr_t bus = sg_dma_address(sg);

		if (pg) {
			if (pdev)
				pci_unmap_page(pdev, bus, PAGE_SIZE, dir);
			__free_page(pg);
		} else
			break;
	}
	sg_free_table(sgt);
	memset(sgt, 0, sizeof(struct sg_table));
}

static int sgt_alloc_with_pages(struct sg_table *sgt, unsigned int npages,
				int dir, struct pci_dev *pdev)
{
	struct scatterlist *sg;
	int i;

	if (sg_alloc_table(sgt, npages, GFP_KERNEL)) {
		pr_info("sgt OOM.\n");
		return -ENOMEM;
	}

	sg = sgt->sgl;
	for (i = 0; i < npages; i++, sg = sg_next(sg)) {
		struct page *pg = alloc_page(GFP_KERNEL);

        	if (!pg) {
			pr_info("%d/%u, page OOM.\n", i, npages);
			goto err_out;
		}

		if (pdev) {
			dma_addr_t bus = pci_map_page(pdev, pg, 0, PAGE_SIZE,
							dir);
                	if (unlikely(pci_dma_mapping_error(pdev, bus))) {
				pr_info("%d/%u, page 0x%p map err.\n",
					 i, npages, pg);
				__free_page(pg);
				goto err_out;
			}
			sg_dma_address(sg) = bus;
			sg_dma_len(sg) = PAGE_SIZE;
		}
		sg_set_page(sg, pg, PAGE_SIZE, 0);
	}

	sgt->orig_nents = sgt->nents = npages;

	return 0;

err_out:
	sgt_free_with_pages(sgt, dir, pdev);
	return -ENOMEM; 
}

int xdma_cyclic_transfer_setup(struct xdma_engine *engine)
{
	struct xdma_dev *xdev;
	struct xdma_transfer *xfer;
	dma_addr_t bus;
	unsigned long flags;
	int i;
	int rc;

	BUG_ON(!engine);
	xdev = engine->xdev;
	BUG_ON(!xdev);

	if (engine->cyclic_req) {
		pr_info("%s: exclusive access already taken.\n",
			engine->name);
		return -EBUSY;
	}

	spin_lock_irqsave(&engine->lock, flags);

	engine->rx_tail = 0;
	engine->rx_head = 0;
	engine->rx_overrun = 0;
	engine->eop_found = 0;

	rc = sgt_alloc_with_pages(&engine->cyclic_sgt, CYCLIC_RX_PAGES_MAX,
				engine->dir, xdev->pdev);
	if (rc < 0) {
		pr_info("%s cyclic pages %u OOM.\n",
			engine->name, CYCLIC_RX_PAGES_MAX);
		goto err_out;
	}

	engine->cyclic_req = xdma_init_request(&engine->cyclic_sgt, 0);
	if (!engine->cyclic_req) {
		pr_info("%s cyclic request OOM.\n", engine->name);
		rc = -ENOMEM;
		goto err_out;
	}

#ifdef __LIBXDMA_DEBUG__
	xdma_request_cb_dump(engine->cyclic_req);
#endif

	rc = transfer_init(engine, engine->cyclic_req);
	if (rc < 0)
		goto err_out;

	xfer = &engine->cyclic_req->xfer;

	/* replace source addresses with result write-back addresses */
	memset(engine->cyclic_result, 0,
		CYCLIC_RX_PAGES_MAX * sizeof(struct xdma_result));
	bus = engine->cyclic_result_bus;
        for (i = 0; i < xfer->desc_num; i++) {
		xfer->desc_virt[i].src_addr_lo = cpu_to_le32(PCI_DMA_L(bus));
        	xfer->desc_virt[i].src_addr_hi = cpu_to_le32(PCI_DMA_H(bus));
                bus += sizeof(struct xdma_result);
        }
	/* set control of all descriptors */
        for (i = 0; i < xfer->desc_num; i++) {
                xdma_desc_control_clear(xfer->desc_virt + i, LS_BYTE_MASK);
                xdma_desc_control_set(xfer->desc_virt + i,
				 XDMA_DESC_EOP | XDMA_DESC_COMPLETED);
        }

	/* make this a cyclic transfer */
	xdma_transfer_cyclic(xfer);

#ifdef __LIBXDMA_DEBUG__
	transfer_dump(xfer);
#endif

	if(enable_credit_mp){
		//write_register(RX_BUF_PAGES,&engine->sgdma_regs->credits);
		write_register(128, &engine->sgdma_regs->credits, 0);
	}

	spin_unlock_irqrestore(&engine->lock, flags);

	/* start cyclic transfer */
	transfer_queue(engine, xfer);

	return 0;

	/* unwind on errors */
err_out:
	if (engine->cyclic_req) {
		xdma_request_free(engine->cyclic_req);	
		engine->cyclic_req = NULL;
	}
	
	if (engine->cyclic_sgt.orig_nents) {
		sgt_free_with_pages(&engine->cyclic_sgt, engine->dir,
				xdev->pdev);
		engine->cyclic_sgt.orig_nents = 0;
		engine->cyclic_sgt.nents = 0;
		engine->cyclic_sgt.sgl = NULL;
	}

	spin_unlock_irqrestore(&engine->lock, flags);

	return rc;
}


static int cyclic_shutdown_polled(struct xdma_engine *engine)
{
	BUG_ON(!engine);

	spin_lock(&engine->lock);

	dbg_tfr("Polling for shutdown completion\n");
	do {
		engine_status_read(engine, 1, 0);
		schedule();
	} while (engine->status & XDMA_STAT_BUSY);

	if ((engine->running) && !(engine->status & XDMA_STAT_BUSY)) {
		dbg_tfr("Engine has stopped\n");

		if (!list_empty(&engine->transfer_list))
			engine_transfer_dequeue(engine);

		engine_service_shutdown(engine);
	}

	dbg_tfr("Shutdown completion polling done\n");
	spin_unlock(&engine->lock);

	return 0;
}

static int cyclic_shutdown_interrupt(struct xdma_engine *engine)
{
	int rc;

	BUG_ON(!engine);

	rc = wait_event_interruptible_timeout(engine->shutdown_wq,
				!engine->running, msecs_to_jiffies(10000));

#if 0
	if (rc) {
		dbg_tfr("wait_event_interruptible=%d\n", rc);
		return rc;
	}
#endif

	if (engine->running) {
		pr_info("%s still running?!, %d\n", engine->name, rc);
		return -EINVAL;
	}

	return rc;
}

int xdma_cyclic_transfer_teardown(struct xdma_engine *engine)
{
	int rc;
	struct xdma_dev *xdev = engine->xdev;
	struct xdma_transfer *transfer;
	unsigned long flags;

	transfer = engine_cyclic_stop(engine);

	spin_lock_irqsave(&engine->lock, flags);
	if (transfer) {
		dbg_tfr("%s: stop transfer 0x%p.\n", engine->name, transfer);
		if (transfer != &engine->cyclic_req->xfer) {
			pr_info("%s unexpected transfer 0x%p/0x%p\n",
				engine->name, transfer,
				&engine->cyclic_req->xfer);
		}
	}
	/* allow engine to be serviced after stop request */
	spin_unlock_irqrestore(&engine->lock, flags);

	/* wait for engine to be no longer running */
	if (poll_mode) 
		rc = cyclic_shutdown_polled(engine);
	else
		rc = cyclic_shutdown_interrupt(engine);

	/* obtain spin lock to atomically remove resources */
	spin_lock_irqsave(&engine->lock, flags);

	if (engine->cyclic_req) {
		xdma_request_free(engine->cyclic_req);	
		engine->cyclic_req = NULL;
	}

	if (engine->cyclic_sgt.orig_nents) {
		sgt_free_with_pages(&engine->cyclic_sgt, engine->dir,
				xdev->pdev);
		engine->cyclic_sgt.orig_nents = 0;
		engine->cyclic_sgt.nents = 0;
		engine->cyclic_sgt.sgl = NULL;
	}

	spin_unlock_irqrestore(&engine->lock, flags);

	return 0;
}

int engine_addrmode_set(struct xdma_engine *engine, unsigned long arg)
{
	int rv;
	unsigned long dst; 
	u32 w = XDMA_CTRL_NON_INCR_ADDR;

	dbg_perf("IOCTL_XDMA_ADDRMODE_SET\n");
	rv = get_user(dst, (int __user *)arg);

	if (rv == 0) { 
		engine->non_incr_addr = !!dst;
		if (engine->non_incr_addr)
			write_register(w, &engine->regs->control_w1s, 
				(unsigned long)(&engine->regs->control_w1s) -
				(unsigned long)(&engine->regs));
		else
			write_register(w, &engine->regs->control_w1c,
				(unsigned long)(&engine->regs->control_w1c) - 
				(unsigned long)(&engine->regs));
	}
	engine_alignments(engine);

	return rv;
}

