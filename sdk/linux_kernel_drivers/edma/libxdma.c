/*
 * Driver for XDMA for Xilinx XDMA IP core
 *
 * Copyright (C) 2007-2017 Xilinx, Inc.
 *
 * Karen Xie <karen.xie@xilinx.com>
 */

#define pr_fmt(fmt)     KBUILD_MODNAME ":%s: " fmt, __func__

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/string.h>
#include <linux/mm.h>
#include <linux/errno.h>
//#include <linux/device.h>
#include <linux/sched.h>

#include "libxdma.h"
#include "libxdma_api.h"

/* SECTION: Module licensing */

#define DRV_MODULE_NAME		"edma"
#ifdef __LIBXDMA_MOD__
#define DRV_MODULE_DESC		"Xilinx XDMA Base Driver"
#define DRV_MODULE_VERSION	"1.0"
#define DRV_MODULE_RELDATE	"Feb. 2017"

static char version[] =
	DRV_MODULE_DESC " " DRV_MODULE_NAME
	" v" DRV_MODULE_VERSION " (" DRV_MODULE_RELDATE ")\n";

MODULE_AUTHOR("Xilinx, Inc.");
MODULE_DESCRIPTION(DRV_MODULE_DESC);
MODULE_VERSION(DRV_MODULE_VERSION);
MODULE_LICENSE("GPL v2");

#endif

/*
 * xdma device management
 * maintains a list of the xdma devices
 */
static LIST_HEAD(xdev_list);
static DEFINE_MUTEX(xdev_mutex);

static LIST_HEAD(xdev_rcu_list);
static DEFINE_SPINLOCK(xdev_rcu_lock);

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

	dbg_init("xdev 0x%p, idx %d.\n", xdev, xdev->idx);

	spin_lock(&xdev_rcu_lock);
	list_add_tail_rcu(&xdev->rcu_node, &xdev_rcu_list);
	spin_unlock(&xdev_rcu_lock);
}

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
                if (xdev->pci_dev == pdev) {
                        mutex_unlock(&xdev_mutex);
                        return xdev;
                }
        }
        mutex_unlock(&xdev_mutex);
        return NULL;
}
EXPORT_SYMBOL_GPL(xdev_find_by_pdev);


static void engine_msix_teardown(struct xdma_engine *engine);

/* SECTION: Function definitions */
inline void write_register(u32 value, void *iomem)
{
	iowrite32(value, iomem);
}

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

static u64 find_feature_id(const struct xdma_dev *lro)
{
	u64 low = 0;
	u64 high = 0;
#define FEATURE_ID 0x031000

	low = ioread32(lro->bar[lro->user_bar_idx] + FEATURE_ID);
	high = ioread32(lro->bar[lro->user_bar_idx] + FEATURE_ID + 8);
	return low | (high << 32);
}

/* channel_interrupts_enable -- Enable interrupts we are interested in */
static void channel_interrupts_enable(struct xdma_dev *lro, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->channel_int_enable_w1s);
}

/* channel_interrupts_disable -- Disable interrupts we not interested in */
static void channel_interrupts_disable(struct xdma_dev *lro, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->channel_int_enable_w1c);
}

/* user_interrupts_enable -- Enable interrupts we are interested in */
static void user_interrupts_enable(struct xdma_dev *lro, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->user_int_enable_w1s);
}

/* user_interrupts_disable -- Disable interrupts we not interested in */
static void user_interrupts_disable(struct xdma_dev *lro, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);

	write_register(mask, &reg->user_int_enable_w1c);
}

/* read_interrupts -- Print the interrupt controller status */
static u32 read_interrupts(struct xdma_dev *lro)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)
		(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);
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

static void engine_reg_dump(struct xdma_engine *engine)
{
	u32 w;

	BUG_ON(!engine);

	w = read_register(&engine->regs->identifier);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (id).\n",
		engine->name, &engine->regs->identifier, w);
	w &= BLOCK_ID_MASK;
	if (w != BLOCK_ID_HEAD) {
		dbg_init("%s: engine id missing, 0x%08x exp. 0xad4bXX01.\n",
			 engine->name, w);
		return;
	}
	/* extra debugging; inspect complete engine set of registers */
	w = read_register(&engine->regs->status);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (status).\n",
		engine->name, &engine->regs->status, w);
	w = read_register(&engine->regs->control);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (control)\n",
		engine->name, &engine->regs->control, w);
	w = read_register(&engine->sgdma_regs->first_desc_lo);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (first_desc_lo)\n",
		engine->name, &engine->sgdma_regs->first_desc_lo, w);
	w = read_register(&engine->sgdma_regs->first_desc_hi);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (first_desc_hi)\n",
		engine->name, &engine->sgdma_regs->first_desc_hi, w);
	w = read_register(&engine->sgdma_regs->first_desc_adjacent);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (first_desc_adjacent).\n",
		engine->name, &engine->sgdma_regs->first_desc_adjacent, w);
	w = read_register(&engine->regs->completed_desc_count);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (completed_desc_count).\n",
		engine->name, &engine->regs->completed_desc_count, w);
	w = read_register(&engine->regs->interrupt_enable_mask);
	dbg_init("%s: ioread32(0x%p) = 0x%08x (interrupt_enable_mask)\n",
		engine->name, &engine->regs->interrupt_enable_mask, w);
}

/**
 * engine_status_read() - read status of SG DMA engine (optionally reset)
 *
 * Stores status in engine->status.
 *
 * @return -1 on failure, status register otherwise
 */
static u32 engine_status_read(struct xdma_engine *engine, int clear, int dump)
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
		dbg_sg("SG engine %s status: 0x%08x: %s%s%s%s%s%s%s%s%s.\n",
			engine->name, (u32)engine->status,
			(value & XDMA_STAT_BUSY) ? "BUSY " : "IDLE ",
			(value & XDMA_STAT_DESC_STOPPED) ?
					 "DESC_STOPPED " : "",
			(value & XDMA_STAT_DESC_COMPLETED) ?
					"DESC_COMPLETED " : "",
			(value & XDMA_STAT_ALIGN_MISMATCH) ?
					"ALIGN_MISMATCH " : "",
			(value & XDMA_STAT_MAGIC_STOPPED) ?
					"MAGIC_STOPPED " : "",
			(value & XDMA_STAT_FETCH_STOPPED) ?
					"FETCH_STOPPED " : "",
			(value & XDMA_STAT_READ_ERROR) ? "READ_ERROR " : "",
			(value & XDMA_STAT_DESC_ERROR) ? "DESC_ERROR " : "",
			(value & XDMA_STAT_IDLE_STOPPED) ?
					 "IDLE_STOPPED " : "");
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
	w |= (u32)XDMA_CTRL_IE_DESC_STOPPED;
	w |= (u32)XDMA_CTRL_IE_DESC_COMPLETED;


	dbg_tfr("Stopping SG DMA %s engine; writing 0x%08x to 0x%p.\n",
			engine->name, w, (u32 *)&engine->regs->control);
	write_register(w, &engine->regs->control);
	/* dummy read of status register to flush all previous writes */
	dbg_tfr("xdma_engine_stop(%s) done\n", engine->name);
}

static void engine_start_mode_config(struct xdma_engine *engine)
{
	u32 w;

	BUG_ON(!engine);

	/* write control register of SG DMA engine */
	w = (u32)XDMA_CTRL_RUN_STOP;
	w |= (u32)XDMA_CTRL_IE_READ_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESC_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
	w |= (u32)XDMA_CTRL_IE_MAGIC_STOPPED;

	w |= (u32)XDMA_CTRL_IE_DESC_STOPPED;
	w |= (u32)XDMA_CTRL_IE_DESC_COMPLETED;

	/* set non-incremental addressing mode */
	if (engine->non_incr_addr)
		w |= (u32)XDMA_CTRL_NON_INCR_ADDR;

	dbg_tfr("iowrite32(0x%08x to 0x%p) (control)\n", w,
			(void *)&engine->regs->control);
	/* start the engine */
	write_register(w, &engine->regs->control);

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
	write_register(w, &engine->sgdma_regs->first_desc_lo);
	/* write upper 32-bit of bus address of transfer first descriptor */
	w = cpu_to_le32(PCI_DMA_H(transfer->desc_bus));
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_hi)\n", w,
			(void *)&engine->sgdma_regs->first_desc_hi);
	write_register(w, &engine->sgdma_regs->first_desc_hi);

	if (transfer->desc_adjacent > 0) {
		extra_adj = transfer->desc_adjacent - 1;
		if (extra_adj > MAX_EXTRA_ADJ)
			extra_adj = MAX_EXTRA_ADJ;
	}
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_adjacent)\n",
		extra_adj, (void *)&engine->sgdma_regs->first_desc_adjacent);
	write_register(extra_adj, &engine->sgdma_regs->first_desc_adjacent);

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
	BUG_ON(!transfer);

	/* synchronous I/O? */
	/* awake task on transfer's wait queue */
	wake_up_interruptible(&transfer->wq);

	return transfer;
}

struct xdma_transfer *engine_service_transfer_list(struct xdma_engine *engine,
		struct xdma_transfer *transfer, u32 *pdesc_completed)
{
	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(!pdesc_completed);

	/*
	 * iterate over all the transfers completed by the engine,
	 * except for the last (i.e. use > instead of >=).
	 */
	while (transfer && (*pdesc_completed > transfer->desc_num)) {
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
		if (value & XDMA_STAT_BUSY)
			dbg_tfr("%s engine has errors but is still BUSY\n",
				engine->name);
	}

	dbg_tfr("Aborted %s engine transfer 0x%p\n", engine->name, transfer);
	dbg_tfr("%s engine was %d descriptors into transfer (with %d desc)\n",
		engine->name, desc_completed, transfer->desc_num);
	dbg_tfr("%s engine status = %d\n", engine->name, engine->status);
	
	/* mark transfer as failed */
	transfer->state = TRANSFER_STATE_FAILED;
	xdma_engine_stop(engine);
}

struct xdma_transfer *engine_service_final_transfer(struct xdma_engine *engine,
			struct xdma_transfer *transfer, u32 *pdesc_completed)
{
	u32 err_flags;
	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(!pdesc_completed);

	err_flags = XDMA_STAT_MAGIC_STOPPED;
	err_flags |= XDMA_STAT_ALIGN_MISMATCH;
	err_flags |= XDMA_STAT_READ_ERROR;
	err_flags |= XDMA_STAT_DESC_ERROR;

	/* inspect the current transfer */
	if (transfer) {
		if (engine->status & err_flags) {
			engine_err_handle(engine, transfer, *pdesc_completed);
			return transfer;
		}

		if (engine->status & XDMA_STAT_BUSY)
			dbg_tfr("Engine %s is unexpectedly busy - ignoring\n",
				engine->name);

		/* the engine stopped on current transfer? */
		if (*pdesc_completed < transfer->desc_num) {
			transfer->state = TRANSFER_STATE_FAILED;
			dbg_tfr("%s, xfer 0x%p, stopped half-way, %d/%d.\n",
				engine->name, transfer, *pdesc_completed,
				transfer->desc_num);
		} else {
			dbg_tfr("engine %s completed transfer\n", engine->name);
			dbg_tfr("Completed transfer ID = 0x%p\n", transfer);
			dbg_tfr("*pdesc_completed=%d, transfer->desc_num=%d",
				*pdesc_completed, transfer->desc_num);

			/*
			 * if the engine stopped on this transfer,
			 * it should be the last
			 */
			WARN_ON(*pdesc_completed > transfer->desc_num);
			/* mark transfer as succesfully completed */
			transfer->state = TRANSFER_STATE_COMPLETED;
		}

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

static void engine_service_resume(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer_started;

	BUG_ON(!engine);

	/* engine stopped? */
	if (!engine->running) {
		/* engine was requested to be shutdown? */
		if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
			engine->shutdown |= ENGINE_SHUTDOWN_IDLE;
			/* awake task on engine's shutdown wait queue */
			wake_up_interruptible(&engine->shutdown_wq);
		} else if (!list_empty(&engine->transfer_list)) {
			/* (re)start engine */
			transfer_started = engine_start(engine);
			dbg_tfr("re-started %s engine with pending xfer 0x%p\n",
				engine->name, transfer_started);
		} else {
			dbg_tfr("no pending transfers, %s engine stays idle.\n",
				engine->name);
		}
	} else {
		/* engine is still running? */
		if (list_empty(&engine->transfer_list)) {
			dbg_tfr("no queued transfers but %s engine running!\n",
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
static int engine_service(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer = NULL;
	u32 desc_count;
	int rc  = 0;

	BUG_ON(!engine);

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
	engine_status_read(engine, 1, 0);

	/*
	 * engine was running but is no longer busy, or writeback occurred,
	 * shut down
	 */
	if (engine->running && !(engine->status & XDMA_STAT_BUSY))
		engine_service_shutdown(engine);

	/*
	 * If called from the ISR, or if an error occurred, the descriptor
	 * count will be zero.  In this scenario, read the descriptor count
	 * from HW.  In polled mode descriptor completion, this read is
	 * unnecessary and is skipped to reduce latency
	 */
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

	/* Restart the engine following the servicing */
	engine_service_resume(engine);

	return rc;
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
	engine_service(engine);

	/* re-enable interrupts for this engine */
	if(engine->lro->msix_enabled){
		write_register(engine->interrupt_enable_mask_value,
			       &engine->regs->interrupt_enable_mask_w1s);
	}else{
		channel_interrupts_enable(engine->lro, engine->irq_bitmask);
	}
	/* unlock the engine */
	spin_unlock_irqrestore(&engine->lock, flags);
}

static irqreturn_t user_irq_service(int irq, struct xdma_irq *user_irq)
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
	struct xdma_dev *lro;
	struct interrupt_regs *irq_regs;
	int user_irq_bit;
	struct xdma_engine *engine;
	int channel;

	dbg_irq("(irq=%d) <<<< INTERRUPT SERVICE ROUTINE\n", irq);
	BUG_ON(!dev_id);
	lro = (struct xdma_dev *)dev_id;

	if (!lro) {
		WARN_ON(!lro);
		dbg_irq("xdma_isr(irq=%d) lro=%p ??\n", irq, lro);
		return IRQ_NONE;
	}

	irq_regs = (struct interrupt_regs *)(lro->bar[lro->config_bar_idx] +
			XDMA_OFS_INT_CTRL);

	/* read channel interrupt requests */
	ch_irq = read_register(&irq_regs->channel_int_request);
	dbg_irq("ch_irq = 0x%08x\n", ch_irq);

	/*
	 * disable all interrupts that fired; these are re-enabled individually
	 * after the causing module has been fully serviced.
	 */
	channel_interrupts_disable(lro, ch_irq);

	/* read user interrupts - this read also flushes the above write */
	user_irq = read_register(&irq_regs->user_int_request);
	dbg_irq("user_irq = 0x%08x\n", user_irq);

	for (user_irq_bit = 0; user_irq_bit < MAX_USER_IRQ; user_irq_bit++) {
		if (user_irq & (1 << user_irq_bit))
			user_irq_service(user_irq_bit, &lro->user_irq[user_irq_bit]);
	}

	/* iterate over H2C (PCIe read) */
	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		engine = &lro->engine_h2c[channel];
		/* engine present and its interrupt fired? */
		if ((engine->magic == MAGIC_ENGINE) &&
		    (engine->irq_bitmask & ch_irq)) {
			dbg_tfr("schedule_work(engine=%p)\n", engine);
			schedule_work(&engine->work);
		}
	}

	/* iterate over C2H (PCIe write) */
	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		engine = &lro->engine_c2h[channel];
		/* engine present and its interrupt fired? */
		if ((engine->magic == MAGIC_ENGINE) &&
		    (engine->irq_bitmask & ch_irq)) {
			dbg_tfr("schedule_work(engine=%p)\n", engine);
			schedule_work(&engine->work);
		}
	}

	lro->irq_count++;
	return IRQ_HANDLED;
}

/*
 * xdma_user_irq() - Interrupt handler for user interrupts in MSI-X mode
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_user_irq(int irq, void *dev_id)
{
	struct xdma_irq *user_irq;

	dbg_irq("(irq=%d) <<<< INTERRUPT SERVICE ROUTINE\n", irq);

	BUG_ON(!dev_id);
	user_irq = (struct xdma_irq *)dev_id;

	return  user_irq_service(irq, user_irq);
}

/*
 * xdma_channel_irq() - Interrupt handler for channel interrupts in MSI-X mode
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_channel_irq(int irq, void *dev_id)
{
	struct xdma_dev *lro;
	struct xdma_engine *engine;
	struct interrupt_regs *irq_regs;

	dbg_irq("(irq=%d) <<<< INTERRUPT service ROUTINE\n", irq);
	BUG_ON(!dev_id);

	engine = (struct xdma_engine *)dev_id;
	lro = engine->lro;

	if (!lro) {
		WARN_ON(!lro);
		dbg_irq("xdma_channel_irq(irq=%d) lro=%p ??\n", irq, lro);
		return IRQ_NONE;
	}

	irq_regs = (struct interrupt_regs *)(lro->bar[lro->config_bar_idx] +
			XDMA_OFS_INT_CTRL);

	/* Disable the interrupt for this engine */
	//channel_interrupts_disable(lro, engine->irq_bitmask);
	engine->interrupt_enable_mask_value = read_register(&engine->regs->interrupt_enable_mask);
	write_register(engine->interrupt_enable_mask_value, &engine->regs->interrupt_enable_mask_w1c);
	/* Dummy read to flush the above write */
	read_register(&irq_regs->channel_int_pending);
	/* Schedule the bottom half */
	schedule_work(&engine->work);

	/*
	 * RTO - need to protect access here if multiple MSI-X are used for
	 * user interrupts
	 */
	lro->irq_count++;
	return IRQ_HANDLED;
}

/*
 * Unmap the BAR regions that had been mapped earlier using map_bars()
 */
static void unmap_bars(struct xdma_dev *lro, struct pci_dev *dev)
{
	int i;

	for (i = 0; i < XDMA_BAR_NUM; i++) {
		/* is this BAR mapped? */
		if (lro->bar[i]) {
			/* unmap BAR */
			pci_iounmap(dev, lro->bar[i]);
			/* mark as unmapped */
			lro->bar[i] = NULL;
		}
	}
}

static int map_single_bar(struct xdma_dev *lro, struct pci_dev *dev, int idx)
{
	resource_size_t bar_start;
	resource_size_t bar_len;
	resource_size_t map_len;

	bar_start = pci_resource_start(dev, idx);
	bar_len = pci_resource_len(dev, idx);
	map_len = bar_len;

	lro->bar[idx] = NULL;

	/* do not map BARs with length 0. Note that start MAY be 0! */
	if (!bar_len) {
		dbg_init("BAR #%d is not present - skipping\n", idx);
		return 0;
	}

	/* BAR size exceeds maximum desired mapping? */
	if (bar_len > INT_MAX) {
		dbg_init("Limit BAR %d mapping from %llu to %d bytes\n", idx,
			(u64)bar_len, INT_MAX);
		map_len = (resource_size_t)INT_MAX;
	}
	/*
	 * map the full device memory or IO region into kernel virtual
	 * address space
	 */
	dbg_init("BAR%d: %llu bytes to be mapped.\n", idx, (u64)map_len);
	lro->bar[idx] = pci_iomap(dev, idx, map_len);

	if (!lro->bar[idx]) {
		dbg_init("Could not map BAR %d.\n", idx);
		return -1;
	}

	dbg_init("BAR%d at 0x%llx mapped at 0x%p, length=%llu(/%llu)\n", idx,
		(u64)bar_start, lro->bar[idx], (u64)map_len, (u64)bar_len);

	return (int)map_len;
}

static int is_config_bar(struct xdma_dev *lro, int idx)
{
	u32 irq_id = 0;
	u32 cfg_id = 0;
	int flag = 0;
	u32 mask = 0xffff0000; /* Compare only XDMA ID's not Version number */
	struct interrupt_regs *irq_regs =
		(struct interrupt_regs *) (lro->bar[idx] + XDMA_OFS_INT_CTRL);
	struct config_regs *cfg_regs =
		(struct config_regs *)(lro->bar[idx] + XDMA_OFS_CONFIG);

	irq_id = read_register(&irq_regs->identifier);
	cfg_id = read_register(&cfg_regs->identifier);

	if (((irq_id & mask)== IRQ_BLOCK_ID) && ((cfg_id & mask)== CONFIG_BLOCK_ID)) {
		dbg_init("BAR %d is the XDMA config BAR\n", idx);
		flag = 1;
	} else {
		dbg_init("BAR %d is not XDMA config BAR\n", idx);
		dbg_init("BAR %d is NOT the XDMA config BAR: 0x%x, 0x%x.\n", idx, irq_id, cfg_id);
		flag = 0;
	}

	return flag;
}

static void identify_bars(struct xdma_dev *lro, int *bar_id_list, int num_bars,
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

	BUG_ON(!lro);
	BUG_ON(!bar_id_list);

	dbg_init("lro 0x%p, bars %d, config at %d.\n",
		lro, num_bars, config_bar_pos);

	switch (num_bars) {
	case 1:
		/* Only one BAR present - no extra work necessary */
		break;

	case 2:
		if (config_bar_pos == 0) {
			lro->bypass_bar_idx = bar_id_list[1];
			dbg_init("bypass bar %d.\n", lro->bypass_bar_idx);
		} else if (config_bar_pos == 1) {
			lro->user_bar_idx = bar_id_list[0];
			dbg_init("user bar %d.\n", lro->user_bar_idx);
		} else {
			dbg_init("2, XDMA config BAR unexpected %d.\n",
				config_bar_pos);
		}
		break;

	case 3:
	case 4:
		if (config_bar_pos == 1 || config_bar_pos == 2) {
			/* user bar at bar #0 */
			lro->user_bar_idx = bar_id_list[0];
			/* bypass bar at the last bar */
			lro->bypass_bar_idx = bar_id_list[num_bars - 1];
			dbg_init("bypass bar %d, user bar %d.\n",
				 lro->bypass_bar_idx, lro->user_bar_idx);
		} else {
			dbg_init("3/4, XDMA config BAR unexpected %d.\n",
				config_bar_pos);
		}
		break;

	default:
		/* Should not occur - warn user but safe to continue */
		dbg_init("Unexpected number of BARs (%d)\n", num_bars);
		dbg_init("Only XDMA config BAR accessible\n");
		break;

	}
}

/* map_bars() -- map device regions into kernel virtual address space
 *
 * Map the device memory regions into kernel virtual address space after
 * verifying their sizes respect the minimum sizes needed
 */
static int map_bars(struct xdma_dev *lro, struct pci_dev *dev)
{
	int rc;
	int i;
	int bar_id_list[XDMA_BAR_NUM];
	int bar_id_idx = 0;
	int config_bar_pos = 0;

	/* iterate through all the BARs */
	for (i = 0; i < XDMA_BAR_NUM; i++) {
		int bar_len;

		bar_len = map_single_bar(lro, dev, i);
		if (bar_len == 0) {
			continue;
		} else if (bar_len < 0) {
			rc = -1;
			goto fail;
		}

		/* Try to identify BAR as XDMA control BAR */
		if ((bar_len >= XDMA_BAR_SIZE) && (lro->config_bar_idx < 0)) {

			if (is_config_bar(lro, i)) {
				lro->config_bar_idx = i;
				config_bar_pos = bar_id_idx;
				dbg_init("config bar %d, pos %d.\n",
					lro->config_bar_idx, config_bar_pos);
			}
		}

		bar_id_list[bar_id_idx] = i;
		bar_id_idx++;
	}

	/* The XDMA config BAR must always be present */
	if (lro->config_bar_idx < 0) {
		dbg_init("Failed to detect XDMA config BAR\n");
		rc = -1;
		goto fail;
	}

	identify_bars(lro, bar_id_list, bar_id_idx, config_bar_pos);

	/* successfully mapped all required BAR regions */
	rc = 0;
	goto success;
fail:
	/* unwind; unmap any BARs that we did map */
	unmap_bars(lro, dev);
success:
	return rc;
}

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
	dbg_desc("\n");
}

static void transfer_dump(struct xdma_transfer *transfer)
{
	int i;
	struct xdma_desc *desc_virt = transfer->desc_virt;

	pr_info("transfer 0x%p, state 0x%x, f 0x%x, dir %d, len %u, last %d.\n",
		transfer, transfer->state, transfer->flags, transfer->dir,
		transfer->xfer_len, transfer->last_in_request);
	pr_info("transfer 0x%p, desc %d, bus 0x%llx, adj %d.\n",
		transfer, transfer->desc_num, (u64)transfer->desc_bus,
		transfer->desc_adjacent);
	for (i = 0; i < transfer->desc_num; i += 1)
		dump_desc(desc_virt + i);
}

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
static struct xdma_desc *xdma_desc_alloc(struct pci_dev *dev, int number,
		dma_addr_t *desc_bus_p)
{
	struct xdma_desc *desc_virt;	/* virtual address */
	dma_addr_t desc_bus;		/* bus address */
	int i;
	int adj = number - 1;
	int extra_adj;
	u32 temp_control;

	BUG_ON(number < 1);

	/* allocate a set of cache-coherent contiguous pages */
	desc_virt = (struct xdma_desc *)pci_alloc_consistent(dev,
			number * sizeof(struct xdma_desc), desc_bus_p);
	if (!desc_virt)
		return NULL;
	/* get bus address of the first descriptor */
	desc_bus = *desc_bus_p;

	/* create singly-linked list for SG DMA controller */
	for (i = 0; i < number - 1; i++) {
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

	/* return the virtual address of the first descriptor */
	return desc_virt;
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
static void xdma_desc_control(struct xdma_desc *first, u32 control_field)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control) & ~(LS_BYTE_MASK);

	BUG_ON(control_field & ~(LS_BYTE_MASK));
	/* merge adjacent and control field */
	control |= control_field;
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_free - Free cache-coherent linked list of N descriptors.
 *
 * @dev Pointer to pci_dev
 * @number Number of descriptors to be allocated
 * @desc_virt Pointer to (i.e. virtual address of) first descriptor in list
 * @desc_bus Bus address of first descriptor in list
 */
static void xdma_desc_free(struct pci_dev *dev, int number,
		struct xdma_desc *desc_virt, dma_addr_t desc_bus)
{
	BUG_ON(!desc_virt);
	BUG_ON(number < 0);
	/* free contiguous list */
	pci_free_consistent(dev, number * sizeof(struct xdma_desc), desc_virt,
		desc_bus);
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
	/* length (in bytes) must be a non-negative multiple of four */
//	BUG_ON(len & 3);

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
	int rc = 0;
	struct xdma_transfer *transfer_started;
	unsigned long flags;

	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(transfer->desc_num == 0);
	dbg_tfr("transfer_queue(transfer=0x%p).\n", transfer);

	/* lock the engine state */
	spin_lock_irqsave(&engine->lock, flags);
	engine->prev_cpu = get_cpu();
	put_cpu();

	/* engine is being shutdown; do not accept new transfers */
	if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
		rc = -1;
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
	return rc;
};

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

static void engine_destroy(struct xdma_dev *lro, struct xdma_engine *engine)
{
	BUG_ON(!lro);
	BUG_ON(!engine);

	dbg_sg("Shutting down engine %s%d", engine->name, engine->channel);

	/* Disable interrupts to stop processing new events during shutdown */
	write_register(0x0, &engine->regs->interrupt_enable_mask);

	engine_msix_teardown(engine);

	memset(engine, 0, sizeof(struct xdma_engine));
	/* Decrement the number of engines available */
	lro->engines_num--;
}

static void engine_msix_teardown(struct xdma_engine *engine)
{
	BUG_ON(!engine);
	if (engine->msix_irq_line) {
		dbg_sg("Release IRQ#%d for engine %p\n", engine->msix_irq_line,
			engine);
		free_irq(engine->msix_irq_line, engine);
	}
}

static int engine_msix_setup(struct xdma_engine *engine)
{
	int rc = 0;
	u32 vector;
	struct xdma_dev *lro;

	BUG_ON(!engine);
	lro = engine->lro;
	BUG_ON(!lro);

	vector = lro->entry[lro->engines_num + MAX_USER_IRQ].vector;

	dbg_init("Requesting IRQ#%d for engine %p\n", vector, engine);
	rc = request_irq(vector, xdma_channel_irq, 0, DRV_MODULE_NAME, engine);
	if (rc) {
		dbg_init("Unable to request_irq for engine %d\n",
			lro->engines_num);
	} else {
		dbg_init("Requested IRQ#%d for engine %d\n", vector,
			lro->engines_num);
		engine->msix_irq_line = vector;
	}

	return rc;
}

/* engine_create() - Create an SG DMA engine bookkeeping data structure
 *
 * An SG DMA engine consists of the resources for a single-direction transfer
 * queue; the SG DMA hardware, the software queue and interrupt handling.
 *
 * @dev Pointer to pci_dev
 * @offset byte address offset in BAR[lro->config_bar_idx] resource for the
 * SG DMA * controller registers.
 * @dir: DMA_TO/FROM_DEVICE
 * @streaming Whether the engine is attached to AXI ST (rather than MM)
 */
static int engine_init(struct xdma_engine *engine, struct xdma_dev *lro,
			int offset, enum dma_data_direction dir, int channel)
{
	u32 reg_value;
	int sgdma_offset = offset + SGDMA_OFFSET_FROM_CHANNEL;
	int rc;

	/* set magic */
	engine->magic = MAGIC_ENGINE;

	engine->channel = channel;

	/* engine interrupt request bit */
	engine->irq_bitmask = (1 << XDMA_ENG_IRQ_NUM) - 1;
	engine->irq_bitmask <<= (lro->engines_num * XDMA_ENG_IRQ_NUM);
	engine->bypass_offset = lro->engines_num * BYPASS_MODE_SPACING;

	/* initialize spinlock */
	spin_lock_init(&engine->lock);
	/* initialize transfer_list */
	INIT_LIST_HEAD(&engine->transfer_list);
	/* parent */
	engine->lro = lro;
	/* register address */
	engine->regs = (lro->bar[lro->config_bar_idx] + offset);
	engine->sgdma_regs = (lro->bar[lro->config_bar_idx] + sgdma_offset);
	/* remember SG DMA direction */
	engine->dir = dir;
	sprintf(engine->name, "%s%d",
		(dir == DMA_TO_DEVICE) ? "H2C" : "C2H", channel);

	dbg_init("engine %p name %s irq_bitmask=0x%08x\n", engine, engine->name,
		(int)engine->irq_bitmask);

	/* initialize the deferred work for transfer completion */
	INIT_WORK(&engine->work, engine_service_work);

	/* Configure per-engine MSI-X vector if MSI-X is enabled */
	if (lro->msix_enabled) {
		rc = engine_msix_setup(engine);
		if (rc) {
			dbg_init("MSI-X config for engine %p failed\n", engine);
			return rc;
		}
	}

	lro->engines_num++;

	/* initialize wait queue */
	init_waitqueue_head(&engine->shutdown_wq);

	write_register(XDMA_CTRL_NON_INCR_ADDR, &engine->regs->control_w1c);

	engine_alignments(engine);

	/* Configure error interrupts by default */
	reg_value = XDMA_CTRL_IE_DESC_ALIGN_MISMATCH;
	reg_value |= XDMA_CTRL_IE_MAGIC_STOPPED;
	reg_value |= XDMA_CTRL_IE_MAGIC_STOPPED;
	reg_value |= XDMA_CTRL_IE_READ_ERROR;
	reg_value |= XDMA_CTRL_IE_DESC_ERROR;

	/* enable the relevant completion interrupts */
	reg_value |= XDMA_CTRL_IE_DESC_STOPPED;
	reg_value |= XDMA_CTRL_IE_DESC_COMPLETED;

	/* Apply engine configurations */
	write_register(reg_value, &engine->regs->interrupt_enable_mask);

	/* all engine setup completed successfully */
	return 0;
}

/* transfer_destroy() - free transfer */
static void transfer_destroy(struct xdma_dev *lro,
			struct xdma_transfer *transfer, bool force)
{
	/* free descriptors */
	xdma_desc_free(lro->pci_dev, transfer->desc_num, transfer->desc_virt,
			transfer->desc_bus);


	if ((force || transfer->last_in_request) &&
		(transfer->flags & XFER_FLAG_NEED_UNMAP)) {
        	struct sg_table *sgt = transfer->sgt;
		if (sgt->nents) {
			pci_unmap_sg(lro->pci_dev, sgt->sgl, sgt->nents,
					transfer->dir);
			sgt->nents = 0;
		}
	}

	/* free transfer */
	kfree(transfer);
}

static int transfer_build(struct xdma_engine *engine,
			struct xdma_transfer *transfer, u64 ep_addr,
			struct scatterlist **sgl_p, unsigned int nents)
{
	struct scatterlist *sg = *sgl_p;
	int i = 0;
	int j = 0;
	dma_addr_t cont_addr = sg_dma_address(sg);
	unsigned int cont_len = sg_dma_len(sg);
	unsigned int next_len = 0;

	dbg_desc("sg %d/%u: addr=0x%llx, len=0x%x\n",
		i, nents, cont_addr, cont_len);
	for (i = 1, sg = sg_next(sg); i < nents; i++, sg = sg_next(sg)) {
		dma_addr_t next_addr = sg_dma_address(sg);
		next_len = sg_dma_len(sg);

		dbg_desc("sg %d/%u: addr=0x%llx, len=0x%x, cont 0x%llx,0x%x.\n",
			i, nents, next_addr, next_len, cont_addr, cont_len);
		/* contiguous ? */
		if (next_addr == (cont_addr + cont_len)) {
			cont_len += next_len;
			continue;
		}

	dbg_desc("DESC %d: addr=0x%llx, 0x%x, ep_addr=0x%llx\n",
		j, (u64)cont_addr, cont_len, (u64)ep_addr);
		/* fill in descriptor entry j with transfer details */
		xdma_desc_set(transfer->desc_virt + j, cont_addr, ep_addr,
				 cont_len, transfer->dir);
		transfer->xfer_len += cont_len;

		/* for non-inc-add mode don't increment ep_addr */
		if (!engine->non_incr_addr)
			ep_addr += cont_len;

		/* start new contiguous block */
		cont_addr = next_addr;
		cont_len = next_len;
		j++;
	}
	BUG_ON(j > nents);

	if (cont_len) {
		dbg_desc("DESC %d: addr=0x%llx, 0x%x, ep_addr=0x%llx\n",
			j, (u64)cont_addr, cont_len, (u64)ep_addr);
		xdma_desc_set(transfer->desc_virt + j, cont_addr, ep_addr,
			 cont_len, transfer->dir);
		transfer->xfer_len += cont_len;
	}

	*sgl_p = sg;
	return j;
}

static struct xdma_transfer *transfer_create(struct xdma_engine *engine,
			u64 ep_addr, struct scatterlist **sgl_p, int nents)
{
	struct xdma_dev *lro = engine->lro;
	struct xdma_transfer *transfer;
	int i = 0;
	int last = 0;
	u32 control;

	transfer = kzalloc(sizeof(struct xdma_transfer), GFP_KERNEL);
	if (!transfer) {
		dbg_tfr("OOM.\n");
		return NULL;
	}

	/* remember direction of transfer */
	transfer->dir = engine->dir;

	/* allocate descriptor list */
	transfer->desc_virt = xdma_desc_alloc(lro->pci_dev, nents,
				&transfer->desc_bus);
	dbg_sg("transfer->desc_bus = 0x%llx.\n", (u64)transfer->desc_bus);

	last = transfer_build(engine, transfer, ep_addr, sgl_p, nents);

	/* terminate last descriptor */
	xdma_desc_link(transfer->desc_virt + last, 0, 0);
	/* stop engine, EOP for AXI ST, req IRQ on last descriptor */
	control = XDMA_DESC_STOPPED;
	control |= XDMA_DESC_EOP;
	control |= XDMA_DESC_COMPLETED;
	xdma_desc_control(transfer->desc_virt + last, control);

	last++;
	/* last is the number of descriptors */
	transfer->desc_num = transfer->desc_adjacent = last;

	dbg_sg("transfer 0x%p has %d descriptors\n", transfer,
		transfer->desc_num);
	/* fill in adjacent numbers */
	for (i = 0; i < transfer->desc_num; i++) {
		xdma_desc_adjacent(transfer->desc_virt + i,
			transfer->desc_num - i - 1);
	}

	/* initialize wait queue */
	init_waitqueue_head(&transfer->wq);

	return transfer;
}

static void transfer_abort(struct xdma_engine *engine,
			struct xdma_transfer *transfer)
{
	struct xdma_transfer *head;

	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(transfer->desc_num == 0);

	head = list_entry(engine->transfer_list.next, struct xdma_transfer,
			entry);
	if (head == transfer)
               list_del(engine->transfer_list.next);
	else
		pr_info("engine %s, transfer 0x%p NOT found, 0x%p.\n", 
			engine->name, transfer, head);
}

int xdma_xfer_submit(void *channel, enum dma_data_direction dir, u64 ep_addr,
			 struct sg_table *sgt, int dma_mapped, int timeout_ms)
{
	int rv = 0;
	ssize_t done = 0;
	struct xdma_engine *engine = (struct xdma_engine *)channel;
	struct scatterlist *sg = sgt->sgl;
	struct xdma_dev *lro;
	int nents;

        BUG_ON(!engine);
        BUG_ON(engine->magic != MAGIC_ENGINE);

	lro = engine->lro;
	/* check the direction */
	if (engine->dir != dir) {
		dbg_tfr("channel 0x%p, %s, dir 0x%x/0x%x mismatch.\n",
			channel, engine->name, engine->dir, dir);
		return -EINVAL;
	}

	if (!dma_mapped) {
		nents = pci_map_sg(lro->pci_dev, sg, sgt->orig_nents, dir);
		if (!nents) {
			dbg_tfr("map sgl failed, sgt 0x%p.\n", sgt);
			return -EIO;
		}
		sgt->nents = nents;
	} else {
		BUG_ON(!sgt->nents);
		nents = sgt->nents;
	}
	
	while (nents) {
		unsigned long flags;
		unsigned int xfer_nents = min_t(unsigned int, 
					nents, XDMA_TRANSFER_MAX_DESC);
		struct xdma_transfer *transfer;

		/* build transfer */	
		transfer = transfer_create(engine, ep_addr, &sg, xfer_nents);
		if (!transfer) {
			dbg_tfr("OOM.\n");
			if (!dma_mapped) {
				pci_unmap_sg(lro->pci_dev, sgt->sgl,
						sgt->orig_nents, dir);
				sgt->nents = 0;
			}
			return -ENOMEM;
		}

		if (!dma_mapped)
			transfer->flags = XFER_FLAG_NEED_UNMAP;

		/* last transfer for the given request? */
		nents -= xfer_nents;
		if (!nents) {
			transfer->last_in_request = 1;
			transfer->sgt = sgt;
		}

		//transfer_dump(transfer);

		rv = transfer_queue(engine, transfer);
		if (rv < 0) {
			dbg_tfr("unable to submit %s.\n", engine->name);
			transfer_destroy(lro, transfer, 1);
			return -ERESTARTSYS;
		}

		rv = wait_event_interruptible_timeout(transfer->wq,
                        (transfer->state != TRANSFER_STATE_SUBMITTED),
			msecs_to_jiffies(timeout_ms));

		spin_lock_irqsave(&engine->lock, flags);
		switch(transfer->state) {
		case TRANSFER_STATE_COMPLETED:
			spin_unlock_irqrestore(&engine->lock, flags);
			dbg_tfr("transfer %p, %u completed.\n", transfer,
				transfer->xfer_len);
			done += transfer->xfer_len;
			ep_addr += transfer->xfer_len;
			transfer_destroy(lro, transfer, 0);
			break;
		case TRANSFER_STATE_FAILED:
			spin_unlock_irqrestore(&engine->lock, flags);
			pr_info("transfer %p, %u failed.\n", transfer,
				transfer->xfer_len);
			transfer_destroy(lro, transfer, 1);
			return -EIO;
		default:
			/* transfer can still be in-flight */
			pr_info("xfer 0x%p,%u, state 0x%x, timed out.\n",
				 transfer, transfer->xfer_len, transfer->state);
			transfer_abort(engine, transfer);
			spin_unlock_irqrestore(&engine->lock, flags);

			xdma_engine_stop(engine);
			transfer_dump(transfer);
			transfer_destroy(lro, transfer, 1);
			return -ERESTARTSYS;
		}
	} /* while (sg) */

	return done;
}
EXPORT_SYMBOL_GPL(xdma_xfer_submit);

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

static struct xdma_dev *alloc_dev_instance(struct pci_dev *pdev)
{
	int i;
	struct xdma_dev *lro;

	BUG_ON(!pdev);

	/* allocate zeroed device book keeping structure */
	lro = kzalloc(sizeof(struct xdma_dev), GFP_KERNEL);
	if (!lro) {
		dbg_init("Could not kzalloc(xdma_dev).\n");
		return NULL;
	}

	lro->magic = MAGIC_DEVICE;
	lro->config_bar_idx = -1;
	lro->user_bar_idx = -1;
	lro->bypass_bar_idx = -1;
	lro->irq_line = -1;

	/* create a driver to device reference */
	lro->pci_dev = pdev;
	dbg_init("probe() lro = 0x%p\n", lro);

	/* Set up data user IRQ data structures */
	for (i = 0; i < MAX_USER_IRQ; i++) {
		lro->user_irq[i].lro = lro;
		spin_lock_init(&lro->user_irq[i].events_lock);
		init_waitqueue_head(&lro->user_irq[i].events_wq);
		lro->user_irq[i].handler = NULL;
		lro->user_irq[i].user_idx = i; /* 0 ~ 15 */
	}

	return lro;
}

static int probe_scan_for_msi(struct xdma_dev *lro, struct pci_dev *pdev)
{
	int i;
	int rc = 0;
	int req_nvec = MAX_NUM_ENGINES + MAX_USER_IRQ;

	BUG_ON(!lro);
	BUG_ON(!pdev);

	if (msi_msix_capable(pdev, PCI_CAP_ID_MSIX)) {
		dbg_init("Enabling MSI-X\n");
		for (i = 0; i < req_nvec; i++)
			lro->entry[i].entry = i;

		rc = pci_enable_msix(pdev, lro->entry, req_nvec);
		if (rc < 0)
			dbg_init("Couldn't enable MSI-X mode: rc = %d\n", rc);

		lro->msix_enabled = 1;
	} else if (msi_msix_capable(pdev, PCI_CAP_ID_MSI)) {
		/* enable message signalled interrupts */
		dbg_init("pci_enable_msi()\n");
		rc = pci_enable_msi(pdev);
		if (rc < 0)
			dbg_init("Couldn't enable MSI mode: rc = %d\n", rc);
		lro->msi_enabled = 1;
	} else {
		dbg_init("MSI/MSI-X not detected - using legacy interrupts\n");
	}

	return rc;
}

static int request_regions(struct xdma_dev *lro, struct pci_dev *pdev)
{
	int rc;

	BUG_ON(!lro);
	BUG_ON(!pdev);

	dbg_init("pci_request_regions()\n");
	rc = pci_request_regions(pdev, DRV_MODULE_NAME);
	/* could not request all regions? */
	if (rc) {
		dbg_init("pci_request_regions() = %d, device in use?\n", rc);
		/* assume device is in use so do not disable it later */
		lro->regions_in_use = 1;
	} else {
		lro->got_regions = 1;
	}

	return rc;
}

static int set_dma_mask(struct pci_dev *pdev)
{
	int rc = 0;

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
		rc = -1;
	}

	return rc;
}

static u32 build_vector_reg(u32 a, u32 b, u32 c, u32 d)
{
	u32 reg_val = 0;

	reg_val |= (a & 0x1f) << 0;
	reg_val |= (b & 0x1f) << 8;
	reg_val |= (c & 0x1f) << 16;
	reg_val |= (d & 0x1f) << 24;

	return reg_val;
}

static void write_msix_vectors(struct xdma_dev *lro)
{
	struct interrupt_regs *int_regs;
	u32 reg_val;

	BUG_ON(!lro);
	int_regs = (struct interrupt_regs *)
			(lro->bar[lro->config_bar_idx] + XDMA_OFS_INT_CTRL);

	/* user irq MSI-X vectors */
	reg_val = build_vector_reg(0, 1, 2, 3);
	write_register(reg_val, &int_regs->user_msi_vector[0]);

	reg_val = build_vector_reg(4, 5, 6, 7);
	write_register(reg_val, &int_regs->user_msi_vector[1]);

	reg_val = build_vector_reg(8, 9, 10, 11);
	write_register(reg_val, &int_regs->user_msi_vector[2]);

	reg_val = build_vector_reg(12, 13, 14, 15);
	write_register(reg_val, &int_regs->user_msi_vector[3]);

	/* channel irq MSI-X vectors */
	reg_val = build_vector_reg(16, 17, 18, 19);
	write_register(reg_val, &int_regs->channel_msi_vector[0]);

	reg_val = build_vector_reg(20, 21, 22, 23);
	write_register(reg_val, &int_regs->channel_msi_vector[1]);
}

static int msix_irq_setup(struct xdma_dev *lro)
{
	int i;
	int rc;

	BUG_ON(!lro);
	write_msix_vectors(lro);

	for (i = 0; i < MAX_USER_IRQ; i++) {
		rc = request_irq(lro->entry[i].vector, xdma_user_irq, 0,
			DRV_MODULE_NAME, &lro->user_irq[i]);

		if (rc) {
			dbg_init("Couldn't use IRQ#%d, rc=%d\n",
				lro->entry[i].vector, rc);
			break;
		}

		dbg_init("Using IRQ#%d with 0x%p\n", lro->entry[i].vector,
			&lro->user_irq[i]);
	}

	/* If any errors occur, free IRQs that were successfully requested */
	if (rc) {
		while (--i >= 0)
			free_irq(lro->entry[i].vector, &lro->user_irq[i]);
	}

	return rc;
}

static void irq_teardown(struct xdma_dev *lro)
{
	int i;

	BUG_ON(!lro);

	if (lro->msix_enabled) {
		for (i = 0; i < MAX_USER_IRQ; i++) {
			dbg_init("Releasing IRQ#%d\n", lro->entry[i].vector);
			free_irq(lro->entry[i].vector, &lro->user_irq[i]);
		}
	} else if (lro->irq_line != -1) {
		dbg_init("Releasing IRQ#%d\n", lro->irq_line);
		free_irq(lro->irq_line, lro);
	}
}

static int irq_setup(struct xdma_dev *lro, struct pci_dev *pdev)
{
	int rc = 0;
	u32 irq_flag;
	u8 val;
	void *reg;
	u32 w;

	BUG_ON(!lro);

	if (lro->msix_enabled) {
		rc = msix_irq_setup(lro);
	} else {
		if (!lro->msi_enabled){
			pci_read_config_byte(pdev, PCI_INTERRUPT_PIN, &val);
			dbg_init("Legacy Interrupt register value = %d\n", val);
			if (val > 1) {
				val--;
				w = (val<<24) | (val<<16) | (val<<8)| val;
				// Program IRQ Block Channel vactor and IRQ Block User vector with Legacy interrupt value
				reg = lro->bar[lro->config_bar_idx] + 0x2080;   // IRQ user
				write_register(w, reg);      
				write_register(w, reg+0x4);
				write_register(w, reg+0x8);
				write_register(w, reg+0xC);
				reg = lro->bar[lro->config_bar_idx] + 0x20A0;   // IRQ Block
				write_register(w, reg);     
				write_register(w, reg+0x4);
			}
		}
		irq_flag = lro->msi_enabled ? 0 : IRQF_SHARED;
		lro->irq_line = (int)pdev->irq;
		rc = request_irq(pdev->irq, xdma_isr, irq_flag, DRV_MODULE_NAME, lro);
		if (rc)
			dbg_init("Couldn't use IRQ#%d, rc=%d\n", pdev->irq, rc);
		else
			dbg_init("Using IRQ#%d with 0x%p\n", pdev->irq, lro);
	}

	return rc;
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

static void remove_engines(struct xdma_dev *lro)
{
	struct xdma_engine *engine;
	int i;

	BUG_ON(!lro);

	/* iterate over channels */
	for (i = 0; i < XDMA_CHANNEL_NUM_MAX; i++) {
		engine = &lro->engine_h2c[i];
		if (engine->magic == MAGIC_ENGINE) {
			dbg_sg("Remove %s, %d", engine->name, engine->channel);
			engine_destroy(lro, engine);
			dbg_sg("%s, %d removed", engine->name, engine->channel);
		}

		engine = &lro->engine_c2h[i];
		if (engine->magic == MAGIC_ENGINE) {
			dbg_sg("Remove %s, %d", engine->name, engine->channel);
			engine_destroy(lro, engine);
			dbg_sg("%s, %d removed", engine->name, engine->channel);
		}
	}
}

static int probe_for_engine(struct xdma_dev *lro, enum dma_data_direction dir,
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
		engine = &lro->engine_h2c[channel];
	} else {
		offset += H2C_CHANNEL_OFFSET;
		engine_id_expected = XDMA_ID_C2H;
		engine = &lro->engine_c2h[channel];
	}

	regs = lro->bar[lro->config_bar_idx] + offset;
	engine_id = get_engine_id(regs);
	channel_id = get_engine_channel_id(regs);

	if ((engine_id != engine_id_expected) || (channel_id != channel)) {
		dbg_tfr("%s %d engine, reg off 0x%x, id mismatch 0x%x,0x%x,"
			"exp 0x%x,0x%x, SKIP.\n",
		 	dir == DMA_TO_DEVICE ? "H2C" : "C2H",
			 channel, offset, engine_id, channel_id,
			engine_id_expected, channel_id != channel);
		return 0;
	}

	dbg_tfr("found AXI %s %d engine, reg. off 0x%x, id 0x%x,0x%x.\n",
		 dir == DMA_TO_DEVICE ? "H2C" : "C2H", channel,
		 offset, engine_id, channel_id);

	/* allocate and initialize engine */
	rv = engine_init(engine, lro, offset, dir, channel);
	if (rv != 0) {
		dbg_tfr("failed to create AXI %s %d engine.\n",
			dir == DMA_TO_DEVICE ? "H2C" : "C2H",
			channel);
		return rv;
	}

	return 0;
}

static int probe_engines(struct xdma_dev *lro)
{
	int channel;
	int rc = 0;

	BUG_ON(!lro);

	/* iterate over channels */
	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		rc = probe_for_engine(lro, DMA_TO_DEVICE, channel);
		if (rc)
			goto fail;
	}

	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		rc = probe_for_engine(lro, DMA_FROM_DEVICE, channel);
		if (rc)
			break;
	}

	return rc;

fail:
	dbg_init("Engine probing failed - unwinding\n");
	remove_engines(lro);

	return rc;
}

int xdma_device_open(struct pci_dev *pdev, xdma_channel_tuple **tuple_p)
{
	int i, j;
	int rc = 0;
	struct xdma_dev *lro = NULL;
	xdma_channel_tuple *tuple;

	tuple = kzalloc(sizeof(xdma_channel_tuple) * XDMA_CHANNEL_NUM_MAX,
			GFP_KERNEL);
	if (!tuple)
		return -ENOMEM;

	/* allocate zeroed device book keeping structure */
	lro = alloc_dev_instance(pdev);
	if (!lro)
		goto err_alloc;

	rc = pci_enable_device(pdev);
	if (rc) {
		dbg_init("pci_enable_device() failed, rc = %d.\n", rc);
		goto err_enable;
	}

	/* enable bus master capability */
	dbg_init("pci_set_master()\n");
	pci_set_master(pdev);

	rc = probe_scan_for_msi(lro, pdev);
	if (rc < 0)
		goto err_scan_msi;

	rc = request_regions(lro, pdev);
	if (rc)
		goto err_regions;

	rc = map_bars(lro, pdev);
	if (rc)
		goto err_map;

	rc = set_dma_mask(pdev);
	if (rc)
		goto err_mask;

	rc = irq_setup(lro, pdev);
	if (rc)
		goto err_interrupts;

	rc = probe_engines(lro);
	if (rc)
		goto err_engines;

	channel_interrupts_enable(lro, ~0);

	/* Flush writes */
	read_interrupts(lro);

	lro->feature_id = find_feature_id(lro);
	
	xdev_list_add(lro);

	for (i = 0, j = 0; i < XDMA_CHANNEL_NUM_MAX; i++) {
		if (lro->engine_h2c[i].magic == MAGIC_ENGINE) {
			tuple[j].h2c = &lro->engine_h2c[i];
			tuple[j].c2h = &lro->engine_c2h[i];
			j++;
		}
	}
	*tuple_p = tuple;
	return j;

err_engines:
	remove_engines(lro);
	irq_teardown(lro);
err_interrupts:
err_mask:
	unmap_bars(lro, pdev);
err_map:
	if (lro->got_regions)
		pci_release_regions(pdev);
err_regions:
	if (lro->msi_enabled)
		pci_disable_msi(pdev);
err_scan_msi:
	if (!lro->regions_in_use)
		pci_disable_device(pdev);
err_enable:
	kfree(lro);
err_alloc:
	kfree(tuple);
	return rc;
}
EXPORT_SYMBOL_GPL(xdma_device_open);

void xdma_device_close(struct pci_dev *pdev, xdma_channel_tuple *tuple)
{
	struct xdma_dev *lro;

	if (!pdev)
		return;

	lro = xdev_find_by_pdev(pdev);
	if (!lro) {
		dbg_sg("remove(dev = 0x%p) empty.\n", pdev);
		return;
	}
	dbg_sg("remove(dev = 0x%p) where pdev->dev.driver_data = 0x%p\n",
		   pdev, lro);
	if (lro->pci_dev != pdev) {
		dbg_sg("pci_dev(0x%lx) != pdev(0x%lx)\n",
			(unsigned long)lro->pci_dev, (unsigned long)pdev);
	}

	channel_interrupts_disable(lro, ~0);
	user_interrupts_disable(lro, ~0);
	read_interrupts(lro);

	remove_engines(lro);
	irq_teardown(lro);
	unmap_bars(lro, pdev);

	if (lro->got_regions)
		pci_release_regions(pdev);

	if (lro->msix_enabled) {
		pci_disable_msix(pdev);
		lro->msix_enabled = 0;
	} else if (lro->msi_enabled) {
		pci_disable_msi(pdev);
		lro->msi_enabled = 0;
	}

	if (!lro->regions_in_use)
		pci_disable_device(pdev);

	xdev_list_remove(lro);

	kfree(lro);

	if (tuple)
		kfree(tuple);
}
EXPORT_SYMBOL_GPL(xdma_device_close);

int xdma_device_restart(struct pci_dev *pdev)
{
	struct xdma_dev *lro;

	if (!pdev)
		return -EINVAL;

	lro = xdev_find_by_pdev(pdev);
	if (!lro) {
		dbg_sg("pdev 0x%p, no match found.\n", pdev);
		return -EINVAL;
	}
	dbg_sg("NOT implemented.\n");
	return -EINVAL;
}
EXPORT_SYMBOL_GPL(xdma_device_restart);

int xdma_user_isr_register(struct pci_dev *pdev, unsigned int mask,
		irq_handler_t handler, const char *name, void *dev)
{
	struct xdma_dev *lro;
	int i;

	if (!pdev)
		return -EINVAL;

	lro = xdev_find_by_pdev(pdev);
	if (!lro) {
		dbg_irq("pdev 0x%p, no match found.\n", pdev);
		return -EINVAL;
	}

	for (i = 0; i < MAX_USER_IRQ && mask; i++) {
		unsigned int bit = (1 << i);

		if ((bit & mask) == 0)
			continue;

		mask &= ~bit;
		lro->user_irq[i].handler = handler;
		lro->user_irq[i].name = name;
		lro->user_irq[i].dev = dev;
	}

	return 0;
}
EXPORT_SYMBOL_GPL(xdma_user_isr_register);

int xdma_user_isr_enable(struct pci_dev *pdev, unsigned int mask)
{
	struct xdma_dev *lro;

	if (!pdev)
		return -EINVAL;

	lro = xdev_find_by_pdev(pdev);
	if (!lro) {
		dbg_irq("pdev 0x%p, no match found.\n", pdev);
		return -EINVAL;
	}

	/* enable user interrupts */
	user_interrupts_enable(lro, mask);
	read_interrupts(lro);

	return 0;
}
EXPORT_SYMBOL_GPL(xdma_user_isr_enable);

int xdma_user_isr_disable(struct pci_dev *pdev, unsigned int mask)
{
	struct xdma_dev *lro;
	
	if (!pdev)
		return -EINVAL;

	lro = xdev_find_by_pdev(pdev);
	if (!lro) {
		dbg_irq("pdev 0x%p, no match found.\n", pdev);
		return -EINVAL;
	}

	user_interrupts_disable(lro, mask);
	read_interrupts(lro);

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
