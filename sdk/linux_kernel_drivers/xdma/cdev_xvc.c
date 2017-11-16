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

#include "xdma_cdev.h"
#include "cdev_xvc.h"

#define COMPLETION_LOOP_MAX	100

#define XVC_BAR_LENGTH_REG	0x0
#define XVC_BAR_TMS_REG		0x4
#define XVC_BAR_TDI_REG		0x8
#define XVC_BAR_TDO_REG		0xC
#define XVC_BAR_CTRL_REG	0x10

#ifdef __REG_DEBUG__
/* SECTION: Function definitions */
inline void __write_register(const char *fn, u32 value, void *base,
				unsigned int off)
{
        pr_info("%s: 0x%p, W reg 0x%lx, 0x%x.\n", fn, base, off, value);
        iowrite32(value, base + off);
}

inline u32 __read_register(const char *fn, void *base, unsigned int off)
{
	u32 v = ioread32(base + off);

        pr_info("%s: 0x%p, R reg 0x%lx, 0x%x.\n", fn, base, off, v);
        return v;
}
#define write_register(v,base,off) __write_register(__func__, v, base, off)
#define read_register(base,off) __read_register(__func__, base, off)

#else
#define write_register(v,base,off)	iowrite32(v, (base) + (off))
#define read_register(base,off)		ioread32((base) + (off))
#endif /* #ifdef __REG_DEBUG__ */


static int xvc_shift_bits(void *base, u32 tms_bits, u32 tdi_bits,
			u32 *tdo_bits)
{
	u32 control;
	int count;

	/* set tms bit */
	write_register(tms_bits, base, XVC_BAR_TMS_REG);
	/* set tdi bits and shift data out */
	write_register(tdi_bits, base, XVC_BAR_TDI_REG);
	/* enable shift operation */
	write_register(0x1, base, XVC_BAR_CTRL_REG);

	/* poll for completion */
	count = COMPLETION_LOOP_MAX;
	while (count) {
		/* read control reg to check shift operation completion */
		control = read_register(base, XVC_BAR_CTRL_REG);
		if ((control & 0x01) == 0)
			break;

		count--;
	}

	if (!count)	{
		pr_warn("XVC bar transaction timed out (0x%0X)\n", control);
		return -ETIMEDOUT;
	}

	/* read tdo bits back out */
	*tdo_bits = read_register(base, XVC_BAR_TDO_REG);

	return 0;
}

static long xvc_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
        struct xdma_cdev *xcdev = (struct xdma_cdev *)filp->private_data;
	struct xdma_dev *xdev;
	struct xvc_ioc xvc_obj;
	unsigned int opcode;
	unsigned int total_bits;
	unsigned int total_bytes;
	unsigned char *buffer = NULL;
	unsigned char *tms_buf = NULL;
	unsigned char *tdi_buf = NULL;
	unsigned char *tdo_buf = NULL;
	unsigned int bits, bits_left;
	void __iomem *iobase;
	int rv;

	rv = xcdev_check(__func__, xcdev, 0);
	if (rv < 0)
		return rv;
	xdev = xcdev->xdev;

	if (cmd != XDMA_IOCXVC) {
		pr_info("ioctl 0x%x, UNKNOWN cmd.\n", cmd);
		return -ENOIOCTLCMD;
	}

	rv = copy_from_user((void *)&xvc_obj, (void __user *)arg,
				sizeof(struct xvc_ioc));
	/* anything not copied ? */
	if (rv) {
		pr_info("copy_from_user xvc_obj failed: %d.\n", rv);
		goto cleanup;
	}

	opcode = xvc_obj.opcode;

	/* Invalid operation type, no operation performed */
	if (opcode != 0x01 && opcode != 0x02) {
		pr_info("UNKNOWN opcode 0x%x.\n", opcode);
		return -EINVAL;
	}

	total_bits = xvc_obj.length;
	total_bytes = (total_bits + 7) >> 3;

	buffer = (char *)kmalloc(total_bytes * 3, GFP_KERNEL);
	if (!buffer) {
		pr_info("OOM %u, op 0x%x, len %u bits, %u bytes.\n",
			3 * total_bytes, opcode, total_bits, total_bytes);
		rv = -ENOMEM;
		goto cleanup;
	}
	tms_buf = buffer;
	tdi_buf = tms_buf + total_bytes;
	tdo_buf = tdi_buf + total_bytes;

	rv = copy_from_user((void *)tms_buf, xvc_obj.tms_buf, total_bytes);
	if (rv) {
		pr_info("copy tmfs_buf failed: %d/%u.\n", rv, total_bytes);
		goto cleanup;
	}
	rv = copy_from_user((void *)tdi_buf, xvc_obj.tdi_buf, total_bytes);
	if (rv) {
		pr_info("copy tdi_buf failed: %d/%u.\n", rv, total_bytes);
		goto cleanup;
	}

	/* exclusive access */
	spin_lock(&xcdev->lock);

	iobase = xdev->bar[xcdev->bar] + xcdev->base;
	/* set length register to 32 initially if more than one
	 * word-transaction is to be done */
	if (total_bits >= 32)
		write_register(0x20, iobase, XVC_BAR_LENGTH_REG);

	for (bits = 0, bits_left = total_bits; bits < total_bits; bits += 32,
		bits_left -= 32) {
		unsigned int bytes = bits >> 3;
		unsigned int shift_bytes = 4;
		u32 tms_store = 0;
		u32 tdi_store = 0;
		u32 tdo_store = 0;
		
		if (bits_left < 32) {
			/* set number of bits to shift out */
			write_register(bits_left, iobase, XVC_BAR_LENGTH_REG);
			shift_bytes = (bits_left + 7) >> 3;
		}

		memcpy(&tms_store, tms_buf + bytes, shift_bytes);
		memcpy(&tdi_store, tdi_buf + bytes, shift_bytes);

		/* Shift data out and copy to output buffer */
		rv = xvc_shift_bits(iobase, tms_store, tdi_store, &tdo_store);
		if (rv < 0)
			goto cleanup;

		memcpy(tdo_buf + bytes, &tdo_store, shift_bytes);
	}

	/* if testing bar access swap tdi and tdo bufferes to "loopback" */
	if (opcode == 0x2) {
		char *tmp = tdo_buf;

		tdo_buf = tdi_buf;
		tdi_buf = tmp;
	}

	rv = copy_to_user((void *)xvc_obj.tdo_buf, tdo_buf, total_bytes);
	if (rv) {
		pr_info("copy back tdo_buf failed: %d/%u.\n", rv, total_bytes);
		rv = -EFAULT;
		goto cleanup;
	}

cleanup:
	if (buffer)
		kfree(buffer);

	mmiowb();
	spin_unlock(&xcdev->lock);

	return rv;
}

/*
 * character device file operations for the XVC
 */
static const struct file_operations xvc_fops = {
        .owner = THIS_MODULE,
        .open = char_open,
        .release = char_close,
        .unlocked_ioctl = xvc_ioctl,
};

void cdev_xvc_init(struct xdma_cdev *xcdev)
{
#ifdef __XVC_BAR_NUM__
	xcdev->bar = __XVC_BAR_NUM__;
#endif
#ifdef __XVC_BAR_OFFSET__
	xcdev->base = __XVC_BAR_OFFSET__;
#else
	xcdev->base = XVC_BAR_OFFSET_DFLT;
#endif
	pr_info("xcdev 0x%p, bar %u, offset 0x%lx.\n",
		xcdev, xcdev->bar, xcdev->base);
	cdev_init(&xcdev->cdev, &xvc_fops);
}
