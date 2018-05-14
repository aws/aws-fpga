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
 * Sonal Santan <sonal.santan@xilinx.com>
 *
 ******************************************************************************/

#define pr_fmt(fmt)     KBUILD_MODNAME ":%s: " fmt, __func__

#include <linux/types.h>
#include <linux/uaccess.h>
#include <linux/vmalloc.h>
#include <linux/slab.h>
#include <linux/cdev.h>
#include <linux/fs.h>
#include <linux/device.h>
#include <linux/io.h>

#include "xocl_xvc.h"
#include "xvc_pcie_ioctl.h"

#define DEFAULT_XVC_BAR_OFFSET 0xC0000  // DSA 4.1 and 5.0
#define DEFAULT_XVC_BAR        0

#define COMPLETION_LOOP_MAX	100

#define XVC_BAR_LENGTH_REG	0x0
#define XVC_BAR_TMS_REG		0x4
#define XVC_BAR_TDI_REG		0x8
#define XVC_BAR_TDO_REG		0xC
#define XVC_BAR_CTRL_REG	0x10

#define XVC_DEV_NAME "xvc"

static dev_t xvc_dev;
static int instance = 0;
static struct class *xvc_class = NULL;

#ifdef __REG_DEBUG__
/* SECTION: Function definitions */
static inline void __write_register(const char *fn, u32 value, void *base,
				unsigned int off)
{
        pr_info("%s: 0x%p, W reg 0x%lx, 0x%x.\n", fn, base, off, value);
        iowrite32(value, base + off);
}

static inline u32 __read_register(const char *fn, void *base, unsigned int off)
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

static long xvc_ioctl_helper(struct xocl_xvc *xvc, const void __user *arg)
{
	struct xil_xvc_ioc xvc_obj;
	unsigned int opcode;
	unsigned int total_bits;
	unsigned int total_bytes;
	unsigned int bits, bits_left;
	unsigned char *buffer = NULL;
	unsigned char *tms_buf = NULL;
	unsigned char *tdi_buf = NULL;
	unsigned char *tdo_buf = NULL;
	void __iomem *iobase = xvc->bar + DEFAULT_XVC_BAR_OFFSET;
	int rv;

	rv = copy_from_user((void *)&xvc_obj, arg,
				sizeof(struct xil_xvc_ioc));
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

	return rv;
}

long xvc_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
	struct xocl_xvc *xvc = filp->private_data;
	return xvc_ioctl_helper(xvc, (void __user *)arg);
}

static int char_open(struct inode *inode, struct file *file)
{
	struct xocl_xvc *xvc = NULL;

	/* pointer to containing structure of the character device inode */
	xvc = container_of(inode->i_cdev, struct xocl_xvc, sys_cdev);
	/* create a reference to our char device in the opened file */
	file->private_data = xvc;
	return 0;
}

/*
 * Called when the device goes from used to unused.
 */
static int char_close(struct inode *inode, struct file *file)
{
	return 0;
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

int xocl_xvc_device_init(struct xocl_xvc *xvc, struct device *dev)
{
	int err;
#ifdef __XVC_BAR_NUM__
	xcdev->bar = __XVC_BAR_NUM__;
#endif
#ifdef __XVC_BAR_OFFSET__
	xcdev->base = __XVC_BAR_OFFSET__;
#else
	xvc->base = XVC_BAR_OFFSET_DFLT;
#endif
	pr_info("xcdev 0x%p, offset 0x%lx.\n",
		xvc, xvc->base);

	cdev_init(&xvc->sys_cdev, &xvc_fops);
	xvc->sys_cdev.owner = THIS_MODULE;
	xvc->instance = instance++;
	xvc->sys_cdev.dev = MKDEV(MAJOR(xvc_dev), xvc->instance);
	err = cdev_add(&xvc->sys_cdev, xvc->sys_cdev.dev, 1);
	if (err)
		return err;

	xvc->sys_device = device_create(xvc_class, dev,
					xvc->sys_cdev.dev,
					NULL, XVC_DEV_NAME "%d", xvc->instance);
	if (IS_ERR(xvc->sys_device)) {
		err = PTR_ERR(xvc->sys_device);
		cdev_del(&xvc->sys_cdev);
	}

	if (!err)
		pr_info("XVC device instance %d initialized\n", xvc->instance);
	return err;
}


int xocl_xvc_device_fini(struct xocl_xvc *xvc)
{
	device_destroy(xvc_class, xvc->sys_cdev.dev);
	cdev_del(&xvc->sys_cdev);
	return 0;
}

int xocl_xvc_chardev_init()
{
	int err = 0;

	err = alloc_chrdev_region(&xvc_dev, 0, 16, XVC_DEV_NAME);
	if (err < 0)
		goto err_register_chrdev;

	xvc_class = class_create(THIS_MODULE, XVC_DEV_NAME);
	if (IS_ERR(xvc_class)) {
		err = PTR_ERR(xvc_class);
		goto err_class_create;
	}
	return 0;

err_class_create:
	unregister_chrdev_region(xvc_dev, 16);
err_register_chrdev:
	return err;
}

void xocl_xvc_chardev_exit()
{
	unregister_chrdev_region(xvc_dev, 16);
	class_destroy(xvc_class);
}
