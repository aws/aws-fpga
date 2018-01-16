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

#include "libxdma_api.h"
#include "xdma_cdev.h"

#define write_register(v,mem,off) iowrite32(v, mem)

static int copy_desc_data(struct xdma_transfer *transfer, char __user *buf,
		size_t *buf_offset, size_t buf_size)
{
	int i;
	int copy_err;
	int rc = 0;

	BUG_ON(!buf);
	BUG_ON(!buf_offset);

	/* Fill user buffer with descriptor data */
	for (i = 0; i < transfer->desc_num; i++) {
		if (*buf_offset + sizeof(struct xdma_desc) <= buf_size) {
			copy_err = copy_to_user(&buf[*buf_offset],
				transfer->desc_virt + i,
				sizeof(struct xdma_desc));

			if (copy_err) {
				dbg_sg("Copy to user buffer failed\n");
				*buf_offset = buf_size;
				rc = -EINVAL;
			} else {
				*buf_offset += sizeof(struct xdma_desc);
			}
		} else {
			rc = -ENOMEM;
		}
	}

	return rc;
}

static ssize_t char_bypass_read(struct file *file, char __user *buf,
		size_t count, loff_t *pos)
{
	struct xdma_dev *xdev;
	struct xdma_engine *engine;
	struct xdma_cdev *xcdev = (struct xdma_cdev *)file->private_data;
	struct xdma_transfer *transfer;
	struct list_head *idx;
	size_t buf_offset = 0;
	int rc = 0;

	rc = xcdev_check(__func__, xcdev, 1);
	if (rc < 0)
		return rc;
	xdev = xcdev->xdev;
	engine = xcdev->engine;

	dbg_sg("In char_bypass_read()\n");

	if (count & 3) {
		dbg_sg("Buffer size must be a multiple of 4 bytes\n");
		return -EINVAL;
	}

	if (!buf) {
		dbg_sg("Caught NULL pointer\n");
		return -EINVAL;
	}

	if (xdev->bypass_bar_idx < 0) {
		dbg_sg("Bypass BAR not present - unsupported operation\n");
		return -ENODEV;
	}

	spin_lock(&engine->lock);

	if (!list_empty(&engine->transfer_list)) {
		list_for_each(idx, &engine->transfer_list) {
			transfer = list_entry(idx, struct xdma_transfer, entry);

			rc = copy_desc_data(transfer, buf, &buf_offset, count);
		}
	}

	spin_unlock(&engine->lock);

	if (rc < 0)
		return rc;
	else
		return buf_offset;
}

static ssize_t char_bypass_write(struct file *file, const char __user *buf,
		size_t count, loff_t *pos)
{
	struct xdma_dev *xdev;
	struct xdma_engine *engine;
	struct xdma_cdev *xcdev = (struct xdma_cdev *)file->private_data;

	u32 desc_data;
	u32 *bypass_addr;
	size_t buf_offset = 0;
	int rc = 0;
	int copy_err;

	rc = xcdev_check(__func__, xcdev, 1);
	if (rc < 0)
		return rc;
	xdev = xcdev->xdev;
	engine = xcdev->engine;

	if (count & 3) {
		dbg_sg("Buffer size must be a multiple of 4 bytes\n");
		return -EINVAL;
	}

	if (!buf) {
		dbg_sg("Caught NULL pointer\n");
		return -EINVAL;
	}

	if (xdev->bypass_bar_idx < 0) {
		dbg_sg("Bypass BAR not present - unsupported operation\n");
		return -ENODEV;
	}

	dbg_sg("In char_bypass_write()\n");

	spin_lock(&engine->lock);

	/* Write descriptor data to the bypass BAR */
	bypass_addr = (u32 *)xdev->bar[xdev->bypass_bar_idx];
	bypass_addr += engine->bypass_offset;
	while (buf_offset < count) {
		copy_err = copy_from_user(&desc_data, &buf[buf_offset],
			sizeof(u32));
		if (!copy_err) {
			write_register(desc_data, bypass_addr, bypass_addr - engine->bypass_offset);
			buf_offset += sizeof(u32);
			rc = buf_offset;
		} else {
			dbg_sg("Error reading data from userspace buffer\n");
			rc = -EINVAL;
			break;
		}
	}

	spin_unlock(&engine->lock);


	return rc;
}


/*
 * character device file operations for bypass operation
 */

static const struct file_operations bypass_fops = {
	.owner = THIS_MODULE,
	.open = char_open,
	.release = char_close,
	.read = char_bypass_read,
	.write = char_bypass_write,
	.mmap = bridge_mmap,
};

void cdev_bypass_init(struct xdma_cdev *xcdev)
{
        cdev_init(&xcdev->cdev, &bypass_fops);
}
