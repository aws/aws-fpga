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

#include <linux/ioctl.h>
#include "version.h"
#include "xdma_cdev.h"
#include "cdev_ctrl.h"

/*
 * character device file operations for control bus (through control bridge)
 */
static ssize_t char_ctrl_read(struct file *fp, char __user *buf, size_t count,
		loff_t *pos)
{
	struct xdma_cdev *xcdev = (struct xdma_cdev *)fp->private_data;
	struct xdma_dev *xdev;
	void *reg;
	u32 w;
	int rv;

	rv = xcdev_check(__func__, xcdev, 0);
	if (rv < 0)
		return rv;	
	xdev = xcdev->xdev;

	/* only 32-bit aligned and 32-bit multiples */
	if (*pos & 3)
		return -EPROTO;
	/* first address is BAR base plus file position offset */
	reg = xdev->bar[xcdev->bar] + *pos;
	//w = read_register(reg);
	w = ioread32(reg);
	dbg_sg("char_ctrl_read(@%p, count=%ld, pos=%d) value = 0x%08x\n", reg,
		(long)count, (int)*pos, w);
	rv = copy_to_user(buf, &w, 4);
	if (rv)
		dbg_sg("Copy to userspace failed but continuing\n");

	*pos += 4;
	return 4;
}

static ssize_t char_ctrl_write(struct file *file, const char __user *buf,
			size_t count, loff_t *pos)
{
	struct xdma_cdev *xcdev = (struct xdma_cdev *)file->private_data;
	struct xdma_dev *xdev;
	void *reg;
	u32 w;
	int rv;

	rv = xcdev_check(__func__, xcdev, 0);
	if (rv < 0)
		return rv;	
	xdev = xcdev->xdev;

	/* only 32-bit aligned and 32-bit multiples */
	if (*pos & 3)
		return -EPROTO;

	/* first address is BAR base plus file position offset */
	reg = xdev->bar[xcdev->bar] + *pos;
	rv = copy_from_user(&w, buf, 4);
	if (rv) {
		pr_info("copy from user failed %d/4, but continuing.\n", rv);
	}

	dbg_sg("char_ctrl_write(0x%08x @%p, count=%ld, pos=%d)\n", w, reg,
		(long)count, (int)*pos);
	//write_register(w, reg);
	iowrite32(w, reg);
	*pos += 4;
	return 4;
}

static long version_ioctl(struct xdma_cdev *xcdev, void __user *arg)
{
	struct xdma_ioc_info obj;
	struct xdma_dev *xdev = xcdev->xdev;
	int rv;

	rv = copy_from_user((void *)&obj, arg, sizeof(struct xdma_ioc_info));
	if (rv) {
		pr_info("copy from user failed %d/%ld.\n",
			rv, sizeof(struct xdma_ioc_info));
		return -EFAULT;
	}
	memset(&obj, 0, sizeof(obj));
	obj.vendor = xdev->pdev->vendor;
	obj.device = xdev->pdev->device;
	obj.subsystem_vendor = xdev->pdev->subsystem_vendor;
	obj.subsystem_device = xdev->pdev->subsystem_device;
	obj.feature_id = xdev->feature_id;
	obj.driver_version = DRV_MOD_VERSION_NUMBER;
	obj.domain = 0;
	obj.bus = PCI_BUS_NUM(xdev->pdev->devfn);
	obj.dev = PCI_SLOT(xdev->pdev->devfn);
	obj.func = PCI_FUNC(xdev->pdev->devfn);
	if (copy_to_user(arg, &obj, sizeof(struct xdma_ioc_info)))
		return -EFAULT;
	return 0;
}

long char_ctrl_ioctl(struct file *filp, unsigned int cmd, unsigned long arg)
{
	struct xdma_cdev *xcdev = (struct xdma_cdev *)filp->private_data;
	struct xdma_dev *xdev;
	struct xdma_ioc_base ioctl_obj;
	long result = 0;
	int rv;

	rv = xcdev_check(__func__, xcdev, 0);
	if (rv < 0)
		return rv;	
	xdev = xcdev->xdev;

	pr_info("cmd 0x%x, xdev 0x%p, pdev 0x%p.\n", cmd, xdev, xdev->pdev);

	if (_IOC_TYPE(cmd) != XDMA_IOC_MAGIC) {
		pr_err("cmd %u, bad magic 0x%x/0x%x.\n",
			 cmd, _IOC_TYPE(cmd), XDMA_IOC_MAGIC);
		return -ENOTTY;
	}

	if (_IOC_DIR(cmd) & _IOC_READ)
		result = !access_ok(VERIFY_WRITE, (void __user *)arg,
				_IOC_SIZE(cmd));
	else if (_IOC_DIR(cmd) & _IOC_WRITE)
		result =  !access_ok(VERIFY_READ, (void __user *)arg,
				_IOC_SIZE(cmd));

	if (result) {
		pr_err("bad access %ld.\n", result);
		return -EFAULT;
	}

	switch (cmd) {
	case XDMA_IOCINFO:
		if (copy_from_user((void *)&ioctl_obj, (void *) arg,
			 sizeof(struct xdma_ioc_base))) {
			pr_err("copy_from_user failed.\n");
			return -EFAULT;
		}

		if (ioctl_obj.magic != XDMA_XCL_MAGIC) {
			pr_err("magic 0x%x !=  XDMA_XCL_MAGIC (0x%x).\n",
				ioctl_obj.magic, XDMA_XCL_MAGIC);
			return -ENOTTY;
		}

		return version_ioctl(xcdev, (void __user *)arg);
	case XDMA_IOCOFFLINE:
		if (!xdev) {
			pr_info("cmd %u, xdev NULL.\n", cmd);
			return -EINVAL;
		}
		xdma_device_offline(xdev->pdev, xdev);
		break;
	case XDMA_IOCONLINE:
		if (!xdev) {
			pr_info("cmd %u, xdev NULL.\n", cmd);
			return -EINVAL;
		}
		xdma_device_online(xdev->pdev, xdev);
		break;
	default:
		pr_err("UNKNOWN ioctl cmd 0x%x.\n", cmd);
		return -ENOTTY;
	}
	return 0;
}

/* maps the PCIe BAR into user space for memory-like access using mmap() */
int bridge_mmap(struct file *file, struct vm_area_struct *vma)
{
	struct xdma_dev *xdev;
	struct xdma_cdev *xcdev = (struct xdma_cdev *)file->private_data;
	unsigned long off;
	unsigned long phys;
	unsigned long vsize;
	unsigned long psize;
	int rv;

	rv = xcdev_check(__func__, xcdev, 0);
	if (rv < 0)
		return rv;	
	xdev = xcdev->xdev;

	off = vma->vm_pgoff << PAGE_SHIFT;
	/* BAR physical address */
	phys = pci_resource_start(xdev->pdev, xcdev->bar) + off;
	vsize = vma->vm_end - vma->vm_start;
	/* complete resource */
	psize = pci_resource_end(xdev->pdev, xcdev->bar) -
		pci_resource_start(xdev->pdev, xcdev->bar) + 1 - off;

	dbg_sg("mmap(): xcdev = 0x%08lx\n", (unsigned long)xcdev);
	dbg_sg("mmap(): cdev->bar = %d\n", xcdev->bar);
	dbg_sg("mmap(): xdev = 0x%p\n", xdev);
	dbg_sg("mmap(): pci_dev = 0x%08lx\n", (unsigned long)xdev->pdev);

	dbg_sg("off = 0x%lx\n", off);
	dbg_sg("start = 0x%llx\n",
		(unsigned long long)pci_resource_start(xdev->pdev,
		xcdev->bar));
	dbg_sg("phys = 0x%lx\n", phys);

	if (vsize > psize)
		return -EINVAL;
	/*
	 * pages must not be cached as this would result in cache line sized
	 * accesses to the end point
	 */
	vma->vm_page_prot = pgprot_noncached(vma->vm_page_prot);
	/*
	 * prevent touching the pages (byte access) for swap-in,
	 * and prevent the pages from being swapped out
	 */
	vma->vm_flags |= VMEM_FLAGS;
	/* make MMIO accessible to user space */
	rv = io_remap_pfn_range(vma, vma->vm_start, phys >> PAGE_SHIFT,
			vsize, vma->vm_page_prot);
	dbg_sg("vma=0x%p, vma->vm_start=0x%lx, phys=0x%lx, size=%lu = %d\n",
		vma, vma->vm_start, phys >> PAGE_SHIFT, vsize, rv);

	if (rv)
		return -EAGAIN;
	return 0;
}

/*
 * character device file operations for control bus (through control bridge)
 */
static const struct file_operations ctrl_fops = {
	.owner = THIS_MODULE,
	.open = char_open,
	.release = char_close,
	.read = char_ctrl_read,
	.write = char_ctrl_write,
	.mmap = bridge_mmap,
	.unlocked_ioctl = char_ctrl_ioctl,
};

void cdev_ctrl_init(struct xdma_cdev *xcdev)
{
	cdev_init(&xcdev->cdev, &ctrl_fops);
}
