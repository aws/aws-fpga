/*
 * Copyright (C) 2016-2018 Xilinx, Inc
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
 *    Hem Neema <hem.neema@xilinx.com>
 *
 * A GEM style device manager for PCIe based OpenCL accelerators.
 *
 * This software is licensed under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation, and
 * may be copied, distributed, and modified under those terms.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#include <linux/module.h>
#include <linux/version.h>
#if LINUX_VERSION_CODE <= KERNEL_VERSION(3,0,0)
#include <drm/drm_backport.h>
#endif
#include <drm/drmP.h>
#include <drm/drm_gem.h>
#include <linux/aer.h>
#include <linux/eventfd.h>
#ifdef XOCL_CMA_ALLOC
#include <linux/cma.h>
#endif
#include "xocl_drv.h"
#include "xocl_ioctl.h"
#include "xocl_xdma.h"
#include "xclbin.h"

#define XOCL_DRIVER_NAME        "xocl"
#define XOCL_DRIVER_DESC        "Xilinx PCIe Accelerator Device Manager"
#define XOCL_DRIVER_DATE        "20171111"
#define XOCL_DRIVER_MAJOR       2017
#define XOCL_DRIVER_MINOR       4
#define XOCL_DRIVER_PATCHLEVEL  5


#define XOCL_DRIVER_VERSION			\
	__stringify(XOCL_DRIVER_MAJOR) "."	\
	__stringify(XOCL_DRIVER_MINOR) "."	\
	__stringify(XOCL_DRIVER_PATCHLEVEL)

#define XOCL_DRIVER_VERSION_NUMBER					\
	((XOCL_DRIVER_MAJOR)*1000 + (XOCL_DRIVER_MINOR)*100 + XOCL_DRIVER_PATCHLEVEL)


#define XOCL_FILE_PAGE_OFFSET   0x100000

#ifndef VM_RESERVED
#define VM_RESERVED (VM_DONTEXPAND | VM_DONTDUMP)
#endif

static const struct pci_device_id pciidlist[] = {
	{ PCI_DEVICE(0x10ee, 0x4A48), },
	{ PCI_DEVICE(0x10ee, 0x4A88), },
	{ PCI_DEVICE(0x10ee, 0x4B48), },
	{ PCI_DEVICE(0x10ee, 0x4B88), },
	{ PCI_DEVICE(0x10ee, 0x6850), },
	{ PCI_DEVICE(0x10ee, 0x6890), },
	{ PCI_DEVICE(0x10ee, 0x6950), },
	{ PCI_DEVICE(0x10ee, 0x6990), },
	{ PCI_DEVICE(0x10ee, 0x6A50), },
	{ PCI_DEVICE(0x10ee, 0x6A90), },
	{ PCI_DEVICE(0x10ee, 0x6E50), },
	{ PCI_DEVICE(0x10ee, 0x6B10), },
	//{ PCI_DEVICE(0x1d0f, 0x1042), },
	{ PCI_DEVICE(0x1d0f, 0xf000), },
	{ 0, }
};

MODULE_DEVICE_TABLE(pci, pciidlist);

static struct cma *xocl_cma = NULL;

static void xocl_print_dev_info(const struct drm_xocl_dev *xdev)
{
	DRM_INFO("%s [Timestamp 0x%llx]\n", xdev->header.VBNVName, xdev->header.TimeSinceEpoch);
	DRM_INFO("%d bi-directional DMA channels\n", xdev->channel);
	DRM_INFO("%d DDR channels, Total RAM = %dGB\n", xdev->header.DDRChannelCount,
		 xdev->header.DDRChannelSize * xdev->header.DDRChannelCount);
	DRM_INFO("PCI Resource 0x%llx [Size 0x%llxKB]\n", xdev->res_start, xdev->res_len/1024);
}

static int probe_feature_rom(struct drm_xocl_dev *xdev)
{
	u32 val;
	unsigned short ddr = (xdev->ddev->pdev->subsystem_device >> 12) & 0x000f;
	val = ioread32(xdev->user_bar + XOCL_FEATURE_ROM);
	// Magic number check
	if (val != 0x786e6c78) {
      if (xdev->ddev->pdev->vendor == 0x1d0f && (xdev->ddev->pdev->device == 0x1042 || xdev->ddev->pdev->device == 0xf000)) {
        printk(KERN_INFO "XOCL: Found AWS VU9P Device without featureROM\n");
        //This is AWS device. Fill the FeatureROM struct. Right now it doesn't have FeatureROM
        memset(xdev->header.EntryPointString, 0, sizeof(xdev->header.EntryPointString));
        strncpy(xdev->header.EntryPointString, "xlnx", 4);
        memset(xdev->header.FPGAPartName, 0, sizeof(xdev->header.FPGAPartName));
        strncpy(xdev->header.FPGAPartName, "AWS VU9P", 8);
        memset(xdev->header.VBNVName, 0, sizeof(xdev->header.VBNVName));
        strncpy(xdev->header.VBNVName, "xilinx_aws-vu9p-f1_dynamic_5_0", 35);
        xdev->header.MajorVersion = 4;
        xdev->header.MinorVersion = 0;
        xdev->header.VivadoBuildID = 0xabcd;
        xdev->header.IPBuildID = 0xabcd;
        xdev->header.TimeSinceEpoch = 0xabcd;
        xdev->header.DDRChannelCount = 4;
        xdev->header.DDRChannelSize = 16;
        xdev->header.FeatureBitMap = 0x0;
        printk(KERN_INFO "XOCL: Enabling AWS dynamic 5.0 DSA\n");
        xdev->header.FeatureBitMap = UNIFIED_PLATFORM;
        xdev->unified = true;
      } else {
        DRM_ERROR("XOCL: Probe of Feature ROM failed\n");
        return -ENODEV;
      }
	} else {
	    printk(KERN_INFO "XOCL: Printing PCI VendorID: %llx\n", xdev->ddev->pdev->vendor);
	    printk(KERN_INFO "XOCL: Printing PCI DeviceID: %llx\n", xdev->ddev->pdev->device);
	    memcpy_fromio(&xdev->header, xdev->user_bar + XOCL_FEATURE_ROM, sizeof(struct FeatureRomHeader));
	    // Sanity check
	    if (strstr(xdev->header.VBNVName, "-xare")) {//This is ARE device
	      xdev->header.DDRChannelCount = xdev->header.DDRChannelCount - 1; //ARE is mapped like another DDR inside FPGA; map_connects as M04_AXI
	    }
	    if (ddr != xdev->header.DDRChannelCount) {
	        DRM_ERROR("XOCL: Feature ROM DDR channel count not consistent\n");
	        return -ENODEV;
	    }

	    if(xdev->header.FeatureBitMap & UNIFIED_PLATFORM) {
	        xdev->unified = true;
	    }
	}

    printk(KERN_INFO "XOCL: ROM magic : %s\n", xdev->header.EntryPointString);
	printk(KERN_INFO "XOCL: VBNV: %s", xdev->header.VBNVName);
	printk(KERN_INFO "XOCL: DDR channel count : %d\n", xdev->header.DDRChannelCount);
	printk(KERN_INFO "XOCL: DDR channel size: %d GB\n", xdev->header.DDRChannelSize);
	printk(KERN_INFO "XOCL: Major Version: %d \n", xdev->header.MajorVersion);
	printk(KERN_INFO "XOCL: Minor Version: %d \n", xdev->header.MinorVersion);
	printk(KERN_INFO "XOCL: IPBuildID: %u\n", xdev->header.IPBuildID);
	printk(KERN_INFO "XOCL: TimeSinceEpoch: %llx\n", xdev->header.TimeSinceEpoch);
	printk(KERN_INFO "XOCL: FeatureBitMap: %llx\n", xdev->header.FeatureBitMap);

//	if(xdev->header.MajorVersion >= 10)
//		printk(KERN_INFO "Printing DRBaseAddress: %llx\n", xdev->header.DRBaseAddress);
	return 0;
}

static int xocl_drm_load(struct drm_device *ddev, unsigned long flags)
{
	struct drm_xocl_dev *xdev;
	unsigned i;
	int result = 0;
	unsigned long long segment = 0;
	unsigned short ddr = 0;
	unsigned long long ddr_size = 0;

#if LINUX_VERSION_CODE <= KERNEL_VERSION(4,4,0)
	drm_dev_set_unique(ddev, dev_name(ddev->dev));
#endif

	xdev = devm_kzalloc(ddev->dev, sizeof(*xdev), GFP_KERNEL);
	if (!xdev)
		return -ENOMEM;
	xdev->ddev = ddev;
	ddev->dev_private = xdev;

	xdev->res_start = pci_resource_start(xdev->ddev->pdev, 0);
	xdev->res_len = pci_resource_end(xdev->ddev->pdev, 0) - xdev->res_start + 1;

	xdev->user_bar = pci_iomap(xdev->ddev->pdev, 0, xdev->res_len);
	if (!xdev->user_bar)
		return -EIO;

	result = probe_feature_rom(xdev);
	if (result)
		goto bar_cleanup;


	if (xdev->unified) {
		memset(&xdev->topology, 0, sizeof(struct drm_xocl_mem_topology));
		memset(&xdev->connectivity, 0, sizeof(struct drm_xocl_connectivity));
		memset(&xdev->layout, 0, sizeof(struct drm_xocl_layout));
		memset(&xdev->debug_layout, 0, sizeof(struct drm_xocl_debug_layout));
	} else {
		printk(KERN_INFO "XOCL : non-unified ddr initialization.\n");
		ddr = xocl_ddr_channel_count(ddev);
		ddr_size = xocl_ddr_channel_size(ddev);

		xdev->mm = devm_kzalloc(ddev->dev, sizeof(struct drm_mm) * ddr, GFP_KERNEL);
		xdev->mm_usage_stat = devm_kzalloc(ddev->dev, sizeof(struct drm_xocl_mm_stat) * ddr, GFP_KERNEL);
		if (!xdev->mm || !xdev->mm_usage_stat) {
			result = -ENOMEM;
			goto bar_cleanup;
		}

		for (i = 0; i < ddr; i++) {
			drm_mm_init(&xdev->mm[i], segment, ddr_size);
			segment += ddr_size;
		}
	}

	mutex_init(&xdev->mm_lock);
	// Now call XDMA core init
	DRM_INFO("Enable XDMA core\n");
	result = xdma_init_glue(xdev);
	if (result) {
		DRM_ERROR("XDMA device initialization failed with err code: %d\n", result);
		goto mm_cleanup;
	}

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);

	sema_init(&xdev->channel_sem[0], xdev->channel);
	sema_init(&xdev->channel_sem[1], xdev->channel);
	/* Initialize bit mask to represent individual channels */
	xdev->channel_bitmap[0] = BIT(xdev->channel);
	xdev->channel_bitmap[0]--;
	xdev->channel_bitmap[1] = xdev->channel_bitmap[0];

	xdev->channel_usage[0] = devm_kzalloc(ddev->dev, sizeof(unsigned long long) * xdev->channel, GFP_KERNEL);
	xdev->channel_usage[1] = devm_kzalloc(ddev->dev, sizeof(unsigned long long) * xdev->channel, GFP_KERNEL);

	if (!xdev->channel_usage[0] || !xdev->channel_usage[1]) {
		result = -ENOMEM;
		goto xdma_cleanup;
	}

	xdev->cma_blk = xocl_cma;

	mutex_init(&xdev->stat_lock);
	xdev->offline = false;
	xocl_print_dev_info(xdev);

	//Init xocl sysfs
	xocl_fini_sysfs(&xdev->ddev->pdev->dev);
	result = xocl_init_sysfs(&xdev->ddev->pdev->dev);
	if (result) {
		DRM_ERROR("failed to create sysds file for xocl: %d\n", result);
		goto all_cleanup;
	}

	xocl_init_exec(xdev);
	xdev->xvc.bar = xdev->user_bar;
#ifdef XOCL_BUILTIN_XVC
	xocl_xvc_device_init(&xdev->xvc, &xdev->ddev->pdev->dev);
#endif
	return result;

all_cleanup:
	mutex_destroy(&xdev->stat_lock);
xdma_cleanup:
	xdma_fini_glue(xdev);
mm_cleanup:
	if (!xdev->unified) {
		for (i = 0; i < ddr; i++) {
			drm_mm_takedown(&xdev->mm[i]);
		}
	}
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
bar_cleanup:
	pci_iounmap(xdev->ddev->pdev, xdev->user_bar);
	xdev->user_bar = NULL;
	return result;
}

static int xocl_drm_unload(struct drm_device *drm)
{
	int i = 0;
	struct drm_xocl_dev *xdev = drm->dev_private;
	const unsigned short ddr = xocl_ddr_channel_count(drm);

	xdev->offline = true;
#ifdef XOCL_BUILTIN_XVC
	xocl_xvc_device_fini(&xdev->xvc);
#endif
	xocl_fini_exec(xdev);

	if(xdev->unified) {
		for (i = 0; i < ddr; i++) {
			if(xdev->topology.m_data[i].m_used)
				drm_mm_takedown(&xdev->mm[i]);
		}
		vfree(xdev->topology.m_data);
		vfree(xdev->topology.topology);
		memset(&xdev->topology, 0, sizeof(xdev->topology));
		vfree(xdev->connectivity.connections);
		memset(&xdev->connectivity, 0, sizeof(xdev->connectivity));
		vfree(xdev->layout.layout);
		memset(&xdev->layout, 0, sizeof(xdev->layout));
		vfree(xdev->debug_layout.layout);
		memset(&xdev->debug_layout, 0, sizeof(xdev->debug_layout));
	} else {
		for (i = 0; i < ddr; i++) {
			drm_mm_takedown(&xdev->mm[i]);
		}
	}

	mutex_destroy(&xdev->stat_lock);
	mutex_destroy(&xdev->mm_lock);

	pci_iounmap(xdev->ddev->pdev, xdev->user_bar);
	xdma_fini_glue(xdev);
	xocl_fini_sysfs(&xdev->ddev->pdev->dev);
	dev_set_drvdata(&xdev->ddev->pdev->dev, NULL);
	return 0;
}

#if (LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0) ||  \
        (defined(RHEL_RELEASE_CODE) && \
        RHEL_RELEASE_CODE >=RHEL_RELEASE_VERSION(7,5)))
static void xocl_drm_unload2(struct drm_device *drm)
{
	xocl_drm_unload(drm);
}
#endif

static void xocl_free_object(struct drm_gem_object *obj)
{
	xocl_free_bo(obj);
}

static int xocl_mmap(struct file *filp, struct vm_area_struct *vma)
{
	int ret;
	struct drm_file *priv = filp->private_data;
	struct drm_device *dev = priv->minor->dev;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct mm_struct *mm = current->mm;
	unsigned long vsize;

	//DRM_DEBUG("mmap operation 0x%lx 0x%lx 0x%lx\n", vma->vm_start, vma->vm_end, vma->vm_pgoff);
	/* If the page offset is > than 4G, then let GEM handle that and do what
	 * it thinks is best,we will only handle page offsets less than 4G.
	 */
	if (likely(vma->vm_pgoff >= XOCL_FILE_PAGE_OFFSET)) {
		ret = drm_gem_mmap(filp, vma);
		if (ret)
			return ret;
		/* Clear VM_PFNMAP flag set by drm_gem_mmap()
		 * we have "struct page" for all backing pages for bo
		 */
		vma->vm_flags &= ~VM_PFNMAP;
		/* Clear VM_IO flag set by drm_gem_mmap()
		 * it prevents gdb from accessing mapped buffers
		 */
		vma->vm_flags &= ~VM_IO;
		vma->vm_flags |= VM_MIXEDMAP;
		vma->vm_flags |= mm->def_flags;
		vma->vm_pgoff = 0;

		/* Override pgprot_writecombine() mapping setup by drm_gem_mmap()
		 * which results in very poor read performance
		 */
		if (vma->vm_flags & (VM_READ | VM_MAYREAD))
			vma->vm_page_prot = vm_get_page_prot(vma->vm_flags);
		else
			vma->vm_page_prot = pgprot_writecombine(vm_get_page_prot(vma->vm_flags));
		return ret;
	}

	if (vma->vm_pgoff != 0)
		return -EINVAL;

	vsize = vma->vm_end - vma->vm_start;
	if (vsize > xdev->res_len)
		return -EINVAL;

	vma->vm_page_prot = pgprot_noncached(vma->vm_page_prot);
	vma->vm_flags |= VM_IO;
	vma->vm_flags |= VM_RESERVED;

	ret = io_remap_pfn_range(vma, vma->vm_start,
				 xdev->res_start >> PAGE_SHIFT,
				 vsize, vma->vm_page_prot);
	DRM_INFO("io_remap_pfn_range ret code: %d", ret);

	return ret;

}

int xocl_gem_fault(struct vm_area_struct *vma, struct vm_fault *vmf)
{
	struct drm_xocl_bo *xobj = to_xocl_bo(vma->vm_private_data);
	loff_t num_pages;
	unsigned int page_offset;
	int ret = 0;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,10,0)
	page_offset = (vmf->address - vma->vm_start) >> PAGE_SHIFT;
#else
	page_offset = ((unsigned long)vmf->virtual_address - vma->vm_start) >> PAGE_SHIFT;
#endif

	if (!xobj->pages)
		return VM_FAULT_SIGBUS;

	num_pages = DIV_ROUND_UP(xobj->base.size, PAGE_SIZE);
	if (page_offset > num_pages)
		return VM_FAULT_SIGBUS;

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,10,0)
	ret = vm_insert_page(vma, vmf->address, xobj->pages[page_offset]);
#else
	ret = vm_insert_page(vma, (unsigned long)vmf->virtual_address, xobj->pages[page_offset]);
#endif
	switch (ret) {
	case -EAGAIN:
	case 0:
	case -ERESTARTSYS:
		return VM_FAULT_NOPAGE;
	case -ENOMEM:
		return VM_FAULT_OOM;
	default:
		return VM_FAULT_SIGBUS;
	}
}

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
int xocl_gem_fault2(struct vm_fault *vmf)
{
	return xocl_gem_fault(vmf->vma, vmf);
}
#endif

static int xocl_info_ioctl(struct drm_device *dev,
			void *data,
			struct drm_file *filp)
{
	struct drm_xocl_info *obj = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct pci_dev *pdev = xdev->ddev->pdev;
	printk(KERN_INFO "%s %s INFO IOCTL \n", DRV_NAME, __FUNCTION__);

	obj->vendor = pdev->vendor;
	obj->device = pdev->device;
	obj->subsystem_vendor = pdev->subsystem_vendor;
	obj->subsystem_device = pdev->subsystem_device;
	obj->driver_version = XOCL_DRIVER_VERSION_NUMBER;
	obj->pci_slot = PCI_SLOT(pdev->devfn);

	printk(KERN_INFO "%s %s PCI Slot: %d \n", DRV_NAME, __FUNCTION__, obj->pci_slot);
	return 0;
}

static int xocl_client_open(struct drm_device *dev, struct drm_file *filp)
{
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_client_ctx *fpriv = kzalloc(sizeof(*fpriv), GFP_KERNEL);
	if (!fpriv)
		return -ENOMEM;
	filp->driver_priv = fpriv;
	mutex_init(&fpriv->lock);
	atomic_set(&fpriv->trigger, 0);
	xocl_track_ctx(xdev, fpriv);
	DRM_INFO("Pid %d opened device\n", pid_nr(task_tgid(current)));
	return 0;
}

static void xocl_client_release(struct drm_device *dev, struct drm_file *filp)
{
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_client_ctx *fpriv = filp->driver_priv;
	int i;
	unsigned bit;

	if (!fpriv)
		return;

	xocl_untrack_ctx(xdev, fpriv);
	if (!fpriv->eventfd_bitmap)
		goto out;

	/* Clear all the eventfd structures */
	mutex_lock(&xdev->exec.user_msix_table_lock);
	for (i = XOCL_USER_INTR_START; i < XOCL_USER_INTR_END; i++) {
		bit = 1 << i;
		if (!(fpriv->eventfd_bitmap & bit))
			continue;
		xdma_user_interrupt_config(xdev, i, false);
		eventfd_ctx_put(xdev->exec.user_msix_table[i]);
		xdev->exec.user_msix_table[i] = NULL;
	}
	fpriv->eventfd_bitmap = 0;
	mutex_unlock(&xdev->exec.user_msix_table_lock);
out:
	mutex_destroy(&fpriv->lock);
	kfree(fpriv);
	filp->driver_priv = NULL;
	DRM_INFO("Pid %d closed device\n", pid_nr(task_tgid(current)));
}

static unsigned int xocl_poll(struct file *filp, poll_table *wait)
{
	int counter;
	struct drm_file *priv = filp->private_data;
	struct drm_device *dev = priv->minor->dev;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_client_ctx *fpriv = priv->driver_priv;
	int ret = 0;

	BUG_ON(!fpriv);
	poll_wait(filp, &xdev->exec.poll_wait_queue, wait);
	/*
	 * Mutex lock protects from two threads from the same application
	 * calling poll concurrently using the same file handle
	 */
	mutex_lock(&fpriv->lock);
	counter = atomic_read(&fpriv->trigger);
	if (counter > 0) {
		/*
		 * Use atomic here since the trigger may be incremented by interrupt
		 * handler running concurrently
		 */
		atomic_dec(&fpriv->trigger);
		ret = POLLIN;
	}
	mutex_unlock(&fpriv->lock);
	return ret;
}

static const struct drm_ioctl_desc xocl_ioctls[] = {
	DRM_IOCTL_DEF_DRV(XOCL_CREATE_BO, xocl_create_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_USERPTR_BO, xocl_userptr_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_MAP_BO, xocl_map_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_SYNC_BO, xocl_sync_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_INFO_BO, xocl_info_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_PWRITE_BO, xocl_pwrite_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_PREAD_BO, xocl_pread_bo_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_CTX, xocl_ctx_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_INFO, xocl_info_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_READ_AXLF, xocl_read_axlf_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_PWRITE_UNMGD, xocl_pwrite_unmgd_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_PREAD_UNMGD, xocl_pread_unmgd_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_USAGE_STAT, xocl_usage_stat_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_USER_INTR, xocl_user_intr_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
	DRM_IOCTL_DEF_DRV(XOCL_EXECBUF, xocl_execbuf_ioctl,
			  DRM_AUTH|DRM_UNLOCKED|DRM_RENDER_ALLOW),
};

static const struct file_operations xocl_driver_fops = {
	.owner		= THIS_MODULE,
	.open		= drm_open,
	.mmap		= xocl_mmap,
	.poll		= xocl_poll,
	.read		= drm_read,
	.unlocked_ioctl = drm_ioctl,
	.release	= drm_release,
};

static const struct vm_operations_struct xocl_vm_ops = {
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
	.fault = xocl_gem_fault2,
#else
	.fault = xocl_gem_fault,
#endif
	.open = drm_gem_vm_open,
	.close = drm_gem_vm_close,
};

static struct drm_driver xocl_drm_driver = {
	.driver_features		= DRIVER_GEM | DRIVER_PRIME |
	                                  DRIVER_RENDER,
	.postclose                      = xocl_client_release,
	.open                           = xocl_client_open,
	.load				= xocl_drm_load,
#if (LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0) ||  \
        (defined(RHEL_RELEASE_CODE) && \
        RHEL_RELEASE_CODE >=RHEL_RELEASE_VERSION(7,5)))
	.unload                         = xocl_drm_unload2,
#else
	.unload				= xocl_drm_unload,
#endif
	.gem_free_object		= xocl_free_object,
	.gem_vm_ops			= &xocl_vm_ops,
	.prime_handle_to_fd		= drm_gem_prime_handle_to_fd,
	.prime_fd_to_handle		= drm_gem_prime_fd_to_handle,
	.gem_prime_import		= drm_gem_prime_import,
	.gem_prime_export		= drm_gem_prime_export,
	.gem_prime_get_sg_table         = xocl_gem_prime_get_sg_table,
	.gem_prime_import_sg_table      = xocl_gem_prime_import_sg_table,
	.gem_prime_vmap                 = xocl_gem_prime_vmap,
	.gem_prime_vunmap               = xocl_gem_prime_vunmap,
	.ioctls				= xocl_ioctls,
	.num_ioctls			= ARRAY_SIZE(xocl_ioctls),
	.fops				= &xocl_driver_fops,
#if LINUX_VERSION_CODE >= KERNEL_VERSION(3, 18, 0)
	.set_busid                      = drm_pci_set_busid,
#endif
	.name				= XOCL_DRIVER_NAME,
	.desc				= XOCL_DRIVER_DESC,
	.date				= XOCL_DRIVER_DATE,
	.major				= XOCL_DRIVER_MAJOR,
	.minor				= XOCL_DRIVER_MINOR,
	.patchlevel			= XOCL_DRIVER_PATCHLEVEL,
};

// TODO: Umang remove the additional DRM_INFO's once this driver has been
// in production for some time. 07/06/2017.
static int xocl_driver_load(struct pci_dev *pdev,
			  const struct pci_device_id *ent)
{
	struct drm_device *dev;
	int ret;

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);

	dev = drm_dev_alloc(&xocl_drm_driver, &pdev->dev);
	if (IS_ERR(dev))
		return PTR_ERR(dev);

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	ret = pci_enable_device(pdev);
	if (ret)
		goto err_free;

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	dev->pdev = pdev;
	pci_set_drvdata(pdev, dev);

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	ret = drm_dev_register(dev, ent->driver_data);
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	if (ret) {
		goto err_reg;
	}

	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	return 0;

err_reg:
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	pci_disable_device(pdev);
err_free:
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	drm_dev_unref(dev);
	return ret;

}

static int xocl_pci_probe(struct pci_dev *pdev,
			  const struct pci_device_id *ent)
{
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	return xocl_driver_load(pdev, ent);
}

static void xocl_pci_remove(struct pci_dev *pdev)
{
	struct drm_device *dev = pci_get_drvdata(pdev);
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	pci_disable_device(pdev);
	drm_put_dev(dev);
}

static pci_ers_result_t xocl_error_detected(struct pci_dev *pdev,
					    pci_channel_state_t state)
{
	struct xdma_pci_dev *xpdev = dev_get_drvdata(&pdev->dev);

	switch (state) {
	case pci_channel_io_normal:
		return PCI_ERS_RESULT_CAN_RECOVER;
	case pci_channel_io_frozen:
		DRM_INFO("dev 0x%p,0x%p, frozen state error, reset controller\n",
			 pdev, xpdev);
		//xdma_dev_disable(xpdev, false);
		return PCI_ERS_RESULT_NEED_RESET;
	case pci_channel_io_perm_failure:
		DRM_INFO("dev 0x%p,0x%p, failure state error, req. disconnect\n",
			 pdev, xpdev);
		return PCI_ERS_RESULT_DISCONNECT;
	}
	return PCI_ERS_RESULT_NEED_RESET;
}

static pci_ers_result_t xocl_slot_reset(struct pci_dev *pdev)
{
	struct drm_device *ddev = pci_get_drvdata(pdev);

	DRM_INFO("0x%p restart after slot reset\n", ddev->dev_private);
	pci_restore_state(pdev);
	//queue_work(xdma_workq, &dev->reset_work);
	return PCI_ERS_RESULT_RECOVERED;
}

static void xocl_error_resume(struct pci_dev *pdev)
{
	struct drm_device *ddev = pci_get_drvdata(pdev);

	DRM_INFO("dev 0x%p,0x%p.\n", pdev, ddev->dev_private);
	pci_cleanup_aer_uncorrect_error_status(pdev);
}

void xocl_reset_notify(struct pci_dev *pdev, bool prepare)
{
	struct drm_device *ddev = dev_get_drvdata(&pdev->dev);
	struct drm_xocl_dev *xdev;

	if(ddev) {
		xdev = ddev->dev_private;
	}
	else {
		DRM_ERROR("%s: %s ddev is null", DRV_NAME, __FUNCTION__);
		return;
	}

	if(xdev)
		DRM_INFO("%s: %s dev 0x%p,0x%p, prepare %d.\n", DRV_NAME, __FUNCTION__,
				pdev, ddev->dev_private, prepare);
	else {
		DRM_ERROR("%s: %s xdev is null", DRV_NAME, __FUNCTION__);
		return;
	}

	if (prepare) {
		xdev->offline = true;
		xdma_device_offline(pdev, xdev->xdma_handle);
	}
	else {
		xdma_device_online(pdev, xdev->xdma_handle);
		xdev->offline = false;
	}
}
EXPORT_SYMBOL_GPL(xocl_reset_notify);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
static void xocl_reset_prepare(struct pci_dev *pdev)
{
	xocl_reset_notify(pdev, true);
}

static void xocl_reset_done(struct pci_dev *pdev)
{
	xocl_reset_notify(pdev, false);
}
#endif

static const struct pci_error_handlers xocl_err_handler = {
	.error_detected	= xocl_error_detected,
	.slot_reset	= xocl_slot_reset,
	.resume		= xocl_error_resume,
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0)
	.reset_prepare  = xocl_reset_prepare,
	.reset_done     = xocl_reset_done,
#elif LINUX_VERSION_CODE >= KERNEL_VERSION(3,16,0)
	.reset_notify	= xocl_reset_notify,
#endif
};


static struct pci_driver xocl_pci_driver = {
	.name = XOCL_DRIVER_NAME,
	.id_table = pciidlist,
	.probe = xocl_pci_probe,
	.remove = xocl_pci_remove,
	.err_handler = &xocl_err_handler,
};

/* init xilinx opencl drm platform */
static int __init xocl_init(void)
{
	int result;
#ifdef XOCL_BUILTIN_XVC
	result = xocl_xvc_chardev_init();
	if (result) {
		DRM_ERROR("XVC registration failed with error code: %d\n", result);
		return result;
	}
#endif
	result = pci_register_driver(&xocl_pci_driver);
	if (result) {
		DRM_ERROR("PCIe registration failed with error code: %d\n", result);
		goto unregister_xvc;
	}

#ifdef XOCL_CMA_ALLOC
	result = cma_init_reserved_mem(XOCL_CMA_BASE, XOCL_CMA_SIZE, 0, &xocl_cma);
	if (result) {
		DRM_ERROR("CMA region allocation for PCI Slave failed with error code: %d\n", result);
		goto unregister_pci;
	}
#endif
	return 0;

unregister_pci:
	pci_unregister_driver(&xocl_pci_driver);

unregister_xvc:
#ifdef XOCL_BUILTIN_XVC
	xocl_xvc_chardev_exit();
#endif
	return result;
}

static void __exit xocl_exit(void)
{
	DRM_INFO("%s:%d:%s()", __FILE__, __LINE__, __func__);
	pci_unregister_driver(&xocl_pci_driver);
#ifdef XOCL_BUILTIN_XVC
	xocl_xvc_chardev_exit();
#endif
}

module_init(xocl_init);
module_exit(xocl_exit);


MODULE_VERSION(__stringify(XOCL_DRIVER_MAJOR) "."
	       __stringify(XOCL_DRIVER_MINOR) "."
	       __stringify(XOCL_DRIVER_PATCHLEVEL));

MODULE_DESCRIPTION(XOCL_DRIVER_DESC);
MODULE_AUTHOR("Sonal Santan <sonal.santan@xilinx.com>");
MODULE_LICENSE("GPL");

// 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
