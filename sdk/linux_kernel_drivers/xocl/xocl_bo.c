/*
 * Copyright (C) 2016-2018 Xilinx, Inc
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
 *    Sarabjeet Singh <sarabjeet.singh@xilinx.com>
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

#include <linux/bitops.h>
#include <linux/swap.h>
#include <linux/dma-buf.h>
#include <linux/pagemap.h>
#include <linux/version.h>
#ifdef XOCL_CMA_ALLOC
#include <linux/cma.h>
#endif
#if LINUX_VERSION_CODE <= KERNEL_VERSION(3,0,0)
#include <drm/drm_backport.h>
#endif
#include <drm/drmP.h>
#include "xocl_drv.h"
#include "xocl_ioctl.h"
#include "xocl_xdma.h"

#if (LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0) ||	\
	(defined(RHEL_RELEASE_CODE) && \
	RHEL_RELEASE_CODE >=RHEL_RELEASE_VERSION(7,5)))
static inline void drm_free_large(void *ptr)
{
	kvfree(ptr);
}

static inline void *drm_malloc_ab(size_t nmemb, size_t size)
{
	return kvmalloc_array(nmemb, sizeof(struct page *), GFP_KERNEL);
}
#endif

static inline int xocl_drm_mm_insert_node(struct drm_mm *mm,
					  struct drm_mm_node *node,
					  u64 size)
{
#if (LINUX_VERSION_CODE >= KERNEL_VERSION(4, 13, 0) ||	\
	(defined(RHEL_RELEASE_CODE) && \
	RHEL_RELEASE_CODE >=RHEL_RELEASE_VERSION(7,5)))
	return drm_mm_insert_node_generic(mm, node, size, PAGE_SIZE, 0, 0);
#else
	return drm_mm_insert_node_generic(mm, node, size, PAGE_SIZE, 0, 0, 0);
#endif
}


static inline void __user *to_user_ptr(u64 address)
{
	return (void __user *)(uintptr_t)address;
}

static size_t xocl_bo_physical_addr(const struct drm_xocl_bo *xobj)
{
	uint64_t paddr = xobj->mm_node ? xobj->mm_node->start : 0xffffffffffffffffull;

	//Sarab: Need to check for number of hops & size of DDRs
	if (xobj->flags & XOCL_BO_ARE)
		paddr |= XOCL_ARE_HOP;
	return paddr;
}

void xocl_describe(const struct drm_xocl_bo *xobj)
{
	size_t size_in_kb = xobj->base.size / 1024;
	size_t physical_addr = xocl_bo_physical_addr(xobj);
	unsigned ddr = xocl_bo_ddr_idx(xobj->flags);
	unsigned userptr = xocl_bo_userptr(xobj) ? 1 : 0;

	DRM_DEBUG("%p: H[%p] SIZE[0x%zxKB] D[0x%zx] DDR[%u] UPTR[%u] SGLCOUNT[%u]\n",
		  xobj, xobj->vmapping, size_in_kb, physical_addr, ddr, userptr, xobj->sgt->orig_nents);
}

static void xocl_free_mm_node(struct drm_xocl_bo *xobj)
{
	struct drm_xocl_dev *xdev = xobj->base.dev->dev_private;
	unsigned ddr = xocl_bo_ddr_idx(xobj->flags);
	if (!xobj->mm_node)
		return;

	mutex_lock(&xdev->mm_lock);
	xdev->mm_usage_stat[ddr].memory_usage -= xobj->base.size;
	xdev->mm_usage_stat[ddr].bo_count--;
	drm_mm_remove_node(xobj->mm_node);
	mutex_unlock(&xdev->mm_lock);
	kfree(xobj->mm_node);
	xobj->mm_node = NULL;
}

void xocl_free_bo(struct drm_gem_object *obj)
{
	struct drm_xocl_bo *xobj = to_xocl_bo(obj);
	struct drm_xocl_dev *xdev = xobj->base.dev->dev_private;
	int npages = obj->size >> PAGE_SHIFT;
	DRM_DEBUG("Freeing BO %p\n", xobj);

	if (xobj->vmapping)
		vunmap(xobj->vmapping);
	xobj->vmapping = NULL;

	if (xobj->pages) {
		if (xocl_bo_userptr(xobj)) {
			release_pages(xobj->pages, npages, 0);
			drm_free_large(xobj->pages);
		}
#ifdef XOCL_CMA_ALLOC
		else if (xocl_bo_cma(xobj)) {
			if (xobj->pages[0])
				cma_release(xdev->cma_blk, xobj->pages[0], npages);
			drm_free_large(xobj->pages);
		}
#endif
		else if (!xocl_bo_import(xobj)) {
			drm_gem_put_pages(obj, xobj->pages, false, false);
		}
	}
	xobj->pages = NULL;

	if (!xocl_bo_import(xobj)) {
		DRM_DEBUG("Freeing regular buffer\n");
		if (xobj->sgt)
			sg_free_table(xobj->sgt);
		xobj->sgt = NULL;
		xocl_free_mm_node(xobj);
	}
	else {
		DRM_DEBUG("Freeing imported buffer\n");
		if (!(xobj->flags & XOCL_BO_ARE))
			xocl_free_mm_node(xobj);

		if (obj->import_attach) {
			DRM_DEBUG("Unnmapping attached dma buf\n");
			dma_buf_unmap_attachment(obj->import_attach, xobj->sgt, DMA_TO_DEVICE);
			drm_prime_gem_destroy(obj, NULL);
		}
	}

	//If it is imported BO then we do not delete SG Table
	//And if is imported from ARE device then we do not free the mm_node as well

	//Sarab: Call detach here........
	//to let the exporting device know that importing device do not need it anymore..
	//else free_bo i.e this function is not called for exporting device
	//as it assumes that the exported buffer is still being used
	//dmabuf->ops->release(dmabuf);
	//The drm_driver.gem_free_object callback is responsible for cleaning up the dma_buf attachment and references acquired at import time.

	/* This crashes machine.. Using above code instead
	 * drm_prime_gem_destroy calls detach function..
	 struct dma_buf *imported_dma_buf = obj->dma_buf;
	 if (imported_dma_buf->ops->detach)
	 imported_dma_buf->ops->detach(imported_dma_buf, obj->import_attach);
	*/

	drm_gem_object_release(obj);
	kfree(xobj);
}


static inline int check_bo_user_flags(const struct drm_device *dev, unsigned flags)
{
	const unsigned ddr_count = xocl_ddr_channel_count(dev);
	struct drm_xocl_dev *xdev = dev->dev_private;
	unsigned ddr;

	if(ddr_count == 0)
		return -EINVAL;
	if (flags == 0xffffffff)
		return 0;
	if (flags == DRM_XOCL_BO_EXECBUF)
		return 0;
#ifdef XOCL_CMA_ALLOC
	if (flags == DRM_XOCL_BO_CMA)
		return 0;
#else
	if (flags == DRM_XOCL_BO_CMA)
		return -EINVAL;
#endif
	ddr = xocl_bo_ddr_idx(flags);
	if (ddr == 0xffffffff)
		return 0;
	if (ddr >= ddr_count)
		return -EINVAL;
	if (xdev->unified) {
		if  (xdev->topology.m_data[ddr].m_used != 1) {
			printk(KERN_INFO "Bank %d is marked as unused in axlf\n", ddr);
			return -EINVAL;
		}
	}
	return 0;
}


static struct drm_xocl_bo *xocl_create_bo(struct drm_device *dev,
					  uint64_t unaligned_size,
					  unsigned user_flags)
{
	size_t size = PAGE_ALIGN(unaligned_size);
	struct drm_xocl_bo *xobj;
	struct drm_xocl_dev *xdev = dev->dev_private;
	unsigned ddr = xocl_bo_ddr_idx(user_flags);
	const unsigned ddr_count = xocl_ddr_channel_count(dev);
	int err = 0;

	if (!size)
		return ERR_PTR(-EINVAL);

	/* Either none or only one DDR should be specified */
	if (check_bo_user_flags(dev, user_flags))
		return ERR_PTR(-EINVAL);

	xobj = kzalloc(sizeof(*xobj), GFP_KERNEL);
	if (!xobj)
		return ERR_PTR(-ENOMEM);

	err = drm_gem_object_init(dev, &xobj->base, size);
	if (err)
		goto out3;

	if (user_flags == DRM_XOCL_BO_EXECBUF) {
		xobj->flags = XOCL_BO_EXECBUF;
		xobj->mm_node = NULL;
		xobj->metadata.state = DRM_XOCL_EXECBUF_STATE_ABORT;
		return xobj;
	}

#ifdef XOCL_CMA_ALLOC
	if (user_flags == DRM_XOCL_BO_CMA) {
		xobj->flags = XOCL_BO_CMA;
		xobj->mm_node = NULL;
		return xobj;
	}
#endif

	xobj->mm_node = kzalloc(sizeof(*xobj->mm_node), GFP_KERNEL);
	if (!xobj->mm_node) {
		err = -ENOMEM;
		goto out3;
	}

	mutex_lock(&xdev->mm_lock);
	if (ddr != 0xffffffff) {
		/* Attempt to allocate buffer on the requested DDR */
		DRM_DEBUG("%s:%s:%d: %u\n", __FILE__, __func__, __LINE__, ddr);
		err = xocl_drm_mm_insert_node(&xdev->mm[ddr], xobj->mm_node, xobj->base.size);
		if (err)
			goto out2;
	}
	else {
		/* Attempt to allocate buffer on any DDR */
		for (ddr = 0; ddr < ddr_count; ddr++) {
			DRM_DEBUG("%s:%s:%d: %u\n", __FILE__, __func__, __LINE__, ddr);
			if(xdev->unified && !xdev->topology.m_data[ddr].m_used)
			    continue;
			err = xocl_drm_mm_insert_node(&xdev->mm[ddr], xobj->mm_node, xobj->base.size);
			if (err == 0)
				break;
		}
		if (err)
			goto out2;
	}
	xdev->mm_usage_stat[ddr].memory_usage += xobj->base.size;
	xdev->mm_usage_stat[ddr].bo_count++;
	mutex_unlock(&xdev->mm_lock);
	/* Record the DDR we allocated the buffer on */
	xobj->flags |= (1 << ddr);

	return xobj;
out2:
	mutex_unlock(&xdev->mm_lock);
	kfree(xobj->mm_node);
	drm_gem_object_release(&xobj->base);
out3:
	kfree(xobj);
	return ERR_PTR(err);
}

/*
 * For ARE device do not reserve DDR space
 * In below import it will reuse the mm_node which is already created by other application
 */

static struct drm_xocl_bo *xocl_create_bo_forARE(struct drm_device *dev,
						 uint64_t unaligned_size,
						 struct drm_mm_node   *exporting_mm_node)
{
	struct drm_xocl_bo *xobj;
	size_t size = PAGE_ALIGN(unaligned_size);
	int err = 0;

	if (!size)
		return ERR_PTR(-EINVAL);

	xobj = kzalloc(sizeof(*xobj), GFP_KERNEL);
	if (!xobj)
		return ERR_PTR(-ENOMEM);

	err = drm_gem_object_init(dev, &xobj->base, size);
	if (err)
		goto out3;

	xobj->mm_node = exporting_mm_node;
	if (!xobj->mm_node) {
		err = -ENOMEM;
		goto out3;
	}

	/* Record that this buffer is on remote device to be access over ARE*/
	xobj->flags = XOCL_BO_ARE;
	return xobj;
out3:
	kfree(xobj);
	return ERR_PTR(err);
}


int xocl_create_bo_ioctl(struct drm_device *dev,
			 void *data,
			 struct drm_file *filp)
{
	int ret;
	int j;
	struct drm_xocl_bo *xobj;
	struct page *cpages;
	unsigned int page_count;
	struct drm_xocl_create_bo *args = data;
	unsigned ddr = args->flags & 0xf;
	struct drm_xocl_dev *xdev = dev->dev_private;

	if (args->flags && (args->flags != DRM_XOCL_BO_EXECBUF)) {
		if (hweight_long(ddr) > 1)
			return -EINVAL;
	}

	xobj = xocl_create_bo(dev, args->size, args->flags);

	if (IS_ERR(xobj)) {
		DRM_DEBUG("object creation failed\n");
		return PTR_ERR(xobj);
	}

#ifdef XOCL_CMA_ALLOC
	if (args->flags == DRM_XOCL_BO_CMA) {
		page_count = xobj->base.size >> PAGE_SHIFT;
		xobj->pages = drm_malloc_ab(page_count, sizeof(*xobj->pages));
		if (!xobj->pages) {
			ret = -ENOMEM;
			goto out_free;
		}
		cpages = cma_alloc(xdev->cma_blk, page_count, 0, GFP_KERNEL);
		if (!cpages) {
			ret = -ENOMEM;
			goto out_free;
		}
		for (j = 0; j < page_count; j++)
			xobj->pages[j] = cpages++;
	}
	else {
		xobj->pages = drm_gem_get_pages(&xobj->base);
	}
#else
	xobj->pages = drm_gem_get_pages(&xobj->base);
#endif
	if (IS_ERR(xobj->pages)) {
		ret = PTR_ERR(xobj->pages);
		goto out_free;
	}

	xobj->sgt = drm_prime_pages_to_sg(xobj->pages, xobj->base.size >> PAGE_SHIFT);
	if (IS_ERR(xobj->sgt)) {
		ret = PTR_ERR(xobj->sgt);
		goto out_free;
	}

	xobj->vmapping = vmap(xobj->pages, xobj->base.size >> PAGE_SHIFT, VM_MAP, PAGE_KERNEL);

	if (!xobj->vmapping) {
		ret = -ENOMEM;
		goto out_free;
	}

	ret = drm_gem_create_mmap_offset(&xobj->base);
	if (ret < 0)
		goto out_free;

	ret = drm_gem_handle_create(filp, &xobj->base, &args->handle);
	if (ret < 0)
		goto out_free;

	xocl_describe(xobj);
	drm_gem_object_unreference_unlocked(&xobj->base);
	return ret;

out_free:
	xocl_free_bo(&xobj->base);
	return ret;
}

int xocl_userptr_bo_ioctl(struct drm_device *dev,
			  void *data,
			  struct drm_file *filp)
{
	int ret;
	struct drm_xocl_bo *xobj;
	unsigned int page_count;
	struct drm_xocl_userptr_bo *args = data;
	unsigned ddr = args->flags & 0xf;

	if (offset_in_page(args->addr))
		return -EINVAL;

	if (args->flags & DRM_XOCL_BO_EXECBUF)
		return -EINVAL;

	if (args->flags & DRM_XOCL_BO_CMA)
		return -EINVAL;

	if (args->flags && (hweight_long(ddr) > 1))
		return -EINVAL;

	xobj = xocl_create_bo(dev, args->size, args->flags);

	if (IS_ERR(xobj)) {
		DRM_DEBUG("object creation failed\n");
		return PTR_ERR(xobj);
	}

	/* Use the page rounded size so we can accurately account for number of pages */
	page_count = xobj->base.size >> PAGE_SHIFT;

	xobj->pages = drm_malloc_ab(page_count, sizeof(*xobj->pages));
	if (!xobj->pages) {
		ret = -ENOMEM;
		goto out1;
	}
	ret = get_user_pages_fast(args->addr, page_count, 1, xobj->pages);

	if (ret != page_count)
		goto out0;

	xobj->sgt = drm_prime_pages_to_sg(xobj->pages, page_count);
	if (IS_ERR(xobj->sgt)) {
		ret = PTR_ERR(xobj->sgt);
		goto out0;
	}

	/* TODO: resolve the cache issue */
	xobj->vmapping = vmap(xobj->pages, page_count, VM_MAP, PAGE_KERNEL);

	if (!xobj->vmapping) {
		ret = -ENOMEM;
		goto out1;
	}

	ret = drm_gem_handle_create(filp, &xobj->base, &args->handle);
	if (ret)
		goto out1;

	xobj->flags |= XOCL_BO_USERPTR;
	xocl_describe(xobj);
	drm_gem_object_unreference_unlocked(&xobj->base);
	return ret;

out0:
	drm_free_large(xobj->pages);
	xobj->pages = NULL;
out1:
	xocl_free_bo(&xobj->base);
	DRM_DEBUG("handle creation failed\n");
	return ret;
}


int xocl_map_bo_ioctl(struct drm_device *dev,
		      void *data,
		      struct drm_file *filp)
{
	int ret = 0;
	struct drm_xocl_map_bo *args = data;
	struct drm_gem_object *obj;

	obj = xocl_gem_object_lookup(dev, filp, args->handle);
	if (!obj) {
		DRM_ERROR("Failed to look up GEM BO %d\n", args->handle);
		return -ENOENT;
	}

	if (xocl_bo_userptr(to_xocl_bo(obj))) {
		ret = -EPERM;
		goto out;
	}
	/* The mmap offset was set up at BO allocation time. */
	args->offset = drm_vma_node_offset_addr(&obj->vma_node);
	xocl_describe(to_xocl_bo(obj));
out:
	drm_gem_object_unreference_unlocked(obj);
	return ret;
}

static struct sg_table *alloc_onetime_sg_table(struct page **pages, uint64_t offset, uint64_t size)
{
	int ret;
	unsigned int nr_pages;
	struct sg_table *sgt = kmalloc(sizeof(struct sg_table), GFP_KERNEL);
	if (!sgt)
		return ERR_PTR(-ENOMEM);

	pages += (offset >> PAGE_SHIFT);
	offset &= (~PAGE_MASK);
	nr_pages = PAGE_ALIGN(size + offset) >> PAGE_SHIFT;

	ret = sg_alloc_table_from_pages(sgt, pages, nr_pages, offset, size, GFP_KERNEL);
	if (ret)
		goto cleanup;
	return sgt;

cleanup:
	kfree(sgt);
	return ERR_PTR(-ENOMEM);
}

static int acquire_channel(struct drm_xocl_dev *xdev, enum drm_xocl_sync_bo_dir dir)
{
	int channel = 0;
        int result = 0;

	if (down_interruptible(&xdev->channel_sem[dir])) {
		channel = -ERESTARTSYS;
		goto out;
	}

        for (channel = 0; channel < xdev->channel; channel++) {
		result = test_and_clear_bit(channel, &xdev->channel_bitmap[dir]);
		if (result)
			break;
        }
        if (!result) {
		// How is this possible?
		DRM_ERROR("Failed to acquire a valid channel\n");
		up(&xdev->channel_sem[dir]);
		channel = -EIO;
	}
out:
	return channel;
}

static void release_channel(struct drm_xocl_dev *xdev, enum drm_xocl_sync_bo_dir dir, int channel)
{
        set_bit(channel, &xdev->channel_bitmap[dir]);
        up(&xdev->channel_sem[dir]);
}


int xocl_sync_bo_ioctl(struct drm_device *dev,
		       void *data,
		       struct drm_file *filp)
{
	const struct drm_xocl_bo *xobj;
	struct sg_table *sgt;
	u64 paddr = 0;
	int channel = 0;
	ssize_t ret = 0;
	const struct drm_xocl_sync_bo *args = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	const bool dir = (args->dir == DRM_XOCL_SYNC_BO_TO_DEVICE) ? true : false;
	struct drm_gem_object *gem_obj = xocl_gem_object_lookup(dev, filp,
							       args->handle);
	if (!gem_obj) {
		DRM_ERROR("Failed to look up GEM BO %d\n", args->handle);
		return -ENOENT;
	}

	xobj = to_xocl_bo(gem_obj);
	sgt = xobj->sgt;

	//Sarab: If it is a remote BO then why do sync over ARE.
	//We should do sync directly using the other device which this bo locally.
	//So that txfer is: HOST->PCIE->DDR; Else it will be HOST->PCIE->ARE->DDR
	paddr = xocl_bo_physical_addr(xobj);

	if (paddr == 0xffffffffffffffffull)
		return -EINVAL;

	/* If device is offline (due to error), reject all DMA requests */
	if (xdev->offline)
		return -ENODEV;


	if ((args->offset >= gem_obj->size) || (args->size > gem_obj->size) ||
	    ((args->offset + args->size) > gem_obj->size)) {
		ret = -EINVAL;
		goto out;
	}

	/* only invalidate the range of addresses requested by the user */
	/*
	if (args->dir == DRM_XOCL_SYNC_BO_TO_DEVICE)
		flush_kernel_vmap_range(kaddr, args->size);
	else if (args->dir == DRM_XOCL_SYNC_BO_FROM_DEVICE)
		invalidate_kernel_vmap_range(kaddr, args->size);
	else {
		ret = -EINVAL;
		goto out;
	}
	*/
	paddr += args->offset;

	if (args->offset || (args->size != xobj->base.size)) {
		sgt = alloc_onetime_sg_table(xobj->pages, args->offset, args->size);
		if (IS_ERR(sgt)) {
			ret = PTR_ERR(sgt);
			goto out;
		}
	}

	//drm_clflush_sg(sgt);
	channel = acquire_channel(xdev, args->dir);

	if (channel < 0) {
		ret = -EINVAL;
		goto clear;
	}
	/* Now perform DMA */
	ret = xdma_migrate_bo(xdev, sgt, dir, paddr, channel);
	if (ret >= 0) {
		xdev->channel_usage[args->dir][channel] += ret;
		ret = (ret == args->size) ? 0 : -EIO;
	}
	release_channel(xdev, args->dir, channel);
clear:
	if (args->offset || (args->size != xobj->base.size))
		sg_free_table(sgt);
out:
	drm_gem_object_unreference_unlocked(gem_obj);
	return ret;
}

int xocl_info_bo_ioctl(struct drm_device *dev,
		       void *data,
		       struct drm_file *filp)
{
	const struct drm_xocl_bo *xobj;
	struct drm_xocl_info_bo *args = data;
	struct drm_gem_object *gem_obj = xocl_gem_object_lookup(dev, filp,
								args->handle);

	if (!gem_obj) {
		DRM_ERROR("Failed to look up GEM BO %d\n", args->handle);
		return -ENOENT;
	}

	xobj = to_xocl_bo(gem_obj);

	args->size = xobj->base.size;

	args->paddr = xocl_bo_physical_addr(xobj);
	xocl_describe(xobj);
	drm_gem_object_unreference_unlocked(gem_obj);

	return 0;
}

int xocl_pwrite_bo_ioctl(struct drm_device *dev, void *data,
			 struct drm_file *filp)
{
	struct drm_xocl_bo *xobj;
	const struct drm_xocl_pwrite_bo *args = data;
	struct drm_gem_object *gem_obj = xocl_gem_object_lookup(dev, filp,
							       args->handle);
	char __user *user_data = to_user_ptr(args->data_ptr);
	int ret = 0;
	void *kaddr;

	if (!gem_obj) {
		DRM_ERROR("Failed to look up GEM BO %d\n", args->handle);
		return -ENOENT;
	}

	if ((args->offset > gem_obj->size) || (args->size > gem_obj->size)
	    || ((args->offset + args->size) > gem_obj->size)) {
		ret = -EINVAL;
		goto out;
	}

	if (args->size == 0) {
		ret = 0;
		goto out;
	}

	if (!access_ok(VERIFY_READ, user_data, args->size)) {
		ret = -EFAULT;
		goto out;
	}

	xobj = to_xocl_bo(gem_obj);

	if (xocl_bo_userptr(xobj)) {
		ret = -EPERM;
		goto out;
	}

	kaddr = xobj->vmapping;
	kaddr += args->offset;

	ret = copy_from_user(kaddr, user_data, args->size);
out:
	drm_gem_object_unreference_unlocked(gem_obj);

	return ret;
}

int xocl_pread_bo_ioctl(struct drm_device *dev, void *data,
			struct drm_file *filp)
{
	struct drm_xocl_bo *xobj;
	const struct drm_xocl_pread_bo *args = data;
	struct drm_gem_object *gem_obj = xocl_gem_object_lookup(dev, filp,
							       args->handle);
	char __user *user_data = to_user_ptr(args->data_ptr);
	int ret = 0;
	void *kaddr;

	if (!gem_obj) {
		DRM_ERROR("Failed to look up GEM BO %d\n", args->handle);
		return -ENOENT;
	}

	if (xocl_bo_userptr(to_xocl_bo(gem_obj))) {
		ret = -EPERM;
		goto out;
	}

	if ((args->offset > gem_obj->size) || (args->size > gem_obj->size)
	    || ((args->offset + args->size) > gem_obj->size)) {
		ret = -EINVAL;
		goto out;
	}

	if (args->size == 0) {
		ret = 0;
		goto out;
	}

	if (!access_ok(VERIFY_WRITE, user_data, args->size)) {
		ret = EFAULT;
		goto out;
	}

	xobj = to_xocl_bo(gem_obj);
	kaddr = xobj->vmapping;;
	kaddr += args->offset;

	ret = copy_to_user(user_data, kaddr, args->size);

out:
	drm_gem_object_unreference_unlocked(gem_obj);

	return ret;
}

struct sg_table *xocl_gem_prime_get_sg_table(struct drm_gem_object *obj)
{
	struct drm_xocl_bo *xobj = to_xocl_bo(obj);
	return drm_prime_pages_to_sg(xobj->pages, xobj->base.size >> PAGE_SHIFT);
}


static struct drm_xocl_bo *xocl_is_exporting_xare(struct drm_device *dev, struct dma_buf_attachment *attach)
{
	struct drm_gem_object *exporting_gem_obj;
	struct drm_device *exporting_drm_dev;
	struct drm_xocl_dev *exporting_xdev;

	struct device_driver *importing_dma_driver = dev->dev->driver;
	struct dma_buf *exporting_dma_buf = attach->dmabuf;
	struct device_driver *exporting_dma_driver = attach->dev->driver;
	struct drm_xocl_dev *xdev = dev->dev_private;

	if (!strstr(xdev->header.VBNVName, "-xare"))
		return NULL;

	//We don't know yet if the exporting device is Xilinx/XOCL or third party or USB device
	//So checking it in below code
	if (importing_dma_driver != exporting_dma_driver)
		return NULL;

	//Exporting devices have same driver as us. So this is Xilinx device
	//So now we can get gem_object, drm_device & xocl_dev
	exporting_gem_obj = exporting_dma_buf->priv;
	exporting_drm_dev = exporting_gem_obj->dev;
	exporting_xdev = exporting_drm_dev->dev_private;
	//exporting_xdev->header;//This has FeatureROM header
	if (strstr(exporting_xdev->header.VBNVName, "-xare"))
		return to_xocl_bo(exporting_gem_obj);

	return NULL;
}

struct drm_gem_object *xocl_gem_prime_import_sg_table(struct drm_device *dev,
						      struct dma_buf_attachment *attach, struct sg_table *sgt)
{
	int ret = 0;
	// This is exporting device
	struct drm_xocl_bo *exporting_xobj = xocl_is_exporting_xare(dev, attach);

	// For ARE device resue the mm node from exporting xobj

	// For non ARE devices we need to create a full BO but share the SG table
        // ???? add flags to create_bo.. for DDR bank??

	struct drm_xocl_bo *importing_xobj = exporting_xobj ? xocl_create_bo_forARE(dev, attach->dmabuf->size, exporting_xobj->mm_node) :
		xocl_create_bo(dev, attach->dmabuf->size, 0);

	if (IS_ERR(importing_xobj)) {
		DRM_DEBUG("object creation failed\n");
		return (struct drm_gem_object *)importing_xobj;
	}

	importing_xobj->flags |= XOCL_BO_IMPORT;
	importing_xobj->sgt = sgt;
	importing_xobj->pages = drm_malloc_ab(attach->dmabuf->size >> PAGE_SHIFT, sizeof(*importing_xobj->pages));
	if (!importing_xobj->pages) {
		ret = -ENOMEM;
		goto out_free;
	}

	ret = drm_prime_sg_to_page_addr_arrays(sgt, importing_xobj->pages,
					       NULL, attach->dmabuf->size >> PAGE_SHIFT);
	if (ret)
		goto out_free;

	importing_xobj->vmapping = vmap(importing_xobj->pages, importing_xobj->base.size >> PAGE_SHIFT, VM_MAP,
					PAGE_KERNEL);

	if (!importing_xobj->vmapping) {
		ret = -ENOMEM;
		goto out_free;
	}

	ret = drm_gem_create_mmap_offset(&importing_xobj->base);
	if (ret < 0)
		goto out_free;

	xocl_describe(importing_xobj);
	return &importing_xobj->base;

out_free:
        xocl_free_bo(&importing_xobj->base);
        DRM_ERROR("Buffer import failed\n");
        return ERR_PTR(ret);
}

void *xocl_gem_prime_vmap(struct drm_gem_object *obj)
{
	struct drm_xocl_bo *xobj = to_xocl_bo(obj);
	return xobj->vmapping;
}

void xocl_gem_prime_vunmap(struct drm_gem_object *obj, void *vaddr)
{

}

static int xocl_init_unmgd(struct drm_xocl_unmgd *unmgd, uint64_t data_ptr, uint64_t size,
			   enum drm_xocl_sync_bo_dir dir)
{
	int ret;
	char __user *user_data = to_user_ptr(data_ptr);

	if (!access_ok((dir == DRM_XOCL_SYNC_BO_TO_DEVICE) ? VERIFY_READ : VERIFY_WRITE, user_data, size))
		return -EFAULT;

	memset(unmgd, 0, sizeof(struct drm_xocl_unmgd));

	unmgd->npages = (((unsigned long)user_data + size + PAGE_SIZE - 1) -
			((unsigned long)user_data & PAGE_MASK)) >> PAGE_SHIFT;

	unmgd->pages = drm_malloc_ab(unmgd->npages, sizeof(*unmgd->pages));
	if (!unmgd->pages)
		return -ENOMEM;

	ret = get_user_pages_fast(data_ptr, unmgd->npages, (dir == DRM_XOCL_SYNC_BO_FROM_DEVICE) ? 1 : 0, unmgd->pages);

	if (ret != unmgd->npages)
		goto clear_pages;

	unmgd->sgt = alloc_onetime_sg_table(unmgd->pages, data_ptr & ~PAGE_MASK, size);
	if (IS_ERR(unmgd->sgt)) {
		ret = PTR_ERR(unmgd->sgt);
		goto clear_release;
	}

	return 0;

clear_release:
	release_pages(unmgd->pages, unmgd->npages, 0);
clear_pages:
	drm_free_large(unmgd->pages);
	unmgd->pages = NULL;
	return ret;
}

static void xocl_finish_unmgd(struct drm_xocl_unmgd *unmgd)
{
	if (!unmgd->pages)
		return;
	release_pages(unmgd->pages, unmgd->npages, 0);
	drm_free_large(unmgd->pages);
	unmgd->pages = NULL;
}


int xocl_pwrite_unmgd_ioctl(struct drm_device *dev, void *data,
			    struct drm_file *filp)
{
	int channel;
	struct drm_xocl_unmgd unmgd;
	const struct drm_xocl_pwrite_unmgd *args = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	const enum drm_xocl_sync_bo_dir dir = DRM_XOCL_SYNC_BO_TO_DEVICE;
	ssize_t ret = 0;

	if (args->address_space != 0)
		return -EFAULT;

	if (args->size == 0)
		return 0;

	DRM_DEBUG("%s:%d\n", __func__, __LINE__);
	ret = xocl_init_unmgd(&unmgd, args->data_ptr, args->size, dir);
	if (ret)
		return ret;

	channel = acquire_channel(xdev, dir);
	DRM_DEBUG("%s:%d\n", __func__, __LINE__);
	if (channel < 0) {
		ret = -EINVAL;
		goto clear;
	}
	/* Now perform DMA */
	ret = xdma_migrate_bo(xdev, unmgd.sgt, (dir == DRM_XOCL_SYNC_BO_TO_DEVICE), args->paddr, channel);
	if (ret >= 0) {
		xdev->channel_usage[dir][channel] += ret;
		ret = (ret == args->size) ? 0 : -EIO;
	}
	release_channel(xdev, dir, channel);
	DRM_DEBUG("%s:%llx\n", __func__, xdev->channel_usage[dir][channel]);
clear:
	xocl_finish_unmgd(&unmgd);
	return ret;
}

int xocl_pread_unmgd_ioctl(struct drm_device *dev, void *data,
			   struct drm_file *filp)
{
	int channel;
	struct drm_xocl_unmgd unmgd;
	const struct drm_xocl_pwrite_unmgd *args = data;
	struct drm_xocl_dev *xdev = dev->dev_private;
	const enum drm_xocl_sync_bo_dir dir = DRM_XOCL_SYNC_BO_FROM_DEVICE;
	ssize_t ret = 0;

	DRM_DEBUG("%s:%d\n", __func__, __LINE__);
	if (args->address_space != 0)
		return -EFAULT;

	if (args->size == 0)
		return 0;

	ret = xocl_init_unmgd(&unmgd, args->data_ptr, args->size, dir);
	if (ret)
		return ret;

	DRM_DEBUG("%s:%d\n", __func__, __LINE__);
	channel = acquire_channel(xdev, dir);

	if (channel < 0) {
		ret = -EINVAL;
		goto clear;
	}
	/* Now perform DMA */
	ret = xdma_migrate_bo(xdev, unmgd.sgt, (dir == DRM_XOCL_SYNC_BO_TO_DEVICE), args->paddr, channel);
	if (ret >= 0) {
		xdev->channel_usage[dir][channel] += ret;
		ret = (ret == args->size) ? 0 : -EIO;
	}
	release_channel(xdev, dir, channel);
	DRM_DEBUG("%s:%llx\n", __func__, xdev->channel_usage[dir][channel]);
clear:
	xocl_finish_unmgd(&unmgd);
	return ret;
}

int xocl_usage_stat_ioctl(struct drm_device *dev, void *data,
			  struct drm_file *filp)
{
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_usage_stat *args = data;
	args->mm_channel_count = xocl_ddr_channel_count(dev);
	if (args->mm_channel_count > 8)
		args->mm_channel_count = 8;
	memcpy(args->mm, xdev->mm_usage_stat, sizeof(struct drm_xocl_mm_stat) * args->mm_channel_count);
	args->dma_channel_count = xdev->channel;
	if (args->dma_channel_count > 8)
		args->dma_channel_count = 8;
	memcpy(args->h2c, xdev->channel_usage[DRM_XOCL_SYNC_BO_TO_DEVICE], sizeof(unsigned long long) * args->dma_channel_count);
	memcpy(args->c2h, xdev->channel_usage[DRM_XOCL_SYNC_BO_FROM_DEVICE], sizeof(unsigned long long) * args->dma_channel_count);
	DRM_INFO("%s h2c[0] 0%llx\n", __func__, args->h2c[0]);
	DRM_INFO("%s c2h[0] 0%llx\n", __func__, args->c2h[0]);
	DRM_INFO("%s\n", __func__);
	return 0;
}


// 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
