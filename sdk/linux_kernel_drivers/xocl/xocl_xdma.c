/**
 *  Copyright (C) 2015-2018 Xilinx, Inc
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 */

#include "xocl_drv.h"
#include "xocl_xdma.h"
#include "libxdma_api.h"

static irqreturn_t xocl_xdma_user_isr(int irq, void *arg)
{
	struct drm_xocl_dev *xdev = (struct drm_xocl_dev *)arg;
	xocl_user_event(irq, xdev);
	return IRQ_HANDLED;
}

int xdma_init_glue(struct drm_xocl_dev *xdev)
{
	int ret = 0;
	int user = 0;
	unsigned short mask = ~0;
	xdev->xdma_handle = (struct xdma_dev *) xdma_device_open(DRV_NAME, xdev->ddev->pdev, &user,
								 &xdev->channel, &xdev->channel);
	if (xdev->xdma_handle == NULL) {
		DRM_INFO("%s: XDMA Device Open failed. \n", DRV_NAME);
		ret = -ENOENT;	// TBD: Get the error code from XDMA API.
	}
	ret = xdma_user_isr_register(xdev->xdma_handle, mask, xocl_xdma_user_isr, xdev);
	if (ret)
		xdma_device_close(xdev->ddev->pdev, xdev->xdma_handle);
	else
		DRM_INFO("%s: XDMA Device Open successful. \n", DRV_NAME);
	return ret;
}

void xdma_fini_glue(struct drm_xocl_dev *xdev)
{
	unsigned short mask = ~0;
	xdma_user_isr_register(xdev->xdma_handle, mask, NULL, xdev);
	xdma_device_close(xdev->ddev->pdev, xdev->xdma_handle);
	xdev->xdma_handle = NULL;
	DRM_INFO("%s: XDMA Device Close successful. \n", DRV_NAME);
}


ssize_t xdma_migrate_bo(const struct drm_xocl_dev *xdev, struct sg_table *sgt, bool write,
		    u64 paddr, int channel)
{
	struct page *pg;
	struct scatterlist *sg = sgt->sgl;
	int nents = sgt->orig_nents;
	pid_t pid = current->pid;
	const char* dirstr = write ? "to" : "from";
	int i = 0;
	ssize_t ret;
	unsigned long long pgaddr;
	DRM_DEBUG("%s TID %d, Channel:"
		  "%d, Offset: 0x%llx, Direction: %d\n", __func__, pid, channel, paddr, write ? 1 : 0);
	ret = xdma_xfer_submit(xdev->xdma_handle, channel, write ? 1 : 0, paddr, sgt, false, 10000);
	if (ret >= 0)
		return ret;

	DRM_ERROR("DMA failed %s device addr 0x%llx, tid %d, channel %d\n", dirstr, paddr, pid, channel);
	DRM_ERROR("Dumping SG Page Table\n");
	for (i = 0; i < nents; i++, sg = sg_next(sg)) {
        if (!sg)
            break;
		pg = sg_page(sg);
		if (!pg)
			continue;
		pgaddr = page_to_phys(pg);
		DRM_ERROR("%i, 0x%llx\n", i, pgaddr);
	}
	return ret;
}


int xdma_user_interrupt_config(struct drm_xocl_dev *xdev, int user_intr_number, bool enable)
{
	const unsigned int mask = 1 << user_intr_number;
	return enable ? xdma_user_isr_enable(xdev->xdma_handle, mask) : xdma_user_isr_disable(xdev->xdma_handle, mask);
}
