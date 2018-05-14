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

#ifndef _XCL_XOCL_XDMA_H_
#define _XCL_XOCL_XDMA_H_

#include <linux/types.h>
#include <linux/pci.h>
#include <linux/dma-mapping.h>
#include <linux/interrupt.h>

int xdma_init_glue(struct drm_xocl_dev *xdev);
void xdma_fini_glue(struct drm_xocl_dev *xdev);
ssize_t xdma_migrate_bo(const struct drm_xocl_dev *xdev, struct sg_table *sgt, bool write,
		    u64 paddr, int channel);
int xdma_user_interrupt_config(struct drm_xocl_dev *xdev, int user_intr_number, bool enable);
#endif

// 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
