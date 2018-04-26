/*
 * Copyright (C) 2017-2018 Xilinx, Inc
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
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

#include <linux/list.h>
#include "xocl_drv.h"
#include "xocl_ioctl.h"
#include "xocl_xdma.h"


void xocl_track_ctx(struct drm_xocl_dev *xdev, struct drm_xocl_client_ctx *fpriv)
{
	unsigned long flags;

	spin_lock_irqsave(&xdev->exec.ctx_list_lock, flags);
	list_add_tail(&fpriv->link, &xdev->exec.ctx_list);
	spin_unlock_irqrestore(&xdev->exec.ctx_list_lock, flags);
}

void xocl_untrack_ctx(struct drm_xocl_dev *xdev, struct drm_xocl_client_ctx *fpriv)
{
	unsigned long flags;

	spin_lock_irqsave(&xdev->exec.ctx_list_lock, flags);
	list_del(&fpriv->link);
	spin_unlock_irqrestore(&xdev->exec.ctx_list_lock, flags);
}

