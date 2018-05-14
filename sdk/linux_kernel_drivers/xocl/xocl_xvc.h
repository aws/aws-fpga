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

#ifndef _XCL_XOCL_XVC_DRV_H_
#define _XCL_XOCL_XVC_DRV_H_

#define XVC_BAR_OFFSET_DFLT	0x40000

struct xocl_xvc {
	unsigned long base;		/* bar access offset */
	unsigned int instance;
	struct cdev sys_cdev;
	struct device *sys_device;
	void *__iomem bar;
};

int xocl_xvc_chardev_init(void);
void xocl_xvc_chardev_exit(void);
int xocl_xvc_device_init(struct xocl_xvc *xvc, struct device *dev);
int xocl_xvc_device_fini(struct xocl_xvc *xvc);

#endif
