/*******************************************************************************
 *
 * Xilinx XDMA IP Core Linux Driver
 * Copyright(c) 2015 - 2020 Xilinx, Inc.
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

#ifndef __XVC_IOCTL_H__
#define __XVC_IOCTL_H__

#include <linux/ioctl.h>

/*
 * the bar offset can be changed at compile time via xvc_bar_offset
 */
#define XVC_BAR_OFFSET_DFLT	0x40000	/* DSA 4.0 */

#define XVC_MAGIC 0x58564344  // "XVCD"

struct xvc_ioc {
	unsigned int opcode;
	unsigned int length;
	const char __user *tms_buf;
	const char __user *tdi_buf;
	void __user *tdo_buf;
};

#define XDMA_IOCXVC	_IOWR(XVC_MAGIC, 1, struct xvc_ioc)

#endif /* __XVC_IOCTL_H__ */
