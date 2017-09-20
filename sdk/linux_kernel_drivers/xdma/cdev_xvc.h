/*******************************************************************************
 *
 * Xilinx XDMA IP Core Linux Driver
 *
 * Copyright(c) Sidebranch.
 * Copyright(c) Xilinx, Inc.
 *
 * Karen Xie <karen.xie@xilinx.com>
 * Leon Woestenberg <leon@sidebranch.com>
 *
 ******************************************************************************/

#ifndef __XVC_IOCTL_H__
#define __XVC_IOCTL_H__

#include <linux/ioctl.h>

/*
 * !!! TODO !!!
 * need a better way set the bar offset dynamicly
 */
#define XVC_BAR_OFFSET_DFLT	0x40000	/* DSA 4.0 */

#define XVC_MAGIC 0x58564344  // "XVCD"

struct xvc_ioc {
	unsigned int opcode;
	unsigned int length;
	unsigned char *tms_buf;
	unsigned char *tdi_buf;
	unsigned char *tdo_buf;
};

#define XDMA_IOCXVC	_IOWR(XVC_MAGIC, 1, struct xvc_ioc)

#endif /* __XVC_IOCTL_H__ */
