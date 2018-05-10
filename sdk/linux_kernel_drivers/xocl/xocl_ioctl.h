/**
 *  Copyright (C) 2015-2018 Xilinx, Inc
 *
 *  This file is dual licensed.  It may be redistributed and/or modified
 *  under the terms of the Apache 2.0 License OR version 2 of the GNU
 *  General Public License.
 *
 *  Apache License Verbiage
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  GPL license Verbiage:
 *
 *  This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation; either version 2 of the License, or (at your option) any later version.
 *  This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *  You should have received a copy of the GNU General Public License along with this program; if not, write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 */

/*
 * A GEM style device manager for PCIe based OpenCL accelerators.
 *
 * Copyright (C) 2017 Xilinx, Inc. All rights reserved.
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
 *
 * This software is licensed under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation, and
 * may be copied, distributed, and modified under those terms.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	 See the
 * GNU General Public License for more details.
 */

#ifndef _XCL_XOCL_IOCTL_H_
#define _XCL_XOCL_IOCTL_H_

#if defined(__KERNEL__)
#include <linux/types.h>
#elif defined(__cplusplus)
#include <cstdlib>
#include <cstdint>
#else
#include <stdlib.h>
#include <stdint.h>
#endif

enum {
	/* GEM core ioctls */
	/* Buffer creation */
	DRM_XOCL_CREATE_BO = 0,
	/* Buffer creation from user provided pointer */
	DRM_XOCL_USERPTR_BO,
	/* Map buffer into application user space (no DMA is performed) */
	DRM_XOCL_MAP_BO,
	/* Sync buffer (like fsync) in the desired direction by using DMA */
	DRM_XOCL_SYNC_BO,
	/* Get information about the buffer such as physical address in the device, etc */
	DRM_XOCL_INFO_BO,
	/* Update host cached copy of buffer wih user's data */
	DRM_XOCL_PWRITE_BO,
	/* Update user's data with host cached copy of buffer */
	DRM_XOCL_PREAD_BO,
	/* Other ioctls */
	DRM_XOCL_OCL_RESET,
	/* Currently unused */
	DRM_XOCL_CTX,
	/* Get information from device */
	DRM_XOCL_INFO,
	/* Unmanaged DMA from/to device */
	DRM_XOCL_PREAD_UNMGD,
	DRM_XOCL_PWRITE_UNMGD,
	/* Various usage metrics */
	DRM_XOCL_USAGE_STAT,
	/* Hardware debug command */
	DRM_XOCL_DEBUG,
	/* Command to run on one or more CUs */
	DRM_XOCL_EXECBUF,
        /* Register eventfd for user interrupts */
        DRM_XOCL_USER_INTR,
	/* Read xclbin/axlf */
        DRM_XOCL_READ_AXLF,
	DRM_XOCL_NUM_IOCTLS
};

enum drm_xocl_sync_bo_dir {
	DRM_XOCL_SYNC_BO_TO_DEVICE = 0,
	DRM_XOCL_SYNC_BO_FROM_DEVICE
};

/*
 * Higher 4 bits are for DDR, one for each DDR
 * LSB bit for execbuf
 */
#define DRM_XOCL_BO_BANK0   (0x1)
#define DRM_XOCL_BO_BANK1   (0x1 << 1)
#define DRM_XOCL_BO_BANK2   (0x1 << 2)
#define DRM_XOCL_BO_BANK3   (0x1 << 3)
#define DRM_XOCL_BO_CMA     (0x1 << 30)
#define DRM_XOCL_BO_EXECBUF (0x1 << 31)

struct drm_xocl_create_bo {
	uint64_t size;
	uint32_t handle;
	uint32_t flags;
};

struct drm_xocl_userptr_bo {
	uint64_t addr;
	uint64_t size;
	uint32_t handle;
	uint32_t flags;
};

struct drm_xocl_map_bo {
	uint32_t handle;
	uint32_t pad;
	uint64_t offset;
};

/**
 * struct drm_xocl_sync_bo - used for SYNQ_BO IOCTL
 * @handle:	GEM object handle
 * @flags:	Unused
 * @size:	Number of bytes to migrate
 * @offset:	Offset into the object to write to
 * @dir:	DRM_XOCL_SYNC_DIR_XXX
 */
struct drm_xocl_sync_bo {
	uint32_t handle;
	uint32_t flags;
	uint64_t size;
	uint64_t offset;
	enum drm_xocl_sync_bo_dir dir;
};

/**
 * struct drm_xocl_info_bo - used for INFO_BO IOCTL
 * @handle:	GEM object handle
 * @size:	Size of buffer object in bytes
 * @paddr:	physical address (out)
 */
struct drm_xocl_info_bo {
	uint32_t handle;
	uint32_t flags;
	uint64_t size;
	uint64_t paddr;
};

struct drm_xocl_axlf {
	struct axlf *xclbin;
};

/**
 * struct drm_xocl_pwrite_bo - used for PWRITE_BO IOCTL
 * @handle:	GEM object handle
 * @pad:	Padding
 * @offset:	Offset into the buffer object to write to
 * @size:	Length of data to write
 * @data_ptr:	Pointer to read the data from
 */
struct drm_xocl_pwrite_bo {
	uint32_t handle;
	uint32_t pad;
	uint64_t offset;
	uint64_t size;
	uint64_t data_ptr;
};

/**
 * struct drm_xocl_pread_bo - used for PREAD_BO IOCTL
 * @handle:	GEM object handle
 * @pad:	Padding
 * @offset:	Offset into the buffer object to read from
 * @size:	Length of data to read
 * @data_ptr:	Pointer to write the data into
 */
struct drm_xocl_pread_bo {
	uint32_t handle;
	uint32_t pad;
	uint64_t offset;
	uint64_t size;
	uint64_t data_ptr;
};

enum drm_xocl_ctx_code {
        XOCL_CTX_OP_ALLOC_CTX = 0,
        XOCL_CTX_OP_FREE_CTX
};

struct drm_xocl_ctx {
	enum drm_xocl_ctx_code op;
        char uuid[16];
	uint32_t cu_bitmap;
	uint32_t flags;
};

struct drm_xocl_info {
	unsigned short vendor;
	unsigned short device;
	unsigned short subsystem_vendor;
	unsigned short subsystem_device;
	unsigned int dma_engine_version;
	unsigned int driver_version;
	unsigned int pci_slot;
	char reserved[64];
};


/**
 * struct drm_xocl_pwrite_unmgd (used with PWRITE_UNMGD IOCTL)
 * @address_space: Address space in the DSA; currently only 0 is suported
 * @pad:	   Padding
 * @offset:	   Physical address in the specified address space
 * @size:	   Length of data to write
 * @data_ptr:	   Pointer to read the data from
 */
struct drm_xocl_pwrite_unmgd {
	uint32_t address_space;
	uint32_t pad;
	uint64_t paddr;
	uint64_t size;
	uint64_t data_ptr;
};

/**
 * struct drm_xocl_pread_unmgd (used for PREAD_UNMGD IOCTL)
 * @address_space: Address space in the DSA; currently only 0 is valid
 * @pad:	   Padding
 * @offset:	   Physical address in the specified address space
 * @size:	   Length of data to write
 * @data_ptr:	   Pointer to write the data to
 */
struct drm_xocl_pread_unmgd {
	uint32_t address_space;
	uint32_t pad;
	uint64_t paddr;
	uint64_t size;
	uint64_t data_ptr;
};


struct drm_xocl_mm_stat {
	size_t memory_usage;
	unsigned int bo_count;
};

/**
 * struct drm_xocl_stats (used for STATS IOCTL)
 * @address_space: Address space in the DSA; currently only 0 is valid
 * @pad:	   Padding
 * @offset:	   Physical address in the specified address space
 * @size:	   Length of data to write
 * @data_ptr:	   Pointer to write the data to
 */
struct drm_xocl_usage_stat {
	unsigned dma_channel_count;
	unsigned mm_channel_count;
	uint64_t h2c[8];
	uint64_t c2h[8];
	struct drm_xocl_mm_stat mm[8];
};

enum drm_xocl_debug_code {
        DRM_XOCL_DEBUG_ACQUIRE_CU = 0,
        DRM_XOCL_DEBUG_RELEASE_CU,
        DRM_XOCL_DEBUG_NIFD_RD,
        DRM_XOCL_DEBUG_NIFD_WR,
};

struct drm_xocl_debug {
        uint32_t ctx_id;
	enum drm_xocl_debug_code code;
	unsigned int code_size;
        uint64_t code_ptr;
};

/**
 * Opcodes for the embedded scheduler provided by the client to the driver
 */
enum drm_xocl_execbuf_code {
        DRM_XOCL_EXECBUF_RUN_KERNEL = 0,
        DRM_XOCL_EXECBUF_RUN_KERNEL_XYZ,
        DRM_XOCL_EXECBUF_PING,
        DRM_XOCL_EXECBUF_DEBUG,
};

/**
 * State of exec request managed by the kernel driver
 */
enum drm_xocl_execbuf_state {
        DRM_XOCL_EXECBUF_STATE_COMPLETE = 0,
        DRM_XOCL_EXECBUF_STATE_RUNNING,
        DRM_XOCL_EXECBUF_STATE_SUBMITTED,
        DRM_XOCL_EXECBUF_STATE_QUEUED,
        DRM_XOCL_EXECBUF_STATE_ERROR,
        DRM_XOCL_EXECBUF_STATE_ABORT,
};

/**
 * Layout of BO of EXECBUF kind
 */
struct drm_xocl_execbuf_bo {
        enum drm_xocl_execbuf_state state;
        enum drm_xocl_execbuf_code code;
        uint64_t cu_bitmap;
        uint64_t token;
        char buf[3584]; // inline regmap layout
};

struct drm_xocl_execbuf {
        uint32_t ctx_id;
        uint32_t exec_bo_handle;
};

/**
 * struct drm_xocl_user_intr (used for XOCL_USER_INTR IOCTL)
 * @ctx_id:        Context created before with CTX ioctl
 * @fd:	           File descriptor created with eventfd system call
 * @msix:	   User interrupt number (0 to 15)
 */
struct drm_xocl_user_intr {
        uint32_t ctx_id;
        int fd;
        int msix;
};


#define DRM_IOCTL_XOCL_CREATE_BO      DRM_IOWR(DRM_COMMAND_BASE +       \
					       DRM_XOCL_CREATE_BO, struct drm_xocl_create_bo)
#define DRM_IOCTL_XOCL_USERPTR_BO     DRM_IOWR(DRM_COMMAND_BASE +	\
					       DRM_XOCL_USERPTR_BO, struct drm_xocl_userptr_bo)
#define DRM_IOCTL_XOCL_MAP_BO	      DRM_IOWR(DRM_COMMAND_BASE +       \
					       DRM_XOCL_MAP_BO, struct drm_xocl_map_bo)
#define DRM_IOCTL_XOCL_SYNC_BO	      DRM_IOW (DRM_COMMAND_BASE +       \
					       DRM_XOCL_SYNC_BO, struct drm_xocl_sync_bo)
#define DRM_IOCTL_XOCL_INFO_BO	      DRM_IOWR(DRM_COMMAND_BASE +       \
					       DRM_XOCL_INFO_BO, struct drm_xocl_info_bo)
#define DRM_IOCTL_XOCL_PWRITE_BO      DRM_IOW (DRM_COMMAND_BASE +       \
					       DRM_XOCL_PWRITE_BO, struct drm_xocl_pwrite_bo)
#define DRM_IOCTL_XOCL_PREAD_BO	      DRM_IOWR(DRM_COMMAND_BASE +       \
					       DRM_XOCL_PREAD_BO, struct drm_xocl_pread_bo)
#define DRM_IOCTL_XOCL_CTX	      DRM_IOWR(DRM_COMMAND_BASE +       \
					       DRM_XOCL_CTX, struct drm_xocl_ctx)
#define DRM_IOCTL_XOCL_INFO	      DRM_IOR(DRM_COMMAND_BASE +        \
					      DRM_XOCL_INFO, struct drm_xocl_info)
#define DRM_IOCTL_XOCL_READ_AXLF      DRM_IOW(DRM_COMMAND_BASE +        \
					      DRM_XOCL_READ_AXLF, struct drm_xocl_axlf)
#define DRM_IOCTL_XOCL_PWRITE_UNMGD   DRM_IOW (DRM_COMMAND_BASE +	\
					       DRM_XOCL_PWRITE_UNMGD, struct drm_xocl_pwrite_unmgd)
#define DRM_IOCTL_XOCL_PREAD_UNMGD    DRM_IOWR(DRM_COMMAND_BASE +	\
					       DRM_XOCL_PREAD_UNMGD, struct drm_xocl_pread_unmgd)
#define DRM_IOCTL_XOCL_USAGE_STAT     DRM_IOR(DRM_COMMAND_BASE +	\
					      DRM_XOCL_USAGE_STAT, struct drm_xocl_usage_stat)
#define DRM_IOCTL_XOCL_DEBUG          DRM_IOWR(DRM_COMMAND_BASE +	\
					       DRM_XOCL_DEBUG, struct drm_xocl_debug)
#define DRM_IOCTL_XOCL_EXECBUF        DRM_IOWR(DRM_COMMAND_BASE +	\
					       DRM_XOCL_EXECBUF, struct drm_xocl_execbuf)
#define DRM_IOCTL_XOCL_USER_INTR      DRM_IOWR(DRM_COMMAND_BASE +	\
					       DRM_XOCL_USER_INTR, struct drm_xocl_user_intr)

#endif
