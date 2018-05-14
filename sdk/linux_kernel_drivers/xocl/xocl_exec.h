/**
 * Copyright (C) 2017-2018 Xilinx, Inc
 *
 * Authors:
 *    Sonal Santan <sonal.santan@xilinx.com>
 *
 * Compute unit execution, interrupt management and client context core data structures.
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

#ifndef _XCL_XOCL_EXEC_H_
#define _XCL_XOCL_EXEC_H_

#include <linux/mutex.h>
#include <linux/init_task.h>
#include <linux/list.h>
#include <linux/wait.h>

#define XOCL_CSR_INTR0 0
#define XOCL_CSR_INTR1 1
#define XOCL_CSR_INTR2 2
#define XOCL_CSR_INTR3 3

#define XOCL_USER_INTR_START 4
#define XOCL_USER_INTR_END 16

#define XOCL_MAX_SLOTS 128
#define XOCL_MAX_CUS 128
#define XOCL_MAX_U32_SLOT_MASKS (((XOCL_MAX_SLOTS-1)>>5) + 1)
#define XOCL_MAX_U32_CU_MASKS (((XOCL_MAX_CUS-1)>>5) + 1)

struct eventfd_ctx;
struct drm_xocl_dev;

struct drm_xocl_client_ctx {
	struct list_head    link;
	atomic_t            trigger;
	/*
	 * Bitmap to indicate all the user interrupts registered. These are unmanaged
	 * interrupts directly used by the non-OpenCL application. The corresponding
	 * eventfd objects are stored in drm_xocl_dev::user_msix_table
	 */
	unsigned int        eventfd_bitmap;
	struct mutex        lock;
};

/**
 * struct drm_xocl_exec_core: Core data structure for command execution on a device
 *
 * @user_msix_table: Eventfd table for user interrupts
 * @user_msix_table_lock: Eventfd table lock
 * @ctx_list: Context list populated with device context
 * @ctx_list_lock: Context list lock
 * @poll_wait_queue: Wait queue for device polling
 * @scheduler: Command queue scheduler
 * @submitted_cmds: Tracking of command submitted for execution on this device
 * @num_slots: Number of command queue slots
 * @num_cus: Number of CUs in loaded program
 * @cu_shift_offset: CU idx to CU address shift value
 * @cu_base_addr: Base address of CU address space
 * @polling_mode: If set then poll for command completion
 * @cq_interrupt: If set then trigger interrupt to MB on new commands
 * @configured: Flag to indicate that the core data structure has been initialized
 * @slot_status: Bitmap to track status (busy(1)/free(0)) slots in command queue
 * @num_slot_masks: Number of slots status masks used (computed from @num_slots)
 * @cu_status: Bitmap to track status (busy(1)/free(0)) of CUs. Unused in ERT mode.
 * @num_cu_masks: Number of CU masks used (computed from @num_cus)
 * @sr0: If set, then status register [0..31] is pending with completed commands (ERT only).
 * @sr1: If set, then status register [32..63] is pending with completed commands (ERT only).
 * @sr2: If set, then status register [64..95] is pending with completed commands (ERT only).
 * @sr3: If set, then status register [96..127] is pending with completed commands (ERT only).
 * @ops: Scheduler operations vtable
 */
struct drm_xocl_exec_core {
	struct eventfd_ctx        *user_msix_table[16];
	struct mutex               user_msix_table_lock;

	struct list_head           ctx_list;
	spinlock_t	           ctx_list_lock;
	wait_queue_head_t          poll_wait_queue;
	
	struct xocl_sched          *scheduler;

	struct xocl_cmd            *submitted_cmds[XOCL_MAX_SLOTS];

	unsigned int               num_slots;
	unsigned int               num_cus;
	unsigned int               cu_shift_offset;
	u32                        cu_base_addr;
	unsigned int               polling_mode;
	unsigned int               cq_interrupt;
	unsigned int               configured;

	/* Bitmap tracks busy(1)/free(0) slots in cmd_slots*/
	u32                        slot_status[XOCL_MAX_U32_SLOT_MASKS];
	unsigned int               num_slot_masks; /* ((num_slots-1)>>5)+1 */

	u32                        cu_status[XOCL_MAX_U32_CU_MASKS];
	unsigned int               num_cu_masks; /* ((num_cus-1)>>5+1 */

	/* Status register pending complete.  Written by ISR, cleared by scheduler */
	atomic_t                   sr0;
	atomic_t                   sr1;
	atomic_t                   sr2;
	atomic_t                   sr3;

	/* Operations for dynamic indirection dependt on MB or kernel scheduler */
	struct xocl_sched_ops* ops;
};

int xocl_init_exec(struct drm_xocl_dev *xdev);
int xocl_fini_exec(struct drm_xocl_dev *xdev);

int xocl_init_test_thread(struct drm_xocl_dev *xdev);
int xocl_fini_test_thread(struct drm_xocl_dev *xdev);

void xocl_track_ctx(struct drm_xocl_dev *xdev, struct drm_xocl_client_ctx *fpriv);
void xocl_untrack_ctx(struct drm_xocl_dev *xdev, struct drm_xocl_client_ctx *fpriv);

#endif
