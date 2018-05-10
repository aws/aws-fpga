/*
 * Copyright (C) 2017-2018 Xilinx, Inc
 *
 * Authors:
 *    Soren Soe <soren.soe@xilinx.com>
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
#include <linux/bitmap.h>
#include <linux/list.h>
#include <linux/eventfd.h>
#include <linux/kthread.h>
#include "ert.h"
#include "xocl_drv.h"
#include "xocl_exec.h"
#include "xocl_xdma.h"

//#define SCHED_VERBOSE
#define SCHED_THREAD_ENABLE

#if 0
static unsigned long zero = 0;
static unsigned long time_ns(void)
{
	struct timeval now;
	do_gettimeofday(&now);
	if (!zero)
		zero = timeval_to_ns(&now);
	return timeval_to_ns(&now) - zero;
}
#endif

#define sched_error_on(xdev,expr,msg)			                  \
({		                                                          \
	unsigned int ret = 0;                                             \
	if ((expr)) {						          \
		DRM_INFO("Assertion failed: %s:%d:%s:%s %s\n"             \
			 ,__FILE__,__LINE__,__FUNCTION__,#expr,msg);      \
		xdev->exec.scheduler->error=1;                            \
		ret = 1; 					          \
	}                                                                 \
	(ret);                                                            \
})


#ifdef SCHED_VERBOSE
# define SCHED_DEBUG(msg) printk(msg)
# define SCHED_DEBUGF(format,...) printk(format, ##__VA_ARGS__)
#else
# define SCHED_DEBUG(msg)
# define SCHED_DEBUGF(format,...)
#endif

#define XOCL_U32_MASK 0xFFFFFFFF

/**
 * struct xocl_sched: scheduler for xocl_cmd objects
 *
 * @scheduler_thread: thread associated with this scheduler
 * @use_count: use count for this scheduler
 * @wait_queue: conditional wait queue for scheduler thread
 * @error: set to 1 to indicate scheduler error
 * @command_queue: list of command objects managed by scheduler
 * @intc: boolean flag set when there is a pending interrupt for command completion
 * @poll: number of running commands in polling mode
 */
struct xocl_sched
{
	struct task_struct        *scheduler_thread;
	unsigned int               use_count;

	wait_queue_head_t          wait_queue;
	unsigned int               error;

	struct list_head           command_queue;
	atomic_t                   intc; /* pending interrupt */
	atomic_t                   poll; /* number of cmds to poll */
};

static struct xocl_sched global_scheduler0;

/**
 * Command data used by scheduler
 *
 * @list: command object moves from list to list
 * @bo: underlying drm buffer object 
 * @xdev: device handle
 * @xs: scehduler processing this commands
 * @state: state of command object per scheduling
 * @cu_idx: index of CU executing this cmd object; used in penguin mode only
 * @slot_idx: command queue index of this command object
 * @packet: mapped ert packet object from user space
 */
struct xocl_cmd
{
	struct list_head list;
	struct drm_xocl_bo *bo;
	struct drm_xocl_dev *xdev;
	struct xocl_sched *xs;
	enum ert_cmd_state state;
	int cu_idx;
	int slot_idx;

	struct ert_packet *packet;
};

/**
 * set_cmd_int_state() - Set internal command state used by scheduler only
 *
 * @xcmd: command to change internal state on
 * @state: new command state per ert.h
 */
inline void
set_cmd_int_state(struct xocl_cmd* xcmd, enum ert_cmd_state state)
{
	SCHED_DEBUGF("->set_cmd_int_state(,%d)\n",state);
	xcmd->state = state;
	SCHED_DEBUG("<-set_cmd_int_state\n");
}

/**
 * set_cmd_state() - Set both internal and external state of a command
 *
 * The state is reflected externally through the command packet
 * as well as being captured in internal state variable
 *
 * @xcmd: command object
 * @state: new state
 */
inline void
set_cmd_state(struct xocl_cmd* xcmd, enum ert_cmd_state state)
{
	SCHED_DEBUGF("->set_cmd_state(,%d)\n",state);
	xcmd->state = state;
	xcmd->packet->state = state;
	SCHED_DEBUG("<-set_cmd_state\n");
}

/**
 * List of free xocl_cmd objects.
 *
 * @free_cmds: populated with recycled xocl_cmd objects
 * @cmd_mutex: mutex lock for cmd_list
 *
 * Command objects are recycled for later use and only freed when kernel
 * module is unloaded.
 */
static LIST_HEAD(free_cmds);
static DEFINE_MUTEX(free_cmds_mutex);

/**
 * List of new pending xocl_cmd objects 
 *
 * @pending_cmds: populated from user space with new commands for buffer objects
 * @num_pending: number of pending commands
 *
 * Scheduler copies pending commands to its private queue when necessary
 */
static LIST_HEAD(pending_cmds);
static DEFINE_MUTEX(pending_cmds_mutex);
static atomic_t num_pending = ATOMIC_INIT(0);

/**
 * get_free_xocl_cmd() - Get a free command object
 *
 * Get from free/recycled list or allocate a new command if necessary.
 *
 * Return: Free command object
 */
static struct xocl_cmd*
get_free_xocl_cmd(void)
{
	struct xocl_cmd* cmd;
	SCHED_DEBUG("-> get_free_xocl_cmd\n");
	mutex_lock(&free_cmds_mutex);
	cmd=list_first_entry_or_null(&free_cmds,struct xocl_cmd,list);
	if (cmd)
		list_del(&cmd->list);
        mutex_unlock(&free_cmds_mutex);
	if (!cmd)
		cmd = kmalloc(sizeof(struct xocl_cmd),GFP_KERNEL);
	if (!cmd)
		return ERR_PTR(-ENOMEM);
	SCHED_DEBUGF("<- get_free_xocl_cmd %p\n",cmd);
	return cmd;
}

/**
 * add_cmd() - Add a new command to pending list
 *
 * @xdev: device owning adding the buffer object 
 * @bo: buffer objects from user space from which new command is created
 *
 * Scheduler copies pending commands to its internal command queue.
 *
 * Return: 0 on success, -errno on failure
 */
static int
add_cmd(struct drm_xocl_dev *xdev, struct drm_xocl_bo* bo)
{
	struct xocl_cmd *xcmd = get_free_xocl_cmd();
	SCHED_DEBUG("-> add_cmd\n");
	xcmd->bo=bo;
	xcmd->xdev=xdev;
	xcmd->cu_idx=-1;
	xcmd->slot_idx=-1;
	xcmd->packet = (struct ert_packet*)bo->vmapping;
	xcmd->xs = xdev->exec.scheduler;
	set_cmd_state(xcmd,ERT_CMD_STATE_NEW);
	mutex_lock(&pending_cmds_mutex);
	list_add_tail(&xcmd->list,&pending_cmds);
	mutex_unlock(&pending_cmds_mutex);

	/* wake scheduler */
	atomic_inc(&num_pending);
	wake_up_interruptible(&xcmd->xs->wait_queue);
	
	SCHED_DEBUG("<- add_cmd\n");
	return 0;
}

/**
 * recycle_cmd() - recycle a command objects 
 *
 * @xcmd: command object to recycle
 *
 * Command object is added to the freelist
 *
 * Return: 0
 */
static int
recycle_cmd(struct xocl_cmd* xcmd)
{
	SCHED_DEBUGF("recycle %p\n",xcmd);
	mutex_lock(&free_cmds_mutex);
	list_del(&xcmd->list);
	list_add_tail(&xcmd->list,&free_cmds);
	mutex_unlock(&free_cmds_mutex);
	return 0;
}

/**
 * delete_cmd_list() - reclaim memory for all allocated command objects
 */
static void
delete_cmd_list(void)
{
	struct xocl_cmd *xcmd;
	struct list_head *pos, *next;

	mutex_lock(&free_cmds_mutex);
	list_for_each_safe(pos, next, &free_cmds) {
		xcmd = list_entry(pos, struct xocl_cmd, list);
		list_del(pos);
		kfree(xcmd);
	}
	mutex_unlock(&free_cmds_mutex);
}



/**
 * struct xocl_sched_ops: scheduler specific operations
 *
 * Scheduler can operate in MicroBlaze mode (mb/ert) or in penguin mode. This
 * struct differentiates specific operations.  The struct is per device node,
 * meaning that one device can operate in ert mode while another can operate in
 * penguin mode.
 */
struct xocl_sched_ops
{
	int (*submit) (struct xocl_cmd *xcmd);
	void (*query) (struct xocl_cmd *xcmd);
};

static struct xocl_sched_ops mb_ops;
static struct xocl_sched_ops penguin_ops;

/**
 * is_ert() - Check if running in embedded (ert) mode.
 * 
 * Return: %true of ert mode, %false otherwise
 */
inline unsigned int
is_ert(struct drm_xocl_dev *xdev)
{
	return xdev->exec.ops == &mb_ops;
}

/**
 * ffs_or_neg_one() - Find first set bit in a 32 bit mask.
 * 
 * @mask: mask to check
 *
 * First LSBit is at position 0.
 *
 * Return: Position of first set bit, or -1 if none
 */
inline int
ffs_or_neg_one(u32 mask)
{
	if (!mask)
		return -1;
	return ffs(mask)-1;
}

/**
 * ffz_or_neg_one() - First first zero bit in bit mask
 * 
 * @mask: mask to check
 * Return: Position of first zero bit, or -1 if none
 */
inline int
ffz_or_neg_one(u32 mask)
{
	if (mask==XOCL_U32_MASK)
		return -1;
	return ffz(mask);
}


/**
 * slot_size() - slot size per device configuration
 *
 * Return: Command queue slot size
 */
inline unsigned int
slot_size(struct drm_xocl_dev *xdev)
{
	return ERT_CQ_SIZE / xdev->exec.num_slots;
}

/**
 * cu_mask_idx() - CU mask index for a given cu index
 *
 * @cu_idx: Global [0..127] index of a CU
 * Return: Index of the CU mask containing the CU with cu_idx
 */
inline unsigned int
cu_mask_idx(unsigned int cu_idx)
{
	return cu_idx >> 5; /* 32 cus per mask */
}

/**
 * cu_idx_in_mask() - CU idx within its mask
 *
 * @cu_idx: Global [0..127] index of a CU
 * Return: Index of the CU within the mask that contains it
 */
inline unsigned int
cu_idx_in_mask(unsigned int cu_idx)
{
	return cu_idx - (cu_mask_idx(cu_idx) << 5);
}

/**
 * cu_idx_from_mask() - Given CU idx within a mask return its global idx [0..127]
 *
 * @cu_idx: Index of CU with mask identified by mask_idx
 * @mask_idx: Mask index of the has CU with cu_idx
 * Return: Global cu_idx [0..127]
 */
inline unsigned int
cu_idx_from_mask(unsigned int cu_idx, unsigned int mask_idx)
{
	return cu_idx + (mask_idx << 5);
}

/**
 * slot_mask_idx() - Slot mask idx index for a given slot_idx
 *
 * @slot_idx: Global [0..127] index of a CQ slot
 * Return: Index of the slot mask containing the slot_idx
 */
inline unsigned int
slot_mask_idx(unsigned int slot_idx)
{
	return slot_idx >> 5;
}

/**
 * slot_idx_in_mask() - Index of command queue slot within the mask that contains it
 *
 * @slot_idx: Global [0..127] index of a CQ slot
 * Return: Index of slot within the mask that contains it
 */
inline unsigned int
slot_idx_in_mask(unsigned int slot_idx)
{
	return slot_idx - (slot_mask_idx(slot_idx) << 5);
}

/**
 * slot_idx_from_mask_idx() - Given slot idx within a mask, return its global idx [0..127]
 *
 * @slot_idx: Index of slot with mask identified by mask_idx
 * @mask_idx: Mask index of the mask hat has slot with slot_idx
 * Return: Global slot_idx [0..127]
 */
inline unsigned int
slot_idx_from_mask_idx(unsigned int slot_idx,unsigned int mask_idx)
{
	return slot_idx + (mask_idx << 5);
}

/**
 * opcode() - Command opcode
 *
 * @cmd: Command object
 * Return: Opcode per command packet
 */
inline u32
opcode(struct xocl_cmd* xcmd)
{
	return xcmd->packet->opcode;
}

/**
 * payload_size() - Command payload size
 *
 * @xcmd: Command object
 * Return: Size in number of words of command packet payload
 */
inline u32
payload_size(struct xocl_cmd *xcmd)
{
	return xcmd->packet->count;
}

/**
 * packet_size() - Command packet size
 *
 * @xcmd: Command object
 * Return: Size in number of words of command packet
 */
inline u32
packet_size(struct xocl_cmd *xcmd)
{
	return payload_size(xcmd) + 1;
}

/**
 * cu_masks() - Number of command packet cu_masks
 *
 * @xcmd: Command object
 * Return: Total number of CU masks in command packet
 */
inline u32
cu_masks(struct xocl_cmd *xcmd)
{
	struct ert_start_kernel_cmd *sk;
	if (opcode(xcmd)!=ERT_START_KERNEL)
		return 0;
	sk = (struct ert_start_kernel_cmd *)xcmd->packet;
	return 1 + sk->extra_cu_masks;
}

/**
 * regmap_size() - Size of regmap is payload size (n) minus the number of cu_masks
 * 
 * @xcmd: Command object
 * Return: Size of register map in number of words
 */
inline u32
regmap_size(struct xocl_cmd* xcmd)
{
	return payload_size(xcmd) - cu_masks(xcmd);
}

/**
 * cu_idx_to_addr() - Convert CU idx into it relative bar address.
 *
 * @xdev: Device handle
 * @cu_idx: Global CU idx
 * Return: Address of CU relative to bar
 */
inline u32
cu_idx_to_addr(struct drm_xocl_dev *xdev,unsigned int cu_idx)
{
	return (cu_idx << xdev->exec.cu_shift_offset) + xdev->exec.cu_base_addr;
}

/**
 * cu_idx_to_bitmask() - Compute the cu bitmask for cu_idx
 *
 * Subtract 32 * lower bitmasks prior to bitmask repsenting
 * this index.  For example, f.x cu_idx=67
 *  1 << (67 - (67>>5)<<5) = 
 *  1 << (67 - (2<<5)) = 
 *  1 << (67 - 64) =
 *  1 << 3 =
 *  0b1000 for position 4 in third bitmask
 *
 * @xdev: Device handle
 * @cu_idx: Global index [0..127] of CU
 *
 * This function computes the bitmask for cu_idx in the mask that stores cu_idx
 *
 * Return: Bitmask with bit set for corresponding CU
 */
inline u32
cu_idx_to_bitmask(struct drm_xocl_dev *xdev, u32 cu_idx)
{
	return 1 << (cu_idx - (cu_mask_idx(cu_idx)<<5));
}


/**
 * configure() - Configure the scheduler
 *
 * Process the configure command sent from user space. Only one process can
 * configure the scheduler, so if scheduler is already configured, the
 * function should verify that another process doesn't expect different
 * configuration.
 *
 * Future may need ability to query current configuration so as to keep
 * multiple processes in sync.
 *
 * Return: 0 on success, 1 on failure
 */
static int
configure(struct xocl_cmd *xcmd)
{
	struct drm_xocl_dev *xdev=xcmd->xdev;
	struct ert_configure_cmd *cfg;

	if (sched_error_on(xdev,opcode(xcmd)!=ERT_CONFIGURE,"expected configure command"))
		return 1;

	cfg = (struct ert_configure_cmd *)(xcmd->packet);

	if (xdev->exec.configured==0) {
		SCHED_DEBUG("configuring scheduler\n");
		xdev->exec.num_slots = ERT_CQ_SIZE / cfg->slot_size;
		xdev->exec.num_cus = cfg->num_cus;
		xdev->exec.cu_shift_offset = cfg->cu_shift;
		xdev->exec.cu_base_addr = cfg->cu_base_addr;
		xdev->exec.num_cu_masks = ((xdev->exec.num_cus-1)>>5) + 1;

		if (cfg->ert) {
			SCHED_DEBUG("++ configuring embedded scheduler mode\n");
			xdev->exec.ops = &mb_ops;
			xdev->exec.polling_mode = cfg->polling;
			xdev->exec.cq_interrupt = cfg->cq_int;
		}
		else {
			SCHED_DEBUG("++ configuring penguin scheduler mode\n");
			xdev->exec.ops = &penguin_ops;
			xdev->exec.polling_mode = 1;
		}

		DRM_INFO("scheduler config ert(%d) slots(%d), cus(%d), cu_shift(%d), cu_base(0x%x), cu_masks(%d)\n"
			 ,is_ert(xdev)
			 ,xdev->exec.num_slots
			 ,xdev->exec.num_cus
			 ,xdev->exec.cu_shift_offset
			 ,xdev->exec.cu_base_addr
			 ,xdev->exec.num_cu_masks);

		return 0;
	}

	DRM_INFO("reconfiguration of scheduler not supported\n");

	return 1;
}

/**
 * acquire_slot_idx() - Acquire a slot index if available.  Update slot status to busy
 * so it cannot be reacquired.
 *
 * This function is called from scheduler thread
 *
 * Return: Command queue slot index, or -1 if none avaiable
 */
static int
acquire_slot_idx(struct drm_xocl_dev *xdev)
{
	unsigned int mask_idx=0, slot_idx=-1;
	u32 mask;
	SCHED_DEBUG("-> acquire_slot_idx\n");
	for (mask_idx=0; mask_idx<xdev->exec.num_slot_masks; ++mask_idx) {
		mask = xdev->exec.slot_status[mask_idx];
		slot_idx = ffz_or_neg_one(mask);
		if (slot_idx==-1 || slot_idx_from_mask_idx(slot_idx,mask_idx)>=xdev->exec.num_slots)
			continue;
		xdev->exec.slot_status[mask_idx] ^= (1<<slot_idx);
		SCHED_DEBUGF("<- acquire_slot_idx returns %d\n",slot_idx_from_mask_idx(slot_idx,mask_idx));
		return slot_idx_from_mask_idx(slot_idx,mask_idx);
	}
	SCHED_DEBUGF("<- acquire_slot_idx returns -1\n");
	return -1;
}

/**
 * release_slot_idx() - Release a slot index
 * 
 * Update slot status mask for slot index.  Notify scheduler in case
 * release is via ISR
 * 
 * @xdev: scheduler
 * @slot_idx: the slot index to release
 */
static void
release_slot_idx(struct drm_xocl_dev *xdev, unsigned int slot_idx)
{
	unsigned int mask_idx = slot_mask_idx(slot_idx);
	unsigned int pos = slot_idx_in_mask(slot_idx);
	SCHED_DEBUGF("<-> release_slot_idx slot_status[%d]=0x%x, pos=%d\n"
		     ,mask_idx,xdev->exec.slot_status[mask_idx],pos);
	xdev->exec.slot_status[mask_idx] ^= (1<<pos);
}

/**
 * get_cu_idx() - Get index of CU executing command at idx
 *
 * This function is called in polling mode only and 
 * the command at cmd_idx is guaranteed to have been 
 * started on a CU
 * 
 * Return: Index of CU, or -1 on error
 */
inline unsigned int
get_cu_idx(struct drm_xocl_dev *xdev, unsigned int cmd_idx)
{
	struct xocl_cmd *xcmd = xdev->exec.submitted_cmds[cmd_idx];
	if (sched_error_on(xdev,!xcmd,"no submtted cmd"))
		return -1;
	return xcmd->cu_idx;
}

/**
 * cu_done() - Check status of CU
 * 
 * @cu_idx: Index of cu to check
 *
 * This function is called in polling mode only.  The cu_idx
 * is guaranteed to have been started
 *
 * Return: %true if cu done, %false otherwise
 */
inline int
cu_done(struct drm_xocl_dev *xdev, unsigned int cu_idx)
{
	u32 cu_addr = cu_idx_to_addr(xdev,cu_idx);
	SCHED_DEBUGF("-> cu_done(,%d) checks cu at address 0x%x\n",cu_idx,cu_addr);
	/* done is indicated by AP_DONE(2) alone or by AP_DONE(2) | AP_IDLE(4)
	 * but not by AP_IDLE itself.  Since 0x10 | (0x10 | 0x100) = 0x110 
	 * checking for 0x10 is sufficient. */
	if (ioread32(xdev->user_bar + cu_addr) & 2) {
		unsigned int mask_idx = cu_mask_idx(cu_idx);
		unsigned int pos = cu_idx_in_mask(cu_idx);
		xdev->exec.cu_status[mask_idx] ^= 1<<pos;
		SCHED_DEBUG("<- cu_done returns 1\n");
		return true;
	}
	SCHED_DEBUG("<- cu_done returns 0\n");
	return false;
}

/**
 * cmd_done() - Check of a command is done
 * 
 * @cmd_idx: Slot index of command to check
 *
 * This function is called in polling mode only.  The command
 * at cmd_idx is guaranteed to have been started on a CU.
 *
 * Return: %true if command is done, %false otherwise
 */
inline int
cmd_done(struct drm_xocl_dev *xdev, unsigned int cmd_idx)
{
	struct xocl_cmd *xcmd = xdev->exec.submitted_cmds[cmd_idx];
	u32 opc = 0;
	SCHED_DEBUGF("-> cmd_done(,%d)\n",cmd_idx);

	if (sched_error_on(xdev,!xcmd || xcmd->slot_idx!=cmd_idx,"no command or missing slot index"))
		return false;

	opc = opcode(xcmd);
	if (opc==ERT_START_CU) {
		int val = cu_done(xdev,get_cu_idx(xdev,cmd_idx));
		SCHED_DEBUGF("<- cmd_done (cu_done) returns %d\n",val);
		return val;
	}
	if (opc==ERT_CONFIGURE) {
		SCHED_DEBUG("<- cmd_done (configure) returns 1\n");
		return true;
	}
	SCHED_DEBUG("<- cmd_done returns 0\n");
	return false;
}

/**
 * notify_host() - Notify user space that a command is complete.
 */
static void
notify_host(struct xocl_cmd *xcmd)
{
	struct list_head *ptr;
	struct drm_xocl_client_ctx *entry;
	struct drm_xocl_dev *xdev = xcmd->xdev;
	unsigned long flags = 0;

	SCHED_DEBUG("-> notify_host\n");

	/* now for each client update the trigger counter in the context */
	spin_lock_irqsave(&xdev->exec.ctx_list_lock, flags);
	list_for_each(ptr, &xdev->exec.ctx_list) {
		entry = list_entry(ptr, struct drm_xocl_client_ctx, link);
		atomic_inc(&entry->trigger);
	}
	spin_unlock_irqrestore(&xdev->exec.ctx_list_lock, flags);
	/* wake up all the clients */
	wake_up_interruptible(&xdev->exec.poll_wait_queue);
	SCHED_DEBUG("<- notify_host\n");
}

/**
 * mark_cmd_complete() - Move a command to complete state
 *
 * Commands are marked complete in two ways
 *  1. Through polling of CUs or polling of MB status register
 *  2. Through interrupts from MB
 * In both cases, the completed commands are residing in the completed_cmds
 * list and the number of completed commands is reflected in num_completed.
 *
 * @xcmd: Command to mark complete
 *
 * The command is removed from the slot it occupies in the device command
 * queue. The slot is released so new commands can be submitted.  The host
 * is notified that some command has completed.
 */
static void
mark_cmd_complete(struct xocl_cmd *xcmd)
{
	SCHED_DEBUGF("-> mark_cmd_complete(,%d)\n",xcmd->slot_idx);
	xcmd->xdev->exec.submitted_cmds[xcmd->slot_idx] = NULL;
	set_cmd_state(xcmd,ERT_CMD_STATE_COMPLETED);
	if (xcmd->xdev->exec.polling_mode)
		atomic_dec(&xcmd->xs->poll);
	release_slot_idx(xcmd->xdev,xcmd->slot_idx);
	notify_host(xcmd);
	SCHED_DEBUGF("<- mark_cmd_complete\n");
}

/**
 * mark_mask_complete() - Move all commands in mask to complete state
 *
 * @mask: Bitmask with queried statuses of commands
 * @mask_idx: Index of the command mask. Used to offset the actual cmd slot index
 */
static void
mark_mask_complete(struct drm_xocl_dev *xdev, u32 mask, unsigned int mask_idx)
{
	int bit_idx=0,cmd_idx=0;
	SCHED_DEBUGF("-> mark_mask_complete(,0x%x,%d)\n",mask,mask_idx);
	if (!mask)
		return;
	for (bit_idx=0, cmd_idx=mask_idx<<5; bit_idx<32; mask>>=1,++bit_idx,++cmd_idx)
		if (mask & 0x1)
			mark_cmd_complete(xdev->exec.submitted_cmds[cmd_idx]);
	SCHED_DEBUG("<- mark_mask_complete\n");
}

/**
 * queued_to_running() - Move a command from queued to running state if possible
 *
 * @xcmd: Command to start
 *
 * Upon success, the command is not necessarily running. In ert mode the
 * command will have been submitted to the embedded scheduler, whereas in
 * penguin mode the command has been started on a CU.
 *
 * Return: %true if command was submitted to device, %false otherwise
 */
static int
queued_to_running(struct xocl_cmd *xcmd)
{
	int retval = false;
	
	SCHED_DEBUG("-> queued_to_running\n");
	
	if (opcode(xcmd)==ERT_CONFIGURE)
		configure(xcmd);

	if (xcmd->xdev->exec.ops->submit(xcmd)) {
		set_cmd_int_state(xcmd,ERT_CMD_STATE_RUNNING);
		if (xcmd->xdev->exec.polling_mode)
			atomic_inc(&xcmd->xs->poll);
		xcmd->xdev->exec.submitted_cmds[xcmd->slot_idx] = xcmd;
		retval = true;
	}

	SCHED_DEBUGF("<- queued_to_running returns %d\n",retval);

	return retval;
}

/**
 * running_to_complete() - Check status of running commands
 *
 * @xcmd: Command is in running state
 *
 * If a command is found to be complete, it marked complete prior to return
 * from this function.
 */
static void
running_to_complete(struct xocl_cmd *xcmd)
{
	SCHED_DEBUG("-> running_to_complete\n");

	xcmd->xdev->exec.ops->query(xcmd);

	SCHED_DEBUG("<- running_to_complete\n");
}

/**
 * complete_to_free() - Recycle a complete command objects
 *
 * @xcmd: Command is in complete state
 */
static void
complete_to_free(struct xocl_cmd *xcmd)
{
	SCHED_DEBUG("-> complete_to_free\n");

	drm_gem_object_unreference_unlocked(&xcmd->bo->base);
	recycle_cmd(xcmd);

	SCHED_DEBUG("<- complete_to_free\n");
}

/**
 * scheduler_queue_cmds() - Queue any pending commands
 *
 * The scheduler copies pending commands to its internal command queue where
 * is is now in queued state.
 */
static void
scheduler_queue_cmds(struct xocl_sched *xs)
{
	struct xocl_cmd *xcmd;

	SCHED_DEBUG("-> scheduler_queue_cmds\n");
	mutex_lock(&pending_cmds_mutex);
	while (!list_empty(&pending_cmds)) {
		xcmd = list_first_entry(&pending_cmds,struct xocl_cmd,list);
		if (xcmd->xs != xs)
			continue;
		list_del(&xcmd->list);
		list_add_tail(&xcmd->list,&xs->command_queue);
		set_cmd_int_state(xcmd,ERT_CMD_STATE_QUEUED);
		atomic_dec(&num_pending);
	}
	mutex_unlock(&pending_cmds_mutex);
	SCHED_DEBUG("<- scheduler_queue_cmds\n");
}

/**
 * scheduler_iterator_cmds() - Iterate all commands in scheduler command queue
 */
static void
scheduler_iterate_cmds(struct xocl_sched *xs)
{
	struct xocl_cmd *xcmd;
	struct list_head *pos, *next;

	SCHED_DEBUG("-> scheduler_iterate_cmds\n");
	list_for_each_safe(pos, next, &xs->command_queue) {
		xcmd = list_entry(pos, struct xocl_cmd, list);

		if (xcmd->state == ERT_CMD_STATE_QUEUED)
			queued_to_running(xcmd);
		if (xcmd->state == ERT_CMD_STATE_RUNNING)
			running_to_complete(xcmd);
		if (xcmd->state == ERT_CMD_STATE_COMPLETED)
			complete_to_free(xcmd);
		
	}
	SCHED_DEBUG("<- scheduler_iterate_cmds\n");
}

/**
 * scheduler_wait_condition() - Check status of scheduler wait condition
 * 
 * Scheduler must wait (sleep) if 
 *   1. there are no pending commands
 *   2. no pending interrupt from embedded scheduler
 *   3. no pending complete commands in polling mode
 *
 * Return: 1 if scheduler must wait, 0 othewise
 */
static int
scheduler_wait_condition(struct xocl_sched *xs)
{
	if (kthread_should_stop() || xs->error) {
		SCHED_DEBUG("scheduler wakes kthread_should_stop\n");
		return 0;
	}

	if (atomic_read(&num_pending)) {
		SCHED_DEBUG("scheduler wakes to copy new pending commands\n");
		return 0;
	}

	if (atomic_read(&xs->intc)) {
		SCHED_DEBUG("scheduler wakes on interrupt\n");
		atomic_set(&xs->intc,0);
		return 0;
	}

	if (atomic_read(&xs->poll)) {
		SCHED_DEBUG("scheduler wakes to poll\n");
		return 0;
	}

	SCHED_DEBUG("scheduler waits ...\n");
	return 1;
}

/**
 * scheduler_wait() - check if scheduler should wait
 * 
 * See scheduler_wait_condition().
 */
static void
scheduler_wait(struct xocl_sched *xs)
{
	wait_event_interruptible(xs->wait_queue,scheduler_wait_condition(xs)==0);
}

/**
 * scheduler_loop() - Run one loop of the scheduler
 */
static void
scheduler_loop(struct xocl_sched *xs)
{
	SCHED_DEBUG("scheduler_loop\n");

	scheduler_wait(xs);

	if (xs->error) {
		DRM_INFO("scheduler encountered unexpected error and exits\n");
		return;
	}

	/* queue new pending commands */
	scheduler_queue_cmds(xs);

	/* iterate all commands */
	scheduler_iterate_cmds(xs);
}

/**
 * scheduler() - Command scheduler thread routine
 */
#if defined(__GNUC__) && !defined(SCHED_THREAD_ENABLE)
__attribute__((unused))
#endif
static int
scheduler(void* data)
{
	struct xocl_sched *xs = (struct xocl_sched *)data;
	while (!kthread_should_stop() && !xs->error)
		scheduler_loop(xs);
	DRM_INFO("%s:%d scheduler thread exits with value %d\n",__FILE__,__LINE__,xs->error);
	return xs->error;
}

/**
 * init_scheduler_thread() - Initialize scheduler thread if necessary
 *
 * Return: 0 on success, -errno otherwise
 */
static int
init_scheduler_thread(void)
{
#ifdef SCHED_THREAD_ENABLE
	SCHED_DEBUGF("init_scheduler_thread use_count=%d\n",global_scheduler0.use_count);
	if (global_scheduler0.use_count++)
		return 0;

	init_waitqueue_head(&global_scheduler0.wait_queue);
	global_scheduler0.error = 0;

	INIT_LIST_HEAD(&global_scheduler0.command_queue);
	atomic_set(&global_scheduler0.intc,0);
	atomic_set(&global_scheduler0.poll,0);

	global_scheduler0.scheduler_thread = kthread_run(scheduler,(void*)&global_scheduler0,"xocl-scheduler-thread0");
	if (IS_ERR(global_scheduler0.scheduler_thread)) {
		int ret = PTR_ERR(global_scheduler0.scheduler_thread);
		DRM_ERROR(__func__);
		return ret;
	}
#endif
	return 0;
}

/**
 * fini_scheduler_thread() - Finalize scheduler thread if unused
 *
 * Return: 0 on success, -errno otherwise
 */
static int
fini_scheduler_thread(void)
{
	int retval = 0;
	SCHED_DEBUGF("fini_scheduler_thread use_count=%d\n",global_scheduler0.use_count);
	if (--global_scheduler0.use_count)
		return 0;

	retval = kthread_stop(global_scheduler0.scheduler_thread);

	/* clear stale command objects if any */
	while (!list_empty(&pending_cmds)) {
		struct xocl_cmd *xcmd = list_first_entry(&pending_cmds,struct xocl_cmd,list);
		DRM_INFO("deleting stale pending cmd\n");
		list_del(&xcmd->list);
		drm_gem_object_unreference_unlocked(&xcmd->bo->base);
	}
	while (!list_empty(&global_scheduler0.command_queue)) {
		struct xocl_cmd *xcmd = list_first_entry(&global_scheduler0.command_queue,struct xocl_cmd,list);
		DRM_INFO("deleting stale scheduler cmd\n");
		list_del(&xcmd->list);
		drm_gem_object_unreference_unlocked(&xcmd->bo->base);
	}
	
	delete_cmd_list();

	return retval;
}


/**
 * mb_query() - Check command status of argument command
 *
 * @xcmd: Command to check
 *
 * This function is for ERT mode.  In polling mode, check the command status
 * register containing the slot assigned to the command.  In interrupt mode
 * check the interrupting status register.  The function checks all commands in
 * the same command status register as argument command so more than one
 * command may be marked complete by this function.
 */
static void
mb_query(struct xocl_cmd *xcmd)
{
	struct drm_xocl_dev *xdev = xcmd->xdev;
	unsigned int cmd_mask_idx = slot_mask_idx(xcmd->slot_idx);

	SCHED_DEBUGF("-> mb_query slot_idx=%d, cmd_mask_idx=%d\n",xcmd->slot_idx,cmd_mask_idx);

	if (xdev->exec.polling_mode
	    || (cmd_mask_idx==0 && atomic_read(&xdev->exec.sr0))
	    || (cmd_mask_idx==1 && atomic_read(&xdev->exec.sr1))
	    || (cmd_mask_idx==2 && atomic_read(&xdev->exec.sr2))
	    || (cmd_mask_idx==3 && atomic_read(&xdev->exec.sr3))) {
		u32 csr_addr = ERT_STATUS_REGISTER_ADDR + (cmd_mask_idx<<2);
		u32 mask = ioread32(xcmd->xdev->user_bar + csr_addr);
		if (mask)
			mark_mask_complete(xcmd->xdev,mask,cmd_mask_idx);
		SCHED_DEBUGF("++ mb_query csr_addr=0x%x mask=0x%x\n",csr_addr,mask);
	}
		    
	SCHED_DEBUGF("<- mb_query\n");
}

/**
 * penguin_query() - Check command status of argument command
 *
 * @xcmd: Command to check
 *
 * Function is called in penguin mode (no embedded scheduler).
 */
static void
penguin_query(struct xocl_cmd *xcmd)
{
	u32 opc = opcode(xcmd);

	SCHED_DEBUGF("-> penguin_queury() slot_idx=%d\n",xcmd->slot_idx);

	if (opc==ERT_CONFIGURE || (opc==ERT_START_CU && cu_done(xcmd->xdev,get_cu_idx(xcmd->xdev,xcmd->slot_idx))))
		mark_cmd_complete(xcmd);

	SCHED_DEBUG("<- penguin_queury\n");
}

/**
 * mb_submit() - Submit a command the embedded scheduler command queue
 *
 * @xcmd:  Command to submit
 * Return: %true if successfully submitted, %false otherwise
 */
static int
mb_submit(struct xocl_cmd *xcmd)
{
	u32 slot_addr;

	SCHED_DEBUG("-> mb_submit\n");

	xcmd->slot_idx = acquire_slot_idx(xcmd->xdev);
	if (xcmd->slot_idx<0) {
		SCHED_DEBUG("<- mb_submit returns 0\n");
		return 0;
	}

	slot_addr = ERT_CQ_BASE_ADDR + xcmd->slot_idx*slot_size(xcmd->xdev);
	SCHED_DEBUGF("++ mb_submit slot_idx=%d, slot_addr=0x%x\n",xcmd->slot_idx,slot_addr);

	/* write packet minus header */
	memcpy_toio(xcmd->xdev->user_bar + slot_addr + 4,xcmd->packet->data,(packet_size(xcmd)-1)*sizeof(u32));

	/* write header */
	iowrite32(xcmd->packet->header,xcmd->xdev->user_bar + slot_addr);

	/* trigger interrupt to embedded scheduler if feature is enabled */
	if (xcmd->xdev->exec.cq_interrupt) {
		u32 cq_int_addr = ERT_CQ_STATUS_REGISTER_ADDR + (slot_mask_idx(xcmd->slot_idx)<<2);
		u32 mask = 1<<slot_idx_in_mask(xcmd->slot_idx);
		SCHED_DEBUGF("++ mb_submit writes slot mask 0x%x to CQ_INT register at addr 0x%x\n",
			     mask,cq_int_addr);
		iowrite32(mask,xcmd->xdev->user_bar + cq_int_addr);
	}
	
	SCHED_DEBUG("<- mb_submit returns 1\n");
	return 1;
}

/**
 * get_free_cu() - get index of first available CU per command cu mask
 * 
 * @xcmd: command containing CUs to check for availability
 *
 * This function is called kernel software scheduler mode only, in embedded
 * scheduler mode, the hardware scheduler handles the commands directly.
 *
 * Return: Index of free CU, -1 of no CU is available.
 */
static int
get_free_cu(struct xocl_cmd *xcmd)
{
	int mask_idx=0;
	SCHED_DEBUG("-> get_free_cu\n");
	for (mask_idx=0; mask_idx<xcmd->xdev->exec.num_cu_masks; ++mask_idx) {
		u32 cmd_mask = xcmd->packet->data[mask_idx]; /* skip header */
		u32 busy_mask = xcmd->xdev->exec.cu_status[mask_idx];
		int cu_idx = ffs_or_neg_one((cmd_mask | busy_mask) ^ busy_mask);
		if (cu_idx>=0) {
			xcmd->xdev->exec.cu_status[mask_idx] ^= 1<<cu_idx;
			SCHED_DEBUGF("<- get_free_cu returns %d\n",cu_idx_from_mask(cu_idx,mask_idx));
			return cu_idx_from_mask(cu_idx,mask_idx);
		}
	}
	SCHED_DEBUG("<- get_free_cu returns -1\n");
	return -1;
}

/**
 * configure_cu() - transfer command register map to specified CU and start the CU.
 *
 * @xcmd: command with register map to transfer to CU
 * @cu_idx: index of CU to configure
 *
 * This function is called in kernel software scheduler mode only.
 */
static void
configure_cu(struct xocl_cmd *xcmd, int cu_idx)
{
	u32 i;
	void* user_bar = xcmd->xdev->user_bar;
	u32 cu_addr = cu_idx_to_addr(xcmd->xdev,cu_idx);
	u32 size = regmap_size(xcmd);
	struct ert_start_kernel_cmd *ecmd = (struct ert_start_kernel_cmd *)xcmd->packet;

	SCHED_DEBUGF("-> configure_cu cu_idx=%d, cu_addr=0x%x, regmap_size=%d\n"
		     ,cu_idx,cu_addr,size);

	/* write register map, but skip first word (AP_START) */
	/* can't get memcpy_toio to work */
	/* memcpy_toio(user_bar + cu_addr + 4,ecmd->data + ecmd->extra_cu_masks + 1,(size-1)*4); */
	for (i=1; i<size; ++i)
		iowrite32(*(ecmd->data + ecmd->extra_cu_masks + i),user_bar + cu_addr + (i<<2));

	/* start CU at base + 0x0 */
	iowrite32(0x1,user_bar + cu_addr);

	SCHED_DEBUG("<- configure_cu\n");
}

/**
 * penguin_submit() - penguin submit of a command
 *
 * @xcmd: command to submit
 *
 * Special processing for configure command.  Configuration itself is
 * done/called by queued_to_running before calling penguin_submit.  In penguin
 * mode configuration need to ensure that the command is retired properly by
 * scheduler, so assign it a slot index and let normal flow continue.
 *
 * Return: %true on successful submit, %false otherwise
 */
static int
penguin_submit(struct xocl_cmd *xcmd)
{
	SCHED_DEBUG("-> penguin_submit\n");

	/* configuration was done by submit_cmds, ensure the cmd retired properly */
	if (opcode(xcmd)==ERT_CONFIGURE) {
		xcmd->slot_idx = acquire_slot_idx(xcmd->xdev);
		SCHED_DEBUG("<- penguin_submit (configure)\n");
		return 1;
	}

	if (opcode(xcmd)!=ERT_START_CU)
		return 0;

	/* extract cu list */
	xcmd->cu_idx = get_free_cu(xcmd);
	if (xcmd->cu_idx<0)
		return 0;
	
	xcmd->slot_idx = acquire_slot_idx(xcmd->xdev);
	if (xcmd->slot_idx<0)
		return 0;

	/* found free cu, transfer regmap and start it */
	configure_cu(xcmd,xcmd->cu_idx);
	
	SCHED_DEBUGF("<- penguin_submit cu_idx=%d slot=%d\n",xcmd->cu_idx,xcmd->slot_idx);
	
	return 1;
}


/**
 * mb_ops: operations for ERT scheduling
 */
static struct xocl_sched_ops mb_ops = {
	.submit = mb_submit,
	.query = mb_query,
};

/**
 * penguin_ops: operations for kernel mode scheduling
 */
static struct xocl_sched_ops penguin_ops = {
	.submit = penguin_submit,
	.query = penguin_query,
};

/**
 * xocl_user_event() - Interrupt service routine for MB interrupts
 *
 * Called by xocl_xdma_user_isr() which is our stub for user ISR registered with libxdma
 * Kernel doc says eventfd_signal() does not sleep so it should be okay to call this in ISR
 * TODO: Add support for locking so xdev->user_msix_table[irq] is not deleted/changed by
 * xocl_user_intr_ioctl() while we are using it.
 */
int
xocl_user_event(int irq, struct drm_xocl_dev *xdev)
{
	SCHED_DEBUGF("xocl_user_event %d\n",irq);
	if (irq>=XOCL_CSR_INTR0 && irq<=XOCL_CSR_INTR3 && is_ert(xdev) && !xdev->exec.polling_mode) {

		if (irq==0)
			atomic_set(&xdev->exec.sr0,1);
		else if (irq==1)
			atomic_set(&xdev->exec.sr1,1);
		else if (irq==2)
			atomic_set(&xdev->exec.sr2,1);
		else if (irq==3)
			atomic_set(&xdev->exec.sr3,1);

		/* wake up all scheduler ... currently one only */
		atomic_set(&global_scheduler0.intc,1);
		wake_up_interruptible(&global_scheduler0.wait_queue);
		return 0;
	}
	if (!xdev->exec.user_msix_table[irq])
		return -EFAULT;
	if (eventfd_signal(xdev->exec.user_msix_table[irq], 1) == 1)
		return 0;
	return -EFAULT;
}


/**
 * xocl_execbuf_ioctl() - Entry point for exec buffer.
 *
 * @dev: Device node calling execbuf
 * @data: Payload
 * @filp: 
 *
 * Function adds exec buffer to the pending list of commands
 *
 * Return: 0 on success, -errno otherwise
 */
int
xocl_execbuf_ioctl(struct drm_device *dev,
		   void *data,
		   struct drm_file *filp)
{
	struct drm_gem_object *obj;
	struct drm_xocl_bo *xobj;
	struct drm_xocl_dev *xdev = dev->dev_private;
	struct drm_xocl_execbuf *args = data;
	int ret = 0;

	SCHED_DEBUG("-> xocl_execbuf_ioctl\n");
	obj = xocl_gem_object_lookup(dev, filp, args->exec_bo_handle);
	if (!obj) {
		DRM_INFO("Failed to look up GEM BO %d\n", args->exec_bo_handle);
		return -ENOENT;
	}

	xobj = to_xocl_bo(obj);
	if (!xocl_bo_execbuf(xobj)) {
		ret = -EINVAL;
		goto out;
	}

	/* Add the command to pending list */
	if (add_cmd(xdev,xobj)) {
		ret = -EINVAL;
		goto out;
	}

	/* we keep a bo reference which is released later when the bo is retired when task is done */
	SCHED_DEBUG("<- xocl_execbuf_ioctl\n");
	return ret;
out:
	drm_gem_object_unreference_unlocked(&xobj->base);
	return ret;
}

/**
 * xocl_init_exec() - Initialize the command execution for device
 *
 * @xdev: Device node to initialize
 *
 * Return: 0 on success, -errno otherwise
 */
int
xocl_init_exec(struct drm_xocl_dev *xdev)
{
	unsigned int i;

	mutex_init(&xdev->exec.user_msix_table_lock);
	spin_lock_init(&xdev->exec.ctx_list_lock);
	INIT_LIST_HEAD(&xdev->exec.ctx_list);
	init_waitqueue_head(&xdev->exec.poll_wait_queue);
	
	xdev->exec.scheduler = &global_scheduler0;

        for (i=0; i<XOCL_MAX_SLOTS; ++i)
		xdev->exec.submitted_cmds[i] = NULL;

	xdev->exec.num_slots = 16;
	xdev->exec.num_cus = 0;
	xdev->exec.cu_base_addr = 0;
	xdev->exec.cu_shift_offset = 0;
	xdev->exec.cq_interrupt = 0;
	xdev->exec.polling_mode = 1;

	for (i=0; i<XOCL_MAX_U32_SLOT_MASKS; ++i)
		xdev->exec.slot_status[i] = 0;
	xdev->exec.num_slot_masks = 1;

	for (i=0; i<XOCL_MAX_U32_CU_MASKS; ++i)
		xdev->exec.cu_status[i] = 0;
	xdev->exec.num_cu_masks = 0;

	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR0, true);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR1, true);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR2, true);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR3, true);
	xdev->exec.ops = &penguin_ops;

	atomic_set(&xdev->exec.sr0,0);
	atomic_set(&xdev->exec.sr1,0);
	atomic_set(&xdev->exec.sr2,0);
	atomic_set(&xdev->exec.sr3,0);
	
	init_scheduler_thread();
	return 0;
}

/**
 * xocl_fini_exec() - Finalize the command execution for device
 *
 * @xdev: Device node to finalize
 *
 * Return: 0 on success, -errno otherwise
 */
int xocl_fini_exec(struct drm_xocl_dev *xdev)
{
	int i;

	fini_scheduler_thread();

	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR0, false);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR1, false);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR2, false);
	xdma_user_interrupt_config(xdev, XOCL_CSR_INTR3, false);
	for (i=0; i<16; i++) {
		xdma_user_interrupt_config(xdev, i, false);
		if (xdev->exec.user_msix_table[i])
			eventfd_ctx_put(xdev->exec.user_msix_table[i]);
	}
	mutex_destroy(&xdev->exec.user_msix_table_lock);
		
	return 0;
}
