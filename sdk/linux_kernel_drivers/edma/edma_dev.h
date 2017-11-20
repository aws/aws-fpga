/*
 * Copyright 2015 Amazon.com, Inc. or its affiliates.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#ifndef EDMA_DEV_H
#define EDMA_DEV_H

#include <linux/u64_stats_sync.h>

int edma_dev_init(struct backend_device* backend_device);
int edma_dev_cleanup(struct backend_device* backend_device);

struct transient_buffer_page
{
	u8* virt_buffer;
	dma_addr_t phys_base_addr;
};

/* Transient buffer is used to store write and read
requests that come from the application to the backend
and vise-versa */
struct transient_buffer {
	u32 number_of_transactions;
	u32 head;
	u32 tail;
	struct transient_buffer_page* page_array;
}____cacheline_aligned;

struct request{
	u32 size;
	u32 offset;
	//TODO:add timestamp
	u8* virt_data;
	dma_addr_t phys_data;
}____cacheline_aligned;


struct edma_queue_stats {
	u64 write_requests;
	u64 read_requests;
	u64 read_submitted_bytes;
	u64 read_completed_bytes;
	u64 write_submitted_bytes;
	u64 write_completed_bytes;
	u64 fsync_count;
	u64 no_space_left_error;
	u64 dma_submit_error;
	u64 fsync_busy_count;
	u64 read_timeouts_error;
	u64 opened_times;
	struct u64_stats_sync syncp;
}____cacheline_aligned;


struct edma_event_stats {
	u64 opened_times;
	struct u64_stats_sync syncp;
}____cacheline_aligned;

/* EBCS is the structure used to manage the transient buffer */
struct edma_buffer_control_structure{

	struct transient_buffer transient_buffer;
	struct request* request;
	struct mutex ebcs_mutex;
	u32 next_to_use;
	u32 next_to_clean;
	u32 ebcs_depth;
	void *dma_queue_handle;
	u64* completed_buffer;
	u32 completed_size;
}____cacheline_aligned;


struct edma_queue_private_data
{
	struct edma_buffer_control_structure read_ebcs;
	struct edma_buffer_control_structure write_ebcs;
	struct edma_queue_stats stats;
	struct mutex edma_mutex;
	unsigned long state;
	struct edma_device *dma_device;
} ____cacheline_aligned;

struct edma_event_private_data
{
	wait_queue_head_t event_wq;
	struct edma_event_stats stats;
	bool event_happend;
	spinlock_t event_lock;
}____cacheline_aligned;


#endif
