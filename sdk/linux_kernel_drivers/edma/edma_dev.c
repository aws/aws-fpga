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
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/fs.h>
#include <linux/uaccess.h>
#include <linux/semaphore.h>
#include <linux/cdev.h>
#include <linux/spinlock.h>
#include <linux/mutex.h>
#include <linux/vmalloc.h>
#include <linux/delay.h>
#include <linux/dma-mapping.h>
#include <linux/sched.h>
#include <linux/poll.h>
#include <linux/slab.h>
#include <linux/pci.h>
#include "edma.h"
#include "edma_dev.h"
#include "edma_backend.h"

#define QUEUE_DEVICE_NAME "edma"
#define EVENT_DEVICE_NAME "fpga"
#define SLEEP_MINIMUM_USEC 		(1 * 100)
#define SLEEP_MAXIMUM_USEC 		(4 * 100)
#define RELEASE_SLEEP_MSEC 		(5)
#define RELEASE_TIMEOUT_MSEC 		(((fsync_timeout_sec) + 1) * 1000)
#define NUM_POLLS_PER_SCHED		(100)
#define CEIL(a, b)	(((a) + (b-1)) / (b))

extern struct class* edma_class;

//This is a bi-directional DMA queue
struct edma_char_queue_device{
	dev_t dev_no;
	struct cdev cdev;
	struct pci_dev *pdev;
	struct edma_queue_private_data *device_private_data;
	u32 major;
	u32 fpga_number;
};

struct edma_char_event_device{
	dev_t dev_no;
	struct cdev cdev;
	struct pci_dev *pdev;
	u32 major;
	struct edma_event_private_data* events_private_data;
};


static unsigned int transient_buffer_size = 32 * 1024 * 1024;
module_param(transient_buffer_size, uint, 0);
MODULE_PARM_DESC(transient_buffer_size, "Transient buffer size. (default=32MB)");

static unsigned int single_transaction_size = 8 * PAGE_SIZE;
module_param(single_transaction_size, uint, 0);
MODULE_PARM_DESC(single_transaction_size, "The size of a single transaction over the DMA. (default=32KB)");

unsigned int edma_queue_depth = 1024;
module_param(edma_queue_depth, uint, 0);
MODULE_PARM_DESC(edma_queue_depth, "EDMA queue depth. (default=1024)");

static unsigned int fsync_timeout_sec = 9;
module_param(fsync_timeout_sec, uint, 0);
MODULE_PARM_DESC(fsync_timeout_sec, "fsync timeout sec. (default=9)");

//TODO: add a callback for the backend to notify fatal error - reset

static DECLARE_BITMAP(edma_fpga_alloc_bitmap, MAX_NUMBER_OF_EDMA_DEVICE);
static DEFINE_SPINLOCK(edma_fpga_alloc_lock);

static inline bool is_releasing(void* state)
{
	if(unlikely(test_bit(EDMA_STATE_QUEUE_RELEASING_BIT, state))) {
		//Wait and if fsync still running - return
		edma_dbg("Releasing\n");
			return true;
	}

	return false;
}


static inline int wait_is_fsync_running(struct edma_queue_private_data* private_data, struct mutex* mutex)
{
	if(unlikely(test_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT, &private_data->state))) {
		//Wait and if fsync still running - return
		edma_dbg("FSync is running\n");

		u64_stats_update_begin(&private_data->stats.syncp);
		private_data->stats.fsync_busy_count++;
		u64_stats_update_end(&private_data->stats.syncp);

		mutex_unlock(mutex);
		usleep_range(SLEEP_MINIMUM_USEC, SLEEP_MAXIMUM_USEC);
		mutex_lock(mutex);

		if(unlikely(test_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT, &private_data->state)))
			return -EBUSY;
	}

	return 0;

}

/*
 * This function will only be called after we make sure that read,write and fsync
 * are are no longer working with the queue we are releasing
 */
static void edma_dev_release_resources( struct edma_buffer_control_structure* ebcs)
{
	int i;

	BUG_ON(!ebcs);

	if(ebcs->request) {
		vfree(ebcs->request);
		ebcs->request = NULL;
	}

	for(i = 0; i < (ebcs->transient_buffer.number_of_transactions); i++){
		if(ebcs->transient_buffer.page_array[i].phys_base_addr != 0) {
			dma_free_coherent(NULL, single_transaction_size,
					ebcs->transient_buffer.page_array[i].virt_buffer,
					ebcs->transient_buffer.page_array[i].phys_base_addr);

			ebcs->transient_buffer.page_array[i].virt_buffer = NULL;
			ebcs->transient_buffer.page_array[i].phys_base_addr = 0;
		}
	}

	if(ebcs->transient_buffer.page_array) {
		vfree(ebcs->transient_buffer.page_array);
		ebcs->transient_buffer.page_array = NULL;
	}
}

static void edma_dev_initialize_read_ebcs(struct edma_buffer_control_structure* ebcs)
{
	int i;

	//if we have not enough memory for the read ebcs
	BUG_ON((ebcs->transient_buffer.number_of_transactions < ebcs->ebcs_depth));

	for(i = 0; i < ebcs->ebcs_depth; i++)
	{
		ebcs->request[i].phys_data = ebcs->transient_buffer.page_array[i].phys_base_addr;
		ebcs->request[i].virt_data = (u8 *)(ebcs->transient_buffer.page_array[i].virt_buffer);
		ebcs->request[i].size = single_transaction_size;
		ebcs->request[i].offset = 0;

#ifndef SUPPORT_M2M
		//last one - don't submit
		if(unlikely(i == ebcs->ebcs_depth - 1))
			break;

		edma_backend_submit_s2m_request((u64*)(ebcs->request[i].phys_data), ebcs->request[i].size, ebcs->dma_queue_handle, 0);
#endif //SUPPORT_M2M
	}

#ifndef SUPPORT_M2M
	ebcs->next_to_use = ebcs->ebcs_depth - 1;
#endif
}

static inline int edma_dev_allocate_resources( struct edma_buffer_control_structure* ebcs)
{
	int ret = 0;
	int i;
	u32 transient_buffer_rounded_to_transaction_size = 0;

	BUG_ON(!ebcs);

	//round transient_buffer_size to be a multiplication product of page_size
	transient_buffer_rounded_to_transaction_size =  CEIL(transient_buffer_size, single_transaction_size);

	//allocate the page_array
	ebcs->transient_buffer.page_array = vzalloc(sizeof(struct transient_buffer_page) * transient_buffer_rounded_to_transaction_size );
	if(unlikely(!ebcs->transient_buffer.page_array)) {
		ret = -ENOMEM;
		goto edma_dev_allocate_resources_done;
	}

	for(i = 0; i < transient_buffer_rounded_to_transaction_size; i++)
	{
		ebcs->transient_buffer.page_array[i].virt_buffer = dma_alloc_coherent(
				NULL,
				single_transaction_size, &(ebcs->transient_buffer.page_array[i].phys_base_addr),
				GFP_KERNEL | __GFP_ZERO);

		if(unlikely(!(ebcs->transient_buffer.page_array[i].virt_buffer))) {
					ret = -ENOMEM;
					goto edma_dev_allocate_resources_dma_fail;
		}
	}

	ebcs->ebcs_depth = edma_queue_depth;
	ebcs->request =
			(struct request*) vzalloc(
					sizeof(struct request)
					* ebcs->ebcs_depth);
	if(unlikely(!ebcs->request)) {
		ret = -ENOMEM;
		goto edma_dev_allocate_resources_dma_fail;
	}

	ebcs->transient_buffer.number_of_transactions = transient_buffer_rounded_to_transaction_size;
	ebcs->transient_buffer.head = 0;
	ebcs->transient_buffer.tail = 0;
	ebcs->next_to_clean = 0;
	ebcs->next_to_use = 0;
	ebcs->completed_buffer = NULL;
	ebcs->completed_size = 0;

	mutex_init(&ebcs->ebcs_mutex);

	goto edma_dev_allocate_resources_done;

edma_dev_allocate_resources_dma_fail:
	for(i = 0; i < transient_buffer_rounded_to_transaction_size; i++)
	{
		dma_free_coherent(NULL, single_transaction_size,
				ebcs->transient_buffer.page_array[i].virt_buffer,
				ebcs->transient_buffer.page_array[i].phys_base_addr);
		ebcs->transient_buffer.page_array[i].virt_buffer = NULL;
		ebcs->transient_buffer.page_array[i].phys_base_addr = 0;
	}


	vfree(ebcs->transient_buffer.page_array);
	ebcs->transient_buffer.page_array = NULL;

edma_dev_allocate_resources_done:
	return ret;
}


static inline void recycle_completed_descriptors(struct edma_buffer_control_structure* write_ebcs,
		struct edma_queue_private_data *private_data)
{
	u64* buffer_to_clean = NULL;
	u32 buffer_size = 0;

	edma_backend_get_completed_m2s_request(&buffer_to_clean, &buffer_size, write_ebcs->dma_queue_handle);

	while(buffer_to_clean != NULL) //as long as we have something to clean
	{
		struct request* request_to_clean =
				write_ebcs->request
						+ write_ebcs->next_to_clean;

		u64_stats_update_begin(&private_data->stats.syncp);
		private_data->stats.write_completed_bytes += buffer_size;
		u64_stats_update_end(&private_data->stats.syncp);

		BUG_ON(request_to_clean->phys_data
				!= (uintptr_t)buffer_to_clean ); //next to clean is not the next one completed.

		write_ebcs->transient_buffer.tail =
				EDMA_RING_IDX_NEXT(write_ebcs->transient_buffer.tail,
						write_ebcs->transient_buffer.number_of_transactions);

		request_to_clean->phys_data = 0;
		request_to_clean->virt_data = NULL;
		request_to_clean->offset = 0;
		request_to_clean->size = 0;

		//read the data from the buffer, clean the request.
		write_ebcs->next_to_clean =
				EDMA_RING_IDX_NEXT(
						write_ebcs->next_to_clean,
						write_ebcs->ebcs_depth);

		edma_backend_get_completed_m2s_request(&buffer_to_clean, &buffer_size, write_ebcs->dma_queue_handle);
	}

}


static int edma_dev_open(struct inode *inode, struct file *filp)
{

	int ret = 0;
	struct edma_char_queue_device* edma_char;
	struct edma_queue_private_data *device_private_data;

	edma_dbg("\n-->%s Opening %s\n", __func__, filp->f_path.dentry->d_name.name);

	edma_char = container_of(inode->i_cdev, struct edma_char_queue_device, cdev);
	device_private_data = &(edma_char->device_private_data[MINOR(inode->i_rdev)]);

	mutex_lock(&device_private_data->edma_mutex);
	filp->private_data = device_private_data;

	if(device_private_data->stats.opened_times == 0) {

		device_private_data->state = EDMA_STATE_RUNNING;

		ret = edma_dev_allocate_resources(&device_private_data->read_ebcs);
		if(unlikely(ret))
			goto edma_open_done;

		edma_dev_initialize_read_ebcs(&device_private_data->read_ebcs);
		ret = edma_dev_allocate_resources(&(device_private_data->write_ebcs));

		if(unlikely(ret))
		{
			edma_dev_release_resources(&device_private_data->read_ebcs);
			goto edma_open_done;
		}

		edma_backend_start(device_private_data->write_ebcs.dma_queue_handle, MINOR(inode->i_rdev));
		u64_stats_init(&device_private_data->stats.syncp);
	}

	u64_stats_update_begin(&device_private_data->stats.syncp);
	device_private_data->stats.opened_times++;
	u64_stats_update_end(&device_private_data->stats.syncp);

edma_open_done:
	mutex_unlock(&device_private_data->edma_mutex);

	edma_dbg("\n-->%s Done\n", __func__);

	return ret;
}


static int edma_dev_release(struct inode *inode, struct file *file)
{
	int ret = 0;
	int timeout = 0;
	struct edma_char_queue_device* edma_char;
	struct edma_queue_private_data *device_private_data;

	edma_dbg("\n--> %s\n", __func__);

	edma_char = container_of(inode->i_cdev, struct edma_char_queue_device, cdev);

	device_private_data = &(edma_char->device_private_data[MINOR(inode->i_rdev)]);

	BUG_ON(!file->private_data);

	mutex_lock(&device_private_data->edma_mutex);

	BUG_ON(device_private_data->stats.opened_times < 1);

	u64_stats_update_begin(&device_private_data->stats.syncp);
	device_private_data->stats.opened_times--;
	u64_stats_update_end(&device_private_data->stats.syncp);

	if (device_private_data->stats.opened_times == 0){

		/* Get both read and write lock and update status to releasing.
		* This makes sure that outstanding read/write transactions will finish and
		* new will not start. Only open() will unset the RELEASING state. */
		mutex_lock(&device_private_data->write_ebcs.ebcs_mutex);
		mutex_lock(&device_private_data->read_ebcs.ebcs_mutex);

		// !!! Super important that for every lock of ebcs (read and write) check for releasing status !!!

		set_bit(EDMA_STATE_QUEUE_RELEASING_BIT, &device_private_data->state);

		// Now that we signaled to the other threads that we want to release
		// we can unlock the locks
		// the code in the read/write/fsync function should always check the 
		// EDMA_STATE_QUEUE_RELEASING_BIT often to stop quickly
		mutex_unlock(&device_private_data->read_ebcs.ebcs_mutex);
		mutex_unlock(&device_private_data->write_ebcs.ebcs_mutex);

		while (test_bit(EDMA_STATE_READ_IN_PROGRESS_BIT,
				&device_private_data->state)
				|| test_bit(EDMA_STATE_WRITE_IN_PROGRESS_BIT,
						&device_private_data->state)
				|| test_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT,
						&device_private_data->state)) {
			msleep(RELEASE_SLEEP_MSEC);
			if (timeout > RELEASE_TIMEOUT_MSEC) {
				pr_err("%s: DMA still in-progress, timeout=%u\n", 
						__func__, timeout);
				break;
			}
			timeout += RELEASE_SLEEP_MSEC;
		}

		// if still running - panic
		BUG_ON( test_bit(EDMA_STATE_READ_IN_PROGRESS_BIT,
				&device_private_data->state)
				|| test_bit(EDMA_STATE_WRITE_IN_PROGRESS_BIT,
						&device_private_data->state)
				|| test_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT,
						&device_private_data->state));

		// Once we reach this point, we know that we can release
		edma_backend_stop(device_private_data->write_ebcs.dma_queue_handle);

		edma_dev_release_resources(&device_private_data->write_ebcs);
		edma_dev_release_resources(&device_private_data->read_ebcs);

		file->private_data = NULL;
	}

	mutex_unlock(&device_private_data->edma_mutex);

	edma_dbg("\n-->%s Done\n", __func__);

	return ret;
}


//TODO: reminder -the interrupt routing/write/read should have the following in-order code:
// set_bit (INT_RUNNING/READ/WRITE)
static ssize_t edma_dev_read(struct file *filp, char *buffer, size_t len,
		loff_t * off)
{
	int ret = 0;
	size_t data_copied_from_current_transaction = 0;
	size_t total_data_copied = 0;
	struct edma_buffer_control_structure* read_ebcs = NULL;
	struct request* request_to_clean = NULL;
	struct request* request_to_submit = NULL;
	size_t copy_size;
	struct edma_queue_private_data* private_data = filp->private_data;

	BUG_ON(!private_data);

	edma_dbg("\n-->%s Reading %zu bytes from %s in offset 0x%llx\n", __func__, len, filp->f_path.dentry->d_name.name, *off);

	read_ebcs = &private_data->read_ebcs;
	mutex_lock(&read_ebcs->ebcs_mutex);

	u64_stats_update_begin(&private_data->stats.syncp);
	private_data->stats.read_requests++;
	u64_stats_update_end(&private_data->stats.syncp);

	if(unlikely(is_releasing(&private_data->state)))
		goto edma_dev_read_done;

	if(unlikely(len == 0))
		goto edma_dev_read_done;

	set_bit(EDMA_STATE_READ_IN_PROGRESS_BIT,&private_data->state);

	request_to_clean = read_ebcs->request + read_ebcs->next_to_clean;
	request_to_submit = read_ebcs->request + read_ebcs->next_to_use;

	copy_size = min_t(size_t, request_to_clean->size, len);

	if(likely(read_ebcs->completed_buffer == NULL))
	{
#ifdef SUPPORT_M2M
		//for m2m before completing a descriptor we need to submit one
		ret = edma_backend_submit_s2m_request(
				(u64*)request_to_clean->phys_data, copy_size,
				read_ebcs->dma_queue_handle, *off);

		if (ret < 0) {
			if (ret == -EIO) {
				u64_stats_update_begin(&private_data->stats.syncp);
				private_data->stats.read_timeouts_error++;
				u64_stats_update_end(&private_data->stats.syncp);
			}

			pr_err("%s: read failed (%d)\n", __func__, ret);
			goto edma_dev_read_done;
		}

		u64_stats_update_begin(&private_data->stats.syncp);
		private_data->stats.read_submitted_bytes += copy_size;
		u64_stats_update_end(&private_data->stats.syncp);

#endif

		ret = edma_backend_get_completed_s2m_request(&read_ebcs->completed_buffer,
				&read_ebcs->completed_size, read_ebcs->dma_queue_handle);

		if(ret){
			edma_dbg("EDMA: Failed to send %d characters to the user\n", ret);
		}

		u64_stats_update_begin(&private_data->stats.syncp);
		private_data->stats.read_completed_bytes += read_ebcs->completed_size;
		u64_stats_update_end(&private_data->stats.syncp);

	}
	else
		copy_size = min_t(size_t, (read_ebcs->completed_size - request_to_clean->offset), len);

	while(read_ebcs->completed_buffer != NULL && total_data_copied < len){
		BUG_ON(unlikely(request_to_clean->phys_data != (uintptr_t)read_ebcs->completed_buffer)); //next to clean is not the next one completed.

		ret = copy_to_user(buffer + total_data_copied,
				request_to_clean->virt_data
						+ request_to_clean->offset,
				copy_size);

		if(unlikely(ret)){
			//if copy to user failed - we try again once and change the offset and break without further cleaning
			//ret is the number of bytes that were not copied.
			ret = copy_to_user(buffer + (copy_size - ret),
					request_to_clean->virt_data + (copy_size - ret), ret);

			if(ret){
				edma_dbg("EDMA: Failed to send %d characters to the user\n", ret);
				request_to_clean->offset = ret;
				data_copied_from_current_transaction += (copy_size - request_to_clean->offset) - ret;
				total_data_copied += data_copied_from_current_transaction;
				break;
			}
		}

		data_copied_from_current_transaction += copy_size - ret;
		total_data_copied += data_copied_from_current_transaction;

		*off = *off + data_copied_from_current_transaction;

		//Make sure that user reads the entire buffer, otherwise - don't clean it.
		if(data_copied_from_current_transaction + request_to_clean->offset < read_ebcs->completed_size) {
			request_to_clean->offset += data_copied_from_current_transaction;
			copy_size = min_t(size_t, (read_ebcs->completed_size - request_to_clean->offset), len - total_data_copied);
		} else {
			read_ebcs->completed_buffer = NULL;
			read_ebcs->completed_size = 0;
			data_copied_from_current_transaction = 0;

			//read the data from the buffer, clean the request.
			read_ebcs->next_to_clean = EDMA_RING_IDX_NEXT(
					read_ebcs->next_to_clean,
					read_ebcs->ebcs_depth);

			request_to_clean = read_ebcs->request + read_ebcs->next_to_clean;

#ifdef SUPPORT_M2M
			if(total_data_copied < len) {
				copy_size = min_t(size_t, len - total_data_copied, single_transaction_size);
				ret = edma_backend_submit_s2m_request(
						(u64*)request_to_clean->phys_data,
						copy_size, read_ebcs->dma_queue_handle, *off);

				if (ret) {
					u64_stats_update_begin(&private_data->stats.syncp);
					private_data->stats.read_timeouts_error++;
					u64_stats_update_end(&private_data->stats.syncp);

					pr_err("%s: read failed (%d)\n", __func__, ret);
					goto edma_dev_read_done;
				}

				edma_backend_get_completed_s2m_request(
						&read_ebcs->completed_buffer,
						&read_ebcs->completed_size,
						read_ebcs->dma_queue_handle);

				u64_stats_update_begin(&private_data->stats.syncp);
				private_data->stats.read_completed_bytes += read_ebcs->completed_size;
				u64_stats_update_end(&private_data->stats.syncp);


			}
#else
			//submit new RX descriptor to the backend
			ret = edma_backend_submit_s2m_request(
					(u64*)request_to_submit->phys_data,
					request_to_submit->size, read_ebcs->dma_queue_handle, *off);

			u64_stats_update_begin(&private_data->stats.syncp);
			private_data->stats.read_submitted_bytes += request_to_submit->size;
			u64_stats_update_end(&private_data->stats.syncp);

			if (ret)
				goto edma_dev_read_done;


			//after submitting the request use the next one
			read_ebcs->next_to_use = EDMA_RING_IDX_NEXT(
					read_ebcs->next_to_use,
					read_ebcs->ebcs_depth);

			request_to_submit = read_ebcs->request + read_ebcs->next_to_use;

			//only in case we didn't complete what user wanted to read - we need to complete another descriptor
			if(total_data_copied < len) {
				data_copied_from_current_transaction = 0;
				edma_backend_get_completed_s2m_request(
						&read_ebcs->completed_buffer,
						&read_ebcs->completed_size,
						read_ebcs->dma_queue_handle);
			}

			u64_stats_update_begin(&private_data->stats.syncp);
			private_data->stats.read_completed_bytes += read_ebcs->completed_size;
			u64_stats_update_end(&private_data->stats.syncp);

#endif

		}
	}

	//There is a possibility that data_left_to_read is not 0 and that's OK.
	//1. data isn't ready - user should issue read again
	//2. user asked to read more that the size of a transaction

edma_dev_read_done:
	clear_bit(EDMA_STATE_READ_IN_PROGRESS_BIT,&private_data->state);
	mutex_unlock(&read_ebcs->ebcs_mutex);

	edma_dbg("\n-->%s Done\n", __func__);

	return ret == 0 ? total_data_copied : ret ;
}


static ssize_t edma_dev_write(struct file *filp, const char *buff, size_t len,
		loff_t * off)
{
	int ret = 0;
	struct edma_buffer_control_structure* write_ebcs;
	struct request* request;
	size_t data_copied = 0;
	size_t data_to_copy = len;
	int number_of_transactions = CEIL(len,single_transaction_size);
	struct edma_queue_private_data* private_data = (struct edma_queue_private_data*)filp->private_data;
	int i;

	BUG_ON(!private_data);

	edma_dbg("\n--> %s Writing %zu bytes to %s in offset 0x%llx\n", __func__, len, filp->f_path.dentry->d_name.name, *off);

	write_ebcs = &private_data->write_ebcs;
	mutex_lock(&write_ebcs->ebcs_mutex);

	if(is_releasing(&((struct edma_queue_private_data*)filp->private_data)->state))
		goto edma_dev_write_done;

	if(unlikely(len == 0))
		goto edma_dev_write_done;

	set_bit(EDMA_STATE_WRITE_IN_PROGRESS_BIT, &private_data->state);

	ret = wait_is_fsync_running(private_data, &write_ebcs->ebcs_mutex);
	if(unlikely(ret))
		goto edma_dev_write_done;

	u64_stats_update_begin(&private_data->stats.syncp);
	private_data->stats.write_requests++;
	u64_stats_update_end(&private_data->stats.syncp);

	//request for each page
	for (i = 0; i < number_of_transactions; i++)
	{
		size_t copy_to_rquest_size = min_t(size_t, data_to_copy, single_transaction_size);

		//no requests available.
		if(EDMA_RING_IDX_NEXT(write_ebcs->next_to_use,write_ebcs->ebcs_depth)
					== write_ebcs->next_to_clean) {
			u64_stats_update_begin(&private_data->stats.syncp);
			private_data->stats.no_space_left_error++;
			u64_stats_update_end(&private_data->stats.syncp);

			//wait for write to be processed
			mutex_unlock(&write_ebcs->ebcs_mutex);
			usleep_range(SLEEP_MINIMUM_USEC, SLEEP_MAXIMUM_USEC);
			mutex_lock(&write_ebcs->ebcs_mutex);

			//if releasing no need to wait
			if(unlikely(is_releasing(&private_data->state)))
				goto edma_dev_write_done;

			if(EDMA_RING_IDX_NEXT(write_ebcs->next_to_use,
					write_ebcs->ebcs_depth)
					== write_ebcs->next_to_clean) {
				//if we have no requests left - try to recycle completed descriptors
				recycle_completed_descriptors(write_ebcs, private_data);

				//if still no requests left - we are done.
				if(EDMA_RING_IDX_NEXT(write_ebcs->next_to_use,
						write_ebcs->ebcs_depth)
						== write_ebcs->next_to_clean) {
					break;
				}

			}
		}

		request = write_ebcs->request + write_ebcs->next_to_use;
		request->phys_data = write_ebcs->transient_buffer.page_array[write_ebcs->transient_buffer.head].phys_base_addr;
		request->virt_data = (u8*)(write_ebcs->transient_buffer.page_array[write_ebcs->transient_buffer.head].virt_buffer);
		request->size = single_transaction_size;

		ret = copy_from_user(request->virt_data, buff + data_copied, copy_to_rquest_size);
		if(unlikely(ret)){
			edma_dbg("EDMA: Failed to copy %d characters from the user\n", ret);
			ret = copy_from_user(
					request->virt_data + copy_to_rquest_size - ret,
					buff + data_copied + copy_to_rquest_size - ret, ret);
			if(unlikely(ret)){
				ret= -EINVAL;
				goto edma_dev_write_done;
			}
		}

		if(edma_backend_submit_m2s_request((u64*)request->phys_data, copy_to_rquest_size, write_ebcs->dma_queue_handle, *off)) {
			u64_stats_update_begin(&private_data->stats.syncp);
			private_data->stats.dma_submit_error++;
			u64_stats_update_end(&private_data->stats.syncp);

			mutex_unlock(&write_ebcs->ebcs_mutex);
			usleep_range(SLEEP_MINIMUM_USEC, SLEEP_MAXIMUM_USEC);
			mutex_lock(&write_ebcs->ebcs_mutex);

			//if releasing no need to wait
			if(unlikely(is_releasing(&private_data->state)))
				goto edma_dev_write_done;

			//if now fsync is running we should wait...
			ret = wait_is_fsync_running(private_data, &write_ebcs->ebcs_mutex);
			if(unlikely(ret))
				goto edma_dev_write_done;
			if(edma_backend_submit_m2s_request((u64*)request->phys_data, copy_to_rquest_size, write_ebcs->dma_queue_handle, *off)) {
				ret = -ENOMEM;
				goto edma_dev_write_done;
			}
		}

		data_copied += copy_to_rquest_size;
		data_to_copy -= copy_to_rquest_size;

		*off =  *off + copy_to_rquest_size;

		u64_stats_update_begin(&private_data->stats.syncp);
		private_data->stats.write_submitted_bytes += data_copied;
		u64_stats_update_end(&private_data->stats.syncp);

		//move the next_to_use by one since we used it
		write_ebcs->next_to_use = EDMA_RING_IDX_NEXT(
				write_ebcs->next_to_use, write_ebcs->ebcs_depth);

		//move head pointer now that we used the head
		write_ebcs->transient_buffer.head = EDMA_RING_IDX_NEXT(
				write_ebcs->transient_buffer.head, write_ebcs->transient_buffer.number_of_transactions);
	}

	edma_backend_m2s_dma_action(write_ebcs->dma_queue_handle);

	recycle_completed_descriptors(write_ebcs, private_data);

edma_dev_write_done:

	clear_bit(EDMA_STATE_WRITE_IN_PROGRESS_BIT, &private_data->state);

	mutex_unlock(&write_ebcs->ebcs_mutex);

	edma_dbg("\n--> %s done. RetVal is %zd\n", __func__, (data_copied == 0 ? ret : data_copied));

	return (data_copied == 0 ? ret : data_copied);
}

#ifdef SUPPORT_M2M
static loff_t edma_dev_llseek(struct file *filp, loff_t offset, int whence)
{
	loff_t pos = 0;

	//Seek is non blocking because for pread() and pwrite() are synced on the file-system level

	switch(whence) {
	case SEEK_SET:
		pos = offset;
		break;
	case SEEK_CUR:
		pos = filp->f_pos + offset;
		break;
	case SEEK_END:
		pos = UINT_MAX + offset;
		break;
	default:
		return -EINVAL;
	}

	if(pos < 0)
		return -EINVAL;


	filp->f_pos = pos;

	return pos;
}
#endif

static int edma_dev_fsync(struct file *filp, loff_t start, loff_t end, int datasync)
{
	int ret = 0;
	bool ebcs_is_clean = false;
	struct edma_buffer_control_structure* write_ebcs;
	struct edma_queue_private_data* private_data = (struct edma_queue_private_data*)filp->private_data;
	u32 sched_limit = 1;
	unsigned long timeout;

	(void)start;
	(void)end;
	(void)datasync;

	BUG_ON(!filp->private_data);

	u64_stats_update_begin(&private_data->stats.syncp);
	private_data->stats.fsync_count++;
	u64_stats_update_end(&private_data->stats.syncp);

	edma_dbg("\n--> %s Fsyncing %s \n", __func__, filp->f_path.dentry->d_name.name);

	write_ebcs = &private_data->write_ebcs;
	mutex_lock(&write_ebcs->ebcs_mutex);

	if(unlikely(is_releasing(&private_data->state)))
		goto edma_dev_fsync_done;

	set_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT, &private_data->state);

        timeout = jiffies + (fsync_timeout_sec * HZ);

	while(!ebcs_is_clean)
	{
		recycle_completed_descriptors(write_ebcs, private_data);

		if(write_ebcs->next_to_clean
				== write_ebcs->next_to_use)
			ebcs_is_clean = true;
		else {
			if (time_after(jiffies, timeout)) {
				pr_err("%s: timeout occurred, fsync_timeout_sec=%u\n", 
					__func__, fsync_timeout_sec);
				ret = -EIO;
				goto edma_dev_fsync_done;
			}

			mutex_unlock(&write_ebcs->ebcs_mutex);

			if ((sched_limit % NUM_POLLS_PER_SCHED) == 0) {
				schedule();
			}
			sched_limit++;

			mutex_lock(&write_ebcs->ebcs_mutex);

			if(unlikely(is_releasing(&private_data->state)))
				goto edma_dev_fsync_done;
		}
	}

edma_dev_fsync_done:
	clear_bit(EDMA_STATE_FSYNC_IN_PROGRESS_BIT, &private_data->state);

	mutex_unlock(&write_ebcs->ebcs_mutex);

	edma_dbg("\n--> %s done.\n", __func__);

	return ret;
}

static struct file_operations queue_fops = {
		.read = edma_dev_read,
		.write = edma_dev_write,
		.open = edma_dev_open,
		.release = edma_dev_release,
		.fsync = edma_dev_fsync,
#ifdef SUPPORT_M2M
		.llseek = edma_dev_llseek,
#endif
		.owner = THIS_MODULE
};

irqreturn_t edma_dev_irq_handler(int irq, void *dev)
{

	struct edma_event_private_data* events_private_data = (struct edma_event_private_data*)dev;
	unsigned long flags;

	BUG_ON(!events_private_data);

	edma_dbg("\n--> %s IRQ number is %d \n", __func__, irq);

	spin_lock_irqsave(&(events_private_data[irq].event_lock), flags);
	events_private_data[irq].event_happend = true;
	wake_up_interruptible(&(events_private_data[irq].event_wq));
	spin_unlock_irqrestore(&(events_private_data[irq].event_lock), flags);

	edma_dbg("\n--> %s done.\n", __func__);

	return IRQ_HANDLED;

}

static unsigned int edma_dev_event_poll(struct file *file, poll_table *wait)
{
	struct edma_char_event_device* edma_event = (struct edma_char_event_device*)file->private_data;
	unsigned long flags;
	unsigned int mask = 0;
	u32 minor = MINOR(file->f_inode->i_rdev);
	u32 event_number = minor;

	BUG_ON(!edma_event);

	edma_dbg("\n--> %s\n", __func__);

	poll_wait(file, &(edma_event->events_private_data[event_number].event_wq),  wait);

	spin_lock_irqsave(&(edma_event->events_private_data[event_number].event_lock), flags);


       if (edma_event->events_private_data[event_number].event_happend){
               mask = POLLIN;
               edma_event->events_private_data[event_number].event_happend = false;
       }

	spin_unlock_irqrestore(&(edma_event->events_private_data[event_number].event_lock), flags);

	edma_dbg("\n--> %s done.\n", __func__);

	return mask;
}


static int edma_dev_event_open(struct inode *inode, struct file *file)
{

	int ret = 0;
	struct edma_char_event_device* edma_event = NULL;
	u32 minor = MINOR(inode->i_rdev);
	u32 event_number = minor;

	edma_event = container_of(inode->i_cdev, struct edma_char_event_device, cdev);
	BUG_ON(!edma_event);

	edma_dbg("\n--> %s\n", __func__);

	file->private_data = edma_event;
	edma_event->events_private_data[event_number].stats.opened_times++;

	//better to enable extra time than to branch
	ret = edma_backend_enable_isr(edma_event->pdev, event_number);

	edma_dbg("\n--> %s done.\n", __func__);

	return ret;

}

static int edma_dev_event_release(struct inode *inode, struct file *file)
{
	struct edma_char_event_device* edma_event = (struct edma_char_event_device*)file->private_data;
	u32 minor = MINOR(inode->i_rdev);
	u32 event_number = minor;
	int ret = 0;

	BUG_ON(!edma_event);

	edma_dbg("\n--> %s\n", __func__);

	edma_event->events_private_data[event_number].stats.opened_times--;
	if(!edma_event->events_private_data[event_number].stats.opened_times)
		ret = edma_backend_disable_isr(edma_event->pdev, event_number);

	edma_dbg("\n--> %s done.\n", __func__);

	return ret;
}


static struct file_operations events_fops = {
		.open = edma_dev_event_open,
		.poll = edma_dev_event_poll,
		.release = edma_dev_event_release,
		.owner = THIS_MODULE
};


static ssize_t print_queue_stats(struct device* dev, struct device_attribute* attr,
                      char *buf)
{
	struct edma_queue_private_data *device_private_data;
	int char_count;

	device_private_data = (struct edma_queue_private_data *)dev_get_drvdata(dev);

	if(!device_private_data)
		char_count = scnprintf(buf, PAGE_SIZE, 
			"No Statistics available. The device is not in use.");

	else
		char_count = scnprintf(buf, PAGE_SIZE,
				"read_requests_submitted - %llu\n"
				"read_requests_completed - %llu\n"
				"write_requests_submitted - %llu\n"
				"write_requests_completed - %llu\n"
				"fsync_count - %llu\n"
				"no_space_left_error - %llu\n"
				"dma_submit_error - %llu\n"
				"fsync_busy_count - %llu\n"
				"read_timeouts_error - %llu\n"
				"opened_times - %llu\n",
				device_private_data[MINOR(dev->devt)].stats.read_submitted_bytes,
				device_private_data[MINOR(dev->devt)].stats.read_completed_bytes,
				device_private_data[MINOR(dev->devt)].stats.write_submitted_bytes,
				device_private_data[MINOR(dev->devt)].stats.write_completed_bytes,
				device_private_data[MINOR(dev->devt)].stats.fsync_count,
				device_private_data[MINOR(dev->devt)].stats.no_space_left_error,
				device_private_data[MINOR(dev->devt)].stats.dma_submit_error,
				device_private_data[MINOR(dev->devt)].stats.fsync_busy_count,
				device_private_data[MINOR(dev->devt)].stats.read_timeouts_error,
				device_private_data[MINOR(dev->devt)].stats.opened_times);

	return char_count;
}

static DEVICE_ATTR(stats, S_IRUSR, print_queue_stats, NULL);

static int alloc_char_devices(u32 count, const char *name, u32* Major, struct cdev* cdev)
{
	int ret = 0;
	dev_t dev_no;

	ret = alloc_chrdev_region(&dev_no, 0, count, name);
	if(unlikely(ret))
		return ret;

	*Major = MAJOR(dev_no);

	ret = cdev_add(cdev, MKDEV(*Major, 0), count);
	if(unlikely(ret))
		unregister_chrdev_region(MKDEV(*Major, 0), count);

	return ret;
}

static struct device* edma_add_queue_device(struct class* edma_class, void* rx_handle, void* tx_handle, struct edma_char_queue_device* edma_queues, u32 fpga_number, u32 minor_index)
{
	int ret = 0;
	struct device* edmaCharDevice = NULL;
	dev_t dev = MKDEV(edma_queues->major, minor_index);

	BUG_ON(minor_index >= MAX_NUMBER_OF_EDMA_DEVICE * MAX_NUMBER_OF_EDMA_QUEUES);

	// Register the device driver
	edmaCharDevice = device_create(edma_class, &edma_queues->pdev->dev, dev, NULL, "%s%d_queue_%d", QUEUE_DEVICE_NAME, fpga_number, minor_index);
	if(unlikely(IS_ERR(edmaCharDevice))) {
		pr_alert("Failed to create the device\n");
		ret = PTR_ERR(edmaCharDevice);;
		goto edma_queue_device_done;
	}

	//Create SysFS stats endpoint
	ret = device_create_file(edmaCharDevice, &dev_attr_stats);
	if(unlikely(ret < 0)) {
		pr_err("failed to create write /sys endpoint - continuing without\n");
		goto edma_queue_device_done;
	}

	// Setup the linkage to device private data
	dev_set_drvdata(edmaCharDevice, edma_queues->device_private_data);

	edma_queues->device_private_data[minor_index].write_ebcs.dma_queue_handle = tx_handle;
	edma_queues->device_private_data[minor_index].read_ebcs.dma_queue_handle = rx_handle;
	edma_queues->fpga_number = fpga_number;

	mutex_init(&edma_queues->device_private_data[minor_index].edma_mutex);

edma_queue_device_done:
	return edmaCharDevice;
}

static struct device* edma_add_user_event(struct class* edma_class, struct edma_char_event_device* edma_events, u32 fpga_number, u32 minor_index)
{
	int ret = 0;
	struct device* edmaCharDevice = NULL;
	dev_t dev = MKDEV(edma_events->major, minor_index);

	BUG_ON(minor_index >= MAX_NUMBER_OF_EDMA_DEVICE * MAX_NUMBER_OF_EDMA_QUEUES);

	edmaCharDevice = device_create(edma_class, &edma_events->pdev->dev, dev, NULL, "%s%d_event%d", EVENT_DEVICE_NAME, fpga_number, minor_index);
	if(unlikely(IS_ERR(edmaCharDevice))) {
		pr_alert("Failed to create the device\n");
		ret = PTR_ERR(edmaCharDevice);;
		goto edma_event_device_done;
	}

	//TODO: Create SysFS stats endpoint
//	ret = device_create_file(edmaCharDevice, &dev_attr_stats);
//	if(unlikely(ret < 0)) {
//		pr_err("failed to create write /sys endpoint - continuing without\n");
//		goto edma_queue_device_done;
//	}

	edma_backend_register_isr(edma_events->pdev, minor_index, edma_dev_irq_handler, edmaCharDevice->kobj.name, edma_events->events_private_data);

edma_event_device_done:
		return edmaCharDevice;
}

static int edma_alloc_fpga_num(void)
{
	u32 fpga_num;

	spin_lock(&edma_fpga_alloc_lock);
	fpga_num = find_first_zero_bit(edma_fpga_alloc_bitmap, MAX_NUMBER_OF_EDMA_DEVICE);

	if (fpga_num == MAX_NUMBER_OF_EDMA_DEVICE) {
		fpga_num = -ENODEV;
		goto out;
	}
	set_bit(fpga_num, edma_fpga_alloc_bitmap);

out:
	spin_unlock(&edma_fpga_alloc_lock);

	pr_debug("%s: fpga_num=%d\n", __func__, fpga_num);
	return fpga_num;
}

static void edma_free_fpga_num(int fpga_num)
{
	pr_debug("%s: fpga_num=%d\n", __func__, fpga_num);

	spin_lock(&edma_fpga_alloc_lock);
	clear_bit(fpga_num, edma_fpga_alloc_bitmap);
	spin_unlock(&edma_fpga_alloc_lock);
}


int edma_dev_init(struct backend_device* backend_device)
{
	int ret = 0;
	struct edma_char_queue_device* edma_queues = NULL;
	struct edma_char_event_device* edma_events = NULL;
	struct device** edmaEventDevices;
	int fpga_number;
	int i;

	fpga_number = edma_alloc_fpga_num();
	if (fpga_number < 0) {
		ret = -ENODEV;
		goto edma_dev_init_done;	
	}

	edma_queues = (struct edma_char_queue_device*)kzalloc(sizeof(struct edma_char_queue_device), GFP_KERNEL);
	if(edma_queues == NULL) {
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	edma_queues->device_private_data = (struct edma_queue_private_data*)kzalloc(backend_device->number_of_queues * sizeof(struct edma_queue_private_data), GFP_KERNEL);
	if(edma_queues->device_private_data == NULL) {
		kfree(edma_queues);
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	edma_events = (struct edma_char_event_device*)kzalloc(sizeof(struct edma_char_event_device), GFP_KERNEL);
	if(edma_events == NULL) {
		kfree(edma_queues->device_private_data);
		kfree(edma_queues);
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	edma_events->events_private_data = (struct edma_event_private_data*)kzalloc(backend_device->number_of_events * sizeof(struct edma_event_private_data), GFP_KERNEL);
	if(edma_events->events_private_data == NULL) {
		kfree(edma_events);
		kfree(edma_queues->device_private_data);
		kfree(edma_queues);
		ret = -ENOMEM;
		goto edma_dev_init_done;

	}

	edmaEventDevices = (struct device**)kzalloc(backend_device->number_of_events * sizeof(struct device*), GFP_KERNEL);
	if(edmaEventDevices == NULL) {
		kfree(edma_events->events_private_data);
		kfree(edma_events);
		kfree(edma_queues->device_private_data);
		kfree(edma_queues);
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	backend_device->frontend_queues_handle = edma_queues;
	backend_device->frontend_events_handle = edma_events;
	backend_device->event_handles = edmaEventDevices;

	edma_queues->cdev.owner = THIS_MODULE;
	edma_events->cdev.owner = THIS_MODULE;
	edma_queues->pdev = backend_device->pdev;
	edma_events->pdev = backend_device->pdev;


	if(unlikely(alloc_char_devices(
			MAX_NUMBER_OF_EDMA_DEVICE
				* MAX_NUMBER_OF_EDMA_QUEUES,
			"edma_queues", &edma_queues->major, &edma_queues->cdev)))
	{
		pr_err("Unable to create char devices for edma_queues");
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	if(unlikely(alloc_char_devices(
			MAX_NUMBER_OF_EDMA_DEVICE
				* MAX_NUMBER_OF_USER_INTERRUPTS,
			"edma_events", &edma_events->major, &edma_events->cdev)))
	{
		pr_err("Unable to create char devices for edma_events");
		ret = -ENOMEM;
		goto edma_dev_init_done;
	}

	cdev_init(&edma_queues->cdev, &queue_fops);
	cdev_init(&edma_events->cdev, &events_fops);

	for(i = 0; i < backend_device->number_of_queues; i++){
		void* device = edma_add_queue_device(edma_class, backend_device->queues[i].rx, backend_device->queues[i].tx, edma_queues, fpga_number, i);
		if(device == NULL) {
			pr_err("unable to create device for fpga %u queue %u", fpga_number, i);
		}
		backend_device->queues[i].char_device_handle = device;
	}

	for(i = 0; i < backend_device->number_of_events; i++)
	{
		init_waitqueue_head(&edma_events->events_private_data[i].event_wq);
		edmaEventDevices[i] = edma_add_user_event(edma_class, edma_events, fpga_number, i);
	}

edma_dev_init_done:

	if ((ret != 0) && (fpga_number >= 0)) {
		edma_free_fpga_num(fpga_number);
	}
	
	return ret;
}

int edma_dev_cleanup(struct backend_device* backend_device)
{
	int i;
	struct edma_char_event_device* edma_events = (struct edma_char_event_device*)(backend_device->frontend_events_handle);
	struct edma_char_queue_device* edma_queues = (struct edma_char_queue_device*)(backend_device->frontend_queues_handle);
	struct device** edmaEventDevices = NULL;
	u32 queue_Major = 0;
	u32 events_Major = 0;
	int fpga_number;

	edmaEventDevices = (struct device**)backend_device->event_handles;

	for(i = 0; i < backend_device->number_of_queues; i++) {

		struct device* dev = (struct device*) (backend_device->queues[i].char_device_handle);
		//if device was allocated
		if(dev) {
			edma_dbg("Releasing queue device %s \n", dev->kobj.name);
			queue_Major = MAJOR (dev->devt);
			device_remove_file(dev, &dev_attr_stats);
			device_destroy(edma_class, dev->devt);
		}
	}

	for(i = 0; i< backend_device->number_of_events; i++)
	{
		if(edmaEventDevices[i]){
			edma_dbg("Releasing event device %s \n", edmaEventDevices[i]->kobj.name);
			events_Major = MAJOR(edmaEventDevices[i]->devt);
			device_remove_file(edmaEventDevices[i], &dev_attr_stats);
			device_destroy(edma_class, edmaEventDevices[i]->devt);
		}
	}

	cdev_del(&edma_events->cdev);
	cdev_del(&edma_queues->cdev);

	unregister_chrdev_region(MKDEV(queue_Major, 0), MAX_NUMBER_OF_EDMA_DEVICE * MAX_NUMBER_OF_EDMA_QUEUES);
	unregister_chrdev_region(MKDEV(events_Major, 0), MAX_NUMBER_OF_EDMA_DEVICE * MAX_NUMBER_OF_USER_INTERRUPTS);

	if(edma_events->events_private_data)
		kfree(edma_events->events_private_data);

	if(edma_events)
		kfree(edma_events);

	if(edma_queues) {
		fpga_number = edma_queues->fpga_number;

		if(edma_queues->device_private_data) {
			kfree(edma_queues->device_private_data);
		}
		kfree(edma_queues);
		edma_free_fpga_num(fpga_number);
	}

	return 0;
}

