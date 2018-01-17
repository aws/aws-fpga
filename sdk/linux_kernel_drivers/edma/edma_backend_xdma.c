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

#include <linux/pci.h>
#include <linux/version.h>
#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/highmem.h>
#include <linux/types.h>
#include <linux/kthread.h>
#include <linux/delay.h>
#include "edma.h"
#include "edma_backend.h"
#include "libxdma_api.h"
#include <linux/string.h>


#define MASTER_PF                                               (0)
#define DRV_MODULE_NAME                                         "edma_xdma_backend"
#define XDMA_TIMEOUT_IN_MSEC                                    (3 * 1000)
#define SLEEP_MIN_USEC                                          (1)
#define SLEEP_MAX_USEC                                          (20)
#define REQUEST_SLEEP_MSEC                                      (10)
#define PCI_VENDOR_ID_AMAZON                                    (0x1d0f)
#define PCI_DEVICE_ID_FPGA                                      (0xf001)
#define XMDA_NUMBER_OF_USER_EVENTS                              (1)
#define XDMA_LIMIT_NUMBER_OF_QUEUES                             (4)
#define CLASS_NAME                                              "edma"


struct class* edma_class;


typedef struct {
	struct sg_table sgt;
	struct scatterlist sgl;
	u64 target_addr;
	u32 completed;
}command_t;

typedef struct {
	void*		xdev;
	int		channel_num;
	command_t* 	queue;
	u32		head;
	u32		tail;
	u32		next_to_recycle;
	struct task_struct *worker_thread;
	unsigned long   thread_status;
}command_queue_t;

typedef struct {
	void* xdev;
	int   channel_num;
	void* buffer;
	u32 size;
} c2h_handle_t;

//TODO: add a thread that monitors the XDMA state (check that not failed)

#if LINUX_VERSION_CODE >= KERNEL_VERSION(4, 8, 0)
static const struct pci_device_id edma_pci_tbl[] = {
#else
static DEFINE_PCI_DEVICE_TABLE(edma_pci_tbl) = {
#endif
	{ PCI_VENDOR_ID_AMAZON, PCI_DEVICE_ID_FPGA,
	  PCI_ANY_ID, PCI_ANY_ID, 0, 0, PCI_ANY_ID},
	{ 0, }
};
MODULE_DEVICE_TABLE(pci, edma_pci_tbl);

static frontend_callback frontend_init_callback;
static frontend_callback frontend_cleanup_callback;
extern unsigned int edma_queue_depth;

static int write_worker_function(void *data)
{
	command_queue_t* command_queue = (command_queue_t*)data;
	command_t*  queue = command_queue->queue;
	bool stopped_on_timeout = false;
	int ret;

	while (true) {
		/* From sched.h:
		 *  set_current_state() includes a barrier so that the write of current->state
		 *  is correctly serialised wrt the caller's subsequent test of whether to
		 *  actually sleep.
		 *
		 * We are using the below pattern to avoid missed wakeups.
		 */
		set_current_state(TASK_INTERRUPTIBLE);

		if (unlikely(kthread_should_stop())) {
			/* We were asked to exit */
			break;
		} else if (unlikely((command_queue->head == command_queue->tail) ||
					stopped_on_timeout)) {
			/* 
			 * Two conditions:
			 *  1.) Queue is empty, sleep until wake_up_process is called.
			 *  2.) If we stopped due to a previous timeout, continue waiting 
			 * 	until we are asked to exit via kthread_stop.
			 */
			schedule();
			continue;
		}

		/* Set running state, process the queue head */
		__set_current_state(TASK_RUNNING);

		ret = xdma_xfer_submit(
			command_queue->xdev,
			command_queue->channel_num,
			true, /* write==true */
			queue[command_queue->head].target_addr,
			&queue[command_queue->head].sgt,
			true, /* dma_mapped==true */
			XDMA_TIMEOUT_IN_MSEC);

		if(ret < 0) {
			pr_err("%s: IO failed with address 0x%llx and size %u\n", __func__,
				queue[command_queue->head].target_addr,
				sg_dma_len(queue[command_queue->head].sgt.sgl));

			/* We'll wait in this state until we are asked to exit */
			stopped_on_timeout = true;
			continue;
		}

		queue[command_queue->head].completed = 1;

		command_queue->head =
			EDMA_RING_IDX_NEXT(
				command_queue->head,edma_queue_depth);
	}

	pr_debug("%s: exiting\n", __func__);
	return 0;
}

static int edma_xdma_probe(struct pci_dev *pdev, const struct pci_device_id *id)
{
	int ret = 0;
	struct device *dev = &pdev->dev;
	void* xdev= NULL;
	int i;
	struct backend_device* backend_device = NULL;
	int user_max = MAX_NUMBER_OF_USER_INTERRUPTS;
	int h2c_channel_max = XDMA_LIMIT_NUMBER_OF_QUEUES;
	int c2h_channel_max = XDMA_LIMIT_NUMBER_OF_QUEUES;
	int number_of_xdma_channels = 0;
	command_queue_t* command_queue = NULL;
	c2h_handle_t* c2h_handles = NULL;

	dev_dbg(dev, ">> %s\n", __func__);

	if (PCI_FUNC(pdev->devfn) != MASTER_PF) {
		dev_dbg(dev, "device function %d is not master, exiting..\n",
			PCI_FUNC(pdev->devfn));
		return ret;
	}

	ret = pcim_enable_device(pdev); //TODO: kcompat
	if (ret) {
		dev_err(dev, "pcim_enable_device failed!\n");
		goto done;
	}

	pci_set_master(pdev);
	pci_save_state(pdev);

	xdev = xdma_device_open(DRV_MODULE_NAME, pdev, &user_max, &h2c_channel_max, &c2h_channel_max);
	if(unlikely(xdev == NULL)){
		ret = -EINVAL;
		goto done;
	}

        BUG_ON(user_max > MAX_NUMBER_OF_USER_INTERRUPTS);
        BUG_ON(h2c_channel_max > XDMA_LIMIT_NUMBER_OF_QUEUES);
        BUG_ON(c2h_channel_max > XDMA_LIMIT_NUMBER_OF_QUEUES);
        BUG_ON(h2c_channel_max != c2h_channel_max);

	if(unlikely(!h2c_channel_max || !c2h_channel_max)){
		ret = -ENODEV;
		goto done;
	}

	number_of_xdma_channels = h2c_channel_max;
	dev_info(dev, "DMA backend opened %d channels\n", number_of_xdma_channels);

	command_queue = (command_queue_t*)kzalloc(
			number_of_xdma_channels * sizeof(command_queue_t),
			GFP_KERNEL);
	if(!command_queue) {
		ret = -ENOMEM;
		goto done;
	}

	backend_device = (struct backend_device*)kzalloc(
			sizeof(struct backend_device), GFP_KERNEL);
	if(!backend_device) {
		ret = -ENOMEM;
		kfree(command_queue);
		goto done;
	}

	backend_device->queues = (struct edma_queue_handle*)kzalloc(
			number_of_xdma_channels * sizeof(struct edma_queue_handle),
			GFP_KERNEL);
	if(!backend_device->queues) {
		ret = -ENOMEM;
		kfree(backend_device);
		kfree(command_queue);
		goto done;
	}

	c2h_handles = (c2h_handle_t*)kzalloc(
			number_of_xdma_channels * sizeof(c2h_handle_t),
			GFP_KERNEL);
	if(!c2h_handles) {
			ret = -ENOMEM;
			kfree(backend_device->queues);
			kfree(backend_device);
			kfree(command_queue);
			goto done;
		}

	for( i = 0; i < number_of_xdma_channels; i++)
	{
		command_queue[i].xdev = xdev;
		command_queue[i].channel_num = i;
		command_queue[i].queue = (command_t*)kzalloc(
				edma_queue_depth * sizeof(command_t), GFP_KERNEL);

		c2h_handles[i].xdev = xdev;
		c2h_handles[i].channel_num = i;

		backend_device->queues[i].rx = &(c2h_handles[i]);
		backend_device->queues[i].tx = &(command_queue[i]);

		smp_wmb();
	}

	backend_device->pdev = pdev;
	backend_device->backend_device_handle = xdev;
	backend_device->number_of_queues = number_of_xdma_channels;

	//TODO: consider moving number of events to an API
	backend_device->number_of_events = XMDA_NUMBER_OF_USER_EVENTS;

	dev_set_drvdata(&pdev->dev, backend_device);

	frontend_init_callback(backend_device);

done:

	dev_dbg(dev, "<< %s\n", __func__);

	if (ret)
		dev_err(dev, "Probe finished with errors[%d]!\n", ret);
	else
		dev_dbg(dev, "Probe done!\n");

	return ret;
}

static void edma_xdma_remove(struct pci_dev *pdev)
{
	struct device *dev = &pdev->dev;
	struct backend_device* backend_device;
	command_queue_t* command_queue;
	c2h_handle_t* c2h_handle;

	dev_dbg(dev, ">> %s\n", __func__);

	if (PCI_FUNC(pdev->devfn) != MASTER_PF)
		return;

	backend_device = (struct backend_device *)dev_get_drvdata(&pdev->dev);
	command_queue = (command_queue_t*)(backend_device->queues[0].tx);
	c2h_handle = (c2h_handle_t *) (backend_device->queues[0].rx);

	xdma_device_close(pdev, backend_device->backend_device_handle);
	frontend_cleanup_callback(backend_device);

	kfree(c2h_handle);
	c2h_handle = NULL;

	kfree(backend_device->queues);
	backend_device->queues = NULL;

	kfree(backend_device);
	backend_device = NULL;

	kfree(command_queue);
	command_queue = NULL;

	dev_dbg(dev, "<< %s\n", __func__);

	return;
}

int edma_backend_register_isr(struct pci_dev *pdev, u32 event_number,
		irq_handler_t handler, const char* name, void* drv)
{
	struct backend_device* backend_device;

	backend_device = (struct backend_device *)dev_get_drvdata(&pdev->dev);

	return xdma_user_isr_register(backend_device->backend_device_handle, 
			BIT(event_number), handler, drv);
}


int edma_backend_enable_isr(struct pci_dev *pdev, u32 event_number)
{
	struct backend_device* backend_device;

	backend_device = (struct backend_device *)dev_get_drvdata(&pdev->dev);

	return xdma_user_isr_enable(backend_device->backend_device_handle, BIT(event_number));
}

int edma_backend_disable_isr(struct pci_dev *pdev, u32 event_number)
{
	struct backend_device* backend_device;

	backend_device = (struct backend_device *)dev_get_drvdata(&pdev->dev);

	return xdma_user_isr_disable(backend_device->backend_device_handle, BIT(event_number));
}


int edma_backend_submit_m2s_request(u64* buffer, u32 size, void *q_handle, u64 target_addr)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;
	struct scatterlist* sgl = &command_queue->queue[command_queue->tail].sgl;
	struct sg_table* sgt = &command_queue->queue[command_queue->tail].sgt;

	edma_dbg(">> %s\n", __func__);

	BUG_ON(EDMA_RING_IDX_NEXT(command_queue->tail, edma_queue_depth) == command_queue->next_to_recycle);

	sg_init_table(sgl, 1);

	sg_dma_address(sgl) = (dma_addr_t)buffer;

	sg_dma_len(sgl) = size;

	sgt->sgl = sgl;
	sgt->nents = sgt->orig_nents = 1;

	command_queue->queue[command_queue->tail].target_addr = target_addr;

	//32-bit is atomic
	command_queue->tail =
			EDMA_RING_IDX_NEXT(
					command_queue->tail,
					edma_queue_depth);

	smp_wmb();

	//See the comment in the write_worker_function regarding missed wakeups 
	wake_up_process(command_queue->worker_thread);

	edma_dbg("<< %s\n", __func__);

	return 0;
}

//TODO: inline
int edma_backend_get_completed_m2s_request(u64** buffer, u32* size, void *q_handle)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;
	command_t* queue = command_queue->queue;
	u32 completed_size = 0;
	u64* completed_buffer = NULL;

	edma_dbg( ">> %s\n", __func__);

	if((command_queue->next_to_recycle != command_queue->head)
			&& (queue[command_queue->next_to_recycle].completed == 1)) {

		completed_buffer = (void*)(sg_dma_address(queue[command_queue->next_to_recycle].sgt.sgl));
		completed_size = sg_dma_len(queue[command_queue->next_to_recycle].sgt.sgl);
		queue[command_queue->next_to_recycle].completed = 0;

		sg_dma_len(queue[command_queue->next_to_recycle].sgt.sgl) = 0;
		sg_dma_address(queue[command_queue->next_to_recycle].sgt.sgl) = 0;

		command_queue->next_to_recycle =
				EDMA_RING_IDX_NEXT(
				command_queue->next_to_recycle,
				edma_queue_depth);
	}

	if(size)
		*size = completed_size;

	if(buffer)
		*buffer = completed_buffer;

	edma_dbg("<< %s\n", __func__);

    return 0;
}

int edma_backend_submit_s2m_request(u64* buffer, u32 size, void *q_handle, u64 target_addr)
{
	struct sg_table sg_table;
	struct scatterlist sg;
	int size_read = 0;
	int ret = 0;
	c2h_handle_t* c2h_handle = (c2h_handle_t*)q_handle;

	sg_init_table(&sg, 1);

	sg_dma_address(&sg) = (dma_addr_t)buffer;
	sg_dma_len(&sg) = size;

	sg_table.sgl = &sg;
	sg_table.nents = sg_table.orig_nents = 1;

	size_read = xdma_xfer_submit(c2h_handle->xdev, c2h_handle->channel_num, 
				false, /* write==false */
				target_addr, &sg_table, 
				true, /* dma_mapped==true */
				XDMA_TIMEOUT_IN_MSEC);
	if (size_read < 0) {
		ret = size_read;
		if (ret != -ENOMEM && ret != -EIO)
			ret = -EIO;

		goto edma_backend_submit_s2m_request_done;
	}

	c2h_handle->buffer = buffer;
	c2h_handle->size = size_read;

edma_backend_submit_s2m_request_done:
	return ret;
}



int edma_backend_get_completed_s2m_request(u64** buffer, u32* size, void *q_handle)
{
	c2h_handle_t* c2h_handle = (c2h_handle_t*)q_handle;

	*buffer = c2h_handle->buffer;
	*size = c2h_handle->size;

	c2h_handle->buffer = NULL;
	c2h_handle->size = 0;

	return 0;
}


int edma_backend_m2s_dma_action(void *tx_dma_q)
{
	(void)tx_dma_q;

	//does nothing

        return 0;
}

static struct pci_driver edma_pci_driver = {
	.name		= DRV_MODULE_NAME,
	.id_table	= edma_pci_tbl,
	.probe		= edma_xdma_probe,
	.remove		= edma_xdma_remove,
};


int edma_backend_stop(void *q_handle)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;
	command_t* queue = command_queue->queue;
	int i;

	if (command_queue->worker_thread) {
		pr_debug("%s: kthread_stop...\n", __func__);

		kthread_stop(command_queue->worker_thread);

		pr_debug("%s: kthread_stop...done\n", __func__);
	}

	for(i = 0; i < edma_queue_depth; i++) {
		memset(&(queue[i]), 0, sizeof(command_t));
	}

	command_queue->head = 0;
	command_queue->tail = 0;
	command_queue->next_to_recycle = 0;
	command_queue->worker_thread = NULL;
	command_queue->thread_status = 0;

	return 0;
}

int edma_backend_start(void *q_handle, int minor)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;

	//launch the worker thread
	command_queue->worker_thread = kthread_run(write_worker_function, command_queue,
			"write_worker_thread_%d", minor);

	return 0;
}


int edma_backend_init(frontend_callback frontend_init, frontend_callback frontend_cleanup)
{

	int ret;

	frontend_init_callback = frontend_init;
	frontend_cleanup_callback = frontend_cleanup;

	if (!edma_class) {
		edma_class = class_create(THIS_MODULE, CLASS_NAME);
		if(unlikely(IS_ERR(edma_class))) {
			ret = PTR_ERR(edma_class);
			return ret;
		}
	}

	return pci_register_driver(&edma_pci_driver);
}

void edma_backend_cleanup(void)
{
	pci_unregister_driver(&edma_pci_driver);

	if(edma_class != NULL) {
		class_unregister(edma_class);
		class_destroy(edma_class);
		edma_class = NULL;
	}
}
