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
#define XDMA_WORKER_SLEEPING_STATUS_BIT                         (0)
#define XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT                      (1)
#define XDMA_WORKER_STOPPED_ON_REQUEST_BIT                      (2)
#define XDMA_WORKER_STOP_REQUEST_BIT                            (3)
#define REQUEST_SLEEP_MSEC                                      (10)
#define PCI_VENDOR_ID_AMAZON                                    (0x1d0f)
#define PCI_DEVICE_ID_FPGA                                      (0xf001)
#define XMDA_NUMBER_OF_USER_EVENTS                              (1)
#define XDMA_LIMIT_NUMBER_OF_QUEUES                             (1)
#define CLASS_NAME                                              "edma"

struct class* edma_class;


typedef struct {
	struct sg_table sgt;
	struct scatterlist sgl;
	u64 target_addr;
	u32 completed;
}command_t;

typedef struct {
	void* channel_handle;
	command_t* 	queue;
	u32		head;
	u32		tail;
	u32		next_to_recycle;
	struct task_struct *worker_thread;
	unsigned long   thread_status;
}command_queue_t;

typedef struct {
	void* channel_handle;
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
extern int edma_queue_depth;

static int write_worker_function(void *data)
{
	command_queue_t* command_queue = (command_queue_t*)data;
	command_t* 	queue = command_queue->queue;

	while(!test_bit(XDMA_WORKER_STOP_REQUEST_BIT, &command_queue->thread_status))
	{
		if(command_queue->head != command_queue->tail)
		{
			int ret = xdma_xfer_submit(
					command_queue->channel_handle,
					DMA_TO_DEVICE,
					queue[command_queue->head].target_addr,
					&queue[command_queue->head].sgt,
					true,
					XDMA_TIMEOUT_IN_MSEC);
			if(ret < 0) { 
				pr_err(	"Thread failed during transaction with address 0x%llx and size %u\n",
					queue[command_queue->head].target_addr,
					sg_dma_len(queue[command_queue->head].sgt.sgl));
				test_and_set_bit(
						XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT,
						&command_queue->thread_status);
				do_exit(-1);
			}

			queue[command_queue->head].completed = 1;

			command_queue->head =
					EDMA_RING_IDX_NEXT(
							command_queue->head,edma_queue_depth);

			//are there still requests in the queue?
			if(command_queue->head != command_queue->tail)
				continue;
		}

		set_bit(XDMA_WORKER_SLEEPING_STATUS_BIT, &command_queue->thread_status);

		set_current_state(TASK_INTERRUPTIBLE);
		schedule();

		clear_bit(XDMA_WORKER_SLEEPING_STATUS_BIT, &command_queue->thread_status);
	}

	set_bit(XDMA_WORKER_STOPPED_ON_REQUEST_BIT,
			&command_queue->thread_status);

	return 0;
}

static int edma_xdma_probe(struct pci_dev *pdev, const struct pci_device_id *id)
{
	int ret = 0;
	struct device *dev = &pdev->dev;
	xdma_channel_tuple* channel_list = NULL;
	int i;
	struct backend_device* backend_device = NULL;
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

	number_of_xdma_channels = xdma_device_open(pdev, &channel_list);
	if(unlikely(number_of_xdma_channels < 0)){
		ret = number_of_xdma_channels;
		goto done;
	}

	if(number_of_xdma_channels > XDMA_LIMIT_NUMBER_OF_QUEUES)
		number_of_xdma_channels = XDMA_LIMIT_NUMBER_OF_QUEUES;

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
			number_of_xdma_channels
					* sizeof(struct edma_queue_handle),
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
		command_queue[i].channel_handle = channel_list[i].h2c;
		command_queue[i].queue = (command_t*)kzalloc(
				edma_queue_depth * sizeof(command_t), GFP_KERNEL);

		c2h_handles[i].channel_handle = channel_list[i].c2h;

		backend_device->queues[i].rx = &(c2h_handles[i]);
		backend_device->queues[i].tx = &(command_queue[i]);

		smp_wmb();
	}

	backend_device->pdev = pdev;
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
	return xdma_user_isr_register(pdev,BIT(event_number), handler, name, drv);
}


int edma_backend_enable_isr(struct pci_dev *pdev, u32 event_number)
{
	return xdma_user_isr_enable(pdev,BIT(event_number));
}

int edma_backend_disable_isr(struct pci_dev *pdev, u32 event_number)
{
	return xdma_user_isr_disable(pdev,BIT(event_number));
}


int edma_backend_submit_m2s_request(u64* buffer, u32 size, void *q_handle, u64 target_addr)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;
	struct scatterlist* sgl = &command_queue->queue[command_queue->tail].sgl;
	struct sg_table* sgt = &command_queue->queue[command_queue->tail].sgt;

	edma_dbg(">> %s\n", __func__);

	if( EDMA_RING_IDX_NEXT(command_queue->tail, edma_queue_depth) == command_queue->next_to_recycle)
		BUG();

	sg_init_table(sgl, 1);

	sg_dma_address(sgl) = (dma_addr_t)buffer;

	sg_dma_len(sgl) = size;

	sgt->sgl = sgl;
	sgt->nents = 1;

	command_queue->queue[command_queue->tail].target_addr = target_addr;

	//32-bit is atomic
	command_queue->tail =
			EDMA_RING_IDX_NEXT(
					command_queue->tail,
					edma_queue_depth);

	smp_wmb();

	/*
	 * detection of a race-condition - the going_to_sleep bit is set but
	 * thread is not asleep so it will miss the wakeup
	 *
	 */

	while((wake_up_process(command_queue->worker_thread) == 0)
			&& test_bit(XDMA_WORKER_SLEEPING_STATUS_BIT,
					&command_queue->thread_status))
		usleep_range(SLEEP_MIN_USEC,SLEEP_MAX_USEC);

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
	sg_table.nents = 1;

	size_read = xdma_xfer_submit(c2h_handle->channel_handle, DMA_FROM_DEVICE, target_addr, &sg_table, true, XDMA_TIMEOUT_IN_MSEC);
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

	//Stop the kthread before reset and make sure it was stopped.
	set_bit(XDMA_WORKER_STOP_REQUEST_BIT, &command_queue->thread_status);

	while((wake_up_process(command_queue->worker_thread) == 0)
			&& test_bit(XDMA_WORKER_SLEEPING_STATUS_BIT,
					&command_queue->thread_status))
		usleep_range(SLEEP_MIN_USEC,SLEEP_MAX_USEC);

	if(!test_bit(XDMA_WORKER_STOPPED_ON_REQUEST_BIT, &command_queue->thread_status) &&
			!test_bit(XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT, &command_queue->thread_status))
		msleep(XDMA_TIMEOUT_IN_MSEC);

	//if still not stopped - panic
	if(!test_bit(XDMA_WORKER_STOPPED_ON_REQUEST_BIT, &command_queue->thread_status) &&
					!test_bit(XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT, &command_queue->thread_status))
		BUG();

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
