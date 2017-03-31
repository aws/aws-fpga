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

#define MASTER_PF					(0)
#define DRV_MODULE_NAME					"emda_xdma_backend"
//FIXME: move to mutable
#define XDMA_TIMEOUT_IN_MSEC				(3 * 1000)
#define XDMA_WORKER_SLEEPING_STATUS_BIT			(0)
#define XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT		(1)
#define XDMA_WORKER_STOPPED_ON_REQUEST_BIT		(2)
#define PCI_VENDOR_ID_AMAZON 				(0x1d0f)
#define PCI_DEVICE_ID_FPGA				(0xf001)
#define XMDA_NUMBER_OF_USER_EVENTS			(16)
#define CLASS_NAME "edma"

struct class* edma_class;


typedef struct
{
	//avoid allocation
	struct sg_table sgt;
	struct scatterlist sgl;
	u64 target_addr;
	u32 completed;

}command_t;

typedef struct
{
	void*		channel_handle;
	command_t* 	queue;
	u32		head;
	u32		tail;
	u32		next_to_recycle;
	struct task_struct *worker_thread;
	unsigned long   thread_status;
}command_queue_t;

//TODO: add a thread that monitors the XDMA state (check that not failed)

static DEFINE_PCI_DEVICE_TABLE(edma_pci_tbl) = {
	{ PCI_VENDOR_ID_AMAZON, PCI_DEVICE_ID_FPGA,
	  PCI_ANY_ID, PCI_ANY_ID, 0, 0, PCI_ANY_ID},
	{ 0, }
};
MODULE_DEVICE_TABLE(pci, edma_pci_tbl);

static frontend_callback frontend_init_callback;
static frontend_callback frontend_cleanup_callback;
static void* read_submitted_buffer;
static u32 read_submitted_size;
extern int edma_queue_depth;

static int write_worker_function(void *data)
{
	command_queue_t* command_queue = (command_queue_t*)data;
	command_t* 	queue = command_queue->queue;

	while(!kthread_should_stop())
	{
		clear_bit(XDMA_WORKER_SLEEPING_STATUS_BIT, &command_queue->thread_status);

		if(command_queue-> head != command_queue->tail)
		{
			int ret = xdma_xfer_submit(
					command_queue->channel_handle,
					DMA_TO_DEVICE,
					queue[command_queue->head].target_addr,
					&queue[command_queue->head].sgt,
					true,
					XDMA_TIMEOUT_IN_MSEC);
			if(ret < 0) { //FIXME: for now assume that timeout - later real error
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
					(command_queue->head + 1) % edma_queue_depth;

			set_bit(XDMA_WORKER_SLEEPING_STATUS_BIT, &command_queue->thread_status);

			//are there still requests in the queue?
			if(command_queue->head != command_queue->tail)
				continue;
		}

		set_current_state(TASK_INTERRUPTIBLE);
		schedule();
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
	if(number_of_xdma_channels < 0) {
		ret = number_of_xdma_channels;
		goto done;
	}

	if(unlikely(number_of_xdma_channels < 0)){
		ret = number_of_xdma_channels;
		goto done;
	}

	dev_info(dev, "xdma opened %d channels\n", number_of_xdma_channels);

	command_queue = (command_queue_t*)kzalloc(
			number_of_xdma_channels * sizeof(command_queue_t), GFP_KERNEL);
	if(!command_queue) {
		ret = -ENOMEM;
		goto done;
	}

	backend_device = (struct backend_device*)kzalloc(sizeof(struct backend_device), GFP_KERNEL);
	if(!backend_device) {
		ret = -ENOMEM;
		kfree(command_queue);
		goto done;
	}

	backend_device->queues = (struct edma_queue_handle*)kzalloc(number_of_xdma_channels * sizeof(struct edma_queue_handle), GFP_KERNEL);
	if(!backend_device->queues) {
		ret = -ENOMEM;
		kfree(backend_device);
		kfree(command_queue);
		goto done;
	}

	for( i = 0; i < number_of_xdma_channels; i++)
	{
		command_queue[i].channel_handle = channel_list[i].h2c;
		command_queue[i].queue = (command_t*)kzalloc(
				edma_queue_depth * sizeof(command_t), GFP_KERNEL);
		command_queue[i].head = command_queue[i].tail = 0;

		backend_device->queues[i].rx = channel_list[i].c2h;
		backend_device->queues[i].tx = &(command_queue[i]);

		smp_wmb();

		command_queue[i].worker_thread = kthread_run(write_worker_function, &command_queue[i],
				"write_worker_thread_%d", i);
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
	int i;
	struct backend_device* backend_device;
	command_queue_t* command_queue;

	dev_dbg(dev, ">> %s\n", __func__);

	if (PCI_FUNC(pdev->devfn) != MASTER_PF)
		return;

	backend_device = (struct backend_device *)dev_get_drvdata(&pdev->dev);
	command_queue = (command_queue_t*)(backend_device->queues[0].tx);

	for( i = 0; i < backend_device->number_of_queues; i++)
		if(command_queue[i].worker_thread->state > 0)
			kthread_stop(command_queue[i].worker_thread);

	for( i = 0; i < backend_device->number_of_queues; i++)
	{
		xdma_device_close(pdev, backend_device->backend_device_handle);

		if(!test_bit(XDMA_WORKER_STOPPED_ON_REQUEST_BIT, &command_queue->thread_status) &&
				!test_bit(XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT, &command_queue->thread_status))
			msleep(XDMA_TIMEOUT_IN_MSEC);

		//if still not stopped - panic
		if(!test_bit(XDMA_WORKER_STOPPED_ON_REQUEST_BIT, &command_queue->thread_status) &&
						!test_bit(XDMA_WORKER_STOPPED_ON_TIMEOUT_BIT, &command_queue->thread_status))
			BUG();

		kfree(command_queue[i].queue);
	}

	frontend_cleanup_callback(backend_device);

	kfree(command_queue);
	command_queue = NULL;

	kfree(backend_device->queues);
	backend_device->queues = NULL;

	kfree(backend_device);
	backend_device = NULL;

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

	pr_info(">> %s\n", __func__);

	if( (command_queue->tail + 1) % edma_queue_depth == command_queue->next_to_recycle)
		BUG();

	sg_init_table(sgl, 1);

	sg_dma_address(sgl) = (dma_addr_t)buffer;

	sg_dma_len(sgl) = size;

	sgt->sgl = sgl;
	sgt->nents = 1;

	command_queue->queue[command_queue->tail].target_addr = target_addr;

	//32-bit is atomic
	command_queue->tail =
			(command_queue->tail + 1)
					% edma_queue_depth;

	smp_wmb();

	/*
	 * detection of a race-condition - the going_to_sleep bit is set but
	 * thread is not asleep so it will miss the wakeup
	 *
	 */

	while((command_queue->worker_thread->state == TASK_RUNNING)
			&& test_bit(XDMA_WORKER_SLEEPING_STATUS_BIT,
					&command_queue->thread_status))
		msleep(XDMA_TIMEOUT_IN_MSEC);

	wake_up_process(command_queue->worker_thread);

	pr_info("<< %s\n", __func__);

	return 0;
}

//TODO: inline
int edma_backend_get_completed_m2s_request(u64** buffer, u32* size, void *q_handle)
{
	command_queue_t* command_queue = (command_queue_t*)q_handle;
	command_t* queue = command_queue->queue;
	u32 completed_size = 0;
	u64* completed_buffer = NULL;

	pr_info( ">> %s\n", __func__);

	if((command_queue->next_to_recycle != command_queue->head)
			&& (queue[command_queue->next_to_recycle].completed == 1)) {

		completed_buffer = (void*)(sg_dma_address(queue[command_queue->next_to_recycle].sgt.sgl));
		completed_size = queue[command_queue->next_to_recycle].sgt.sgl->length;
		queue[command_queue->next_to_recycle].completed = 0;
		command_queue->next_to_recycle =
				(command_queue->next_to_recycle + 1)
						% edma_queue_depth;
	}

	if(size)
		*size = completed_size;

	if(buffer)
		*buffer = completed_buffer;

	pr_info("<< %s\n", __func__);

        return 0;
}

int edma_backend_submit_s2m_request(u64* buffer, u32 size, void *q_handle, u64 target_addr)
{
	struct sg_table sg_table;
	struct scatterlist sg;
	int size_read = 0;
	int ret = 0;

	sg_init_table(&sg, 1);

	sg_dma_address(&sg) = (dma_addr_t)buffer;
	sg_dma_len(&sg) = size;

	sg_table.sgl = &sg;
	sg_table.nents = 1;

	size_read = xdma_xfer_submit(q_handle, DMA_FROM_DEVICE, target_addr, &sg_table, true, XDMA_TIMEOUT_IN_MSEC);
	if (size_read < 0) {
		ret = size_read;
		if (ret != -ENOMEM && ret != -EIO)
			ret = -EIO;

		goto edma_backend_submit_s2m_request_done;
	}

	read_submitted_buffer = buffer;
	read_submitted_size = size_read;

edma_backend_submit_s2m_request_done:
	return ret;
}



int edma_backend_get_completed_s2m_request(u64** buffer, u32* size, void *q_handle)
{
	(void)buffer;
	(void)size;
	(void)q_handle;

	*buffer = (u64*)read_submitted_buffer;
	*size = read_submitted_size;

	read_submitted_buffer = NULL;
	read_submitted_size = 0;

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


int edma_backend_reset(void *dma_q)
{
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
