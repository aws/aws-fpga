#ifndef EDMA_H
#define EDMA_H
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/moduleparam.h>

#define EDMA_RING_IDX_NEXT(idx, ring_size) (((idx) + 1) & ((ring_size) - 1))
#define EDMA_NUM_OF_QUEUES				(4)

#ifdef EDMA_DEBUG_PRINTS
#define edma_dbg pr_info
#else
#define edma_dbg(...)
#endif

struct edma_queue_handle {
	void* tx;
	void* rx;
	void* char_device_handle;
};

struct backend_device {
	struct edma_queue_handle* queues;
	void* event_handles;
	struct pci_dev *pdev;
	u32 number_of_queues;
	u32 number_of_events;
	void* frontend_queues_handle;
	void* frontend_events_handle;
	void* backend_device_handle;
};

typedef int (*frontend_callback)(struct backend_device* backend_device);

enum edma_state_t {
	EDMA_STATE_RUNNING = 0,
	EDMA_STATE_FSYNC_IN_PROGRESS_BIT,
	EDMA_STATE_QUEUE_RELEASING_BIT,
	EDMA_STATE_READ_IN_PROGRESS_BIT,
	EDMA_STATE_WRITE_IN_PROGRESS_BIT,
};

#endif
