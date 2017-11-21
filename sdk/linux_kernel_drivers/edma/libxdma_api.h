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

#ifndef __XDMA_BASE_API_H__
#define __XDMA_BASE_API_H__

#include <linux/types.h>
#include <linux/scatterlist.h>
#include <linux/interrupt.h>

/*
 * functions exported by the xdma driver
 */

typedef struct {
	u64 write_submitted;
	u64 write_completed;
	u64 read_requested;
	u64 read_completed;
	u64 restart;
	u64 open;
	u64 close;
	u64 msix_trigger;
} xdma_statistics;

/*
 * This struct should be constantly updated by XMDA using u64_stats_* APIs
 * The front end will read the structure without locking (That's why updating atomically is a must)
 * every time it prints the statistics.
 */
//static XDMA_Statistics stats;

/* 
 * xdma_device_open - read the pci bars and configure the fpga
 *	should be called from probe()
 * 	NOTE:
 *		user interrupt will not enabled until xdma_user_isr_enable()
 *		is called
 * @pdev: ptr to pci_dev
 * @mod_name: the module name to be used for request_irq
 * @user_max: max # of user/event (interrupts) to be configured
 * @channel_max: max # of c2h and h2c channels to be configured
 * NOTE: if the user/channel provisioned is less than the max specified,
 *	 libxdma will update the user_max/channel_max
 * returns
 *	a opaque handle (for libxdma to identify the device)
 *	NULL, in case of error  
 */
void *xdma_device_open(const char *mod_name, struct pci_dev *pdev,
		 int *user_max, int *h2c_channel_max, int *c2h_channel_max);

/* 
 * xdma_device_close - prepare fpga for removal: disable all interrupts (users
 * and xdma) and release all resources
 *	should called from remove()
 * @pdev: ptr to struct pci_dev
 * @tuples: from xdma_device_open()
 */
void xdma_device_close(struct pci_dev *pdev, void *dev_handle);

/* 
 * xdma_device_restart - restart the fpga
 * @pdev: ptr to struct pci_dev
 * TODO:
 *	may need more refining on the parameter list
 * return < 0 in case of error
 * TODO: exact error code will be defined later
 */
int xdma_device_restart(struct pci_dev *pdev, void *dev_handle);

/*
 * xdma_user_isr_register - register a user ISR handler
 * It is expected that the xdma will register the ISR, and for the user
 * interrupt, it will call the corresponding handle if it is registered and
 * enabled.
 *
 * @pdev: ptr to the the pci_dev struct	
 * @mask: bitmask of user interrupts (0 ~ 15)to be registered
 *		bit 0: user interrupt 0
 *		...
 *		bit 15: user interrupt 15
 *		any bit above bit 15 will be ignored.
 * @handler: the correspoinding handler
 *		a NULL handler will be treated as de-registeration
 * @name: to be passed to the handler, ignored if handler is NULL`
 * @dev: to be passed to the handler, ignored if handler is NULL`
 * return < 0 in case of error
 * TODO: exact error code will be defined later
 */
int xdma_user_isr_register(void *dev_hndl, unsigned int mask,
			 irq_handler_t handler, void *dev);

/*
 * xdma_user_isr_enable/disable - enable or disable user interrupt
 * @pdev: ptr to the the pci_dev struct	
 * @mask: bitmask of user interrupts (0 ~ 15)to be registered
 * return < 0 in case of error
 * TODO: exact error code will be defined later
 */
int xdma_user_isr_enable(void *dev_hndl, unsigned int mask);
int xdma_user_isr_disable(void *dev_hndl, unsigned int mask);

/*
 * xdma_xfer_submit - submit data for dma operation (for both read and write)
 *	This is a blocking call
 * @channel: channle number (< channel_max)
 *	== channel_max means libxdma can pick any channel available:q

 * @dir: DMA_FROM/TO_DEVICE
 * @offset: offset into the DDR/BRAM memory to read from or write to
 * @sg_tbl: the scatter-gather list of data buffers
 * @timeout: timeout in mili-seconds, *currently ignored
 * return # of bytes transfered or
 *	 < 0 in case of error
 * TODO: exact error code will be defined later
 */
ssize_t xdma_xfer_submit(void *dev_hndl, int channel, bool write, u64 ep_addr,
			struct sg_table *sgt, bool dma_mapped, int timeout_ms);
			

/////////////////////missing API////////////////////

//xdma_get_channle_state - if no interrupt on DMA hang is available
//xdma_channle_restart

#endif
