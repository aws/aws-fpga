/*
 * Driver for XDMA for Xilinx FPGA logic
 *
 * Copyright (C) 2007-2015 Sidebranch
 * Copyright (C) 2015-2016 Xilinx, Inc.
 *
 * Based on XDMA Development-Instrumented Driver for Linux
 *
 * Leon Woestenberg <leon@sidebranch.com>
 *
 */
#include <linux/ioctl.h>
#include <linux/types.h>
/* include early, to verify it depends only on the headers above */
#include "xdma-ioctl.h"

#include <linux/module.h>
#include <linux/cdev.h>
#include <linux/dma-mapping.h>
#include <linux/delay.h>
#include <linux/fb.h> /* frame buffer */
#include <linux/fs.h>
#include <linux/init.h>
#include <linux/interrupt.h>
#include <linux/io.h>
#include <linux/jiffies.h>
#include <linux/kernel.h>
#include <linux/mm.h> /* mmap */
#include <linux/mm_types.h> /* mmap */
#if defined(CONFIG_MTD) && 0
#  include <linux/mtd/map.h>
#  include <linux/mtd/mtd.h>
#endif

#include <linux/pci.h>
#include <linux/sched.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/workqueue.h>
#include <linux/version.h>
#include <linux/uio.h>

/* kernel bug: linux/aio.h depends on linux/kobject.h linux/kdev_t.h,
 * but aio.h does not include these in some releases of the kernel. */
#include <linux/aio.h>
#include <linux/splice.h>

#include "xdma-sgm.h"
#include "xdma-core.h"

#include "xbar_sys_parameters.h"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(4,1,0)
#define XDMA_NEW_AIO
#endif

//SD-Accel Specific
/* compile-time options */
#define XDMA_GPL 1

/* the "first_descriptor" registers are in the SGDMA RTL target */
#define USE_RTL_SGDMA_TARGET 1

/* optimistic back-to-back I/O chaining */
/* this is not compatible with descriptors above 32-bit address range,
 * as the implementation depends on atomically writing 32-bits in host
 * memory to link descriptors */
#define CHAIN_MULTIPLE_TRANSFERS 0

/* for test purposes only, not in default IP! */
#define DESC_COUNTER 0

//SD_Accel Specific
#if XDMA_GPL
MODULE_LICENSE("GPL v2");
#else
MODULE_LICENSE("Copyright (C) 2009-2015 Sidebranch and Xilinx, Inc.");
#endif
MODULE_AUTHOR("Leon Woestenberg <leon@sidebranch.com>, Sonal Santan <sonal.santan@xilinx.com>");

MODULE_VERSION(__stringify(XDMA_DRIVER_MAJOR) "."
	       __stringify(XDMA_DRIVER_MINOR) "."
	       __stringify(XDMA_DRIVER_PATCHLEVEL));

MODULE_DESCRIPTION("Xilinx OpenCL driver for PCIe based devices");

#ifndef __devinit
#  define __devinit
#endif
#ifndef __devexit
#  define __devexit
#endif

/* Target internal components on BAR1 */
#define XDMA_OFS_CONFIG 		(0x0000UL)
#define XDMA_OFS_INT_CTRL 		(0x2000UL)
#define XDMA_OFS_SCRATCH_PAD    (0x3020UL)

/* Scatter-Gather internal components on BAR1 */
#define XDMA_OFS_DMA_WRITE 		(0x0200UL)
#define XDMA_OFS_DMA_WRITE_PERF	(0x0300UL)
#define XDMA_OFS_DMA_READ 		(0x0400UL)
#define XDMA_OFS_DMA_READ_PERF	(0x0500UL)

/* Scatter-Gather reference design only, BAR0 */
#define XDMA_OFS_DMA_WRITE_TESTER	(0x1000UL)
#define XDMA_OFS_DMA_READ_TESTER		(0x2000UL)

/* interrupts of Scatter-Gather internal components */
#define XDMA_INT_DMA_WRITE		(1UL << 16)
#define XDMA_INT_DMA_READ		(1UL << 18)
#define XDMA_INT_DMA_WRITE_PERF	(1UL << 17)
#define XDMA_INT_DMA_READ_PERF	(1UL << 19)

/* interrupts of Scatter-Gather reference design only */
#define XDMA_INT_DMA_READ_TESTER	(1UL << 0)

/* sys filesystem */
struct class *g_xdma_class;

static unsigned int major = 0;
module_param(major, uint, 0644);
MODULE_PARM_DESC(major, "Character device major number, 0 for dynamic selection which is default.");

static unsigned int msi = 1;
module_param(msi, uint, 0644);
MODULE_PARM_DESC(msi, "Use 0 to disable MSI interrupting, default is 1 to use MSI interrupting.");

static int bar_map_sizes_min[6] = { 0, XDMA_BAR_SIZE, 0, 0, 0 ,0 };
module_param_array(bar_map_sizes_min, int, NULL/* not interested in count */, 0644);
MODULE_PARM_DESC(bar_map_sizes_min, "Array of BAR minimally required BAR mapping sizes in bytes.");

static int bar_map_sizes_max[6] = { INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX, INT_MAX, };
static int bar_map_sizes_max_nr;
module_param_array(bar_map_sizes_max, int, &bar_map_sizes_max_nr, 0644);
MODULE_PARM_DESC(bar_map_sizes_max, "Array of BAR maximal mapping sizes in bytes. 0 means do not map, -1 means map complete BAR.");

static int bar_map_sizes[6];

//SD_Accel Specific
static bool load_firmware = true;
module_param(load_firmware, bool, 0644);
MODULE_PARM_DESC(load_firmware, "For UltraScale boards load xclbin firmware file from /lib/firmware/xilinx directory (default: true)");

static const struct pci_device_id pci_ids[] = {
	{ PCI_DEVICE(0x10ee, 0x8134), },
	{ PCI_DEVICE(0x10ee, 0x8138), },
	{ PCI_DEVICE(0x10ee, 0x8238), },
	{ PCI_DEVICE(0x10ee, 0x7134), },
	{ PCI_DEVICE(0x10ee, 0x7138), },
	{ PCI_DEVICE(0x10ee, 0x8438), },
	{ PCI_DEVICE(0x10ee, 0x8338), },
	{ PCI_DEVICE(0x10ee, 0x923F), },
	{ 0, }
};
MODULE_DEVICE_TABLE(pci, pci_ids);

static int instance = 0;

/* testing purposes; request interrupt on each descriptor */
#define XDMA_PERFORMANCE_TEST 0
#define FORCE_IR_DESC_COMPLETED 0

#define XDMA_DEBUG 0

/* disable debugging */
#if (XDMA_DEBUG == 0)

#define dbg_desc(...)
#define dbg_io(...)
#define dbg_perf(fmt, ...)
#define dbg_sg(...)
#define dbg_tfr(...)
#define dbg_irq(...)
#define dbg_init(...)

#else

/* descriptor, ioread/write, scatter-gather, transfer debugging */
#define dbg_desc(fmt, ...) printk(KERN_DEBUG fmt, ##__VA_ARGS__)
#define dbg_io(fmt, ...) printk(KERN_DEBUG fmt, ##__VA_ARGS__)
#define dbg_perf(fmt, ...) printk(KERN_DEBUG fmt, ##__VA_ARGS__)
#define dbg_sg(fmt, ...) printk(KERN_DEBUG fmt, ##__VA_ARGS__)
//#define dbg_tfr(fmt, ...) printk(KERN_INFO fmt, ##__VA_ARGS__)
#define dbg_irq(fmt, ...) printk(KERN_INFO fmt, ##__VA_ARGS__)
#define dbg_init(fmt, ...) printk(KERN_INFO fmt, ##__VA_ARGS__)

#define dbg_tfr(format, ...) do {					\
		printk(KERN_INFO "%s%c: " format, engine? (engine->number_in_channel? "C2H": "H2C"): "---", engine? '0' + engine->channel: '-', ##__VA_ARGS__); \
	} while(0)

#endif

#define dbg_desc(...)
#define dbg_io(...)

/* dump XDMA FPGA status during operation */
#define XDMA_STATUS_DUMPS 0

/* maximum number of bytes per transfer request */
#define XDMA_TRANSFER_MAX_BYTES (2048 * 4096)

/* maximum size of a single DMA transfer descriptor; 1<<16 = 64 KB */
#define XDMA_DESC_MAX_BYTES ((1 << 18) - 1)

/** bits of the SG DMA status register */
#define XDMA_STAT_BUSY (1UL << 0)
#define XDMA_STAT_DESCRIPTOR_STOPPED (1UL << 1)
#define XDMA_STAT_DESCRIPTOR_COMPLETED (1UL << 2)
#define XDMA_STAT_ALIGN_MISMATCH (1UL << 3)
#define XDMA_STAT_MAGIC_STOPPED (1UL << 4)
#define XDMA_STAT_FETCH_STOPPED (1UL << 5)
#define XDMA_STAT_IDLE_STOPPED (1UL << 6)
#define XDMA_STAT_READ_ERROR (0x1FUL << 9)
#define XDMA_STAT_DESCRIPTOR_ERROR (0x1FUL << 19)

/** bits of the SGDMA descriptor control field */
#define XDMA_DESC_STOP (1UL << 0)
#define XDMA_DESC_COMPLETED (1UL << 1)
#define XDMA_DESC_EOP (1UL << 4)

#define XDMA_PERF_RUN (1UL << 0)
#define XDMA_PERF_CLEAR (1UL << 1)
#define XDMA_PERF_AUTO (1UL << 2)

#define CHAR_USER 0
#define CHAR_CTRL 1
#define CHAR_EVENTS 2
#define CHAR_BYPASS 3
#define CHAR_XDMA_H2C 4
#define CHAR_XDMA_C2H 5

#define MAGIC_ENGINE 0xEEEEEEEEUL
#define MAGIC_DEVICE 0xDDDDDDDDUL
#define MAGIC_CHAR 0xCCCCCCCCUL

/* upper 16-bit of engine identifier register */
#define XDMA_ID_H2C 0x1fc0U
#define XDMA_ID_C2H 0x1fc1U

	struct config_regs {
		/* identifier 0x4 */
		u32 identifier;
		u32 reserved_1[17];
		u32 align_gran_addr;
	};

/**
 * SG DMA Controller status and control registers
 *
 * These registers make the control interface for DMA transfers.
 *
 * It sits in End Point (FPGA) memory BAR[0] for 32-bit or BAR[0:1] for 64-bit.
 * It references the first descriptor which exists in Root Complex (PC) memory.
 *
 * @note The registers must be accessed using 32-bit (PCI DWORD) read/writes,
 * and their values are in little-endian byte ordering.
 */
struct engine_regs {
	/* identifier 0x4 */
	u32 identifier;
	/* control register 0x8 */
	u32 control;
	/* control register 0xc */
	u32 control_w1s;
	/* control register 0x10 */
	u32 control_w1c;
	u32 reserved_1[12];

	/* status register { 6'h10, 2'b0 } is 0x40 */
	u32 status;
	u32 status_rc;
	/* number of completed descriptors */
	u32 completed_desc_count;
	/* alignments */
	u32 alignments;
	u32 reserved_2[12];
	u32 reserved_3[4];

	/* interrupt mask  { 6'h24, 2'b0 } is 0x90 */
	u32 interrupt_enable_mask;
	u32 interrupt_enable_mask_w1s;
	u32 interrupt_enable_mask_w1c;
        u32 reserved_4[9];

	/* interrupt mask  { 6'h30, 2'b0 } is 0xc0 */
	u32 perf_ctrl;
	u32 perf_cyc_lo;
	u32 perf_cyc_hi;
	u32 perf_dat_lo;
	u32 perf_dat_hi;
	u32 perf_pnd_lo;
	u32 perf_pnd_hi;
	//u32 completed_desc_bytes;
} __attribute__ ((packed));

struct engine_sgdma_regs {
	/* identifier 0x4 */
	u32 identifier;
	u32 reserved_1[31];

	/* bus address to first descriptor in Root Complex memory { 6'h20, 2'b0 } is 0x80 */
	u32 first_desc_lo;
	u32 first_desc_hi;
	/* number of adjacent descriptors at first_desc */
	u32 first_desc_adjacent;
} __attribute__ ((packed));

struct scratch_pad_regs{
	u32 scratch0;
	u32 scratch1;
	u32 scratch2;
	u32 scratch3;
	u32 scratch4;
	u32 scratch5;
	u32 scratch6;
	u32 scratch7;
} __attribute__ ((packed));

/* Performance counter for AXI Streaming
 */
struct performance_regs {
	/* identifier 0xc34900xx */
	u32 identifier;
	/* control register */
	u32 control;
	/* status register */
	u32 status;
	/* 64-bit period in 8 ns units (low 32-bit) */
	u32 period_low;
	/* period (high 32-bit) */
	u32 period_high;
	/* 64-bit performance counter in 8-byte units (low 32-bit) */
	u32 performance_low;
	/* performance (high 32-bit) */
	u32 performance_high;
	/* 64-bit wait counter in 8-byte units (low 32-bit) */
	u32 wait_low;
	/* wait (high 32-bit) */
	u32 wait_high;
} __attribute__ ((packed));
#define PERF_CTRL_RUN 1
#define PERF_CTRL_IE 2

#define PERF_STAT_BUSY 1
#define PERF_STAT_IRQ 2

struct interrupt_regs {
	/* identifier */
	u32 identifier;
	u32 user_int_enable;
	u32 user_int_enable_w1s;
	u32 user_int_enable_w1c;

	u32 channel_int_enable;
	u32 channel_int_enable_w1s;
	u32 channel_int_enable_w1c;
	u32 reserved_1[9];

	u32 user_int_request;
	u32 channel_int_request;
	u32 user_int_pending;
	u32 channel_int_pending;
	u32 reserved_2[12];

	u32 user_msi_vector[8];
	u32 channel_msi_vector[8];
} __attribute__ ((packed));

/* Incremental data tester
 */
struct tester_regs {
	/* identifier 0xae2300xx */
	u32 identifier;
	/* control register */
	u32 control;
	/* status register */
	u32 status;
	/* counter register */
	u32 counter;
} __attribute__ ((packed));

struct xdma_packet_generator_regs {
	u32 control;
} __attribute__ ((packed));

struct xdma_latency_tester_regs {
	u32 id;
	u32 control;
	u32 status;
	u32 delay;
	u32 data;
	u32 counter;
} __attribute__ ((packed));

/**
 * Descriptor for a single contiguous memory block transfer.
 *
 * Multiple descriptors are linked by means of the next pointer. An additional
 * extra adjacent number gives the amount of extra contiguous descriptors.
 *
 * The descriptors are in root complex memory, and the bytes in the 32-bit
 * words must be in little-endian byte ordering.
 */
struct xdma_desc {
	/* descriptor control field (0 / 0x00) */
	u32 control;
	/* number of bytes in the transfer (1 / 0x04) */
	u32 bytes;
	/* source address */
	u32 src_addr_lo;
	u32 src_addr_hi;
	/* destination address */
	u32 dst_addr_lo;
	u32 dst_addr_hi;
	/* next descriptor in the single-linked list of descriptors;
	 * this is the CIe (bus) address of the next descriptor in the
	 * root complex memory. */
	u32 next_lo;
	u32 next_hi;
} __attribute__ ((packed));

/* 32 bytes (four 32-bit words) or 64 bytes (eight 32-bit words) */
struct xdma_result {
	u32 status;
	u32 length;
	u32 reserved_1[6];
} __attribute__ ((packed));

/**
 * Describes a (SG DMA) single transfer for the engine.
 */
struct xdma_transfer {
	/* queue of non-completed transfers */
	struct list_head entry;
	/* virtual address of the first descriptor */
	struct xdma_desc *desc_virt;
	/* bus address of the first descriptor */
	dma_addr_t desc_bus;
	/* number of descriptors adjacent in memory at desc_bus address */
	int desc_adjacent;
	/* number of descriptors involved in the transfer */
	int desc_num;
	/* whether the direction of the transfer is to the device */
	int dir_to_dev;
	/* wait queue for synchronously waiting threads */
	wait_queue_head_t wq;
	/* completion buffer for asynchronous I/O, NULL if not used */
	struct kiocb *iocb;
	/* number of descriptors at desc_virt address */
	int sgl_nents;
	/* user space scatter gather mapper, NULL if not used */
	struct sg_mapping_t *sgm;
	/* user space pages were gotten? */
	int userspace;
	/* state of the transfer */
	int state;
	/* cyclic transfer? */
	int cyclic;
	/* last transfer within an I/O request? */
	int last_in_request;
	/* last transfer within an I/O request? */
	ssize_t size_of_request;
};

#define TRANSFER_STATE_NEW 0
#define TRANSFER_STATE_SUBMITTED 1
#define TRANSFER_STATE_COMPLETED 3
#define TRANSFER_STATE_FAILED 4

struct xdma_engine {
	/* MAGIC_ENGINE == 0xEEEEEEEE */
	unsigned long magic;
	/* parent device */
	struct xdma_dev *lro;

	/* engine indices */
	int channel;
	int number_in_channel;

	/* character device major:minor */
	dev_t cdevno;
	/* character device (embedded struct) */
	struct cdev cdev;

	/* protects concurrent access interrupt context */
	spinlock_t lock;
	/* remember CPU# of (last) locker */
	int prev_cpu;
	/* queue of transfers */
	struct list_head transfer_list;

#define RX_BUF_PAGES 256
	/* for AXI ST, an in-kernel transfer with cyclic descriptor list is used */
#define RX_BUF_SIZE (RX_BUF_PAGES * 4096)
	int streaming;
	u8 *rx_buffer;
	struct xdma_transfer *rx_transfer_cyclic;
	u8 *rx_result_buffer_virt;
	/* bus address */
	dma_addr_t rx_result_buffer_bus;
	/* follows the RTL */
	int rx_tail;
	/* where the application reads from */
	int rx_head;
	int rx_overrun;

	/* if set, indicates non-incremental addressing mode */
	int non_incr_addr;

	/* alignment rules for both directions dir_to_dev = { 0, 1 } */
	unsigned long addr_align;
	int len_granularity;
	int addr_bits;

	/* address offset of the engine in its BAR */
	struct engine_regs *regs;
        struct engine_sgdma_regs *sgdma_regs;
	/* direction of this engine */
	int dir_to_dev;
	/* whether the driver has started the engine */
	int running;
	/* whether the engine stopped accepting new requests */
	int shutdown;
/* engine requested to shutdown */
#define ENGINE_SHUTDOWN_REQUEST 1
/* engine has been shutdown and is idle */
#define ENGINE_SHUTDOWN_IDLE 2
/* stay idle preparing for driver unload */
#define ENGINE_SHUTDOWN_TEARDOWN 4
	/* wait queue for synchronously waiting threads */
	wait_queue_head_t shutdown_wq;
	/* last known status of device */
	u32 status;
	/* interrupt */
	u32 interrupt;

	/* the single bit mask representing the engine interrupt */
	u32 irq_bitmask;

	/* name of this engine */
	char *name;
	/* version of this engine */
	int version;
	/* descriptor prefetch capability */
	int max_extra_adj;
	/* user space scatter gather mapper */
	struct sg_mapping_t *sgm;
	/* total number of descriptors of completed transfers in this run */
	int desc_dequeued;
	/* engine service work */
	struct work_struct work;
        /* performance measurement transfer */
	struct xdma_performance_ioctl *xdma_perf;
	/* if the performance measurement transfer stopped, wake this queue,
	 * we do not want to use the transfer waitqueue because the transfer
	 * can disappear underneath us, while the engine structure remains. */
	wait_queue_head_t xdma_perf_wq;
};


struct xdma_target_bridge {
	/* 0xBBBBBBBB */
	unsigned long magic;
};

#define MAX_XDMA_DEVICES 64
static char dev_present[MAX_XDMA_DEVICES];
/*
 * device attribute
 * returns major and instance device numbers
 */
ssize_t show_device_numbers(struct device *dev, struct device_attribute *attr, char *buf) {
	struct xdma_dev *lro;
	lro = (struct xdma_dev *)dev_get_drvdata(dev);
	return snprintf(buf, PAGE_SIZE, "%d\t%d\n", lro->major, lro->instance);
}
static DEVICE_ATTR(xdma_dev_instance, S_IRUGO, show_device_numbers, NULL);

/* prototypes */
static struct xdma_transfer *transfer_create_kernel(struct xdma_dev *lro, const char *start, size_t count, u64 ep_addr, int dir_to_dev, int force_new_desc);
static void transfer_destroy(struct xdma_dev *lro, struct xdma_transfer *transfer);
static struct xdma_desc *xdma_desc_alloc(struct pci_dev *dev,
					 int number, dma_addr_t *desc_bus_p, struct xdma_desc **desc_last_p);
static void xdma_desc_link(struct xdma_desc *first, struct xdma_desc *second,
			   dma_addr_t second_bus);
static void xdma_desc_set(struct xdma_desc *desc,
			  dma_addr_t rc_bus_addr, u64 ep_addr, int len, int dir_to_dev);
static void xdma_desc_control(struct xdma_desc *first, u32 control_field);
static void xdma_desc_set_source(struct xdma_desc *desc, u64 source);

static int transfer_queue(struct xdma_engine *engine,
			  struct xdma_transfer *transfer);
static void xdma_transfer_cyclic(struct xdma_transfer *transfer);
static struct xdma_char *create_sg_char(struct xdma_dev *lro, int bar,
					struct xdma_engine *engine, int type);
static int destroy_sg_char(struct xdma_char *lro_char);
static void transfer_dump(struct xdma_transfer *transfer);
static u32 engine_status_read(struct xdma_engine *engine, int clear);

void convert_to_info(struct xdma_ioc_info2 *info2, struct xdma_ioc_info *info)
{
	info->base                  = info2->base              ;
	info->vendor                = info2->vendor            ;
	info->device                = info2->device            ;
	info->subsystem_vendor      = info2->subsystem_vendor  ;
	info->subsystem_device      = info2->subsystem_device  ;
	info->dma_engine_version    = info2->dma_engine_version;
	info->driver_version        = info2->driver_version    ;
	info->feature_id            = info2->feature_id        ;
	info->ocl_frequency         = info2->ocl_frequency[0]  ;
	info->pcie_link_width       = info2->pcie_link_width   ;
	info->pcie_link_speed       = info2->pcie_link_speed   ;
}

static void show_device_info(const struct xdma_dev *lro)
{
	struct xdma_ioc_info2 obj;
	const char *ep_name;
	u32 low;
	const struct pci_dev *pdev = lro->pci_dev;

	device_info(lro, &obj);
	ep_name = pdev->bus->name;
	printk(KERN_INFO "%s: Card %d in slot %s:%02x.%1x\n", DRV_NAME, lro->instance, ep_name,
	       PCI_SLOT(pdev->devfn), PCI_FUNC(pdev->devfn));
	printk(KERN_INFO "%s: PCIe GEN%d x %d\n", DRV_NAME, obj.pcie_link_speed, obj.pcie_link_width);
	printk(KERN_INFO "%s: OCL Frequency: %d MHz\n", DRV_NAME, obj.ocl_frequency[0]);
	if(is_multiple_clock(lro))
		printk(KERN_INFO "%s: OCL Frequency2: %d MHz\n", DRV_NAME, obj.ocl_frequency[1]);

	printk(KERN_INFO "%s: Feature ID 0x%016llx\n", DRV_NAME, obj.feature_id);
	printk(KERN_INFO "%s: MIG calibration %s\n", DRV_NAME, obj.mig_calibration ? "true" : "false");
}

static u64 find_feature_id(const struct xdma_dev *lro)
{
	u64 low = 0;
	u64 high = 0;

	low = ioread32(lro->bar[USER_BAR] + FEATURE_ID);
	high = ioread32(lro->bar[USER_BAR] + FEATURE_ID + 8);
	return low | (high << 32);
}


/*
 * Early code for LM96063
 */
static void fan_controller(const struct xdma_dev *lro)
{
	unsigned int pwm_config_reg = 0xABCDEFED;

	if (lro->pci_dev->device != 0x8238) return;

	printk(KERN_INFO "%s: TUL fan setup, Version 1.2 \n", DRV_NAME);
	iowrite32(0xa,lro->bar[USER_BAR] + AXI_I2C_SOFT_RESET);   // theepanm: we reset the AXI_I2C controller
	msleep(100);
	msleep(100);
	iowrite32(0xf,lro->bar[USER_BAR] + AXI_I2C_RX_FIFO_PIRQ); // theepanm: set interupt depth to the full 16-entries amount
	iowrite32(0x2,lro->bar[USER_BAR] + AXI_I2C_CR); 	  // theepanm: set the clear TX-FIFO bit
	iowrite32(0x0,lro->bar[USER_BAR] + AXI_I2C_CR); 	  // theepanm: undo the previous set-bit, such that TX-FIFO can resume normal operation

	iowrite32(0x1e8,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);   // theepanm: this commands selects the I2C mux as our Slave-Device, as defined by its address: 0xE8
	iowrite32(0x208,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);   // theepanm: now we configure it's control registers such that we let it know that we want to access Channel 3 (which connects to the FAN)
	iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);        // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that were previously pushed into the TX_FIFO.
	msleep(100);

	// We want to read the PWM polarity bit ...
	iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
	iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
	iowrite32(0x4a ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
	iowrite32(0x199,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x199 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Read bit
	iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue I2C Stop
	iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
	msleep(100); // we wait for the transmission bytes to go out, and for the FAN to respond by writing to our own RX_FIFO

	pwm_config_reg = ioread32(lro->bar[USER_BAR] + AXI_I2C_RX_FIFO); // theepanm: we read from the RX_FIFO and store its value into the local pwm_config_reg variable
	printk(KERN_INFO "%s: The value of the PWM CONFIG REG is: %x \n", DRV_NAME, pwm_config_reg);

	if ((0x00000010 & pwm_config_reg) != 0) return; // bit 4 is the PWM polarity bit within pwm_config_reg, so we mask all other bits
	// if the above condition is met this means that the PWM polarity bit has already been set, so we do nothing
	else {
		unsigned int max_tach_threshold = 0x2a0;
		// unsigned int config_reg = 0; // debug variable only
		unsigned int sleep_counter = 0;
		unsigned int FAN_SPIN_DOWN_TIME = 12; // this will result in roughly a 2 second delay
		unsigned int tach_value = 0;
		unsigned int tach_reg_lsb = 0; // LS Byte
		unsigned int tach_reg_msb = 0; // MS Byte

		printk(KERN_INFO "%s: We have detected that the polarity bit was NOT set previously.\n", DRV_NAME);
		// Set Fan to a high RPM value. If we're dealing with a reversed polarity board, this will actually set the fan to a low RPM, which we'll detect in the following steps to come once the
		// fan has had a second or two to actually spin down.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x4c ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x22d,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x2d)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		// Give the fan some time to physically spin down at a lower RPM if it is going to.
		for (sleep_counter = 0; sleep_counter <FAN_SPIN_DOWN_TIME; sleep_counter++)
			msleep(100);
		// The above step should have set the fan to a high RPM, if it hasn't we will soon detect this and then fix it by setting the reverse polarity bit.


		// Program the Temperature to Fan Speed Look-up-Table
		// Tmp > 0  degrees Celsius = 30%  Fan Speed
		// Tmp > 50 degrees Celsius = 50%  Fan Speed
		// Tmp > 70 degrees Celsius = 65%  Fan Speed
		// Tmp > 80 degrees Celsius = 75%  Fan Speed
		// Tmp > 90 degrees Celsius = 100% Fan Speed

		// Program the first Tmp > 0 degrees = 30% Fan Speed entry.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x50 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x00 Temperature Value)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x51 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x20E,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x0E = PWM Value 14 in decimal)
		// For debugging, we can set the first entry in the table to 100% so that we can hear the fan.
		//iowrite32(0x22E,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x0E = PWM Value 14 in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);

		// Program the first Tmp > 50 degrees = 50% Fan Speed entry.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x52 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x232,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x32 Temperature Value = 50 degrees in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x53 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x217,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x17 = PWM Value 23 in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);


		// Program the first Tmp > 70 degrees = 65% Fan Speed entry.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x54 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x246,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x46 Temperature Value = 70 degrees in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x55 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x21E,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x1E = PWM Value 30 in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);


		// Program the first Tmp > 80 degrees = 75% Fan Speed entry.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x56 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x250,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x00 Temperature Value = 80 degrees in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x57 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x223,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x23 = PWM Value 35 in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);


		// Program the first Tmp > 90 degrees = 100% Fan Speed entry.
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x58 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x25a,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x00 Temperature Value = 90 degrees in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x59 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
		iowrite32(0x22E,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x2E = PWM Value 46 in decimal)
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);

		// Ends the Programming of the Temperature to Fan RMP% Programming
		/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

		// We will now check the fan's current tachometer value ...
		// First we enable the tachometer enable bit [2] within the 0x03 CONFIGURATION REGISTER
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x03 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x03 : CONFIGURATION REGISTER
		iowrite32(0x204,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x204 Coresponds to I2C Stop + setting the tachmoeter enable bit [2] to 1 with a 0x04
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100);

		/*
		// This read was for debug purposes only.
		// Let's check to see if the Configuration Register has tachometer read enable bit set properly...
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x03 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x46 : TACHOMETER COUNT LSB
		iowrite32(0x199,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x199 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Read bit
		iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue I2C Stop
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100); // we wait for the transmission bytes to go out, and for the FAN to respond by writing to our own RX_FIFO
		config_reg = ioread32(lro->bar[USER_BAR] + AXI_I2C_RX_FIFO); // theepanm: we read from the RX_FIFO and store its value into the local tach_reg_lsb variable
		printk(KERN_INFO "%s: The value in the config reg is: %x \n", DRV_NAME, config_reg);
		*/

		// read the LSB reg first, to lock the MSB
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x46 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x46 : TACHOMETER COUNT LSB
		iowrite32(0x199,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x199 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Read bit
		iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue I2C Stop
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100); // we wait for the transmission bytes to go out, and for the FAN to respond by writing to our own RX_FIFO
		tach_reg_lsb = ioread32(lro->bar[USER_BAR] + AXI_I2C_RX_FIFO); // theepanm: we read from the RX_FIFO and store its value into the local tach_reg_lsb variable
		printk(KERN_INFO "%s: The value of tach_reg_lsb is: %x \n", DRV_NAME, tach_reg_lsb);

		// now read the MSB
		iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
		iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
		iowrite32(0x47 ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x47 : TACHOMETER COUNT MSB
		iowrite32(0x199,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x199 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Read bit
		iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue I2C Stop
		iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
		msleep(100); // we wait for the transmission bytes to go out, and for the FAN to respond by writing to our own RX_FIFO
		tach_reg_msb = ioread32(lro->bar[USER_BAR] + AXI_I2C_RX_FIFO); // theepanm: we read from the RX_FIFO and store its value into the local tach_reg_msb variable
		printk(KERN_INFO "%s: The value of tach_reg_msb is: %x \n", DRV_NAME, tach_reg_msb);

		tach_value   = tach_reg_msb;
		tach_value   = (tach_value<<8);
		printk(KERN_INFO "%s: The tach_value after an 8-bit shift to the left: %x \n", DRV_NAME, tach_value);
		tach_reg_lsb = (0x000000FF & tach_reg_lsb);   // ensure that all other bytes except the LSB is masked
		printk(KERN_INFO "%s: The value of tach_reg_lsb after masking all the upper bytes: %x \n", DRV_NAME, tach_reg_lsb);
		tach_value   = (tach_value | tach_reg_lsb);   // we should now have the last 16-bits of tach_value set to MSB + LSB
		printk(KERN_INFO "%s: The value of tach_value after ORing tach_value with tach_reg_lsb: %x \n", DRV_NAME, tach_value);
		tach_value   = (tach_value>>2);
		printk(KERN_INFO "%s: The final value of tach_value after dropping the last two bits is: %x \n", DRV_NAME, tach_value);


		if (tach_value > max_tach_threshold) {
			printk(KERN_INFO "%s: We have detected that the fan's RPM is too slow.\n", DRV_NAME);
			// Set Polarity Bit
			iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
			iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
			iowrite32(0x4a ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
			iowrite32(0x210,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte
										// In binary we are now also going to turn off bit 5 of the PWM ConFig Register (PWPGM PWM Programming Enable),
										// along with us now setting the polarity bit (i.e. 0001 0000 or 0x10).
										// Bit [5] in this register is enabled by defualt during Power-On and allows you to program the Tmp. to Fan-Speed Look-up-Table.
										// Once you've finished programming the table, and you actually want the fan controller to start using the table, you must de-set this bit.
			iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
			msleep(100);
		}
		else {
			// Just turn off the PWM Programming Enable bit, without setting the Polarity Bit
			iowrite32(0x0  ,lro->bar[USER_BAR] + AXI_I2C_CR); 	// theepanm: disables the Controller, we always do this before we push a new set of commands into the TX_FIFO
			iowrite32(0x198,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x198 Coresponds to I2C Start + the Fan's Slave-Address (7-bits hardwired) + LSB-Write bit
			iowrite32(0x4a ,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: issue the fan's register address: 0x4A : FAN PWM CONFIGURATION REGISTER
			iowrite32(0x200,lro->bar[USER_BAR] + AXI_I2C_TX_FIFO);  // theepanm: 0x230 = I2C Stop + Write-Byte (0x00)
										// We are turning off bit 5 (PWPGM: PWM Programming Enable bit) of the PWM ConFig Register.
										// Bit 5 in this register is enabled by defualt during Power-On and allows you to program the Tmp. to Fan-Speed Look-up-Table.
										// Once you've finished programming the table, and you actually want the fan controller to start using the table, you must de-set this bit.
			iowrite32(0x1  ,lro->bar[USER_BAR] + AXI_I2C_CR);       // theepanm: enables the AXI_I2C Controller, this basically kicks off the start of the transmission bytes that we just pushed into the TX_FIFO.
			msleep(100);

		}
	}
	return;
}



static void log_error_in_csr(void *target, u32 line,int type);

static int interrupt_status(struct xdma_dev *lro)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)(lro->bar[XDMA_BAR_XDMA] + XDMA_OFS_INT_CTRL);
	u32 w;
	int rc = 0;

	dbg_irq("reg = %p\n", reg);
	dbg_irq("&reg->user_int_enable = %p\n", &reg->user_int_enable);

	w = read_register(&reg->user_int_enable);
	dbg_irq("user_int_enable = 0x%08x\n", w);
	w = read_register(&reg->channel_int_enable);
	dbg_irq("channel_int_enable = 0x%08x\n", w);

	w = read_register(&reg->user_int_request);
	dbg_irq("user_int_request = 0x%08x\n", w);
	w = read_register(&reg->channel_int_request);
	dbg_irq("channel_int_request = 0x%08x\n", w);

	w = read_register(&reg->user_int_pending);
	dbg_irq("user_int_pending = 0x%08x\n", w);
	w = read_register(&reg->channel_int_pending);
	dbg_irq("channel_int_pending = 0x%08x\n", w);

	return rc;
}

bool is_ultrascale(const struct xdma_dev *lro)
{
	return (lro->pci_dev->device & 0x8000);
}

bool is_XPR(const struct xdma_dev *lro)
{
	u32 value = lro->pci_dev->subsystem_device;
	value >>= 12;
	value &= 0xf;
	return (value == 4);
}

/*
 * Sysmon is only supported in Ultrascale devices onwards..not in 7 series
 */
bool is_sysmon_supported(const struct xdma_dev *lro)
{
	u16 series = lro->pci_dev->device;
	u16 dsanum = lro->pci_dev->subsystem_device;
	series >>= 12;
	series &= 0xf;
	dsanum &= 0xff;
	printk(KERN_DEBUG "SYSMON: Series: %u, dsanum: 0x%x.\n", series, dsanum);
	return (series > 7) && (dsanum >= 0x32);
}

bool is_multiple_clock(const struct xdma_dev *lro) {
	if (lro->pci_dev->device != 0x8238)
		return false;
	if ((lro->pci_dev->subsystem_device & 0xff00) != 0x4400)
		return false;
	return ((lro->pci_dev->subsystem_device & 0xff) >= 0x31);
}

/* interrupts_enable -- Enable the interrupts we are interested in
 * @TODO use the w1s feature */
int interrupts_enable(struct xdma_dev *lro, int interrupts_offset, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)(lro->bar[XDMA_BAR_XDMA] + XDMA_OFS_INT_CTRL);

	/* implementation with W1S register */
	write_register(mask, &reg->channel_int_enable_w1s);

	return 0;
}

/* interrupts_disable -- Disable the interrupts we are no longer interested in
 * @TODO use the w1c feature */
static int interrupts_disable(struct xdma_dev *lro, int interrupts_offset, u32 mask)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)(lro->bar[XDMA_BAR_XDMA] + XDMA_OFS_INT_CTRL);

	/* implementation with W1C register */
	write_register(mask, &reg->channel_int_enable_w1c);

	return 0;
}

/* read_interrupts -- Print the interrupt controller status */
static u32 read_interrupts(struct xdma_dev *lro, int interrupts_offset)
{
	struct interrupt_regs *reg = (struct interrupt_regs *)(lro->bar[XDMA_BAR_XDMA] + XDMA_OFS_INT_CTRL);
	u32 r;
	u32 w;

	/* extra debugging; inspect complete engine set of registers */
	w = read_register(&reg->user_int_request);
	/* return user interrupts in upper 16-bits */
	r = (w & 0xffffU) << 16;
	dbg_io("ioread32(0x%p) returned 0x%08x (user_int_request).\n", &reg->user_int_request, w);
	w = read_register(&reg->channel_int_request);
	/* return user interrupts in lower 16-bits */
	r |= (w & 0xffffU);
	/* return user interrupts in upper 16-bits */
	dbg_io("ioread32(0x%p) returned 0x%08x (channel_int_request)\n", &reg->channel_int_request, w);

	return r;
}

static void *rvmalloc(unsigned long size)
{
	void *mem;
	unsigned long adr;

	size = PAGE_ALIGN(size);
	mem = vmalloc_32(size);
	if (!mem)
		return NULL;

	adr = (unsigned long)mem;
	while (size > 0) {
		SetPageReserved(vmalloc_to_page((void *)adr));
		adr += PAGE_SIZE;
		size -= PAGE_SIZE;
	}
	return mem;
}

/* free reserved vmalloc()ed memory */
static void rvfree(void *mem, unsigned long size)
{
	unsigned long adr;
	if (!mem)
		return;
	adr = (unsigned long)mem;
	while ((long) size > 0) {
		ClearPageReserved(vmalloc_to_page((void *)adr));
		adr += PAGE_SIZE;
		size -= PAGE_SIZE;
	}
	vfree(mem);
}

static struct xdma_char *create_sg_char(struct xdma_dev *lro, int bar,
					struct xdma_engine *engine, int type);
static int destroy_sg_char(struct xdma_char *lro_char);

static int xdma_performance_submit(struct xdma_dev *lro, struct xdma_engine *engine)
{
	u8 *buffer_virt;
	/* bus address */
	dma_addr_t buffer_bus;
	struct xdma_transfer *transfer;
	u64 ep_addr = 0;
	int size= engine->xdma_perf->transfer_size;
	buffer_virt = pci_alloc_consistent(lro->pci_dev, size, &buffer_bus);
	//printk(KERN_DEBUG "buffer_virt = %p\n", buffer_virt);

	/* allocate transfer data structure */
	transfer = kzalloc(sizeof(struct xdma_transfer), GFP_KERNEL);
	BUG_ON(!transfer);
	/* 0 = write engine (to_dev=0) , 1 = read engine (to_dev=1) */
	transfer->dir_to_dev = engine->dir_to_dev;
	/* set number of descriptors */
	transfer->desc_num = 1;
	/* allocate descriptor list */
	transfer->desc_virt = xdma_desc_alloc(lro->pci_dev,
					      transfer->desc_num, &transfer->desc_bus, NULL);
	BUG_ON(!transfer->desc_virt);
	/* fill in descriptor entry with transfer details */
	xdma_desc_set(transfer->desc_virt, buffer_bus,
		      ep_addr, size, engine->dir_to_dev);
	/* stop engine and request interrupt on last descriptor */
	xdma_desc_control(transfer->desc_virt, 0 /* | XDMA_DESC_COMPLETED | XDMA_DESC_STOP */);
	/* create a linked loop */
	xdma_desc_link(transfer->desc_virt, transfer->desc_virt, transfer->desc_bus);
	transfer->cyclic = 1;
	/* dump transfer for debugging */
	transfer_dump(transfer);
	/* initialize wait queue */
	init_waitqueue_head(&transfer->wq);

	dbg_perf("Queueing XDMA I/O %s request for performance measurement.\n",
		 engine->dir_to_dev? "write (to device)" : "read (from device)");
	transfer_queue(engine, transfer);
	return 0;
}


/**
 * engine_status_read() - read status of SG DMA engine (optionally reset)
 *
 * Stores status in engine->status.
 *
 * @return -1 on failure, status register otherwise
 */
static u32 engine_status_read(struct xdma_engine *engine, int clear)
{
	u32 value, w, desc_completed;
	BUG_ON(!engine);

#if XDMA_STATUS_DUMPS
	dbg_tfr("ioread32(0x%p).\n", &engine->regs->identifier);
	w = read_register(&engine->regs->identifier);
	dbg_tfr("ioread32(0x%p) returned 0x%08x.\n", &engine->regs->identifier, w);
	w &= 0xfff00000UL;
	if (w != 0x1fc00000UL) {
		printk(KERN_ERR "engine identifier not found (found 0x%08x expected 0xad4bXX01).\n", w);
		value = 0xffffffff;
		goto fail_identifier;
	}
	/* extra debugging; inspect complete engine set of registers */
	w = read_register(&engine->regs->status);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (status).\n", &engine->regs->status, w);
	w = read_register(&engine->regs->control);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (control)\n", &engine->regs->control, w);
	w = read_register(&engine->sgdma_regs->first_desc_lo);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (first_desc_lo)\n", &engine->sgdma_regs->first_desc_lo, w);
	w = read_register(&engine->sgdma_regs->first_desc_hi);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (first_desc_hi)\n", &engine->sgdma_regs->first_desc_hi, w);
	w = read_register(&engine->sgdma_regs->first_desc_adjacent);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (first_desc_adjacent).\n", &engine->sgdma_regs->first_desc_adjacent, w);
	w = read_register(&engine->regs->completed_desc_count);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (completed_desc_count).\n", &engine->regs->completed_desc_count, w);
	w = read_register(&engine->regs->interrupt_enable_mask);
	dbg_tfr("ioread32(0x%p) returned 0x%08x (interrupt_enable_mask)\n", &engine->regs->interrupt_enable_mask, w);
#endif

	/* read status register */
	dbg_tfr("Status of SG DMA %s engine:\n", engine->name);
	dbg_tfr("ioread32(0x%p).\n", &engine->regs->status);
        if (clear) {
		value = engine->status = read_register(&engine->regs->status_rc);
	} else {
		value = engine->status = read_register(&engine->regs->status);
	}
	dbg_tfr("status = 0x%08x: %s%s%s%s%s%s%s%s%s\n", (u32)engine->status,
		(value & XDMA_STAT_BUSY) ? "BUSY ": "IDLE ",
		(value & XDMA_STAT_DESCRIPTOR_STOPPED) ? "DESCRIPTOR_STOPPED ": "",
		(value & XDMA_STAT_DESCRIPTOR_COMPLETED) ? "DESCRIPTOR_COMPLETED ": "",
                (value & XDMA_STAT_ALIGN_MISMATCH) ? "ALIGN_MISMATCH ": "",
		(value & XDMA_STAT_MAGIC_STOPPED) ? "MAGIC_STOPPED ": "",
		(value & XDMA_STAT_FETCH_STOPPED) ? "FETCH_STOPPED ": "",
                (value & XDMA_STAT_READ_ERROR) ? "READ_ERROR ": "",
		(value & XDMA_STAT_DESCRIPTOR_ERROR) ? "DESCRIPTOR_ERROR ": "",
		(value & XDMA_STAT_IDLE_STOPPED) ? "IDLE_STOPPED ": "");

	if (value & XDMA_STAT_BUSY) {
		/* read number of completed descriptors after engine start */
		desc_completed = read_register(&engine->regs->completed_desc_count);
		dbg_tfr("desc_completed = %d\n", desc_completed);
	}
fail_identifier:
	return value;
}

/**
 * xdma_engine_stop() - stop an SG DMA engine
 *
 */
static void xdma_engine_stop(struct xdma_engine *engine)
{
	u32 w;

	dbg_tfr("xdma_engine_stop(engine=%p)\n", engine);
	BUG_ON(!engine);

	w = (u32)XDMA_CTRL_IE_DESCRIPTOR_STOPPED;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_COMPLETED;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH;
	w |= (u32)XDMA_CTRL_IE_MAGIC_STOPPED;

	// Disable IDLE STOPPED for MM
	if((engine->streaming && (engine->dir_to_dev==0))|| (engine->xdma_perf)){
		w |= (u32)XDMA_CTRL_IE_IDLE_STOPPED;
	}
	w |= (u32)XDMA_CTRL_IE_READ_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_ERROR;
	dbg_tfr("Stopping SG DMA %s engine; writing 0x%08x to 0x%p.\n",
		engine->name, w, (u32 *)&engine->regs->control);
	write_register(w, &engine->regs->control);

	dbg_tfr("xdma_engine_stop(%s) done\n", engine->name);
}

/**
 * engine_cyclic_stop() - stop a cyclic transfer running on an SG DMA engine
 *
 * engine->lock must be taken
 */
static struct xdma_transfer *engine_cyclic_stop(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer = 0;

	/* transfers on queue? */
	if (!list_empty(&engine->transfer_list)) {
		/* pick first transfer on the queue (was submitted to the engine) */
		transfer = list_entry(engine->transfer_list.next, struct xdma_transfer, entry);
		BUG_ON(!transfer);

		xdma_engine_stop(engine);

		if (transfer->cyclic) {
			if (engine->xdma_perf)
				dbg_perf("Stopping cyclic performance transfer on %s engine\n", engine->name);
			else
				printk(KERN_DEBUG "Stopping cyclic transfer on %s engine\n", engine->name);
			/* make sure the service handler sees the correct transfer state */
			transfer->cyclic = 1;
			/* set STOP flag and interrupt on completion, on the last descriptor */
			xdma_desc_control(transfer->desc_virt + transfer->desc_num - 1, XDMA_DESC_COMPLETED | XDMA_DESC_STOP);
		} else {
			printk(KERN_DEBUG "engine_cyclic_stop(engine=%p) running transfer is not cyclic, calling xdma_engine_stop()\n", engine);
		}
	} else {
		printk(KERN_DEBUG "engine_cyclic_stop(engine=%p) found no running transfer.\n", engine);
	}
	return transfer;
}

/**
 * engine_cyclic_stop() - stop a cyclic transfer running on an SG DMA engine
 *
 * engine_shutdown -- request engine comes to full stop */
static void engine_shutdown(struct xdma_engine *engine)
{
	/* lock the engine */
	spin_lock(&engine->lock);
	/* make sure engine goes full stop */
	engine->shutdown |= ENGINE_SHUTDOWN_REQUEST;
	/* unlock the engine */
	spin_unlock(&engine->lock);
}

static void engine_teardown(struct xdma_engine *engine)
{
	/* lock the engine */
	spin_lock(&engine->lock);
	/* make sure engine does not start again */
	engine->shutdown |= ENGINE_SHUTDOWN_REQUEST | ENGINE_SHUTDOWN_TEARDOWN;
	/* unlock the engine */
	spin_unlock(&engine->lock);
}

static void engine_enable(struct xdma_engine *engine)
{
	/* lock the engine */
	spin_lock(&engine->lock);
	engine->shutdown = 0;
	/* unlock the engine */
	spin_unlock(&engine->lock);
}

/* obtain the 32 most significant (high) bits of a 32-bit or 64-bit address */
#define pci_dma_h(addr) ((addr >> 16) >> 16)
/* obtain the 32 least significant (low) bits of a 32-bit or 64-bit address */
#define pci_dma_l(addr) (addr & 0xffffffffUL)

/**
 * engine_start() - start an idle engine with its first transfer on queue
 *
 * The engine will run and process all transfers that are queued using
 * transfer_queue() and thus have their descriptor lists chained.
 *
 * During the run, new transfers will be processed if transfer_queue() has
 * chained the descriptors before the hardware fetches the last descriptor.
 * A transfer that was chained too late will invoke a new run of the engine
 * initiated from the engine_service() routine.
 *
 * The engine must be idle and at least one transfer must be queued.
 * This function does not take locks; the engine spinlock must already be taken.
 *
 */
static struct xdma_transfer *engine_start(struct xdma_engine *engine)
{
	struct xdma_transfer *transfer;
	u32 w;
	int extra_adj = 0;
	/* engine must be idle */
	BUG_ON(engine->running);
	/* engine transfer queue must not be empty */
	BUG_ON(list_empty(&engine->transfer_list));
	/* inspect first transfer queued on the engine */
	transfer = list_entry(engine->transfer_list.next,
			      struct xdma_transfer, entry);
	BUG_ON(!transfer);

	/* engine is no longer shutdown */
	engine->shutdown = 0;

	dbg_tfr("engine_start(%s): transfer=0x%p.\n", engine->name, transfer);
	/* XXX make sure bus address in within 4GB address space XXX */
	WARN_ON((transfer->desc_bus >> 16) >> 16);
	/* write bus address of first descriptor in Root Complex memory */
	w = (u32)transfer->desc_bus;

	/* initialize number of descriptors of dequeued transfers */
	engine->desc_dequeued = 0;

	/* write lower 32-bit of bus address of transfer first descriptor */
	w = cpu_to_le32(pci_dma_l(transfer->desc_bus));
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_lo)\n", w,
		(void *)&engine->sgdma_regs->first_desc_lo);
	write_register(w, &engine->sgdma_regs->first_desc_lo);
	/* write upper 32-bit of bus address of transfer first descriptor */
	w = cpu_to_le32(pci_dma_h(transfer->desc_bus));
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_hi)\n", w,
		(void *)&engine->sgdma_regs->first_desc_hi);
	write_register(w, &engine->sgdma_regs->first_desc_hi);

	if (transfer->desc_adjacent > 0) {
		extra_adj = transfer->desc_adjacent - 1;
		if (extra_adj > MAX_EXTRA_ADJ)
			extra_adj = MAX_EXTRA_ADJ;
	}
	dbg_tfr("iowrite32(0x%08x to 0x%p) (first_desc_adjacent)\n",
		extra_adj, (void *)&engine->sgdma_regs->first_desc_adjacent);
	write_register(extra_adj, &engine->sgdma_regs->first_desc_adjacent);

	dbg_tfr("ioread32(0x%p) (dummy read flushes writes).\n", &engine->regs->status);

	mmiowb();

        if (engine->xdma_perf) {
		write_register(XDMA_CTRL_IE_DESCRIPTOR_STOPPED |
			       XDMA_CTRL_IE_DESCRIPTOR_COMPLETED |
			       XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH |
			       XDMA_CTRL_IE_MAGIC_STOPPED |
			       // Disable IDLE_STOPPED
			       XDMA_CTRL_IE_IDLE_STOPPED |
			       XDMA_CTRL_IE_READ_ERROR |
			       XDMA_CTRL_IE_DESCRIPTOR_ERROR, &engine->regs->interrupt_enable_mask);
	}

	/* write control register of SG DMA engine */
	w = (u32)XDMA_CTRL_RUN_STOP;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_STOPPED;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_COMPLETED;
        w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH;
	w |= (u32)XDMA_CTRL_IE_MAGIC_STOPPED;

	/* enable IE_IDLE_STOP only for AXI ST C2H */
	if ((engine->streaming && !engine->dir_to_dev)|| (engine->xdma_perf)) {
		w |= (u32)XDMA_CTRL_IE_IDLE_STOPPED;
	}
	/* set non-incremental addressing mode */
	if (engine->non_incr_addr) {
		w |= (u32)XDMA_CTRL_NON_INCR_ADDR;
	}
	w |= (u32)XDMA_CTRL_IE_READ_ERROR;
	w |= (u32)XDMA_CTRL_IE_DESCRIPTOR_ERROR;

	dbg_tfr("iowrite32(0x%08x to 0x%p) (control)\n", w,
		(void *)&engine->regs->control);
	/* start the engine */
	write_register(w, &engine->regs->control);

#if XDMA_STATUS_DUMPS
	/* read status register and report */
	engine_status_read(engine, 0);
#else
	/* dummy read of status register to flush all previous writes */
	w = read_register(&engine->regs->status);
	dbg_tfr("ioread32(0x%p) = 0x%lx (dummy read flushes writes).\n",
		&engine->regs->status, (unsigned long)w);
#endif
	dbg_tfr("%s engine 0x%p now running\n", engine->name, engine);
	/* remember the engine is running */
	engine->running = 1;
	return transfer;
}

//SD_Accel Specific
/* engine_initialize -- Initialize the engine for use, read capabilities */
static int engine_initialize(struct xdma_dev *lro, int interrupts_offset)
{
	void *reg = lro->bar[XDMA_BAR_XDMA] + interrupts_offset;
	u32 w;
	int rc = 0;
	printk(KERN_DEBUG "Read register at BAR %d, address 0x%p.\n", XDMA_BAR_XDMA, reg);
	w = read_register(reg + 0x00);
	/* not a write nor a read engine found? */
	if (((w & 0x00ffff00UL) != 0x00c10000UL) && ((w & 0x00ffff00UL) != 0x00c20000UL)) {
		printk(KERN_DEBUG "Engine identifier not found (found 0x%08x expected 0xC100/0xC200).\n", w);
		rc = -1;
		goto fail_identifier;
	}
	printk(KERN_DEBUG "Engine identifier found 0x%08x with version %u.\n", w, w & 0xffU);

	/* before version 2, 64-bit DMA is not available */
	if ((w & 0xffUL) < 2UL) lro->capabilities &= ~(CAP_64BIT_DMA | CAP_64BIT_DESC);
	/* clear all interrupt event enables, stop engine */
	w = 0x0UL;
	printk(KERN_DEBUG "Set engine controller enable mask: 0x%08x.\n", w);
	write_register(w, reg + 0x04);

fail_identifier:
	return rc;
}

//SD_Accel Specific
static int engine_version(struct xdma_dev *lro, int engine_offset)
{
	void *reg = lro->bar[XDMA_BAR_XDMA] + engine_offset;
	u32 w;
	int rc = 0;

	w = read_register(reg + 0x00);
	/* not a write nor a read engine found? */
	if (((w & 0x00ffff00UL) != 0x00c10000UL) && ((w & 0x00ffff00UL) != 0x00c20000UL)) {
		printk(KERN_DEBUG "Engine identifier not found (found 0x%08x expected 0xC100/0xC200).\n", w);
		rc = -1;
		goto fail_identifier;
	}
	/* engine version */
	rc = w & 0xff;

fail_identifier:
	return rc;
}

/* must be called with engine->lock already acquired */
static int engine_service_cyclic(struct xdma_engine *engine)
{
	struct xdma_result *result;
	int eop_count = 0;
	int start;

	printk(KERN_INFO "engine_service_cyclic()");

	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	result = (struct xdma_result *)engine->rx_result_buffer_virt;
	BUG_ON(!result);

	/* read status register */
	engine_status_read(engine, 1);

	/* where we start receiving in the ring buffer */
	start = engine->rx_tail;

	dbg_tfr("result[engine->rx_tail=%3d].status = 0x%08x, rx->length = %d\n",
		engine->rx_tail, (int)result[engine->rx_tail].status, (int)result[engine->rx_tail].length);

	/* iterate through all newly received RX result descriptors */
	while (result[engine->rx_tail].status) {
		/* EOP bit set in result? */
		if (result[engine->rx_tail].status & RX_STATUS_EOP) {
			eop_count++;
		}
		dbg_tfr("result[engine->rx_tail=%3d].status = 0x%08x, rx->length = %d\n",
			engine->rx_tail, (int)result[engine->rx_tail].status, (int)result[engine->rx_tail].length);
		/* increment tail pointer */
		engine->rx_tail = (engine->rx_tail + 1) % RX_BUF_PAGES;
		/* overrun? */
		if (engine->rx_tail == engine->rx_head) {
			dbg_tfr("engine_service_cyclic(): overrun\n");
			/* flag to user space that overrun has occured */
			engine->rx_overrun = 1;
			/* proceed the head pointer, skip to the last known-good point where new
			 * packets may arrive, from previous iteration */
			while (engine->rx_head != start) {
				/* clear result */
				result[engine->rx_head].status = 0;
				result[engine->rx_head].length = 0;
				/* proceed head pointer so we make progress, even when faulty */
				engine->rx_head = (engine->rx_head + 1) % RX_BUF_PAGES;
			}
		}
	}
	/* wake any reader on EOP, as one or more packets are now in the RX buffer */
	if (eop_count > 0) {
		dbg_tfr("engine_service_cyclic(): wake_up_interruptible() due to %d EOP's\n", eop_count);
		/* awake task on transfer's wait queue */
		wake_up_interruptible(&engine->rx_transfer_cyclic->wq);
	}
	/* engine was running but is no longer busy? */
	if (!(engine->status & XDMA_STAT_BUSY) && engine->running) {
		/* transfers on queue? */
		if (!list_empty(&engine->transfer_list)) {
			struct xdma_transfer *transfer;
			/* pick first transfer on the queue (was submitted to the engine) */
			transfer = list_entry(engine->transfer_list.next,
					      struct xdma_transfer, entry);
			BUG_ON(!transfer);
			BUG_ON(transfer != engine->rx_transfer_cyclic);
			dbg_tfr("%s engine completed cyclic transfer 0x%p (%d desc).\n",
				engine->name, transfer, transfer->desc_num);
			/* remove completed transfer from list */
			list_del(engine->transfer_list.next);
		}
		/* if the engine stopped with RUN still asserted, de-assert RUN now */
		dbg_tfr("engine_service_cyclic(): engine just went idle, resetting RUN_STOP.\n");
		xdma_engine_stop(engine);
		engine->running = 0;
		/* awake task on engine's shutdown wait queue */
		wake_up_interruptible(&engine->shutdown_wq);
	}
	return 0;
}

/**
 * engine_service() - service an SG DMA engine
 *
 * must be called with engine->lock already acquired
 *
 * @engine pointer to struct xdma_engine
 *
 */
static int engine_service(struct xdma_engine *engine)
{
	u32 desc_completed;
	struct xdma_transfer *transfer = 0, *transfer_started;
	int lock_contended = spin_is_locked(&engine->lock);
	int cpu;

    	/* determine current cpu */
	cpu = get_cpu();
	put_cpu();

	/* engine was not started by the driver? */
	if (!engine->running) {
		engine->prev_cpu = cpu;
		dbg_tfr("service() engine was not running, Clearing status.\n");
		engine_status_read(engine, 1);
		return 0;
	}

	dbg_tfr("service() got lock\n");

	dbg_tfr("service(): spinlock was %scontended, previous owner cpu #%d, this cpu #%d.\n",
		lock_contended?"":"not ", engine->prev_cpu, cpu);

	/* read-clear status register */
	engine_status_read(engine, 1);

	/* engine was running but is no longer busy? */
	if (engine->running && !(engine->status & XDMA_STAT_BUSY)) {
		dbg_tfr("service(): engine just went idle, resetting RUN_STOP.\n");
		xdma_engine_stop(engine);
		engine->running = 0;
                /* awake task on engine's shutdown wait queue */
		wake_up_interruptible(&engine->shutdown_wq);
	}

#define XDMA_STAT (XDMA_STAT_BUSY |			\
		   XDMA_STAT_DESCRIPTOR_COMPLETED |	\
		   XDMA_STAT_DESCRIPTOR_STOPPED |	\
		   XDMA_STAT_MAGIC_STOPPED)
			/* engine event which can forward our work? */
			if (engine->status & (XDMA_STAT_DESCRIPTOR_COMPLETED |
					      XDMA_STAT_DESCRIPTOR_STOPPED | XDMA_STAT_MAGIC_STOPPED |
					      XDMA_STAT_IDLE_STOPPED |
					      XDMA_STAT_READ_ERROR |
					      XDMA_STAT_DESCRIPTOR_ERROR |
					      XDMA_STAT_ALIGN_MISMATCH)) {
				if (engine->status & (XDMA_STAT_READ_ERROR | XDMA_STAT_DESCRIPTOR_ERROR | XDMA_STAT_ALIGN_MISMATCH)) {
					printk(KERN_DEBUG "engine_service(): ERROR was found in channel=%08x, status = %08x",
					       engine->channel, engine->status);
				}

					/* read number of completed descriptors after engine start */
					desc_completed = read_register(&engine->regs->completed_desc_count);
					dbg_tfr("engine->regs->completed_desc_count = %d\n", desc_completed);

					/* transfers on queue? */
					if (!list_empty(&engine->transfer_list)) {
						/* pick first transfer on the queue (was submitted to the engine) */
						transfer = list_entry(engine->transfer_list.next,
								      struct xdma_transfer, entry);
						dbg_tfr("head of queue transfer 0x%p has %d descriptors, engine completed %d desc, %d not yet dequeued.\n",
							transfer, (int)transfer->desc_num, (int)desc_completed, (int)desc_completed - engine->desc_dequeued);

						/* performance measurement is running? */
						if (engine->xdma_perf) {
							/* a descriptor was completed? */
							if (engine->status & XDMA_STAT_DESCRIPTOR_COMPLETED) {
								engine->xdma_perf->iterations = desc_completed;
								dbg_perf("transfer->xdma_perf->iterations = %d\n", engine->xdma_perf->iterations);
							}
							/* a descriptor stopped the engine? */
							if (engine->status & XDMA_STAT_DESCRIPTOR_STOPPED) {
								engine->xdma_perf->stopped = 1;
								/* wake any XDMA_PERF_IOCTL_STOP waiting for the performance run to finish */
								wake_up_interruptible(&engine->xdma_perf_wq);
								dbg_perf("transfer->xdma_perf stopped and woken up\n");
							}
						}
					} else {
						dbg_tfr("no transfers on queue, but engine completed %d descriptors?!\n",
							(int)desc_completed);
					}

					/* account for already dequeued transfers during this engine run */
					desc_completed -= engine->desc_dequeued;

					/* iterate over all the transfers completed by the engine,
					 * except for the last (i.e. use > instead of >=). */
					while (transfer && (!transfer->cyclic) &&
					       (desc_completed > transfer->desc_num)) {
						/* remove this transfer from desc_completed */
						desc_completed -= transfer->desc_num;
						dbg_tfr("%s engine completed non-cyclic transfer 0x%p (%d desc).\n",
							engine->name, transfer, transfer->desc_num);
						/* remove completed transfer from list */
						list_del(engine->transfer_list.next);
						/* add to dequeued number of descriptors during this run */
						engine->desc_dequeued += transfer->desc_num;
						/* mark transfer as succesfully completed */
						transfer->state = TRANSFER_STATE_COMPLETED;
						/* asynchronous I/O? */
						if ((transfer->iocb) && (transfer->last_in_request)) {
							struct kiocb *iocb = transfer->iocb;
							ssize_t done = transfer->size_of_request;
							dbg_tfr("Freeing (async I/O request) last transfer %p, iocb %p\n", transfer, transfer->iocb);
							transfer_destroy(engine->lro, transfer);
							transfer = NULL;
							dbg_tfr("Completing async I/O iocb %p with size %d\n", iocb, (int)done);
							/* indicate I/O completion XXX res, res2 */
#if defined(XDMA_NEW_AIO)
							iocb->ki_complete(iocb, done, 0);
#else
							aio_complete(iocb, done, 0);
#endif

							/* synchronous I/O? */
						} else {
							/* awake task on transfer's wait queue */
							wake_up_interruptible(&transfer->wq);
						}
						/* if exists, get the next transfer on the list */
						if (!list_empty(&engine->transfer_list)) {
							transfer = list_entry(engine->transfer_list.next,
									      struct xdma_transfer, entry);
							printk(KERN_DEBUG "Non-completed transfer %p\n", transfer);
							/* no further transfers? */
						} else {
							transfer = NULL;
						}
					}
					/* inspect the current transfer */
					if (transfer) {
						/* engine stopped? (i.e. not busy and stop reason known? */
						if (((engine->status & XDMA_STAT_BUSY) == 0) &&
						    (engine->status & (XDMA_STAT_MAGIC_STOPPED |
								       XDMA_STAT_DESCRIPTOR_STOPPED |
								       XDMA_STAT_IDLE_STOPPED |
								       XDMA_STAT_ALIGN_MISMATCH |
								       XDMA_STAT_READ_ERROR |
								       XDMA_STAT_DESCRIPTOR_ERROR))) {
					dbg_tfr("running %s engine has stopped\n", engine->name);
											    }

/* the engine still working on current transfer? */
if (engine->status & XDMA_STAT_BUSY) {
	dbg_tfr("running %s engine was %d descriptors into transfer 0x%p (with %d desc)\n",
		engine->name, desc_completed, transfer, transfer->desc_num);
	/* engine has stopped  */
} else {
	/* the engine failed on current transfer? */
	if (engine->status & (XDMA_STAT_MAGIC_STOPPED | XDMA_STAT_ALIGN_MISMATCH | XDMA_STAT_READ_ERROR | XDMA_STAT_DESCRIPTOR_ERROR))  {
		dbg_tfr("aborted %s engine was %d descriptors into transfer 0x%p (with %d desc) status= %d\n",
			engine->name, desc_completed, transfer, transfer->desc_num, engine->status);
		/* mark transfer as succesfully completed */
		transfer->state = TRANSFER_STATE_FAILED;
		xdma_engine_stop(engine);
		/* the engine stopped on current transfer? */
	} else {
		if (desc_completed < transfer->desc_num) {
			transfer->state = TRANSFER_STATE_FAILED;
			printk(KERN_DEBUG "Engine stopped half-way transfer %p\n", transfer);
		} else {
			dbg_tfr("stopped %s engine completed transfer 0x%p (%d desc), desc_completed = %d\n",
				engine->name, transfer, transfer->desc_num, desc_completed);
			if (!transfer->cyclic) {
				/* if the engine stopped on this transfer, it should be the last */
				WARN_ON(desc_completed > transfer->desc_num);
			}
			/* mark transfer as succesfully completed */
			transfer->state = TRANSFER_STATE_COMPLETED;
		}
	}
	/* remove completed transfer from list */
	list_del(engine->transfer_list.next);
	/* add to dequeued number of descriptors during this run */
	engine->desc_dequeued += transfer->desc_num;
	/* asynchronous I/O? */
	if ((transfer->iocb) && (transfer->last_in_request)) {
		struct kiocb *iocb = transfer->iocb;
		ssize_t done = transfer->size_of_request;
		dbg_tfr("Freeing (async I/O request) last transfer %p, iocb %p\n", transfer, transfer->iocb);
		transfer_destroy(engine->lro, transfer);
		transfer = NULL;
		dbg_tfr("Completing async I/O iocb %p with size %d\n", iocb, (int)done);
		/* indicate I/O completion XXX res, res2 */
#if defined(XDMA_NEW_AIO)
		iocb->ki_complete(iocb, done, 0);
#else
		aio_complete(iocb, done, 0);
#endif
		/* synchronous I/O? */
	} else {
		/* awake task on transfer's wait queue */
		wake_up_interruptible(&transfer->wq);
	}
}
}
/* engine stopped? */
if (!engine->running) {
	/* engine was requested to be shutdown? */
	if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
		engine->shutdown |= ENGINE_SHUTDOWN_IDLE;
		/* awake task on engine's shutdown wait queue */
		wake_up_interruptible(&engine->shutdown_wq);
		/* more pending transfers? */
	} else if (!list_empty(&engine->transfer_list)) {
		/* (re)start engine */
		transfer_started = engine_start(engine);
		dbg_tfr("re-started %s engine with pending transfer 0x%p\n",
			engine->name, transfer_started);
	} else {
		dbg_tfr("no pending transfers, %s engine remains idle.\n", engine->name);
	}
	/* engine is still running? */
} else {
	if (list_empty(&engine->transfer_list)) {
		dbg_tfr("no transfers on queue but %s engine is running?! cyclic?!\n", engine->name);
		WARN_ON(1);
	}
}
/* engine did not complete a transfer */
} else {
	  dbg_tfr("%s engine triggered unknown interrupt 0x%08x\n", engine->name, engine->status);
  }
/* remember last lock holder */
engine->prev_cpu = cpu;
return 0;
}

/* engine_service_work */
static void engine_service_work(struct work_struct *work)
{
	struct xdma_engine *engine;
	engine = container_of(work, struct xdma_engine, work);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	/* lock the engine */
	spin_lock(&engine->lock);
	/* C2H streaming? */
	if (engine->rx_transfer_cyclic) {
		printk(KERN_INFO "engine_service_cyclic() for %s engine %p\n", engine->name, engine);
		engine_service_cyclic(engine);
		/* no C2H streaming, default */
	} else {
		dbg_tfr("engine_service_work() for %s engine %p\n", engine->name, engine);
		engine_service(engine);
	}
	/* re-enable interrupts for this engine */
	interrupts_enable(engine->lro, XDMA_OFS_INT_CTRL, engine->irq_bitmask);
	/* unlock the engine */
	spin_unlock(&engine->lock);
}

/*
 * xdma_isr() - Interrupt handler
 *
 * @dev_id pointer to xdma_dev
 */
static irqreturn_t xdma_isr(int irq, void *dev_id)
{
	u32 ch_irq;
	u32 user_irq;
	struct xdma_dev *lro;
	struct interrupt_regs *irq_regs;
	int dir_from_dev;
	unsigned long flags;
	dbg_irq("xdma_isr(irq=%d) <<<<<<<<<<<<<<<< INTERRUPT SERVICE ROUTINE\n", irq);
	BUG_ON(!dev_id);
	lro = (struct xdma_dev *)dev_id;
	if (!lro) {
		WARN_ON(!lro);
		printk(KERN_DEBUG "xdma_isr(irq=%d) lro=%p ??\n", irq, lro);
		return IRQ_NONE;
	}
	irq_regs = (struct interrupt_regs *)(lro->bar[XDMA_BAR_XDMA] + XDMA_OFS_INT_CTRL);

	/* read channel interrupt requests */
	ch_irq = read_register(&irq_regs->channel_int_request);
	dbg_irq("read_interrupts() = 0x%08x\n", ch_irq);

	/* disable all interrupts that fired; these are re-enabled individually
	 * after the causing module has been fully serviced.
	 * note: this write has to be flushed, done with read below */
	write_register(ch_irq, &irq_regs->channel_int_enable_w1c);
	//interrupts_disable(lro, XDMA_OFS_INT_CTRL, ch_irq);

	/* read user interrupts */
	/* flushes previous write */
	user_irq = read_register(&irq_regs->user_int_request);

	/* iterate over H2C (PCIe read), then C2H (PCIe write) */
	for (dir_from_dev = 0; dir_from_dev < 2; dir_from_dev++) {
		int dir_to_dev = !dir_from_dev;
		int channel;
		/* iterate over channels */
		for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
                        struct xdma_engine *engine = lro->engine[channel][dir_from_dev];
			/* engine present and its interrupt fired? */
			if (engine && (engine->irq_bitmask & ch_irq)) {
				dbg_tfr("schedule_work(engine = %p)\n", engine);
				schedule_work(&engine->work);
			}
		}
	}

        dbg_irq("user_irq = 0x%08x\n", user_irq);

        spin_lock_irqsave(&lro->events_lock, flags);
	/* new irq events? */
	if ((lro->events_irq | user_irq) != lro->events_irq) {
		dbg_irq("wake_up_interruptible(events_wq) because 0x%08lx | 0x%08lx = 0x%08lx != 0x%08lx\n",
			lro->events_irq, user_irq, lro->events_irq | user_irq, lro->events_irq);
		/* accumulate events into the pending mask */
		lro->events_irq |= user_irq;
		wake_up_interruptible(&lro->events_wq);
	}
        spin_unlock_irqrestore(&lro->events_lock, flags);

	lro->irq_count++;
	return IRQ_HANDLED;
}

/*
 * Unmap the BAR regions that had been mapped earlier using map_bars()
 */
static void unmap_bars(struct xdma_dev *lro, struct pci_dev *dev)
{
	int i;
	for (i = 0; i < XDMA_BAR_NUM; i++) {
		/* is this BAR mapped? */
		if (lro->bar[i]) {
			/* unmap BAR */
			pci_iounmap(dev, lro->bar[i]);
			/* mark as unmapped */
			lro->bar[i] = NULL;
		}
	}
}

/* map_bars() -- map device regions into kernel virtual address space
 *
 * Map the device memory regions into kernel virtual address space after
 * verifying their sizes respect the minimum sizes needed, given by the
 * bar_map_sizes[] array.
 */
static int __devinit map_bars(struct xdma_dev *lro, struct pci_dev *dev)
{
	int rc;
	int i;

	/* iterate through all the BARs */
	for (i = 0; i < XDMA_BAR_NUM; i++) {
		resource_size_t bar_start = pci_resource_start(dev, i);
		resource_size_t bar_end = pci_resource_end(dev, i);
		resource_size_t bar_length = pci_resource_len(dev, i);
		resource_size_t map_length = bar_length;
		lro->bar[i] = NULL;

		/* skip non-present BAR2 and higher */
		if ((!bar_length) && (i >= 2)) continue;

		/* do not map BARs with length 0. Note that start MAY be 0! */
		if (!bar_length) {
			printk(KERN_DEBUG "BAR #%d is not present???\n", i);
			printk(KERN_DEBUG "pci_resource_start(... , %d) = 0x%llx.\n", i, (unsigned long long)bar_start);
			printk(KERN_DEBUG "pci_resource_end(... , %d) = 0x%llx.\n", i, (unsigned long long)bar_end);
			rc = -1;
			goto fail;
		}
		/* BAR length is less than driver requires? */
		if (bar_length < bar_map_sizes_min[i]) {
			printk(KERN_INFO "Failing, driver parameter bar_map_sizes_min[%d] requires %llu bytes, but BAR #%d is only %llu\n",
			       i, (unsigned long long)bar_map_sizes_min[i], i, (unsigned long long)bar_length);
			rc = -1;
			goto fail;
		}
		printk(KERN_INFO "bar_map_sizes_max[%d]=%d\n", i, bar_map_sizes_max[i]);
		/* do not map, and skip, specified BAR mapping with length 0 */
		if (bar_map_sizes_max[i] == 0) {
			printk(KERN_INFO "Skipping BAR #i mapping due to driver parameter bar_map_sizes_max[%d]=0\n", i);
			continue;
			/* BAR size exceeds maximum desired mapping? */
		} else if (bar_length > bar_map_sizes_max[i]) {
			printk(KERN_INFO "Limiting BAR #%d mapping from %llu to %llu bytes, given by driver parameter bar_map_sizes_max[%d]\n",
			       i, (unsigned long long)bar_length, (unsigned long long)bar_map_sizes_max[i], i);
			map_length = (resource_size_t)bar_map_sizes_max[i];
		}
		/* map the full device memory or IO region into kernel virtual
		 * address space */
		dbg_init("BAR%d: %llu bytes to be mapped.\n", i, (unsigned long long)map_length);
		lro->bar[i] = pci_iomap(dev, i, map_length);
		if (!lro->bar[i]) {
			printk(KERN_DEBUG "Could not map BAR #%d. See bar_map_size option to reduce the map size.\n", i);
			rc = -1;
			goto fail;
		}

		bar_map_sizes[i] = bar_length;

		dbg_init("BAR[%d] at 0x%llx mapped at 0x%p with length "
			 "%llu(/%llu).\n", i, (unsigned long long)bar_start,
			 lro->bar[i],
			 (unsigned long long)map_length,
			 (unsigned long long)bar_length);
	}
	/* succesfully mapped all required BAR regions */
	rc = 0;
	goto success;
fail:
	/* unwind; unmap any BARs that we did map */
	unmap_bars(lro, dev);
success:
	return rc;
}

#if defined(CONFIG_MTD) && 0
#  ifdef CONFIG_MTD_COMPLEX_MAPPINGS) && de
static map_word pci_read16(struct map_info *map, unsigned long ofs)
{
	map_word val;
	val.x[0]= ioread16(map->virt + ofs);
	printk(KERN_DEBUG "pci_read16 : %08lx => %02x\n", ofs, val.x[0]);
	return val;
}

static void pci_write16(struct map_info *map, map_word val, unsigned long ofs)
{
	printk(KERN_DEBUG "pci_write16 : %08lx <= %02x\n", ofs, val.x[0]);
	iowrite16(val.x[0], map->virt + ofs);
}

static void pci_copyfrom(struct map_info *map, void *to, unsigned long from, ssize_t len)
{
	printk(KERN_DEBUG "pci_copyfrom : virt= 0x%p, %08p <= %08x, %d\n",
	       map->virt, to, from, len);
	memcpy_fromio(to, map->virt + from, len);
}

static void pci_copyto(struct map_info *map, unsigned long to, const void *from, ssize_t len)
{
	printk(KERN_DEBUG "pci_copyfrom : virt=0x%p, %08p => %08x, %d\n",
	       map->virt, from, to, len);
	memcpy_toio(map->virt + to, from, len);
}

static int probe_flash(struct xdma_dev *lro, int offset)
{
	/* MTD info after probing */
	struct mtd_info *mtd;
	struct map_info *map;
	int rc;
	map = kzalloc(sizeof(struct map_info), GFP_KERNEL);
	if (!map) {
		printk(KERN_DEBUG "Failed to allocate map_info.\n");
		goto fail_map;
	}

	map->name = dev_name(&lro->pci_dev->dev);
	map->phys = pci_resource_start(lro->pci_dev, 0) + 0x800000;
	map->size = 0x800000;
	map->bankwidth = 2;
	map->virt = lro->bar[0] + 0x800000;

	map->read = pci_read16;
	map->write = pci_write16;
	map->copy_from = pci_copyfrom;
	map->copy_to = pci_copyto,

	mtd = do_map_probe("cfi_probe", map);
	printk(KERN_DEBUG "mtd = 0x%p\n", mtd);
	if (!mtd) {
		goto fail_mtd;
	}
	rc = add_mtd_device(mtd);
	printk(KERN_DEBUG "add_mtd_device() = %d\n", rc);
	return 0;
fail_mtd:
	kfree(map);
fail_map:
	return -1;
}
#endif /* ifdef CONFIG_MTD_COMPLEX_MAPPINGS */
#endif /* ifdef CONFIG_MTD */

static void dump_desc(struct xdma_desc *desc_virt)
{
	int j;
	u32 *p = (u32 *)desc_virt;
	const char *field_name[] = { "magic|extra_adjacent|control", "bytes",
				     "src_addr_lo", "src_addr_hi", "dst_addr_lo", "dst_addr_hi",
				     "next_addr", "next_addr_pad" };
	for (j = 0; j < 8; j += 1) {
		dbg_desc("0x%08lx/0x%02x: 0x%08x 0x%08x %s\n",
			 (int)p, (int)p & 15, *p, le32_to_cpu(*p), field_name[j]);
		p++;
	}
	dbg_desc("\n");
}

static void transfer_dump(struct xdma_transfer *transfer)
{
	int i;
	struct xdma_desc *desc_virt = transfer->desc_virt;
	dbg_desc("Descriptor Entry (Pre-Transfer)\n");
	for (i = 0; i < transfer->desc_num; i += 1) {
		dump_desc(desc_virt + i);
	}
}

int adjacent_bound(u32 address)
{
	return (0x1000 - (address & 0x0fffUL)) >> 5;
}

/* xdma_desc_alloc() - Allocate cache-coherent array of N descriptors.
 *
 * Allocates an array of 'number' descriptors in contiguous PCI bus addressable
 * memory. Chains the descriptors as a singly-linked list; the descriptor's next
 * pointer specifies the bus address of the next descriptor.
 *
 *
 * @dev Pointer to pci_dev
 * @number Number of descriptors to be allocated
 * @desc_bus_p Pointer where to store the first descriptor bus address
 * @desc_last_p Pointer where to store the last descriptor virtual address,
 * or NULL.
 *
 * @return Virtual address of the first descriptor
 *
 */
static struct xdma_desc *xdma_desc_alloc(struct pci_dev *dev,
					 int number, dma_addr_t *desc_bus_p, struct xdma_desc **desc_last_p) {
	/* virtual address */
	struct xdma_desc *desc_virt;
	/* bus address */
	dma_addr_t desc_bus;
	int i, adj = number - 1, extra_adj;

	BUG_ON(number < 1);

	/* allocate a set of cache-coherent contiguous pages */
	desc_virt = (struct xdma_desc *)pci_alloc_consistent(dev,
							     number * sizeof(struct xdma_desc), desc_bus_p);
	if (!desc_virt) return NULL;
	/* get bus address of the first descriptor */
	desc_bus = *desc_bus_p;
	WARN_ON((desc_bus >> 16) >> 16);

	/* create singly-linked list for SG DMA controller */
	for (i = 0; i < number - 1; i++) {
		/* increment bus address to next in array */
		desc_bus += sizeof(struct xdma_desc);
		/* XXX assert not using >4GB addresses for descriptors XXX */
		WARN_ON((desc_bus >> 16) >> 16);

		/* singly-linked list uses bus addresses */
		desc_virt[i].next_lo = cpu_to_le32(pci_dma_l(desc_bus));
		desc_virt[i].next_hi = cpu_to_le32(pci_dma_h(desc_bus));
		desc_virt[i].bytes = cpu_to_le32(0);

		/* any adjacent descriptors? */
		if (adj > 0) {
			{
				extra_adj = adj - 1;
			}
			if (extra_adj > MAX_EXTRA_ADJ)
				extra_adj = MAX_EXTRA_ADJ;
			adj--;
		} else
			extra_adj = 0;
#if DESC_COUNTER
		desc_virt[i].control = cpu_to_le32(0xAD4B0000UL |
						   ((i & 0xf) << 12) | (extra_adj << 8));
#else
		desc_virt[i].control = cpu_to_le32(0xAD4B0000UL | (extra_adj << 8));
#endif
	}
	/* { i = number - 1 } */
	/* zero the last descriptor next pointer */
	desc_virt[i].next_lo = cpu_to_le32(0);
	desc_virt[i].next_hi = cpu_to_le32(0);
	desc_virt[i].bytes = cpu_to_le32(0);
#if DESC_COUNTER
	desc_virt[i].control = cpu_to_le32(0xAD4B0000UL | ((i & 0xf) << 12));
#else
	desc_virt[i].control = cpu_to_le32(0xAD4B0000UL);
#endif
	/* caller wants a pointer to last descriptor? */
	if (desc_last_p) {
		*desc_last_p = desc_virt + i;
	}

	/* return the virtual address of the first descriptor */
	return desc_virt;
}

/* xdma_desc_link() - Link two descriptors
 *
 * Link the first descriptor to a second descriptor, or terminate the first.
 *
 * @first first descriptor
 * @second second descriptor, or NULL if first descriptor must be set as last.
 * @second_bus bus address of second descriptor
 */
static void xdma_desc_link(struct xdma_desc *first, struct xdma_desc *second,
			   dma_addr_t second_bus) {
	/* remember reserved control in first descriptor, but zero extra_adjacent! */
	u32 control = le32_to_cpu(first->control) & 0x0000f0ffUL;
	/* second descriptor given? */
	if (second) {
		/* link last descriptor of 1st array to first descriptor of 2nd array */
		first->next_lo = cpu_to_le32(pci_dma_l(second_bus));
		first->next_hi = cpu_to_le32(pci_dma_h(second_bus));
		WARN_ON(first->next_hi);
		/* no second descriptor given */
	} else {
		/* first descriptor is the last */
		first->next_lo = 0;
		first->next_hi = 0;
	}
	/* merge magic, extra_adjacent and control field */
	control |= 0xAD4B0000UL;

	/* write bytes and next_num */
	first->control = cpu_to_le32(control);
}

/* makes an existing transfer cyclic */
static void xdma_transfer_cyclic(struct xdma_transfer *transfer)
{
	/* link last descriptor to first descriptor */
	xdma_desc_link(transfer->desc_virt + transfer->desc_num - 1,
		       transfer->desc_virt, transfer->desc_bus);
	/* remember transfer is cyclic */
	transfer->cyclic = 1;
}

/* xdma_desc_adjacent -- Set how many descriptors are adjacent to this one */
static void xdma_desc_adjacent(struct xdma_desc *desc, int next_adjacent)
{
	int extra_adj = 0;
	/* remember reserved and control bits */
	u32 control = le32_to_cpu(desc->control) & 0x0000f0ffUL;
	if (next_adjacent > 0) {
		extra_adj =  next_adjacent - 1;
		if (extra_adj > MAX_EXTRA_ADJ)
			extra_adj = MAX_EXTRA_ADJ;
	}
	/* merge adjacent and control field */
	control |= 0xAD4B0000UL | (extra_adj << 8);
	/* write control and next_adjacent */
	desc->control = cpu_to_le32(control);
}

/* xdma_desc_control -- Set complete control field of a descriptor. */
static void xdma_desc_control(struct xdma_desc *first, u32 control_field)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control) & 0xffffff00UL;
	BUG_ON(control_field & 0xffffff00UL);
	/* merge adjacent and control field */
	control |= control_field;
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_clear -- Clear bits in control field of a descriptor. */
static void xdma_desc_control_clear(struct xdma_desc *first, u32 clear_mask)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control);
	BUG_ON(clear_mask & 0xffffff00UL);
	/* merge adjacent and control field */
	control &= (~clear_mask);
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}

/* xdma_desc_clear -- Set bits in control field of a descriptor. */
static void xdma_desc_control_set(struct xdma_desc *first, u32 set_mask)
{
	/* remember magic and adjacent number */
	u32 control = le32_to_cpu(first->control);
	BUG_ON(set_mask & 0xffffff00UL);
	/* merge adjacent and control field */
	control |= set_mask;
	/* write control and next_adjacent */
	first->control = cpu_to_le32(control);
}


/* xdma_desc_free - Free cache-coherent linked list of N descriptors.
 *
 * @dev Pointer to pci_dev
 * @number Number of descriptors to be allocated
 * @desc_virt Pointer to (i.e. virtual address of) first descriptor in list
 * @desc_bus Bus address of first descriptor in list
 */
static void xdma_desc_free(struct pci_dev *dev,
			   int number, struct xdma_desc *desc_virt, dma_addr_t desc_bus) {
	BUG_ON(!desc_virt);
	BUG_ON(number < 0);
	/* free contiguous list */
	pci_free_consistent(dev, number * sizeof(struct xdma_desc),
			    desc_virt, desc_bus);
}

/* xdma_desc() - Fill a descriptor with the transfer details
 *
 * @desc pointer to descriptor to be filled
 * @addr root complex address
 * @ep_addr end point address
 * @len number of bytes, must be a (non-negative) multiple of 4.
 * @dir_to_dev If non-zero, source is root complex address and destination
 * is the end point address. If zero, vice versa.
 *
 * Does not modify the next pointer
 */
static void xdma_desc_set(struct xdma_desc *desc,
			  dma_addr_t rc_bus_addr, u64 ep_addr, int len, int dir_to_dev)
{
	/* length (in bytes) must be a non-negative multiple of four */
	BUG_ON(len & 3);
	//BUG_ON(len <= 0);
	/* transfer length */
	desc->bytes = cpu_to_le32(len);
	if (dir_to_dev) {
		/* read from root complex memory (source address) */
		desc->src_addr_lo = cpu_to_le32(pci_dma_l(rc_bus_addr));
		desc->src_addr_hi = cpu_to_le32(pci_dma_h(rc_bus_addr));
		/* write to end point address (destination address) */
		desc->dst_addr_lo = cpu_to_le32(pci_dma_l(ep_addr));
		desc->dst_addr_hi = cpu_to_le32(pci_dma_h(ep_addr));
	} else {
		/* read from end point address (source address) */
		desc->src_addr_lo = cpu_to_le32(pci_dma_l(ep_addr));
		desc->src_addr_hi = cpu_to_le32(pci_dma_h(ep_addr));
		/* write to root complex memory (destination address) */
		desc->dst_addr_lo = cpu_to_le32(pci_dma_l(rc_bus_addr));
		desc->dst_addr_hi = cpu_to_le32(pci_dma_h(rc_bus_addr));
	}
}

static void xdma_desc_set_source(struct xdma_desc *desc, u64 source)
{
	/* read from end point address (source address) */
	desc->src_addr_lo = cpu_to_le32(pci_dma_l(source));
	desc->src_addr_hi = cpu_to_le32(pci_dma_h(source));
}

static void transfer_set_result_addresses(struct xdma_transfer *transfer, u64 result_bus)
{
	int i;
	/* iterate over transfer descriptor list */
	for (i = 0; i < transfer->desc_num; i++) {
		/* set the result ptr in source */
		xdma_desc_set_source(transfer->desc_virt + i, result_bus);
		result_bus += sizeof(struct xdma_result);
	}
}

static void transfer_set_all_control(struct xdma_transfer *transfer, u32 control)
{
	int i;
	for (i = 0; i < transfer->desc_num; i++) {
		xdma_desc_control_clear(transfer->desc_virt + i,  0xFF);
		xdma_desc_control_set(transfer->desc_virt + i, control);
	}
}


/* transfer_queue() - Queue a DMA transfer on the engine
 *
 * @engine DMA engine doing the transfer
 * @transfer DMA transfer submitted to the engine
 *
 * Takes and releases the engine spinlock
 */
static int transfer_queue(struct xdma_engine *engine, struct xdma_transfer *transfer)
{
	int rc = 0;
	struct xdma_transfer *transfer_started;
	BUG_ON(!engine);
	BUG_ON(!transfer);
	BUG_ON(transfer->desc_num == 0);
	dbg_tfr("transfer_queue(transfer=0x%p).\n", transfer);

	/* lock the engine state */
	spin_lock(&engine->lock);
	engine->prev_cpu = get_cpu();
	put_cpu();

	/* engine is being shutdown; do not accept new transfers */
	if (engine->shutdown & ENGINE_SHUTDOWN_REQUEST) {
		rc = -1;
		goto shutdown;
	}

	/* either the engine is still busy and we will end up in the
	 * service handler later, or the engine is idle and we have to
	 * start it with this transfer here */

#if CHAIN_MULTIPLE_TRANSFERS
	/* queue is not empty? try to chain the descriptor lists */
	if (!list_empty(&engine->transfer_list)) {
		struct xdma_transfer *last;
		dbg_tfr("transfer_queue(): list not empty\n");
		/* get last transfer queued on the engine */
		last = list_entry(engine->transfer_list.prev,
				  struct xdma_transfer, entry);
		/* @only when non-cyclic transfer */
		/* link the last transfer's last descriptor to this transfer */
		xdma_desc_link(last->desc_virt + last->desc_num - 1,
			       transfer->desc_virt, transfer->desc_bus);
		/* do not stop now that there is a linked transfers */
		xdma_desc_control_clear(last->desc_virt + last->desc_num - 1, XDMA_DESC_STOP);

		dbg_tfr("transfer_queue(transfer=0x%p, desc=%d) chained after 0x%p with engine %s.\n",
			transfer, transfer->desc_num, last, engine->running? "running" : "idle");
		/* queue is empty */
	} else {
		if (engine->running)
			dbg_tfr("transfer_queue(): queue empty, but engine seems to be running?!!\n");
		else
			dbg_tfr("transfer_queue(): queue empty and engine idle.\n");
		/* engine should not be running */
		WARN_ON(engine->running);
	}
#endif

	/* mark the transfer as submitted */
	transfer->state = TRANSFER_STATE_SUBMITTED;
	/* add transfer to the tail of the engine transfer queue */
	list_add_tail(&transfer->entry, &engine->transfer_list);

	/* engine is idle? */
	if (!engine->running) {
		/* start engine */
		dbg_tfr("transfer_queue(): starting %s engine.\n", engine->name);
		transfer_started = engine_start(engine);
		dbg_tfr("transfer_queue(transfer=0x%p) started %s engine with transfer 0x%p.\n", transfer, engine->name, transfer_started);
	} else {
		dbg_tfr("transfer_queue(transfer=0x%p) queued, with %s engine running.\n", transfer, engine->name);
	}
shutdown:
	/* unlock the engine state */
	dbg_tfr("engine->running = %d\n", engine->running);
	spin_unlock(&engine->lock);
	return rc;
};

//SD_Accel Specific
void engine_reinit(const struct xdma_engine *engine)
{
	printk(KERN_INFO "%s: Re-init DMA Engine %s\n", DRV_NAME, engine->name);
	write_register(XDMA_CTRL_IE_DESCRIPTOR_STOPPED |
		       XDMA_CTRL_IE_DESCRIPTOR_COMPLETED |
		       XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH |
		       XDMA_CTRL_IE_MAGIC_STOPPED |
		       XDMA_CTRL_IE_READ_ERROR |
		       XDMA_CTRL_IE_DESCRIPTOR_ERROR, &engine->regs->interrupt_enable_mask);
}

static void engine_alignments(struct xdma_engine *engine)
{
	u32 w;
	u32 align_bytes;
	u32 granularity_bytes;
	u32 address_bits;

	w = read_register(&engine->regs->alignments);
	dbg_init("engine %p name %s alignments=0x%08x\n", engine, engine->name, (int)w);

	align_bytes = (w & 0x00ff0000U) >> 16;
	granularity_bytes = (w & 0x0000ff00U) >> 8;
	address_bits = (w & 0x000000ffU);

	printk(KERN_INFO "align_bytes = %d\n", align_bytes);
	printk(KERN_INFO "granularity_bytes = %d\n", granularity_bytes);
	printk(KERN_INFO "address_bits = %d\n", address_bits);

	if (w) {
		engine->addr_align = align_bytes;
		engine->len_granularity = granularity_bytes;
		engine->addr_bits = address_bits;
	}
}

/* engine_create() - Create an SG DMA engine bookkeeping data structure
 *
 * An SG DMA engine consists of the resources for a single-direction transfer
 * queue; the SG DMA hardware, the software queue and interrupt handling.
 *
 * @dev Pointer to pci_dev
 * @offset byte address offset in BAR[XDMA_BAR_XDMA] resource for the SG DMA
 * controller registers.
 * @dir_to_dev Whether the engine transfers to the device (PCIe Rd).
 * @streaming Whether the engine is attached to AXI ST (rather than MM)
 */
static struct xdma_engine *engine_create(struct xdma_dev *lro, int offset, int sgdma_offset,
					 int dir_to_dev, int channel, int number_in_channel, int streaming)
{
	/* allocate data structure for engine book keeping */
	struct xdma_engine *engine =
		kzalloc(sizeof(struct xdma_engine), GFP_KERNEL);
	/* memory allocation failure? */
	if (!engine) return NULL;
	/* set magic */
	engine->magic = MAGIC_ENGINE;

	/* indices */
	engine->channel = channel;
	engine->number_in_channel = number_in_channel;

	/* engine interrupt request bit */
	engine->irq_bitmask = (1 << XDMA_ENG_IRQ_NUM) - 1;
	engine->irq_bitmask <<= (lro->engines_num * XDMA_ENG_IRQ_NUM);

	lro->engines_num++;

	/* create virtual memory mapper */
	engine->sgm = sg_create_mapper(XDMA_TRANSFER_MAX_BYTES);
	if (!engine->sgm) {
		printk(KERN_INFO "sg_create_mapper(%d) failed\n", XDMA_TRANSFER_MAX_BYTES);
		goto fail_mapper;
	}
	/* initialize spinlock */
	spin_lock_init(&engine->lock);
	/* initialize transfer_list */
	INIT_LIST_HEAD(&engine->transfer_list);
	/* parent */
	engine->lro = lro;
	/* register address */
	engine->regs = (lro->bar[XDMA_BAR_XDMA] + offset);
	engine->sgdma_regs = (lro->bar[XDMA_BAR_XDMA] + sgdma_offset);
	/* remember SG DMA direction */
	engine->dir_to_dev = dir_to_dev;
	engine->streaming = streaming;
	engine->name = engine->dir_to_dev? "H2C": "C2H";

	dbg_init("engine %p name %s irq_bitmask=0x%08x\n", engine, engine->name, (int)engine->irq_bitmask);

	/* initialize the deferred work for transfer completion */
	INIT_WORK(&engine->work, engine_service_work);
	/* initialize wait queue */
	init_waitqueue_head(&engine->shutdown_wq);
	/* initialize wait queue */
	init_waitqueue_head(&engine->xdma_perf_wq);

	write_register(XDMA_CTRL_NON_INCR_ADDR, &engine->regs->control_w1c);


	/* default is 1 byte alignment */
	engine->addr_align = 1;
	engine->len_granularity = 1;
	engine->addr_bits = 64;
	engine_alignments(engine);

	/* enable interrupts AXI ST C2H case */
	if (streaming && !dir_to_dev) {
		write_register(XDMA_CTRL_IE_DESCRIPTOR_STOPPED |
			       XDMA_CTRL_IE_DESCRIPTOR_COMPLETED |
			       XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH |
			       XDMA_CTRL_IE_MAGIC_STOPPED |
			       // Disable IDLE_STOPPED
			       XDMA_CTRL_IE_IDLE_STOPPED |
			       XDMA_CTRL_IE_READ_ERROR |
			       XDMA_CTRL_IE_DESCRIPTOR_ERROR, &engine->regs->interrupt_enable_mask);
	} else {
		// MM don't enable IDLE_STOP
		write_register(XDMA_CTRL_IE_DESCRIPTOR_STOPPED |
			       XDMA_CTRL_IE_DESCRIPTOR_COMPLETED |
			       XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH |
			       XDMA_CTRL_IE_MAGIC_STOPPED |
			       // Disable IDLE_STOPPED
			       //XDMA_CTRL_IE_IDLE_STOPPED |
			       XDMA_CTRL_IE_READ_ERROR |
			       XDMA_CTRL_IE_DESCRIPTOR_ERROR, &engine->regs->interrupt_enable_mask);
	}

	return engine;

fail_mapper:
	kfree(engine);
	return NULL;
}

/* transfer_destroy() - free transfer */
static void transfer_destroy(struct xdma_dev *lro, struct xdma_transfer *transfer)
{
	/* user space buffer was locked in on account of transfer? */
	if (transfer->sgm) {
		/* unmap scatterlist */
		//dbg_tfr("transfer_destroy(): pci_unmap_sg()\n");
		/* the direction is needed to synchronize caches */
		pci_unmap_sg(lro->pci_dev, transfer->sgm->sgl, transfer->sgm->mapped_pages,
			     transfer->dir_to_dev? DMA_TO_DEVICE: DMA_FROM_DEVICE);
		if (transfer->userspace) {
			/* dirty and unlock the pages */
			sgm_put_user_pages(transfer->sgm, transfer->dir_to_dev? 0 : 1);
			//dbg_tfr("transfer_destroy(): sgm_put_user_pages()\n");
		}
		transfer->sgm->mapped_pages = 0;
		sg_destroy_mapper(transfer->sgm);
	}
	/* free descriptors */
	xdma_desc_free(lro->pci_dev,
		       transfer->sgl_nents, transfer->desc_virt, transfer->desc_bus);
	/* free transfer */
	kfree(transfer);
}

/* xdma_config -- Inspect the XDMA IP Core configuration */
static int xdma_config(struct xdma_dev *lro, unsigned int config_offset)
{
	struct config_regs *reg = (struct config_regs *)(lro->bar[XDMA_BAR_XDMA] + config_offset);
	u32 w;
	int rc = 0;
	w = read_register(&reg->identifier);
	printk(KERN_INFO "xdma_config(): ID = 0x%08x\n", w);

fail_identifier:
	return rc;
}

//SD_Accel Specific

/* transfer_create_user() - Create a DMA transfer to/from a user space buffer
 *
 * Allocates a transfer data structure and an array of descriptors. Builds a
 * descriptor list from the scatter gather list, coalescing adjacent entries.
 *
 * The scatterlist must have been mapped by pci_map_sg(sgm->sgl).
 *
 * @sgl scatterlist.
 * @nents Number of entries in the scatterlist after mapping by pci_map_sg().
 * @first Start index in the scatterlist sgm->sgl.
 *
 * Returns Number of entries in the table on success, -1 on error.
 */
static struct xdma_transfer *transfer_create_user(struct xdma_dev *lro, const char *start, size_t count, u64 ep_addr, int dir_to_dev)
{
	int i = 0, j = 0, new_desc, rc;
	dma_addr_t cont_addr, addr;
	unsigned int cont_len, len, cont_max_len = 0;
	struct scatterlist *sgl;

	/* allocate transfer data structure */
	struct xdma_transfer *transfer =
		kzalloc(sizeof(struct xdma_transfer), GFP_KERNEL);

	dbg_sg("transfer_create_user()\n");

	if (!transfer) return NULL;
	/* remember direction of transfer */
	transfer->dir_to_dev = dir_to_dev;

	/* create virtual memory mapper */
	transfer->sgm = sg_create_mapper(count);
	BUG_ON(!transfer->sgm);
	transfer->userspace = 1;

	/* lock user pages in memory and create a scatter gather list */
	rc = sgm_get_user_pages(transfer->sgm, start, count, !dir_to_dev);
	BUG_ON(rc < 0);

	sgl = transfer->sgm->sgl;

	dbg_sg("mapped_pages=%d.\n", transfer->sgm->mapped_pages);
	dbg_sg("sgl = 0x%p.\n", transfer->sgm->sgl);
	BUG_ON(!lro->pci_dev);
	BUG_ON(!transfer->sgm->sgl);
	BUG_ON(!transfer->sgm->mapped_pages);
	/* map all SG entries into DMA memory */
	transfer->sgl_nents = pci_map_sg(lro->pci_dev, transfer->sgm->sgl,
					 transfer->sgm->mapped_pages, dir_to_dev? DMA_TO_DEVICE: DMA_FROM_DEVICE);
	dbg_sg("hwnents=%d.\n", transfer->sgl_nents);

	/* verify if the page start address got into the first sg entry */
	dbg_sg("sg_page(&sgl[0])=0x%p.\n", sg_page(&transfer->sgm->sgl[0]));
	dbg_sg("sg_dma_address(&sgl[0])=0x%016llx.\n", (u64)sg_dma_address(&transfer->sgm->sgl[0]));
	dbg_sg("sg_dma_len(&sgl[0])=0x%08x.\n", sg_dma_len(&transfer->sgm->sgl[0]));

	/* allocate descriptor list */
	transfer->desc_virt = xdma_desc_alloc(lro->pci_dev,
					      transfer->sgl_nents, &transfer->desc_bus, NULL);
	WARN_ON((transfer->desc_bus >> 16) >> 16);
	dbg_sg("transfer_create_user():\n");
	dbg_sg("transfer->desc_bus = 0x%llx.\n", (u64)transfer->desc_bus);

	/* start first contiguous block */
	cont_addr = addr = sg_dma_address(&transfer->sgm->sgl[i]);
	cont_len = 0;

	/* iterate over all remaining entries but the last */
	for (i = 0; i < transfer->sgl_nents - 1; i++) {
		/* bus address of next entry i + 1 */
		dma_addr_t next = sg_dma_address(&sgl[i + 1]);
		/* length of this entry i */
		len = sg_dma_len(&sgl[i]);
		dbg_desc("SGLE %04d: addr=0x%016llx length=0x%08x\n", i, (u64)addr, len);

		/* add entry i to current contiguous block length */
		cont_len += len;

		new_desc = 0;
		/* entry i + 1 is non-contiguous with entry i? */
		if (next != addr + len) {
			dbg_desc("NON-CONTIGUOUS WITH DESC %d\n", i + 1);
			new_desc = 1;
		}
		/* entry i reached maximum transfer size? */
		else if (cont_len > (XDMA_DESC_MAX_BYTES - PAGE_SIZE)) {
			dbg_desc("BREAK\n");
			new_desc = 1;
		}
		if (new_desc) {
			/* fill in descriptor entry j with transfer details */
			xdma_desc_set(transfer->desc_virt + j, cont_addr,
				      ep_addr, cont_len, dir_to_dev);
#if FORCE_IR_DESC_COMPLETED
			xdma_desc_control(transfer->desc_virt + j, XDMA_DESC_COMPLETED);
#endif
			if (cont_len > cont_max_len) {
				cont_max_len = cont_len;
				dbg_desc("LONGEST CONTIGUOUS LENGTH (SO FAR) = %d\n",
					 cont_max_len);
			}
			dbg_desc("DESC %4d: cont_addr=0x%016llx cont_len=0x%08x, ep_addr=0x%llx\n",
				 j, (u64)cont_addr, cont_len, (unsigned long long)ep_addr);
			/* proceed EP address for next contiguous block */
			ep_addr += cont_len;
			/* start new contiguous block */
			cont_addr = next;
			cont_len = 0;
			j++;
		}
		/* goto entry i + 1 */
		addr = next;
	}
	/* i is the last entry in the scatterlist, add it to the last block */
	len = sg_dma_len(&sgl[i]);
	cont_len += len;
	BUG_ON(j > transfer->sgl_nents);

	/* j is the index of the last descriptor */

	dbg_desc("SGLE %04d: addr=0x%016llx length=0x%08x\n", i, (u64)addr, len);
	dbg_desc("DESC %4d: cont_addr=0x%016llx cont_len=0x%08x, ep_addr=0x%llx\n",
		 j, (u64)cont_addr, cont_len, (unsigned long long)ep_addr);

	/* XXX to test error condition, set cont_len = 0 */

	/* fill in last descriptor entry j with transfer details */
	xdma_desc_set(transfer->desc_virt + j, cont_addr,
		      ep_addr, cont_len, dir_to_dev);
#if XDMA_PERFORMANCE_TEST
	/* create a linked loop */
	xdma_desc_link(transfer->desc_virt + j, transfer->desc_virt, transfer->desc_bus);
#  if FORCE_IR_DESC_COMPLETED
	/* request IRQ on last descriptor */
	xdma_desc_control(transfer->desc_virt + j, XDMA_DESC_COMPLETED);
#  endif
#else
	/* terminate last descriptor */
	xdma_desc_link(transfer->desc_virt + j, 0, 0);
	/* stop engine, EOP for AXI ST, and request IRQ on last descriptor */
	xdma_desc_control(transfer->desc_virt + j, XDMA_DESC_STOP | XDMA_DESC_EOP | XDMA_DESC_COMPLETED);
#endif

	j++;
	/* j is the number of descriptors */
	transfer->desc_num = transfer->desc_adjacent = j;

	dbg_sg("transfer 0x%p has %d descriptors\n", transfer, transfer->desc_num);
	/* fill in adjacent numbers */
	for (i = 0; i < transfer->desc_num; i++) {
		xdma_desc_adjacent(transfer->desc_virt + i,
				   transfer->desc_num - i - 1);
	}

	/* initialize wait queue */
	init_waitqueue_head(&transfer->wq);

	return transfer;
}

/* transfer_create_kernel() - Create a DMA transfer to/from a kernel buffer
 *
 * Allocates a transfer data structure and an array of descriptors. Builds a
 * descriptor list from the scatter gather list, coalescing adjacent entries.
 *
 * The scatterlist must have been mapped by pci_map_sg(sgm->sgl).
 *
 * vmalloc_to_pfn
 *
 * @sgl scatterlist.
 * @nents Number of entries in the scatterlist after mapping by pci_map_sg().
 * @first Start index in the scatterlist sgm->sgl.
 *
 * Returns Number of entries in the table on success, -1 on error.
 */
static struct xdma_transfer *transfer_create_kernel(struct xdma_dev *lro, const char *start, size_t count, u64 ep_addr, int dir_to_dev, int force_new_desc)
{
	int i = 0, j = 0, new_desc, rc;
	dma_addr_t cont_addr, addr;
	unsigned int cont_len, len, cont_max_len = 0;
	struct scatterlist *sgl;

	/* allocate transfer data structure */
	struct xdma_transfer *transfer =
		kzalloc(sizeof(struct xdma_transfer), GFP_KERNEL);

	printk(KERN_INFO "transfer_create_kernel()\n");

	if (!transfer) return NULL;
	/* remember direction of transfer */
	transfer->dir_to_dev = dir_to_dev;

	/* create virtual memory mapper */
	transfer->sgm = sg_create_mapper(count);
	BUG_ON(!transfer->sgm);

	/* create a scatter gather list */
	rc = sgm_kernel_pages(transfer->sgm, start, count, !dir_to_dev);
	BUG_ON(rc < 0);

	sgl = transfer->sgm->sgl;

	dbg_sg("mapped_pages=%d.\n", transfer->sgm->mapped_pages);
	dbg_sg("sgl = 0x%p.\n", transfer->sgm->sgl);
	BUG_ON(!lro->pci_dev);
	BUG_ON(!transfer->sgm->sgl);
	BUG_ON(!transfer->sgm->mapped_pages);
	/* map all SG entries into DMA memory */
	transfer->sgl_nents = pci_map_sg(lro->pci_dev, transfer->sgm->sgl,
					 transfer->sgm->mapped_pages, dir_to_dev? DMA_TO_DEVICE : DMA_FROM_DEVICE);
	dbg_sg("hwnents=%d.\n", transfer->sgl_nents);

	/* verify if the page start address got into the first sg entry */
	dbg_sg("sg_page(&sgl[0])=0x%p.\n", sg_page(&transfer->sgm->sgl[0]));
	dbg_sg("sg_dma_address(&sgl[0])=0x%016llx.\n", (u64)sg_dma_address(&transfer->sgm->sgl[0]));
	dbg_sg("sg_dma_len(&sgl[0])=0x%08x.\n", sg_dma_len(&transfer->sgm->sgl[0]));

	/* allocate descriptor list */
	transfer->desc_virt = xdma_desc_alloc(lro->pci_dev,
					      transfer->sgl_nents, &transfer->desc_bus, NULL);
	dbg_sg("transfer_create_user():\n");
	dbg_sg("transfer->desc_bus = 0x%llx.\n", (u64)transfer->desc_bus);

	/* start first contiguous block */
	cont_addr = addr = sg_dma_address(&transfer->sgm->sgl[i]);
	cont_len = 0;

	/* iterate over all remaining entries but the last */
	for (i = 0; i < transfer->sgl_nents - 1; i++) {
		/* bus address of next entry i + 1 */
		dma_addr_t next = sg_dma_address(&sgl[i + 1]);
		/* length of this entry i */
		len = sg_dma_len(&sgl[i]);
		dbg_desc("SGLE %04d: addr=0x%016llx length=0x%08x\n", i, (u64)addr, len);

		/* add entry i to current contiguous block length */
		cont_len += len;

		new_desc = 0;
		/* entry i + 1 is non-contiguous with entry i? */
		if (next != addr + len) {
			dbg_desc("NON CONTIGUOUS\n");
			new_desc = 1;
		}
		/* entry i reached maximum transfer size? */
		else if (cont_len > (XDMA_DESC_MAX_BYTES - PAGE_SIZE)) {
			dbg_desc("BREAK\n");
			new_desc = 1;
		}
                if (force_new_desc) new_desc = 1;
		if (new_desc) {
			/* fill in descriptor entry j with transfer details */
			xdma_desc_set(transfer->desc_virt + j, cont_addr,
				      ep_addr, cont_len, dir_to_dev);
#if FORCE_IR_DESC_COMPLETED
			xdma_desc_control(transfer->desc_virt + j, XDMA_DESC_COMPLETED);
#endif
			if (cont_len > cont_max_len) {
				cont_max_len = cont_len;
				dbg_desc("DESC %4d: cont_addr=0x%016llx cont_len=0x%08x, ep_addr=0x%llx\n",
					 j, (u64)cont_addr, cont_len, (unsigned long long)ep_addr);
			}
			dbg_desc("DESC %4d: cont_addr=0x%016llx cont_len=0x%08x, ep_addr=0x%llx\n",
				 j, (u64)cont_addr, cont_len, (unsigned long long)ep_addr);
			/* proceed EP address for next contiguous block */
			ep_addr += cont_len;
			/* start new contiguous block */
			cont_addr = next;
			cont_len = 0;
			j++;
		}
		/* goto entry i + 1 */
		addr = next;
	}
	/* i is the last entry in the scatterlist, add it to the last block */
	len = sg_dma_len(&sgl[i]);
	cont_len += len;
	BUG_ON(j > transfer->sgl_nents);

	/* j is the index of the last descriptor */

	dbg_desc("SGLE %04d: addr=0x%016llx length=0x%08x\n", i, (u64)addr, len);
	dbg_desc("DESC %4d: cont_addr=0x%016llx cont_len=0x%08x, ep_addr=0x%llx\n",
		 j, (u64)cont_addr, cont_len, (unsigned long long)ep_addr);

	/* XXX to test error condition, set cont_len = 0 */

	/* fill in last descriptor entry j with transfer details */
	xdma_desc_set(transfer->desc_virt + j, cont_addr,
		      ep_addr, cont_len, dir_to_dev);
	/* terminate last descriptor */
	xdma_desc_link(transfer->desc_virt + j, 0, 0);
	/* request IRQ on last descriptor */
	xdma_desc_control(transfer->desc_virt + j, XDMA_DESC_STOP | XDMA_DESC_EOP | XDMA_DESC_COMPLETED);

	j++;
	/* j is the number of descriptors */
	transfer->desc_num = transfer->desc_adjacent = j;

	dbg_sg("transfer 0x%p has %d descriptors\n", transfer, transfer->desc_num);
	/* fill in adjacent numbers */
	for (i = 0; i < transfer->desc_num; i++) {
		xdma_desc_adjacent(transfer->desc_virt + i,
				   transfer->desc_num - i - 1);
	}

	/* initialize wait queue */
	init_waitqueue_head(&transfer->wq);

	return transfer;
}

/* sg_aio_read_write() -- Read from or write to the device
 *
 * @buf userspace buffer
 * @count number of bytes in the userspace buffer
 * @pos byte-address in device
 * @dir_to_device If !0, a write to the device is performed
 *
 * Iterate over the userspace buffer, taking at most 255 * PAGE_SIZE bytes for
 * each DMA transfer.
 *
 * For each transfer, get the user pages, build a sglist, map, build a
 * descriptor table. submit the transfer. wait for the interrupt handler
 * to wake us on completion.
 */
static ssize_t sg_aio_read_write(struct kiocb *iocb, const struct iovec *iov,
				 unsigned long nr_segs, loff_t pos, int dir_to_dev)
{
	/* fetch file this io request acts on */
	struct file *file = iocb->ki_filp;
	loff_t *ppos = &iocb->ki_pos;
	size_t total_done = 0;
	unsigned long seg;

	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	printk(KERN_INFO "sg_aio_read_write(iocb=0x%p, iov=0x%p, nr_segs=%ld, pos=%llu, dir_to_dev=%d) %s request\n",
	       iocb, iov, nr_segs, (u64)pos, dir_to_dev, dir_to_dev? "write" : "read");

	engine = lro_char->engine;
	/* XXX detect not supported direction */
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);
	/* iterate over all vector segments */
	for (seg = 0; seg < nr_segs; seg++) {
		const char __user *buf = iov[seg].iov_base;
		size_t count = iov[seg].iov_len;
		size_t remaining = count, done = 0;
		char *transfer_addr = (char *)buf;

		/* AXI ST or AXI MM non-incremental addressing mode? */
		if (engine->streaming || engine->non_incr_addr) {
			unsigned long buf_lsb = ((unsigned long)buf) & (engine->addr_align - 1);
			size_t len_lsb = count & ((size_t)engine->len_granularity - 1);
			unsigned long pos_lsb = ((unsigned long)pos) & (engine->addr_align - 1);
			if (buf_lsb != 0) {
				printk(KERN_INFO "FAILURE: non-aligned host buffer address 0x%p\n", buf);
				return -EINVAL;
			}
			if (len_lsb != 0) {
				printk(KERN_INFO "FAILURE: length %d is not a multiple of %d\n", (int)count, (int)engine->len_granularity);
				return -EINVAL;
			}
			/* AXI MM incremental addressing mode */
		} else {
			unsigned long buf_lsb = ((unsigned long)buf) & (engine->addr_align - 1);
			unsigned long pos_lsb = ((unsigned long)pos) & (engine->addr_align - 1);
			if (buf_lsb != pos_lsb) {
				printk(KERN_INFO "FAILURE: host buffer address 0x%p is not aligned to FPGA address 0x%lx.\n",
				       buf, (unsigned long)pos);
				return -EINVAL;
			}
		}


		dbg_tfr("seg %lu: buf=0x%p, count=%lld, pos=%llu\n",
			seg, buf, (s64)count, (u64)pos);
		/* anything left to transfer? */
		while (remaining > 0) {
			struct xdma_transfer *transfer;
			/* DMA transfer size, multiple if necessary */
			size_t transfer_len = (remaining > XDMA_TRANSFER_MAX_BYTES) ?
				XDMA_TRANSFER_MAX_BYTES : remaining;

			/* build device-specific descriptor tables */
			transfer = transfer_create_user(lro, transfer_addr, transfer_len,
							pos, dir_to_dev);
			dbg_sg("segment:%lu transfer=0x%p.\n", seg, transfer);
			BUG_ON(!transfer);

			if (!transfer) {
				remaining = 0;
				done = 0;
				printk(KERN_DEBUG "Could not allocate memory for transfer!");
				return -ENOMEM;
			}

			transfer_dump(transfer);

			/* remember I/O context for later completion */
			transfer->iocb = iocb;
			/* last transfer for the given request? */
			if (transfer_len >= remaining) {
				/* mark as last transfer, using request size */
				transfer->last_in_request = 1;
				transfer->size_of_request = done + transfer_len;
			}
			/* queue the transfer on the hardware */
			transfer_queue(engine, transfer);
			/* calculate the next transfer */
			transfer_addr += transfer_len;
			remaining -= transfer_len;
			done += transfer_len;
			dbg_tfr("remaining = %lld, done = %lld.\n",
				(s64)remaining, (s64)done);
		}
		total_done += done;
	}
	printk(KERN_INFO "sg_aio_read_write() queued a total of %lld bytes, returns -EIOCBQUEUED.\n", (s64)total_done);
	return -EIOCBQUEUED;
}

/**
 * sg_aio_read_write - generic asynchronous read routine
 * @iocb:       kernel I/O control block
 * @iov:        io vector request
 * @nr_segs:    number of segments in the iovec
 * @pos:        current file position
 *
 */
ssize_t sg_aio_read(struct kiocb *iocb, const struct iovec *iov,
		    unsigned long nr_segs, loff_t pos)
{
	printk(KERN_DEBUG "sg_aio_read()\n");
	return sg_aio_read_write(iocb, iov, nr_segs, pos, 0/*dir_to_dev = 0*/);
}

ssize_t sg_aio_write(struct kiocb *iocb, const struct iovec *iov,
		     unsigned long nr_segs, loff_t pos)
{
	printk(KERN_DEBUG "sg_aio_write()\n");
	return sg_aio_read_write(iocb, iov, nr_segs, pos, 1/*dir_to_dev = 1*/);
}

static loff_t char_sgdma_llseek(struct file *file, loff_t off, int whence)
{
	loff_t newpos = 0;
	switch (whence) {
	case 0: /* SEEK_SET */
		newpos = off;
		break;
	case 1: /* SEEK_CUR */
		newpos = file->f_pos + off;
		break;
	case 2: /* SEEK_END, @TODO should work from end of address space */
		newpos = UINT_MAX + off;
		break;
	default: /* can't happen */
		return -EINVAL;
	}
	if (newpos < 0) return -EINVAL;
	file->f_pos = newpos;

	return newpos;
}


/* char_sgdma_read_write() -- Read from or write to the device
 *
 * @buf userspace buffer
 * @count number of bytes in the userspace buffer
 * @pos byte-address in device
 * @dir_to_device If !0, a write to the device is performed
 *
 * Iterate over the userspace buffer, taking at most 255 * PAGE_SIZE bytes for
 * each DMA transfer.
 *
 * For each transfer, get the user pages, build a sglist, map, build a
 * descriptor table. submit the transfer. wait for the interrupt handler
 * to wake us on completion.
 */

static ssize_t char_sgdma_read_write(struct file *file, char __user *buf, size_t count, loff_t *pos, int dir_to_dev)
{
	int rc;
	ssize_t res = 0;
	static int counter = 0;
	int seq = counter++;
	ssize_t remaining = count, done = 0;
	char *transfer_addr = (char *)buf;
	int address_low_bits = 0;
	size_t length_low_bits = 0;
	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;
	/* XXX detect non-supported directions XXX */
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	dbg_tfr("seq:%d char_sgdma_read_write(file=0x%p, buf=0x%p, count=%lld, pos=%llu, dir_to_dev=%d) %s request\n",
		seq, file, buf, (s64)count, (u64)*pos, dir_to_dev, dir_to_dev? "write" : "read");
	dbg_tfr("%s engine channel %d (engine num %d)= 0x%p\n", engine->name, engine->channel, engine->number_in_channel, engine);
	dbg_tfr("lro = 0x%p\n", lro);

	/* data direction does not match engine? */
	if (dir_to_dev != engine->dir_to_dev) {
		if (dir_to_dev) {
			printk(KERN_INFO "FAILURE: Cannot write to C2H engine.\n");
		} else {
			printk(KERN_INFO "FAILURE: Cannot read from H2C engine.\n");
		}
		return -EINVAL;
	}

	/* AXI ST or AXI MM non-incremental addressing mode? */
	if (engine->streaming || engine->non_incr_addr) {
		unsigned long buf_lsb = ((unsigned long)buf) & (engine->addr_align - 1);
		size_t len_lsb = count & ((size_t)engine->len_granularity - 1);
		unsigned long pos_lsb = ((unsigned long)*pos) & (engine->addr_align - 1);
		printk(KERN_INFO "AXI ST or MM non-incremental: buf_lsb = 0x%lx, pos_lsb = 0x%lx, len_lsb = 0x%lx\n", buf_lsb, pos_lsb, len_lsb);

		if (buf_lsb != 0) {
			printk(KERN_INFO "FAILURE: non-aligned host buffer address 0x%p\n", buf);
			return -EINVAL;
		}
		if ((!engine->streaming) && (pos_lsb != 0)) {
			printk(KERN_INFO "FAILURE: non-aligned AXI MM FPGA address 0x%llx\n", (unsigned long long)pos);
			return -EINVAL;
		}
		if (len_lsb != 0) {
			printk(KERN_INFO "FAILURE: length %d is not a multiple of %d\n", (int)count, (int)engine->len_granularity);
			return -EINVAL;
		}
		/* AXI MM incremental addressing mode */
	} else {
		unsigned long buf_lsb = ((unsigned long)buf) & (engine->addr_align - 1);
		unsigned long pos_lsb = ((unsigned long)*pos) & (engine->addr_align - 1);
		//printk(KERN_INFO "AXI MM incrementbuf_lsb = %d, pos_lsb = %d\n", buf_lsb, pos_lsb);
		if (buf_lsb != pos_lsb) {
			printk(KERN_INFO "FAILURE: host buffer address 0x%lx is not aligned to FPGA address 0x%lx\n",
			       (unsigned long)buf, (unsigned long)*pos);
			return -EINVAL;
		}
	}
        remaining = count;
	dbg_tfr("res = %d, remaining = %d\n", res, remaining);
	/* still good and anything left to transfer? */
	while ((res == 0) && (remaining > 0)) {
		struct xdma_transfer *transfer;
		/* DMA transfer size, multiple if necessary */
		size_t transfer_len = (remaining > XDMA_TRANSFER_MAX_BYTES) ?
			XDMA_TRANSFER_MAX_BYTES : remaining;

		/* build device-specific descriptor tables */
		transfer = transfer_create_user(lro, transfer_addr,
						transfer_len, *pos, dir_to_dev);
		dbg_tfr("seq:%d transfer=0x%p.\n", seq, transfer);
		BUG_ON(!transfer);
		if (!transfer) {
			remaining = 0;
			res = -EIO;
			continue;
		}
		transfer_dump(transfer);
		/* last transfer for the given request? */
		if (transfer_len >= remaining) {
			transfer->last_in_request = 1;
			transfer->size_of_request = done + transfer_len;
		}
		//transfer_dump(transfer);

		/* let the device read from the host */
		transfer_queue(engine, transfer);
		/* the function servicing the engine will wake us */
		rc = wait_event_interruptible(transfer->wq, transfer->state != TRANSFER_STATE_SUBMITTED);
		if (rc) dbg_tfr("seq:%d wait_event_interruptible() = %d\n", seq, rc);

		/* transfer was taken off the engine? */
		if (transfer->state != TRANSFER_STATE_SUBMITTED) {
			/* transfer failed? */
			if (transfer->state != TRANSFER_STATE_COMPLETED) {
                                dbg_tfr("transfer %p failed\n", transfer);
				transfer_len = remaining = 0;
				res = -EIO;
			}
                        dbg_tfr("transfer %p completed\n", transfer);
			transfer_destroy(lro, transfer);
			/* wait_event_interruptible() was interrupted by a signal? */
		} else if (rc == -ERESTARTSYS) {
			dbg_tfr("wait_event_interruptible(transfer->wq) == ERESTARTSYS\n");
			/* transfer can still be in-flight */
			engine_status_read(engine, 0);
			read_interrupts(lro, XDMA_OFS_INT_CTRL);
			transfer_len = remaining = 0;

			dbg_tfr("waiting for transfer 0x%p to complete.\n", transfer);
			dbg_tfr("transfer 0x%p has completed, transfer->state = %d\n", transfer, transfer->state);

			res = -ERESTARTSYS;
			if (transfer->state != TRANSFER_STATE_SUBMITTED) {
				transfer_destroy(lro, transfer);
			}
		}
		/* calculate the next transfer */
		transfer_addr += transfer_len;
		remaining -= transfer_len;
		done += transfer_len;
		*pos += transfer_len;
		dbg_tfr("remaining = %lld, done = %lld.\n",
			(s64)remaining, (s64)done);
	}
	/* return error or else number of bytes */
	res = res ? res : done;
	dbg_tfr("seq:%d char_sgdma_read_write() returns %lld.\n", seq, (s64)res);
	//engine_status_read(engine, 0);
#if XDMA_STATUS_DUMPS
	interrupt_status(lro);
#endif
	return res;
}

static ssize_t char_sgdma_read_cyclic(struct file *file, char __user *buf,
				      size_t count, loff_t *pos, int dir_to_dev)
{
	int rc;
	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;
	struct xdma_transfer *transfer;
	struct xdma_result *result;

	int head;
	int eop = 0;
	int packet_length = 0;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;
	/* XXX detect non-supported directions XXX */
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	transfer = engine->rx_transfer_cyclic;
	BUG_ON(!transfer);

	result = (struct xdma_result *)engine->rx_result_buffer_virt;
	BUG_ON(!result);

	dbg_tfr("char_sgdma_read_cyclic()");

	result = (struct xdma_result *)engine->rx_result_buffer_virt;
	/* wait for result at head pointer */
	while (result[engine->rx_head].status == 0) {
		rc = wait_event_interruptible(transfer->wq, result[engine->rx_head].status != 0);
		if (rc) {
			dbg_tfr("char_sgdma_read_cyclic(): wait_event_interruptible() = %d\n", rc);
			return rc;
		}
	}

	spin_lock(&engine->lock);

	/* overrun condition? */
	if (engine->rx_overrun) {
		/* reset overrun flag */
		engine->rx_overrun = 0;
		spin_unlock(&engine->lock);
		/* report overrun */
		return -EIO;
	}

	/* where the host currently is in the ring buffer */
	head = engine->rx_head;
	/* iterate over newly received results */
	while (result[engine->rx_head].status) {
		int fault = 0;
		dbg_tfr("result[engine->rx_head=%3d].status = 0x%08x, rx->length = %d\n",
			engine->rx_head, (int)result[engine->rx_head].status, (int)result[engine->rx_head].length);

		/* overrun occurs when the tail is incremented and then matches head, not here */
		if (engine->rx_head == engine->rx_tail) {
			printk(KERN_DEBUG "engine->rx_head == engine->rx_tail, breaking out.");
			break;
		} else if ((result[engine->rx_head].status >> 16) != 0x52b4) {
				printk(KERN_DEBUG "engine->rx_head has no result magic 0x52b4");
				fault = 1;
			} else if (result[engine->rx_head].length > 4096) {
				printk(KERN_DEBUG "engine->rx_head length exceeds 4096 bytes");
				fault = 1;
			} else if (result[engine->rx_head].length == 0) {
				printk(KERN_DEBUG "engine->rx_head length is zero bytes");
				fault = 1;
				/* valid result */
			} else {
				packet_length += result[engine->rx_head].length;
				/* seen eop? */
				if (result[engine->rx_head].status & RX_STATUS_EOP) {
					dbg_tfr("char_sgdma_read_cyclic(): packet_length = %d (with EOP)\n", packet_length);
					eop = 1;
				} else {
					dbg_tfr("char_sgdma_read_cyclic(): packet_length = %d (ongoing, no EOP yet)\n", packet_length);
				}
			}
		/* clear result */
		result[engine->rx_head].status = 0;
		result[engine->rx_head].length = 0;
		/* proceed head pointer so we make progress, even when fault */
		engine->rx_head = (engine->rx_head + 1) % RX_BUF_PAGES;
		/* unexpected result */
		if (fault) { printk(KERN_DEBUG "char_sgdma_read_cyclic() fault %d\n", fault); spin_unlock(&engine->lock); return -EIO; }
		/* end-of-packet flag, exit the loop */
		if (eop) break;
	}
	spin_unlock(&engine->lock);
	/* EOP found? Transfer anything from head to EOP */
	if (eop) {
		int remaining = packet_length;
		int done = 0;
		while (remaining) {
			int copy = remaining > 4096? 4096: remaining;
			dbg_tfr("char_sgdma_read_cyclic(): copy %d bytes from %p to %p\n", copy, (void *)&engine->rx_buffer[head * 4096], (void *)&buf[done]);
			copy_to_user(&buf[done], &engine->rx_buffer[head * 4096], copy);
			remaining -= copy;
			done += copy;
			head = (head + 1) % RX_BUF_PAGES;
		}
	} else packet_length = 0;

	dbg_tfr("char_sgdma_read_cyclic() returns %d\n", packet_length);
	return packet_length;
}

static long char_sgdma_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;
	int rc = 0;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;

	if (cmd == IOCTL_XDMA_PERF_START) {
		/* performance measurement already running on this engine? */
		if (engine->xdma_perf) {
			dbg_perf("char_sgdma_ioctl(): IOCTL_XDMA_PERF_START failed, performance measurement already seems running!\n");
			return -EBUSY;
		}
		engine->xdma_perf = kzalloc(sizeof(struct xdma_performance_ioctl), GFP_KERNEL);
		if (!engine->xdma_perf) return -ENOMEM;
		rc = copy_from_user(engine->xdma_perf/*to*/,
				    (struct xdma_performance_ioctl *)arg,
				    sizeof(struct xdma_performance_ioctl));
		if (rc < 0) {
			dbg_perf("char_sgdma_ioctl(): Failed to copy from user space %p\n", arg);
			return -EINVAL;
		}
		if (engine->xdma_perf->version != IOCTL_XDMA_PERF_V1) {
			dbg_perf("Unsupported IOCTL version %d\n", engine->xdma_perf->version);
			return -EINVAL;
		}

		write_register(XDMA_PERF_CLEAR, &engine->regs->perf_ctrl);
		(void)read_register(&engine->regs->identifier);
		write_register(XDMA_PERF_AUTO | XDMA_PERF_RUN, &engine->regs->perf_ctrl);
		(void)read_register(&engine->regs->identifier);

		dbg_perf("IOCTL_XDMA_PERF_START, transfer_size = %d\n", engine->xdma_perf->transfer_size);
		/* initialize wait queue */
		init_waitqueue_head(&engine->xdma_perf_wq);
		xdma_performance_submit(lro, engine);

	} else if (cmd == IOCTL_XDMA_PERF_STOP) {
		struct xdma_transfer *transfer;

		dbg_perf("IOCTL_XDMA_PERF_STOP\n");
		/* no performance measurement running on this engine? */
		if (!engine->xdma_perf) {
			//spin_unlock(&engine->lock);
			return -EINVAL;
		}
		/* stop measurement */
		transfer = engine_cyclic_stop(engine);
		dbg_perf("IOCTL_XDMA_PERF_STOP: waiting for measurement to stop\n");

		if (engine->xdma_perf) {
			u32 v;
			u64 value;

			value = (u64)read_register(&engine->regs->completed_desc_count);
			engine->xdma_perf->iterations = value;

			value = (u64)read_register(&engine->regs->perf_cyc_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_cyc_lo);
			engine->xdma_perf->clock_cycle_count = value;

			value = (u64)read_register(&engine->regs->perf_dat_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_dat_lo);
			engine->xdma_perf->data_cycle_count = value;

			value = (u64)read_register(&engine->regs->perf_pnd_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_pnd_lo);
			engine->xdma_perf->pending_count = value;

			rc = copy_to_user((void __user *)arg/*to*/,
					  engine->xdma_perf/*from*/,
					  sizeof(struct xdma_performance_ioctl));
			if (rc) {
				return rc;
			}
		} else {
			dbg_perf("engine->xdma_perf == NULL?\n");
		}

		kfree(engine->xdma_perf);
		engine->xdma_perf = NULL;

	} else if (cmd == IOCTL_XDMA_PERF_GET) {
		dbg_perf("IOCTL_XDMA_PERF_GET\n");
		if (engine->xdma_perf) {
			u32 v;
			u64 value;

			value = (u64)read_register(&engine->regs->completed_desc_count);
			engine->xdma_perf->iterations = value;
			dbg_perf("completed desc count = %ld iterations = %ld\n",value,engine->xdma_perf->iterations);
			value = (u64)read_register(&engine->regs->perf_cyc_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_cyc_lo);
			engine->xdma_perf->clock_cycle_count = value;
			dbg_perf("clk cycle count = %ld iterations = %ld\n",value,engine->xdma_perf->clock_cycle_count);
			value = (u64)read_register(&engine->regs->perf_dat_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_dat_lo);
			engine->xdma_perf->data_cycle_count = value;

			value = (u64)read_register(&engine->regs->perf_pnd_hi) << 32;
			value |= (u64)read_register(&engine->regs->perf_pnd_lo);
			engine->xdma_perf->pending_count = value;
			rc = copy_to_user((void __user *)arg/*to*/,
					  engine->xdma_perf/*from*/,
					  sizeof(struct xdma_performance_ioctl));
			dbg_perf("copy_to_user() = %d\n", rc);
			return rc;
		} else {
			dbg_perf("engine->xdma_perf == NULL?\n");
			return -EPROTO;
		}
	} else if (cmd == IOCTL_XDMA_ADDRMODE_SET) {
		unsigned long dst;
		dbg_perf("IOCTL_XDMA_ADDRMODE_SET\n");
		rc = get_user(dst/*local destination variable*/, (int __user *)arg);
		if (rc == 0) {
			engine->non_incr_addr = !!dst;
			if (engine->non_incr_addr)
				write_register(XDMA_CTRL_NON_INCR_ADDR, &engine->regs->control_w1s);
			else
				write_register(XDMA_CTRL_NON_INCR_ADDR, &engine->regs->control_w1c);
		}
		engine_alignments(engine);

		return rc;
	} else if (cmd == IOCTL_XDMA_ADDRMODE_GET) {
		unsigned long src = !!engine->non_incr_addr;
		dbg_perf("IOCTL_XDMA_ADDRMODE_GET\n");
		rc = put_user(src/*local source variable*/, (int __user *)arg);
		return rc;
	} else { return -EINVAL; }
	return rc;
}

/* sg_write() -- Write to the device
 *
 * @buf userspace buffer
 * @count number of bytes in the userspace buffer
 * @pos byte-address in device
 */
static ssize_t char_sgdma_write(struct file *file, const char __user *buf,
				size_t count, loff_t *pos)
{
	return char_sgdma_read_write(file, (char *)buf, count, pos, 1/*dir_to_dev = 1*/);
}

/* char_sgdma_read() - Read from the device
 *
 * @buf userspace buffer
 * @count number of bytes in the userspace buffer
 *
 * Iterate over the userspace buffer, taking at most 255 * PAGE_SIZE bytes for
 * each DMA transfer.
 *
 * For each transfer, get the user pages, build a sglist, map, build a
 * descriptor table, submit the transfer, wait for the interrupt handler
 * to wake us on completion, free the sglist and descriptors.
 */
static ssize_t char_sgdma_read(struct file *file, char __user *buf,
			       size_t count, loff_t *pos)
{
	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;

	/* fetch device specific data stored earlier during open */
	lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;
	/* XXX detect non-supported directions XXX */
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	if (1 && !engine->dir_to_dev && engine->rx_buffer && engine->rx_transfer_cyclic) {
		return char_sgdma_read_cyclic(file, buf, count, pos, 0/*dir_to_dev = 0*/);
	} else {
		return char_sgdma_read_write(file, buf, count, pos, 0/*dir_to_dev = 0*/);
	}
}

/*
 * Called when the device goes from unused to used.
 */
static int char_open(struct inode *inode, struct file *file)
{
	struct xdma_char *lro_char;
	/* pointer to containing data structure of the character device inode */
	lro_char = container_of(inode->i_cdev, struct xdma_char, cdev);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

        /* create a reference to our char device in the opened file */
	file->private_data = lro_char;
	return 0;
}

/*
 * Called when the device goes from used to unused.
 */
static int char_close(struct inode *inode, struct file *file)
{
	struct xdma_dev *lro;
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	/* fetch device specific data stored earlier during open */
        printk(KERN_DEBUG "Closing node (0x%p, 0x%p)\n", inode, file);
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

    	return 0;
}

/*
 * Called when the device goes from unused to used.
 */
static int char_sgdma_open(struct inode *inode, struct file *file)
{
	int rc = 0;
	struct xdma_char *lro_char;
	struct xdma_dev *lro;
	struct xdma_engine *engine;

	/* pointer to containing data structure of the character device inode */
	lro_char = container_of(inode->i_cdev, struct xdma_char, cdev);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	/* create a reference to our char device in the opened file */
	file->private_data = lro_char;

	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	dbg_tfr("char_sgdma_open(0x%p, 0x%p)\n", inode, file);

	/* atomically set up ring buffer */
	spin_lock(&engine->lock);
	/* AXI ST C2H? Set up a receive ring buffer on the host with a cyclic transfer */
	if (engine->streaming && !engine->dir_to_dev) {
		engine->rx_tail = 0;
		engine->rx_head = 0;
		engine->rx_overrun = 0;
		if (engine->rx_buffer) {
			printk(KERN_INFO "Channel is already open, cannot be opened twice.\n");
			rc = -EBUSY;
			goto fail_in_use;
		}
		engine->rx_buffer = rvmalloc(RX_BUF_SIZE);
		if (engine->rx_buffer == NULL) {
			printk(KERN_INFO "rvmalloc(%d) failed\n", RX_BUF_SIZE);
			goto fail_buffer;
		}
		printk(KERN_INFO "engine->rx_buffer = %p\n", engine->rx_buffer);
		engine->rx_transfer_cyclic = transfer_create_kernel(lro, engine->rx_buffer, RX_BUF_SIZE, 0, engine->dir_to_dev, 1);
		if (engine->rx_buffer == NULL) {
			printk(KERN_INFO "transfer_create_kernel(%d) failed\n", RX_BUF_SIZE);
			goto fail_transfer;
		}
		engine->rx_result_buffer_virt = pci_alloc_consistent(lro->pci_dev, RX_BUF_PAGES * sizeof(struct xdma_result), &engine->rx_result_buffer_bus);
		if (engine->rx_result_buffer_virt == NULL) {
			printk(KERN_INFO "pci_alloc_consistent(%d) failed\n", RX_BUF_SIZE);
			goto fail_result_buffer;
		}
		dbg_init("engine->rx_result_buffer_virt = %p\n", engine->rx_result_buffer_virt);
		dbg_init("engine->rx_result_buffer_bus = %p\n", engine->rx_result_buffer_bus);
		/* replace source addresses with result write-back addresses */
		transfer_set_result_addresses(engine->rx_transfer_cyclic, engine->rx_result_buffer_bus);
		/* set control of all descriptors */
		transfer_set_all_control(engine->rx_transfer_cyclic, XDMA_DESC_EOP | XDMA_DESC_COMPLETED);
		/* make this a cyclic transfer */
		xdma_transfer_cyclic(engine->rx_transfer_cyclic);
		transfer_dump(engine->rx_transfer_cyclic);
		/* for streaming engines, allow only one user, allocate kernel buffer here */
		spin_unlock(&engine->lock);

		/* start cyclic transfer */
		if (engine->rx_transfer_cyclic) {
			transfer_queue(engine, engine->rx_transfer_cyclic);
		}
		return 0;
	}
	goto success;

/* unwind on errors */
fail_result_buffer:
	transfer_destroy(engine->lro, engine->rx_transfer_cyclic);
	engine->rx_transfer_cyclic = NULL;
fail_transfer:
	rvfree(engine->rx_buffer, RX_BUF_SIZE);
	engine->rx_buffer = NULL;
fail_buffer:
fail_in_use:
success:
	/* for streaming engines, allow only one user, allocate kernel buffer here */
	spin_unlock(&engine->lock);

	return rc;
}

/*
 * Called when the device goes from used to unused.
 */
static int char_sgdma_close(struct inode *inode, struct file *file)
{
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;
	struct xdma_dev *lro;
	struct xdma_engine *engine;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);

	/* fetch device specific data stored earlier during open */
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	engine = lro_char->engine;
	BUG_ON(!engine);
	BUG_ON(engine->magic != MAGIC_ENGINE);

	dbg_tfr("char_sgdma_close(0x%p, 0x%p)\n", inode, file);

	/* atomically stop and destroy cyclic transfer */
	spin_lock(&engine->lock);

	if (engine->streaming && !engine->dir_to_dev) {
		int rc;
		struct xdma_transfer *transfer = engine_cyclic_stop(engine);
		if (transfer) {
			dbg_tfr("char_sgdma_close() stopped transfer %p\n", transfer);
			if (transfer != engine->rx_transfer_cyclic) {
				dbg_tfr("char_sgdma_close() unexpected transfer %p vs engine->rx_transfer_cyclic = %p\n",
					transfer, engine->rx_transfer_cyclic);
			}
		}
		/* allow engine to be serviced after stop request */
		spin_unlock(&engine->lock);
		/* wait for engine to be no longer running */
		rc = wait_event_interruptible(engine->shutdown_wq, !engine->running);
		if (rc) {
			dbg_tfr("char_sgdma_close(): wait_event_interruptible(engine->shutdown_wq) = %d\n", rc);
			return rc;
		}
		if (engine->running) {
			dbg_tfr("char_sgdma_close(): engine still running?!\n");
			return -EINVAL;
		}
		dbg_tfr("char_sgdma_close(): wait_event_interruptible(engine->shutdown_wq) = %d\n", rc);

		/* obtain spin lock to atomically remove resources */
		spin_lock(&engine->lock);

		if (engine->rx_transfer_cyclic) {
			transfer_destroy(engine->lro, engine->rx_transfer_cyclic);
			engine->rx_transfer_cyclic = NULL;
		}
		if (engine->rx_buffer) {
			rvfree(engine->rx_buffer, RX_BUF_SIZE);
			engine->rx_buffer = NULL;
		}
		if (engine->rx_result_buffer_virt) {
			/* free contiguous list */
			pci_free_consistent(lro->pci_dev, RX_BUF_PAGES * sizeof(struct xdma_result), engine->rx_result_buffer_virt, engine->rx_result_buffer_bus);
			engine->rx_result_buffer_virt = NULL;
		}
	}
	spin_unlock(&engine->lock);
	return 0;
}

static int __devinit probe(struct pci_dev *pdev, const struct pci_device_id *id)
{
	int rc = 0;
	u16 dcr;
	u32 value;
	int dir_from_dev;
	int channel;
	struct xdma_dev *lro = NULL;
	struct xdma_bitstream_container *clear_contr = NULL;

	printk(KERN_DEBUG "probe(pdev = 0x%p, pci_id = 0x%p)\n", pdev, id);
	//SD_Accel Specific
	clear_contr = dev_get_drvdata(&pdev->dev);
	if (clear_contr)
		printk(KERN_INFO "%s: Found stashed clearing bitstream from previously loaded driver %p\n",
		       DRV_NAME, clear_contr);
	/* allocate zeroed device book keeping structure */
	lro = kzalloc(sizeof(struct xdma_dev), GFP_KERNEL);
	if (!lro) {
		printk(KERN_DEBUG "Could not kzalloc(xdma_dev).\n");
		goto err_alloc;
	}
	lro->magic = MAGIC_DEVICE;
	/* create a device to driver reference */
	dev_set_drvdata(&pdev->dev, lro);
	/* create a driver to device reference */
	lro->pci_dev = pdev;
	printk(KERN_DEBUG "probe() lro = 0x%p\n", lro);
	value = lro->pci_dev->subsystem_device;
	value >>= 4;
	value &= 0xf;
	if (value < 3) {
		printk(KERN_ERR "This driver does not support device version less than 3.0\n");
		rc = -ENXIO;
		goto err_enable;
	}
	/* initialize spinlock for atomically changing events_irq */
	spin_lock_init(&lro->events_lock);
	/* initialize wait queue for events */
	init_waitqueue_head(&lro->events_wq);

	lro->mcap_base = ULTRASCALE_MCAP_CONFIG_BASE;

	if (load_firmware && is_ultrascale(lro)) {
		if (clear_contr && (clear_contr->magic == 0xBBBBBBBBUL)) {
			/* Copy the stashed clear bitstream from previously loaded driver to this initialization of driver */
			memcpy(&lro->stash, clear_contr, sizeof(struct xdma_bitstream_container));
			kfree(clear_contr);
			clear_contr = NULL;
		}
		else {
			lro->stash.magic = 0xBBBBBBBBUL;
		}
		rc = load_boot_firmware(lro);
	}

	if (rc) {
		goto err_enable;
	}

	printk(KERN_DEBUG "pci_indevice()\n");
	rc = pci_enable_device(pdev);
	if (rc) {
		printk(KERN_DEBUG "pci_enable_device() failed, rc = %d.\n", rc);
		goto err_enable;
	}

	/* enable bus master capability */
	printk(KERN_DEBUG "pci_set_master()\n");
	pci_set_master(pdev);

	if (msi) {
		int i;
		int req_nvec = 32;
		/* enable message signaled interrupts */
		printk(KERN_DEBUG "pci_enable_msi()\n");
		rc = pci_enable_msi(pdev);
		if (rc < 0) {
			printk(KERN_DEBUG "Could not enable MSI interrupting; rc = %d.\n", rc);
			rc = -1;
			goto err_msi;
		}
		lro->msi_enabled = 1;
	}
	/* known root complex's max read request sizes */
#ifdef CONFIG_ARCH_TI816X
	printk(KERN_DEBUG "TI816X RC detected: limiting MaxReadReq size to 128 bytes.\n");
	pcie_set_readrq(pdev, 128);
#endif

	printk(KERN_DEBUG "pci_request_regions()\n");
	rc = pci_request_regions(pdev, DRV_NAME);
	/* could not request all regions? */
	if (rc) {
		printk(KERN_DEBUG "pci_request_regions() = %d, device in use?\n", rc);
		/* assume device is in use so do not disable it later */
		lro->regions_in_use = 1;
		goto err_regions;
	}
	lro->got_regions = 1;

	printk(KERN_DEBUG "map_bars()\n");
	/* map BARs */
	rc = map_bars(lro, pdev);
	if (rc)
		goto err_map;

	xdma_config(lro, 0x3000);
	printk("sizeof(dma_addr_t) == %lu.\n", sizeof(dma_addr_t));
#if !defined(__PPC64__)
	/* 64-bit addressing capability for XDMA? */
	if (!pci_set_dma_mask(pdev, DMA_BIT_MASK(64))) {
		/* query for DMA transfer */
		/* @see Documentation/DMA-mapping.txt */
		printk(KERN_DEBUG "pci_set_dma_mask()\n");
		/* use 64-bit DMA */
		printk(KERN_DEBUG "Using a 64-bit DMA mask.\n");
		/* use 32-bit DMA for descriptors */
		rc = pci_set_consistent_dma_mask(pdev, DMA_BIT_MASK(32));
		/* use 64-bit DMA, 32-bit for consistent */
	} else
#endif
		if (!pci_set_dma_mask(pdev, DMA_BIT_MASK(32))) {
			printk(KERN_DEBUG "Could not set 64-bit DMA mask.\n");
			rc = pci_set_consistent_dma_mask(pdev, DMA_BIT_MASK(32));
			/* use 32-bit DMA */
			printk(KERN_DEBUG "Using a 32-bit DMA mask.\n");
		} else {
			printk(KERN_DEBUG "No suitable DMA possible.\n");
			/** @todo Choose proper error return code */
			rc = -1;
			goto err_mask;
		}

	if (rc) {
		printk(KERN_ERR "%s: Unable to set DMA mask.\n", DRV_NAME);
		goto err_mask;
	}
	lro->irq_line = -1;

	/* request irq, MSI interrupts are not shared */
	printk(KERN_DEBUG "request_irq()\n");
	rc = request_irq(pdev->irq, xdma_isr,
			 lro->msi_enabled? 0: IRQF_SHARED, DRV_NAME, (void *)lro);
	if (rc) {
		printk(KERN_DEBUG "Could not request IRQ #%d; rc = %d.\n",
		       pdev->irq, rc);
		lro->irq_line = -1;
		goto err_irq;
	}
	/* remember the allocated irq */
	lro->irq_line = (int)pdev->irq;
	printk(KERN_DEBUG "Succesfully requested IRQ #%d with dev_id 0x%p\n",
	       lro->irq_line, lro);
	/* initialize user character device */
	lro->user_char_dev = create_sg_char(lro, 0/*bar*/, NULL, CHAR_USER);
	if (!lro->user_char_dev) {
		printk(KERN_DEBUG "create_char(user_char_dev) failed\n");
		goto err_user_cdev;
	}
	/* initialize control character device */
	lro->ctrl_char_dev = create_sg_char(lro, 1/*bar*/, NULL, CHAR_CTRL);
	if (!lro->ctrl_char_dev) {
		printk(KERN_DEBUG "create_char(ctrl_char_dev) failed\n");
		goto err_ctrl_cdev;
	}
	/* initialize events character device */
	lro->events_char_dev = create_sg_char(lro, -1/*bar*/, NULL, CHAR_EVENTS);
	if (!lro->events_char_dev) {
		printk(KERN_DEBUG "create_char(events_char_dev) failed\n");
		goto err_events_cdev;
	}
	/* initialize user character device */
	lro->bypass_char_dev = create_sg_char(lro, 2/*bar*/, NULL, CHAR_BYPASS);
	if (!lro->bypass_char_dev) {
		printk(KERN_DEBUG "create_char(bypass_char_dev) failed\n");
		goto err_bypass_cdev;
	}
	rc = interrupts_enable(lro, XDMA_OFS_INT_CTRL, 0x00ffffffUL);

	/* iterate over H2C (PCIe read), then C2H (PCIe write) */
	for (dir_from_dev = 0; dir_from_dev < 2; dir_from_dev++) {
		int dir_to_dev = !dir_from_dev;
		int channel;
		/* iterate over channels */
		for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
			u32 engine_id;
			u32 channel_id;
			u32 version;
			/* register offset for the engine */
			/* read channels at 0x0000, write channels at 0x1000, channels at 0x100 interval */
			int offset = (dir_from_dev * 0x1000U) + (channel * 0x100U);
			int sgdma_offset = offset;
			int streaming = 0;
			struct engine_regs *regs = lro->bar[XDMA_BAR_XDMA] + offset;
			struct engine_sgdma_regs *sgdma_regs;
			/* SGDMA descriptor fetcher */
#if USE_RTL_SGDMA_TARGET
			sgdma_offset += 0x4000U;
#endif
			sgdma_regs = lro->bar[XDMA_BAR_XDMA] + sgdma_offset;

			printk(KERN_DEBUG "Probing for channel %d %s engine at %p\n", channel, dir_to_dev?"H2C":"C2H", regs);
			/* read identifier/version */
			value = ioread32(&regs->identifier);
			dbg_init("Found Engine ID register value 0x%08x\n", value);

			engine_id = (value & 0xffff0000U) >> 16;
			channel_id = (value & 0x00000f00U) >> 8;
			if ((value & 0xfff00000U) != 0x1fc00000U) {
				dbg_init("Found Engine ID 0x%08x, skipping as it is unknown.\n", value);
				continue;
			}
			dbg_init("Found Engine ID value 0x%08x\n", engine_id);
			/* Target Channel ID*/
			channel_id = (value & 0x00000f00U) >> 8;
			if (channel_id != channel) {
				printk(KERN_DEBUG "Expected channel ID %d , but read channel ID %d\n", channel, channel_id);
				continue;
			}

			value = ioread32(&sgdma_regs->identifier);
			dbg_init("Read SGDMA ID value	0x%08x\n", value);
			//printk(KERN_DEBUG "SGDMA  ID 0x%04x\n", (value & 0xffff0000U) >> 16);

			value = ioread32(&regs->identifier);
			version = (value & 0x000000ffU);
			/* bit 15 indicates AXI ST */
			streaming = value & 0x8000U;
			/* no read engine identifier? */
			if (dir_to_dev) {
				if ((engine_id == XDMA_ID_H2C) && (channel_id == channel)) {
					dbg_init("Found channel %d H2C AXI %s engine at %p with identifier 0x%08x\n", channel, streaming?"ST":"MM", regs, (int)value);
					/* allocate and initialize H2C engine */
					lro->engine[channel][dir_from_dev] = engine_create(lro, offset, sgdma_offset, 1/*to_dev*/, channel, 0/*num_in_channel*/, streaming);
					if (!lro->engine[channel][dir_from_dev])
						goto err_engine;
				} else {
					printk(KERN_DEBUG "No H2C engine at %p for channel %d, read 0x%08x\n", regs, channel, (int)value);
					continue;
				}
			} else /*!dir_to_dev*/ {
				if ((engine_id == XDMA_ID_C2H) && (channel_id == channel)) {
					dbg_init("Found channel %d C2H AXI %s engine at %p with identifier 0x%08x\n", channel, streaming?"ST":"MM", regs, (int)value);
					/* allocate and initialize C2H engine */
					lro->engine[channel][dir_from_dev] = engine_create(lro, offset, sgdma_offset, 0/*to_dev*/, channel, 1/*num_in_channel*/, streaming);
					if (!lro->engine[channel][dir_from_dev])
						goto err_engine;
				} else {
					printk(KERN_DEBUG "No C2H engine at %p for channel %d, read 0x%08x\n", regs, channel, (int)value);
					continue;
				}
			}
		}
	}

	/* iterate over H2C (PCIe read), then C2H (PCIe write) */
	for (dir_from_dev = 0; dir_from_dev < 2; dir_from_dev++) {
		/* iterate over channels */
		for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
			/* engine? */
			if (lro->engine[channel][dir_from_dev]) {
				/* initialize XDMA character device */
				lro->sgdma_char_dev[channel][dir_from_dev] = create_sg_char(lro, -1/*bar*/, lro->engine[channel][dir_from_dev],
											    dir_from_dev? CHAR_XDMA_C2H: CHAR_XDMA_H2C);
				if (!lro->sgdma_char_dev[channel]) {
					printk(KERN_DEBUG "create_char(sgdma_char_dev) for channel %d CHAR_XDMA_%s failed\n", channel, dir_from_dev? "C2H": "H2C");
					goto err_sgdma_cdev;
				}
			}
		}
	}
	rc = device_create_file(&pdev->dev, &dev_attr_xdma_dev_instance);
	if (rc) {
		printk(KERN_DEBUG "Failed to create device file \n");
		goto err_sgdma_cdev;
	} else {
		printk(KERN_DEBUG "Device file created sux\n");
	}
	rc = 0;

	if (clear_contr && (clear_contr->magic == 0xBBBBBBBBUL)) {
		/* Copy the stashed clear bitstream from previously loaded driver to this initialization of driver */
		memcpy(&lro->stash, clear_contr, sizeof(struct xdma_bitstream_container));
		kfree(clear_contr);
		clear_contr = NULL;
	}
	else {
		lro->stash.magic = 0xBBBBBBBBUL;
	}

	lro->feature_id = find_feature_id(lro);

	fan_controller(lro);
	if (rc == 0) {
		show_device_info(lro);
		goto end;
	}

	/* iterate over channels */
	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		/* remove SG DMA character device */
		if (lro->sgdma_char_dev[channel][0]) {
			destroy_sg_char(lro->sgdma_char_dev[channel][0]);
			lro->sgdma_char_dev[channel][0] = NULL;
		}
		/* remove SG DMA character device */
		if (lro->sgdma_char_dev[channel][1]) {
			destroy_sg_char(lro->sgdma_char_dev[channel][1]);
			lro->sgdma_char_dev[channel][1] = NULL;
		}
	}

err_sgdma_cdev:
	/* destroy_engine */
err_engine:
	printk(KERN_DEBUG "err_interrupts");
	/* remove bypass character device */
	if (lro->bypass_char_dev)
		destroy_sg_char(lro->bypass_char_dev);
err_bypass_cdev:
	/* remove events character device */
	if (lro->events_char_dev)
		destroy_sg_char(lro->events_char_dev);
err_events_cdev:
	/* remove control character device */
	if (lro->ctrl_char_dev)
		destroy_sg_char(lro->ctrl_char_dev);
err_ctrl_cdev:
	/* remove user character device */
	if (lro->user_char_dev)
		destroy_sg_char(lro->user_char_dev);
err_user_cdev:
err_mask:
err_msi:
	/* disable the device only if it was not in use */
	if (!lro->regions_in_use)
		pci_disable_device(pdev);
	/* free allocated irq */
	if (lro->irq_line > -1)
		free_irq(lro->irq_line, (void *)lro);
err_irq:
	//SD_Accel
	/* disable message signaled interrupts */
	if (lro->msi_enabled)
		pci_disable_msi(pdev);
err_system:
err_map:
	/* unmap the BARs */
	unmap_bars(lro, pdev);
	if (lro->got_regions)
		pci_release_regions(pdev);
err_regions:
	/* disable message signaled interrupts */
	if (lro->msi_enabled)
		pci_disable_msi(pdev);
err_rev:
/* clean up everything before device enable() */
err_enable:
	kfree(lro);
	dev_set_drvdata(&pdev->dev, NULL);
err_alloc:
end:
	return rc;
}

static void __devexit remove(struct pci_dev *pdev)
{
	int channel;
	struct xdma_dev *lro;
	struct xdma_bitstream_container *clear_contr = NULL;

	printk(KERN_DEBUG "remove(0x%p)\n", pdev);
	if ((pdev == 0) || (dev_get_drvdata(&pdev->dev) == 0)) {
		printk(KERN_DEBUG
		       "remove(dev = 0x%p) pdev->dev.driver_data = 0x%p\n",
		       pdev, dev_get_drvdata(&pdev->dev));
		return;
	}
	lro = (struct xdma_dev *)dev_get_drvdata(&pdev->dev);
	printk(KERN_DEBUG
	       "remove(dev = 0x%p) where pdev->dev.driver_data = 0x%p\n",
	       pdev, lro);
	if (lro->pci_dev != pdev) {
		printk(KERN_DEBUG
		       "pdev->dev.driver_data->pci_dev (0x%08lx) != pdev (0x%08lx)\n",
		       (unsigned long)lro->pci_dev, (unsigned long)pdev);
	}

	/* iterate over channels */
	for (channel = 0; channel < XDMA_CHANNEL_NUM_MAX; channel++) {
		/* remove SG DMA character device */
		if (lro->sgdma_char_dev[channel][0]) {
			destroy_sg_char(lro->sgdma_char_dev[channel][0]);
			lro->sgdma_char_dev[channel][0] = NULL;
		}
		/* remove SG DMA character device */
		if (lro->sgdma_char_dev[channel][1]) {
			destroy_sg_char(lro->sgdma_char_dev[channel][1]);
			lro->sgdma_char_dev[channel][1] = NULL;
		}
	}
        /* remove bypass character device */
	if (lro->bypass_char_dev) {
		destroy_sg_char(lro->bypass_char_dev);
		lro->bypass_char_dev = 0;
	}
	/* remove events character device */
	if (lro->events_char_dev) {
		destroy_sg_char(lro->events_char_dev);
		lro->events_char_dev = 0;
	}
	/* remove control character device */
	if (lro->ctrl_char_dev) {
		destroy_sg_char(lro->ctrl_char_dev);
		lro->ctrl_char_dev = 0;
	}
	/* remove user character device */
	if (lro->user_char_dev) {
		destroy_sg_char(lro->user_char_dev);
		lro->user_char_dev = 0;
	}

	/* free IRQ */
	if (lro->irq_line >= 0) {
		printk(KERN_DEBUG "Freeing IRQ #%d for dev_id 0x%08lx.\n",
		       lro->irq_line, (unsigned long)lro);
		free_irq(lro->irq_line, (void *)lro);
	}
	/* MSI was enabled? */
	if (lro->msi_enabled) {
		/* Disable MSI @see Documentation/MSI-HOWTO.txt */
		printk(KERN_DEBUG "Disabling MSI interrupting.\n");
		pci_disable_msi(pdev);
		lro->msi_enabled = 0;
	}
	/* unmap the BARs */
	unmap_bars(lro, pdev);
	printk(KERN_DEBUG "Unmapping BARs.\n");
	if (!lro->regions_in_use) {
		printk(KERN_DEBUG "Disabling device.\n");
		pci_disable_device(pdev);
	}
	if (lro->got_regions)
		/* to be called after pci_disable_device()! */
		pci_release_regions(pdev);

        dev_present[lro->instance] = 0;
        device_remove_file(&pdev->dev, &dev_attr_xdma_dev_instance);

//SD_Accel
        if (is_ultrascale(lro)) {
		/* For Ultrascale stash the clearing bitstream as driver data with device */
		/* It will be retrieved next time driver is loaded and used with the next PR bitstream */
		clear_contr = kmalloc(sizeof(struct xdma_bitstream_container), GFP_KERNEL);
		if (clear_contr)
			memcpy(clear_contr, &lro->stash, sizeof(struct xdma_bitstream_container));
	}
	kfree(lro);
	dev_set_drvdata(&pdev->dev, clear_contr);
}

/* maps the PCIe BAR into user space for memory-like access using mmap() */
static int bridge_mmap(struct file *file, struct vm_area_struct *vma)
{
	int rc;
	struct xdma_dev *lro;
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;
	unsigned long off;
	unsigned long phys;
	unsigned long vsize;
	unsigned long psize;
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	off = vma->vm_pgoff << PAGE_SHIFT;
	/* BAR physical address */
	phys = pci_resource_start(lro->pci_dev, lro_char->bar) + off;
	vsize = vma->vm_end - vma->vm_start;
	/* complete resource */
	psize = pci_resource_end(lro->pci_dev, lro_char->bar) - pci_resource_start(lro->pci_dev, lro_char->bar) + 1 - off;

	printk(KERN_DEBUG "mmap(): lro_char = 0x%08lx\n", (unsigned long)lro_char);
	printk(KERN_DEBUG "mmap(): lro_char->bar = %d\n", lro_char->bar);
	printk(KERN_DEBUG "mmap(): lro = 0x%p\n", lro);
	printk(KERN_DEBUG "mmap(): pci_dev = 0x%08lx\n", (unsigned long)lro->pci_dev);

	printk(KERN_DEBUG "off = 0x%lx\n", off);
	printk(KERN_DEBUG "start = 0x%llx\n", (unsigned long long)pci_resource_start(lro->pci_dev, lro_char->bar));
	printk(KERN_DEBUG "phys = 0x%lx\n", phys);

	if (vsize > psize)
		return -EINVAL;
	/* pages must not be cached as this would result in cache line sized
	   accesses to the end point */
	vma->vm_page_prot = pgprot_noncached(vma->vm_page_prot);
	/* prevent touching the pages (byte access) for swap-in,
	   and prevent the pages from being swapped out */
#ifndef VM_RESERVED
	vma->vm_flags |= VM_IO | VM_DONTEXPAND | VM_DONTDUMP;
#else
	vma->vm_flags |= VM_IO | VM_RESERVED;
#endif
	/* make MMIO accessible to user space */
	rc = io_remap_pfn_range(vma, vma->vm_start, phys >> PAGE_SHIFT,
				vsize, vma->vm_page_prot);
	printk(KERN_DEBUG "io_remap_pfn_range(vma=0x%p, vma->vm_start=0x%lx, phys=0x%lx, size=%lu) = %d\n",
	       vma, vma->vm_start, phys >> PAGE_SHIFT, vsize, rc);
	if (rc)
		return -EAGAIN;
	//vma->vm_ops = &vm_ops;
	return 0;
}

static ssize_t char_ctrl_read(struct file *file, char __user *buf,
			      size_t count, loff_t *pos)
{
	u32 w;
	void *reg;
	struct xdma_dev *lro;
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;

	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	/* only 32-bit aligned and 32-bit multiples */
	if (*pos & 3) return -EPROTO;
	/* first address is BAR base plus file position offset */
	reg = lro->bar[lro_char->bar] + *pos;
	w = read_register(reg);
	printk(KERN_DEBUG "char_ctrl_read(@%p, count=%ld, pos=%d) value = 0x%08x\n", reg, (long)count, (int)*pos, w);
	copy_to_user(buf, &w, 4);
	*pos += 4;
	return 4;
}

static ssize_t char_ctrl_write(struct file *file, const char __user *buf,
			       size_t count, loff_t *pos)
{
	u32 w;
	void *reg;
	struct xdma_dev *lro;
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;

	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	/* only 32-bit aligned and 32-bit multiples */
	if (*pos & 3) return -EPROTO;
	/* first address is BAR base plus file position offset */
	reg = lro->bar[lro_char->bar] + *pos;
	copy_from_user(&w, buf, 4);
	printk(KERN_DEBUG "char_ctrl_write(0x%08x @%p, count=%ld, pos=%d)\n", w, reg, (long)count, (int)*pos);
	write_register(w, reg);
	*pos += 4;
	return 4;
}

static ssize_t char_llseek(struct file *file, loff_t offset, int whence)
{
	loff_t newpos = 0;
	if (whence == 0)
		newpos = offset;
	file->f_pos = newpos;
	printk(KERN_DEBUG "llseek: pos=%lld\n", (signed long long)newpos);
	return newpos;
}

/*
 * character device file operations for events
 */
static ssize_t char_events_read(struct file *file, char __user *buf,
				size_t count, loff_t *pos)
{
	int rc;
	struct xdma_dev *lro;
	struct xdma_char *lro_char = (struct xdma_char *)file->private_data;
        u32 events_user;
	unsigned long flags;

	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);
	lro = lro_char->lro;
	BUG_ON(!lro);
	BUG_ON(lro->magic != MAGIC_DEVICE);

	if (count != 4) return -EPROTO;
	if (*pos & 3) return -EPROTO;

	/* sleep until any interrupt events have occurred, or a signal arrived */
	rc = wait_event_interruptible(lro->events_wq, lro->events_irq != 0);
	if (rc) printk(KERN_INFO "char_events_read(): wait_event_interruptible() = %d\n", rc);
	/* wait_event_interruptible() was interrupted by a signal */
	if (rc == -ERESTARTSYS) {
		return -ERESTARTSYS;
	}

	/* atomically decide which events are passed to the user */
	spin_lock_irqsave(&lro->events_lock, flags);
	events_user = lro->events_irq;
	lro->events_irq = 0;
	spin_unlock_irqrestore(&lro->events_lock, flags);


	//printk(KERN_INFO "wait_event_interruptible() = %d, events_irq = 0x%08lx\n", rc, lro->events_irq);
	copy_to_user(buf, &events_user, 4);

	return 4;
}
/*
 * character device file operations for SG DMA engine
 */
static struct file_operations sg_fops = {
	.owner = THIS_MODULE,
	.open = char_sgdma_open,
	.release = char_sgdma_close,
	.read = char_sgdma_read,
	.write = char_sgdma_write,
	.unlocked_ioctl = char_sgdma_ioctl,
	.llseek = char_sgdma_llseek,
	/* asynchronous */
#if !defined(XDMA_NEW_AIO)
	.aio_read = sg_aio_read,
	.aio_write = sg_aio_write,
#endif
};

/*
 * character device file operations for control bus (through control bridge)
 */
static struct file_operations ctrl_fops = {
	.owner = THIS_MODULE,
	.open = char_open,
	.release = char_close,
	.read = char_ctrl_read,
	.write = char_ctrl_write,
	.mmap = bridge_mmap,
//SD_Accel
        .unlocked_ioctl = char_ctrl_ioctl,
};

/*
 * character device file operations for the irq events
 */
static struct file_operations events_fops = {
	.owner = THIS_MODULE,
	.open = char_open,
	.release = char_close,
	.read = char_events_read,
};


static int destroy_sg_char(struct xdma_char *lro_char)
{
	BUG_ON(!lro_char);
	BUG_ON(lro_char->magic != MAGIC_CHAR);
	BUG_ON(!lro_char->lro);
	BUG_ON(!g_xdma_class);
	BUG_ON(!lro_char->sys_device);
	if (lro_char->sys_device)
		device_destroy(g_xdma_class, lro_char->cdevno);
	cdev_del(&lro_char->cdev);
	unregister_chrdev_region(lro_char->cdevno, 1/*count*/);
	kfree(lro_char);
	return 0;
}

#define XDMA_MINOR_BASE (0)
#define XDMA_MINOR_COUNT (255)

/* create_char() -- create a character device interface to data or control bus
 *
 * If at least one SG DMA engine is specified, the character device interface
 * is coupled to the SG DMA file operations which operate on the data bus. If
 * no engines are specified, the interface is coupled with the control bus.
 */
static struct xdma_char *create_sg_char(struct xdma_dev *lro, int bar,
					struct xdma_engine *engine, int type)
{
	struct xdma_char *lro_char;
	int rc;
	int minor;

	static const char *names[6] = { "xcldma%d_user", "xcldma%d_control", "xcldma%d_events", "xcldma%d_bypass", "xcldma%d_h2c_%d", "xcldma%d_c2h_%d" };
	printk(KERN_DEBUG DRV_NAME " create_sg_char(lro = 0x%p, engine = 0x%p)\n",
	       lro, engine);
	/* allocate book keeping data structure */
	lro_char = kzalloc(sizeof(struct xdma_char), GFP_KERNEL);
	if (!lro_char)
		return NULL;
	lro_char->magic = MAGIC_CHAR;

	/* new instance? */
	if (lro->major == 0) {
		int i = 0;
		// find first free instance number
		while ((dev_present[i] == 1) && (i < MAX_XDMA_DEVICES))
			i++;
		if (i == MAX_XDMA_DEVICES) {
			printk(KERN_DEBUG "Device limit reached\n");
			goto fail_alloc;
		}
		dev_present[i] = 1;
		lro->instance = i;

		/* dynamically pick a number into cdevno */
		if (major == 0) {
			/* allocate a dynamically allocated character device node */
			rc = alloc_chrdev_region(&lro_char->cdevno, XDMA_MINOR_BASE,
						 XDMA_MINOR_COUNT, DRV_NAME);
			/* remember */
			lro->major = MAJOR(lro_char->cdevno);
			printk(KERN_DEBUG "Dynamically allocated major %d, rc = %d\n", lro->major, rc);
			/* major number given, calculate minor into cdevno */
		} else {
			lro->major = major--;
			printk(KERN_DEBUG "Reusing allocated major %d\n", lro->major);
		}
	} else {

	}
        /* minor number is type index for non-SGDMA interfaces */
	minor = type;

	/* minor number is calculated for-SGDMA interfaces */
	if ((type == CHAR_XDMA_H2C) || (type == CHAR_XDMA_C2H)) {
		BUG_ON(!engine);
		BUG_ON(engine->number_in_channel >= 2);
		minor = 32 * (1 + engine->number_in_channel) + engine->channel;
	}
	lro_char->cdevno = MKDEV(lro->major, minor);
	/* do not register yet, create kobjects and name them,
	 * re-use the name during single-minor registration */

	/* are we dealing with a SG DMA character device interface? */
	if (type == CHAR_XDMA_H2C) {
		/* couple the SG DMA device file operations to the character device */
		cdev_init(&lro_char->cdev, &sg_fops);
		rc = kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance, engine->channel);
		WARN_ON(rc);
		printk(KERN_DEBUG DRV_NAME "%d_h2c_%d= %d:%d\n", lro->instance, engine->channel,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));
		/* remember engines */
		lro_char->engine = engine;
		/* user character device interface? */
	} else if (type == CHAR_XDMA_C2H) {
		/* couple the SG DMA device file operations to the character device */
		cdev_init(&lro_char->cdev, &sg_fops);
		/* @todo */
		rc = kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance, engine->channel);
		WARN_ON(rc);
		printk(KERN_DEBUG DRV_NAME "%d_c2h_%d = %d:%d\n", lro->instance, engine->channel,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));
		/* remember engines */
		lro_char->engine = engine;

		/* user character device interface? */
	} else if (type == CHAR_USER) {
		BUG_ON(engine);
		/* remember BAR we are attached to */
		lro_char->bar = bar;
		/* couple the control device file operations to the character device */
		cdev_init(&lro_char->cdev, &ctrl_fops);
		kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance);
		printk(KERN_DEBUG DRV_NAME "%d_user = %d:%d\n", lro->instance,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));
		/* control character device interface */
	} else if (type == CHAR_CTRL) {
		BUG_ON(engine);
		/* remember BAR we are attached to */
		lro_char->bar = bar;
		/* couple the control device file operations to the character device */
		cdev_init(&lro_char->cdev, &ctrl_fops);
		kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance);
		printk(KERN_DEBUG DRV_NAME "%d_control = %d:%d\n", lro->instance,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));
	} else if (type == CHAR_EVENTS) {
		BUG_ON(engine);
		/* couple the events device file operations to the character device */
		cdev_init(&lro_char->cdev, &events_fops);
		kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance);
		printk(KERN_DEBUG DRV_NAME "%d_events = %d:%d\n", lro->instance,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));

	} else if (type == CHAR_BYPASS) {
		BUG_ON(engine);
		/* remember BAR we are attached to */
		lro_char->bar = bar;
		/* couple the control device file operations to the character device */
		cdev_init(&lro_char->cdev, &ctrl_fops);
		kobject_set_name(&lro_char->cdev.kobj, names[type], lro->instance);
		printk(KERN_DEBUG DRV_NAME "%d_bypass = %d:%d\n", lro->instance,
		       MAJOR(lro_char->cdevno), MINOR(lro_char->cdevno));
	}
	lro_char->cdev.owner = THIS_MODULE;

	rc = 0;
	if (major) {
		printk(KERN_INFO "register_chrdev_region(%s)\n", lro_char->cdev.kobj.name);
		rc = register_chrdev_region(lro_char->cdevno, 1, lro_char->cdev.kobj.name);
	}

	if (rc < 0) {
		printk(KERN_INFO "register_chrdev_region()=%d failed.\n", rc);
		goto fail_alloc;
	}


	/* remember parent */
	lro_char->lro = lro;

	/* bring character device live */
	rc = cdev_add(&lro_char->cdev, lro_char->cdevno, XDMA_MINOR_COUNT);
	if (rc < 0) {
		printk(KERN_DEBUG "cdev_add() = %d\n", rc);
		goto fail_add;
	}
	/* create device on our class */
	if (g_xdma_class) {
		/* this must match the enumeration of CHAR_ */
		static const char *name[6] = { "xcldma%d_user", "xcldma%d_control", "xcldma%d_events", "xcldma%d_bypass", "xcldma%d_h2c_%d", "xcldma%d_c2h_%d" };
		BUG_ON(type > 5);

		lro_char->sys_device = device_create(g_xdma_class,
						     &lro->pci_dev->dev, lro_char->cdevno, NULL/*driver data*/,
						     name[type], lro->instance, engine? engine->channel: 0);
		if (!lro_char->sys_device) {
			printk(KERN_DEBUG "device_create(%s) failed\n", name[type]);
			goto fail_device;
		}
	}

	goto success;
fail_device:
	cdev_del(&lro_char->cdev);
fail_add:
	unregister_chrdev_region(lro_char->cdevno, XDMA_MINOR_COUNT);
fail_alloc:
	kfree(lro_char);
	lro_char = NULL;
success:
	return lro_char;
}

static struct pci_driver pci_driver = {
	.name = DRV_NAME,
	.id_table = pci_ids,
	.probe = probe,
	.remove = remove,
	/* resume, suspend are optional */
};

static int __init xdma_init(void)
{
	int i;
	int rc = 0;
	printk(KERN_INFO DRV_NAME " init()\n");

	g_xdma_class = class_create(THIS_MODULE, DRV_NAME);
	if (IS_ERR(g_xdma_class)) {
		printk(KERN_DEBUG DRV_NAME ": failed to create class");
		rc = -1;
		goto err_class;
	}
	rc = pci_register_driver(&pci_driver);
	/* zero out dev_present array */
	for (i = 0; i < MAX_XDMA_DEVICES; i++)
		dev_present[i] = 0;

err_class:
	return rc;
}

static void __exit xdma_exit(void)
{
	printk(KERN_INFO DRV_NAME" exit()\n");
	/* unregister this driver from the PCI bus driver */
	pci_unregister_driver(&pci_driver);
	if (g_xdma_class)
		class_destroy(g_xdma_class);
}

module_init(xdma_init);
module_exit(xdma_exit);
