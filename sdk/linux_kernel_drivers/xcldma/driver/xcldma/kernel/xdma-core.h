/**
 *  Copyright (C) 2015-2016 Xilinx, Inc. All rights reserved.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 */

#include <linux/cdev.h>

#include "xdma-ioctl.h"

#define DRV_NAME "xcldma"

#define XDMA_KNOWN_REVISION (0x01)
#define XDMA_BAR_NUM (2)

#define XDMA_BAR_XDMA (1)

#define USER_BAR (0)

#define XDMA_BAR (1)
/* maximum amount of register space to map */
#define XDMA_BAR_SIZE (0x8000UL)

/* only support one card in the system */
#define XDMA_CARDS_MAX (1)

#define XDMA_CHANNEL_NUM_MAX (4)
/* engines per channel */
#define XDMA_ENGINE_NUM (2)
/* interrupts per engine, rad2_vul.sv:237 .REG_IRQ_OUT	(reg_irq_from_ch[(channel*2) +: 2]), */
#define XDMA_ENG_IRQ_NUM (1)

#define MAX_EXTRA_ADJ (15)

#define RX_STATUS_EOP (1)

#define MAGIC_BITSTREAM 0xBBBBBBBBUL
#define MAGIC_ENGINE 0xEEEEEEEEUL
#define MAGIC_DEVICE 0xDDDDDDDDUL
#define MAGIC_CHAR 0xCCCCCCCCUL

/** bits of the SG DMA control register */
#define XDMA_CTRL_RUN_STOP (1UL << 0)
#define XDMA_CTRL_IE_DESCRIPTOR_STOPPED (1UL << 1)
#define XDMA_CTRL_IE_DESCRIPTOR_COMPLETED (1UL << 2)
#define XDMA_CTRL_IE_DESCRIPTOR_ALIGN_MISMATCH (1UL << 3)
#define XDMA_CTRL_IE_MAGIC_STOPPED (1UL << 4)
#define XDMA_CTRL_IE_IDLE_STOPPED (1UL << 6)
#define XDMA_CTRL_IE_NONALIGNED_STOPPED (1UL << 9)
#define XDMA_CTRL_IE_READ_ERROR (0x1FUL << 9)
#define XDMA_CTRL_IE_DESCRIPTOR_ERROR (0x1FUL << 19)
#define XDMA_CTRL_NON_INCR_ADDR (1UL << 25)
#define XDMA_CTRL_RST (1UL << 31)

/* Target internal components on BAR1 */
#define XDMA_OFS_CONFIG	                (0x0000UL)
#define XDMA_OFS_INT_CTRL		(0x2000UL)

#define XDMA_DRIVER_MAJOR 2016
#define XDMA_DRIVER_MINOR 4
#define XDMA_DRIVER_PATCHLEVEL 1

#define write_register(value, iomem) do { iowrite32(value, iomem); } while(0)
#define read_register(iomem) ioread32(iomem)

/*
 * XDMA character device specific book keeping. Each bus has a character device,
 * the control bus has no XDMA engines attached to it.
 */

struct xdma_bitstream_container {
	/* MAGIC_BITSTREAM == 0xBBBBBBBBUL */
	unsigned long magic;
	char *clear_bitstream;
	u32 clear_bitstream_length;
};

/*
 * XDMA character device specific book keeping. Each bus has a character device,
 * the control bus has no XDMA engines attached to it.
 */
struct xdma_char {
	/* MAGIC_CHAR == 0xCCCCCCCC */
	unsigned long magic;
	/* parent device */
	struct xdma_dev *lro;
	/* character device major:minor */
	dev_t cdevno;
	/* character device (embedded struct) */
	struct cdev cdev;
	/* for character devices on a control bus, -1 otherwise */
	int bar;
	/* for character device interfaces to the data bus, the SG DMA read engine */
	struct xdma_engine *engine;
	/* sysfs device */
	struct device *sys_device;
};

/*
 * XDMA PCIe device specific bookkeeping
 */
struct xdma_dev {
	/* MAGIC_DEVICE == 0xDDDDDDDD */
	unsigned long magic;
	/* the kernel pci device data structure provided by probe() */
	struct pci_dev *pci_dev;

	/*
	 * kernel virtual address of the mapped BAR regions. See (un)map_bars().
	 */
	void *__iomem bar[XDMA_BAR_NUM];
	/*
	 * bus address of the descriptor list in Root Complex memory
	 */
	dma_addr_t table_bus;
	/* if the device regions could not be allocated, assume and remember it
	 * is in use by another driver; this driver must not disable the device.
	 */
	int regions_in_use;
	/* whether msi was enabled for the device */
	int msi_enabled;

	struct msix_entry entry[32];

	/* whether this driver could obtain the regions */
	int got_regions;
	/* irq line succesfully requested by this driver, -1 otherwise */
	int irq_line;

	/* board revision */
	u8 revision;
	/* core capabilities */
	u32 capabilities;
#define CAP_64BIT_DMA 2
#define CAP_64BIT_DESC 4
#define CAP_ENGINE_WRITE 8
#define CAP_ENGINE_READ 16
	/* interrupt count, incremented by the interrupt handler */
	int irq_count;
	/* instance number */
	int instance;
	/* major number */
	int major;
	/* character device major:minor base */
	dev_t cdevno_base;
	/* character device structures */
	struct xdma_char *user_char_dev;
	struct xdma_char *ctrl_char_dev;
	struct xdma_char *events_char_dev;
	struct xdma_char *bypass_char_dev;
	struct xdma_char *sgdma_char_dev[XDMA_CHANNEL_NUM_MAX][2];
	/* number of engines in the system */
	int engines_num;
	struct xdma_engine *engine[XDMA_CHANNEL_NUM_MAX][2];

	/* cumulated (OR'd) irq events */
	u32 events_irq;
	/* spinlock to atomically change events_irq */
	spinlock_t events_lock;
	/* wait queue for synchronously waiting threads */
	wait_queue_head_t events_wq;
//SD_Accel
        struct xdma_bitstream_container stash;
	int axi_gate_frozen;
	unsigned long user_char_dev_opened;
	int mcap_base;
        u64 feature_id;
	// Keeps track of target frequencies requested for this device's OCL region
	unsigned short ocl_frequency[OCL_NUM_CLOCKS];
};

struct xdma_ocl_clockwiz {
	/* target frequency */
	unsigned short ocl;
	/* config0 register */
	unsigned short config0;
	/* config2 register */
	unsigned short config2;
};

struct xdma_ioc_info;
struct xdma_ioc_info2;

long char_ctrl_ioctl(struct file *filp, unsigned int cmd, unsigned long arg);

long load_boot_firmware(struct xdma_dev *lro);

long bitstream_clear_icap(struct xdma_dev *lro);

int interrupts_enable(struct xdma_dev *lro, int interrupts_offset, u32 mask);

void engine_reinit(const struct xdma_engine *engine);

long bitstream_ioctl(struct xdma_char *lro_char, unsigned int cmd, const void __user *arg);

void freezeAXIGate(struct xdma_dev *lro);

void freeAXIGate(struct xdma_dev *lro);

long reset_device_if_running(struct xdma_dev *lro);

u64 featureid(struct xdma_dev *lro);

int load_reset_mini_bitstream(struct xdma_dev *lro);

int device_info(const struct xdma_dev *lro, struct xdma_ioc_info2 *obj);

int load_reset_mini_bitstream(struct xdma_dev *lro);

bool is_ultrascale(const struct xdma_dev *lro);

bool is_XPR(const struct xdma_dev *lro);

bool is_multiple_clock(const struct xdma_dev *lro);

bool is_sysmon_supported(const struct xdma_dev *lro);

void convert_to_info(struct xdma_ioc_info2 *info2, struct xdma_ioc_info *info);

long ocl_freqscaling2(struct xdma_dev *lro, bool force);
