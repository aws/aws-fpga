/*
 * Copyright 2015-2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/** @file
 * FPGA common header 
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#define FPGA_SLOT_MAX           8
#define AFI_ID_STR_MAX			64
#define FPGA_DDR_IFS_MAX		4

/**
 * FPGA Mixed Mode Clock Manager (MMCM) config.
 *
 * MMCM Groups A, B, C are 0, 1, 2 respectively
 */
#define FPGA_MMCM_GROUP_MAX         3
#define FPGA_MMCM_OUT_CLKS_MAX      7
#define CLOCK_COUNT_A		4
#define CLOCK_COUNT_B		2
#define CLOCK_COUNT_C		2

/**
 * Common FPGA command flags.
 */
enum {
	/** reserved */
	FPGA_CMD_RSVD = 1 << 0,
	/** return FPGA image hardware metrics */ 
	FPGA_CMD_GET_HW_METRICS = 1 << 1,
	/** return FPGA image hardware metrics (clear on read */ 
	FPGA_CMD_CLEAR_HW_METRICS = 1 << 2,
	FPGA_CMD_FORCE_SHELL_RELOAD = 1 << 3,

	FPGA_CMD_ALL_FLAGS = FPGA_CMD_GET_HW_METRICS | 
		FPGA_CMD_CLEAR_HW_METRICS|
		FPGA_CMD_FORCE_SHELL_RELOAD,
};

/** 
 * FPGA specific errors
 * e.g. as returned by fpga-load-local-image, fpga-clear-local-image,
 *   and fpga-describe-local-image.
 *
 *  -note that these must fit into an int32_t and must be positive integers.
 *  -this is compatible with the standard errno values such as -EINVAL, -EIO, 
 *  -EPERM, -ENOENT that are also used.
 *
 *  Any additions should also be added to FPGA_ERR2STR (see below).
 */
enum {
    /** Negative values are compatible with standard errno returns */

    /** No error */
    FPGA_ERR_OK = 0,

	/** Reserved: 1, 2 */

	/** AFI command is in-progress (busy) */
	FPGA_ERR_AFI_CMD_BUSY = 3,

	/** Reserved: 4 */

	/** Invalid AFI ID */
	FPGA_ERR_AFI_ID_INVALID = 5,

	/** Reserved: 6-10 */

	/** Invalid AFI_CMD_API_VERSION, see afi_cmd_api.h */
	FPGA_ERR_AFI_CMD_API_VERSION_INVALID = 11, 
	/** CL PCI IDs did not match (e.g. between LF and CL reported values */
	FPGA_ERR_CL_ID_MISMATCH = 12,
	/** CL DDR calibration failed */
	FPGA_ERR_CL_DDR_CALIB_FAILED = 13,
	/** generic/unspecified error */
	FPGA_ERR_FAIL = 14,

	FPGA_ERR_SHELL_MISMATCH = 16,

	FPGA_ERR_POWER_VIOLATION = 17,

	FPGA_ERR_END
};

/** Stringify the FPGA_ERR_XXX errors */
#define FPGA_ERR2STR(error) \
	((error) == FPGA_ERR_OK) ?							"ok" : \
	((error) == FPGA_ERR_AFI_CMD_BUSY) ?				"busy" : \
	((error) == FPGA_ERR_AFI_ID_INVALID) ?				"invalid-afi-id" : \
	((error) == FPGA_ERR_AFI_CMD_API_VERSION_INVALID) ?	"invalid-afi-cmd-api-version" : \
	((error) == FPGA_ERR_CL_ID_MISMATCH) ?				"cl-id-mismatch" : \
	((error) == FPGA_ERR_CL_DDR_CALIB_FAILED) ?			"cl-ddr-calib-failed" : \
	((error) == FPGA_ERR_FAIL) ?						"unspecified-error" : \
	((error) == FPGA_ERR_SHELL_MISMATCH) ?			    "afi-shell-version-mismatch" : \
	((error) == FPGA_ERR_POWER_VIOLATION) ?			    "afi-power-violation" : \
														"internal-error"


/**
 * FPGA status
 * e.g. as reported by fpga-describe-local-image.
 *
 * Any additions should also be added to FPGA_STATUS2STR (see below).
 */
enum {
	/**< FPGA slot has an AFI loaded */ 
	FPGA_STATUS_LOADED = 0,
	/**< FPGA slot is cleared */
    FPGA_STATUS_CLEARED = 1,
	/**< FPGA slot is busy (e.g. loading an AFI) */
    FPGA_STATUS_BUSY = 2,
	/**< FPGA slot is not programmed */
    FPGA_STATUS_NOT_PROGRAMMED = 3,
    /* < Load failed, or worked with errors */
    FPGA_STATUS_LOAD_FAILED = 7,
    FPGA_STATUS_END,
};

/** Stringify the FPGA status */
#define FPGA_STATUS2STR(status) \
	((status) == FPGA_STATUS_LOADED) ?			"loaded" : \
	((status) == FPGA_STATUS_CLEARED) ?			"cleared" : \
	((status) == FPGA_STATUS_BUSY) ?			"busy" : \
	((status) == FPGA_STATUS_NOT_PROGRAMMED) ?	"not-programmed" : \
	((status) == FPGA_STATUS_LOAD_FAILED) ?		"load-failed" : \
												"internal-error"

/**
 * Common FPGA config.
 */
struct fpga_common_cfg {
	uint32_t	reserved;
};

/** Physical function definitions */
enum {
    FPGA_APP_PF = 0,
    FPGA_MGMT_PF = 1,
    FPGA_PF_MAX,
};

/* resource number (base address register) definitions */
enum {
    APP_PF_BAR0 = 0,
    APP_PF_BAR1 = 1,
    APP_PF_BAR4 = 4,
    APP_PF_BAR_MAX
};

enum {
    MGMT_PF_BAR0 = 0,
    MGMT_PF_BAR2 = 2,
    MGMT_PF_BAR4 = 4,
    MGMT_PF_BAR_MAX
};

/* must be the larger of APP_PF_BAR_MAX and MGMT_PF_BAR_MAX */
#define FPGA_BAR_PER_PF_MAX 5

/**
 * FPGA slot specification PCI resource map
 */
struct fpga_pci_resource_map {
	/** These can be used for sanity checking prior to the attach */
	uint16_t vendor_id;
	uint16_t device_id;
	uint16_t subsystem_device_id;
	uint16_t subsystem_vendor_id;
	
	/** e.g. PCI Domain:Bus:Device.Function */
	uint16_t  domain;
	uint8_t   bus;
	uint8_t   dev;
	uint8_t   func;

	/** resource for each bar */
	bool      resource_burstable[FPGA_BAR_PER_PF_MAX]; /* if the PCI BAR has WC attribute */
	uint64_t  resource_size[FPGA_BAR_PER_PF_MAX];
} __attribute((packed));

/**
 * FPGA slot specification with two PFs:
 *  Application PF, Management PF
 */
struct fpga_slot_spec {
	struct fpga_pci_resource_map map[FPGA_PF_MAX];
} __attribute__((packed));

/**
 * AFI vendor/device/subsytem vendor/subsystem IDs.
 * e.g. the expected PCI IDs for a loaded AFI.
 */
struct afi_device_ids {
	uint16_t	vendor_id;
	uint16_t	device_id;
	uint16_t	svid;
	uint16_t	ssid;
} __attribute__((packed));

/** FPGA metadata ids */
struct fpga_meta_ids {
	/** Null terminated, and zero padded */
	char		afi_id[AFI_ID_STR_MAX];
	/** Expected PCI IDs for a loaded AFI */
	struct afi_device_ids afi_device_ids;
} __attribute__((packed));

/** FPGA DDR interface metrics */
struct fpga_ddr_if_metrics_common {
	uint64_t    write_count;
	uint64_t    read_count;
} __attribute__((packed));

/** FPGA clock metrics common */
struct fpga_clocks_common {
    uint64_t    frequency[FPGA_MMCM_OUT_CLKS_MAX];
} __attribute__((packed));


/** FPGA metrics */
struct fpga_metrics_common {
	/** See FPGA_INT_STATUS_XYZ below */
	uint32_t int_status;
	/** See FPGA_PAP_XYZ below */
	uint32_t pcim_axi_protocol_error_status;
	/** FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT: address and count */
	uint64_t dma_pcis_timeout_addr;
	uint32_t dma_pcis_timeout_count;
	/** FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR: address and count */
	uint64_t pcim_range_error_addr;
	uint32_t pcim_range_error_count;
	/** FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR: address and count */
	uint64_t pcim_axi_protocol_error_addr;
	uint32_t pcim_axi_protocol_error_count;
	/** reserved */
	uint8_t reserved2[12]; 
	/** FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT: address and count */
	uint64_t ocl_slave_timeout_addr;
	uint32_t ocl_slave_timeout_count;
	/** FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT: address and count */
	uint64_t bar1_slave_timeout_addr;
	uint32_t bar1_slave_timeout_count;
	/** FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT: address and count */
	uint32_t sdacl_slave_timeout_addr;
	uint32_t sdacl_slave_timeout_count;
	/** FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT: address and count */
	uint32_t virtual_jtag_slave_timeout_addr;
	uint32_t virtual_jtag_slave_timeout_count;
	/** PCI read and write counts */
	uint64_t pcim_write_count;
	uint64_t pcim_read_count;

	/** FPGA DDR interface metrics */
	struct fpga_ddr_if_metrics_common ddr_ifs[FPGA_DDR_IFS_MAX];

	/** FPGA clock metrics */
	struct fpga_clocks_common clocks[FPGA_MMCM_GROUP_MAX];

	/** Power data from the microcontroller */
	uint64_t power_mean;
	uint64_t power_max;
	uint64_t power;
} __attribute__((packed));

/** Common int_status */
enum {
    /** SDACL slave timeout (CL did not respond to cycle from host) */
	FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT = 1 << 0,
	/** Virtual JTAG timeout */
    FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT = 1 << 1,
	/** CL did not respond to DMA cycle from host */
	FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT = 1 << 17,
	/** PCIe master cycle from CL out of range */
	FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR = 1 << 18,
	/** PCIe master cycle from CL - dw_cnt and len mismatch */
	FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR = 1 << 19,
	/** CL OCL did not respond to cycle from host */
	FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT = 1 << 28,
	/** CL BAR1 did not respond to cycle from host */
	FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT = 1 << 29,

	FPGA_INT_STATUS_ALL = 
		FPGA_INT_STATUS_SDACL_SLAVE_TIMEOUT |
		FPGA_INT_STATUS_VIRTUAL_JTAG_SLAVE_TIMEOUT |
		FPGA_INT_STATUS_DMA_PCI_SLAVE_TIMEOUT |
		FPGA_INT_STATUS_PCI_MASTER_RANGE_ERROR | 
		FPGA_INT_STATUS_PCI_MASTER_AXI_PROTOCOL_ERROR |
		FPGA_INT_STATUS_OCL_SLAVE_TIMEOUT |
		FPGA_INT_STATUS_BAR1_SLAVE_TIMEOUT,
};

/** Common pcim_axi_protocol_error_status (PAP) */
enum {
	FPGA_PAP_4K_CROSS_ERROR = 1 << 1,
	FPGA_PAP_BM_EN_ERROR = 1 << 2,
	FPGA_PAP_REQ_SIZE_ERROR = 1 << 3,
	FPGA_PAP_WR_INCOMPLETE_ERROR = 1 << 4,
	FPGA_PAP_FIRST_BYTE_EN_ERROR = 1 << 5,
	FPGA_PAP_LAST_BYTE_EN_ERROR = 1 << 6,
	FPGA_PAP_BREADY_TIMEOUT_ERROR = 1 << 8,
	FPGA_PAP_RREADY_TIMEOUT_ERROR = 1 << 9,
	FPGA_PAP_WCHANNEL_TIMEOUT_ERROR = 1 << 10,

	FPGA_PAP_ERROR_STATUS_ALL = 
		FPGA_PAP_4K_CROSS_ERROR | FPGA_PAP_BM_EN_ERROR |
		FPGA_PAP_REQ_SIZE_ERROR | FPGA_PAP_WR_INCOMPLETE_ERROR |
		FPGA_PAP_FIRST_BYTE_EN_ERROR | FPGA_PAP_LAST_BYTE_EN_ERROR |
		FPGA_PAP_BREADY_TIMEOUT_ERROR |
		FPGA_PAP_RREADY_TIMEOUT_ERROR | 
		FPGA_PAP_WCHANNEL_TIMEOUT_ERROR,
};
