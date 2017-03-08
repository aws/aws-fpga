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
#define FPGA_BAR_PER_PF_MAX	4
#define FPGA_PF_MAX            	3

#define AFI_ID_STR_MAX			64
#define FPGA_DDR_IFS_MAX		4

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

	FPGA_CMD_ALL_FLAGS = FPGA_CMD_GET_HW_METRICS | 
		FPGA_CMD_CLEAR_HW_METRICS,
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
    /** fpga_clk_recipe is invalid */
    FPGA_ERR_CLK_RECIPE_INVALID = 14,
    /** fpga_clk_recipe programming failed */
    FPGA_ERR_CLK_RECIPE_FAILED = 15,

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
	((error) == FPGA_ERR_CLK_RECIPE_INVALID) ?			"invalid-clk-recipe" : \
	((error) == FPGA_ERR_CLK_RECIPE_FAILED) ?			"clk-recipe-failed" : \
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
    FPGA_STATUS_END,
};

/** Stringify the FPGA status */
#define FPGA_STATUS2STR(status) \
	((status) == FPGA_STATUS_LOADED) ?			"loaded" : \
	((status) == FPGA_STATUS_CLEARED) ?		"cleared" : \
	((status) == FPGA_STATUS_BUSY) ?			"busy" : \
	((status) == FPGA_STATUS_NOT_PROGRAMMED) ?	"not-programmed" : \
										"internal-error"

/**
 * Common FPGA config.
 */
struct fpga_common_cfg {
	uint32_t	reserved;
};

/* physical function definitions */
enum {
    FPGA_APP_PF,
    FPGA_MGMT_PF,
    FPGA_MAX_PF
};
/**
 * FPGA slot specification PCI resource map
 */
struct fpga_pci_resource_map {
	/** These can be used for sanity checking prior to the attach */
	uint16_t vendor_id;
	uint16_t device_id;
	uint16_t subsystem_id;
	uint16_t vendor_subsystem_id;
	
	/** e.g. PCI Domain:Bus:Device.Function */
	uint16_t  domain;
	uint8_t   bus;
	uint8_t   dev;
	uint8_t   func;

	/** resource for each bar */
	bool      resource_burstable[6]; /* if the PCI BAR has WC attribute */
	uint64_t  resource_size[6];
} __attribute((packed));

/**
 * FPGA slot specification, with 3 items representing 3 PFs 
 */
struct fpga_slot_spec {
	struct fpga_pci_resource_map map[FPGA_MAX_PF];
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

/** FPGA metrics */
struct fpga_metrics_common {
	/** See FPGA_INT_STATUS_XYZ below */
	uint32_t int_status;
	/** See FPGA_PAP_XYZ below */
	uint32_t pci_axi_protocol_error_status;
	/** FPGA_INT_STATUS_PCI_SLAVE_TIMEOUT: address and count */
	uint64_t ps_timeout_addr; 
	uint32_t ps_timeout_count;
	/** FPGA_INT_STATUS_PCI_RANGE_ERROR: address and count */
	uint64_t pm_range_error_addr;
	uint32_t pm_range_error_count;
	/** FPGA_INT_STATUS_PCI_AXI_PROTOCOL_ERROR: address and count */
	uint64_t pm_axi_protocol_error_addr;
	uint32_t pm_axi_protocol_error_count;
	/** FPGA_INT_STATUS_PCI_SLAVE_SDA_TIMEOUT: address and count */
	uint64_t ps_sda_timeout_addr;
	uint32_t ps_sda_timeout_count;
	/** FPGA_INT_STATUS_PCI_SLAVE_OCL_TIMEOUT: address and count */
	uint64_t ps_ocl_timeout_addr;
	uint32_t ps_ocl_timeout_count;
	/** FPGA_INT_STATUS_PCI_SLAVE_EDMA_TIMEOUT: address and count */
	uint64_t ps_edma_timeout_addr;
	uint32_t ps_edma_timeout_count;
	/** PCI read and write counts */
	uint64_t pm_write_count;
	uint64_t pm_read_count;

	/** FPGA DDR interface metrics */
	struct fpga_ddr_if_metrics_common ddr_ifs[FPGA_DDR_IFS_MAX];
} __attribute__((packed));

/** Common int_status */
enum {
	/** CL did not respond to cycle from host */
	FPGA_INT_STATUS_PCI_SLAVE_TIMEOUT = 1 << 17,
	/** PCIe master cycle from CL out of range */
	FPGA_INT_STATUS_PCI_RANGE_ERROR = 1 << 18,
	/** PCIe master cycle from CL - dw_cnt and len mismatch */
	FPGA_INT_STATUS_PCI_AXI_PROTOCOL_ERROR = 1 << 19,
	/** CL SDA did not respond to cycle from host */
	FPGA_INT_STATUS_PCI_SLAVE_SDA_TIMEOUT = 1 << 27,
	/** CL OCL did not respond to cycle from host */
	FPGA_INT_STATUS_PCI_SLAVE_OCL_TIMEOUT = 1 << 28,
	/** CL EDMA did not respond to cycle from host */
	FPGA_INT_STATUS_PCI_SLAVE_EDMA_TIMEOUT = 1 << 29,

	FPGA_INT_STATUS_ALL = FPGA_INT_STATUS_PCI_SLAVE_TIMEOUT |
		FPGA_INT_STATUS_PCI_RANGE_ERROR | 
		FPGA_INT_STATUS_PCI_AXI_PROTOCOL_ERROR |
		FPGA_INT_STATUS_PCI_SLAVE_SDA_TIMEOUT |
		FPGA_INT_STATUS_PCI_SLAVE_OCL_TIMEOUT |
		FPGA_INT_STATUS_PCI_SLAVE_EDMA_TIMEOUT,
};

/** Common pci_axi_protocol_error_status (PAP) */
enum {
	FPGA_PAP_LEN_ERROR = 1 << 0,
	FPGA_PAP_4K_CROSS_ERROR = 1 << 1,
	FPGA_PAP_BM_EN_ERROR = 1 << 2,
	FPGA_PAP_REQ_SIZE_ERROR = 1 << 3,
	FPGA_PAP_WR_INCOMPLETE_ERROR = 1 << 4,
	FPGA_PAP_FIRST_BYTE_EN_ERROR = 1 << 5,
	FPGA_PAP_LAST_BYTE_EN_ERROR = 1 << 6,
	FPGA_PAP_WSTRB_ERROR = 1 << 7,
	FPGA_PAP_BREADY_TIMEOUT_ERROR = 1 << 8,
	FPGA_PAP_RREADY_TIMEOUT_ERROR = 1 << 9,
	FPGA_PAP_WCHANNEL_TIMEOUT_ERROR = 1 << 10,

	FPGA_PAP_ERROR_STATUS_ALL = FPGA_PAP_LEN_ERROR |
		FPGA_PAP_4K_CROSS_ERROR | FPGA_PAP_BM_EN_ERROR |
		FPGA_PAP_REQ_SIZE_ERROR | FPGA_PAP_WR_INCOMPLETE_ERROR |
		FPGA_PAP_FIRST_BYTE_EN_ERROR | FPGA_PAP_LAST_BYTE_EN_ERROR |
		FPGA_PAP_WSTRB_ERROR | FPGA_PAP_BREADY_TIMEOUT_ERROR |
		FPGA_PAP_RREADY_TIMEOUT_ERROR | 
		FPGA_PAP_WCHANNEL_TIMEOUT_ERROR,
};
