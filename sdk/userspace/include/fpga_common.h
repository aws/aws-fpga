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

#define FPGA_SLOT_MAX           8
#define AFI_ID_STR_MAX			64
#define FPGA_DDR_IFS_MAX		4

/**
 * Common FPGA command flags.
 */
enum {
	/** reserved */
	FPGA_CMD_RSVD = 1 << 0,
	/** reserved */
	FPGA_CMD_RSVD1 = 1 << 1,
	/** reserved */
	FPGA_CMD_RSVD2 = 1 << 2,

	FPGA_CMD_ALL_FLAGS = FPGA_CMD_RSVD | FPGA_CMD_RSVD1 | FPGA_CMD_RSVD2,
};

/**
 * FPGA slot specification PCI resource map
 */
struct fpga_pci_resource_map {
	/** These can be used for sanity checking prior to the attach */
	uint16_t vendor_id;
	uint16_t device_id;

	/** e.g. PCI Domain:Bus:Device.Function */
	uint16_t  domain;
	uint8_t   bus;
	uint8_t   dev;
	uint8_t   func;

	/** e.g. mmap resource0, size */
	uint8_t   resource_num;
	uint64_t  size;
} __attribute((packed));

/**
 * FPGA slot specification
 */
struct fpga_slot_spec {
	struct fpga_pci_resource_map map;
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
#define FPGA_METRICS_COMMON_RESERVED	120
struct fpga_metrics_common {
	uint8_t		reserved[FPGA_METRICS_COMMON_RESERVED];
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
