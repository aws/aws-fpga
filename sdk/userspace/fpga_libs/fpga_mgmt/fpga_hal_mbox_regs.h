/*
 * Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * FPGA HAL mailbox register definitions.
 */

#pragma once

#define BIT(bit)				(1 << (bit))

#define FMB_BASE				0x0

#define FMB_REG(offset)			(FMB_BASE + (offset))
#define FMB_REG_SH_VERSION		FMB_REG(0x0)
#define FMB_REG_VIRT_DIP_LED	FMB_REG(0x4)

/** Virtual DIP/LED register bit definitions */ 
enum {
	FMB_VIRT_DIP_MASK = (1 << 16) - 1,
	FMB_VIRT_LED_SHIFT = 16,
};

#define FMB_REG_STATUS			FMB_REG(0xc)

/** Interrupt Status register bit definitions */ 
enum {
	FMB_RX_EVT = BIT(0),
	FMB_TX_EVT = BIT(1),
	FMB_FLR_EVT = BIT(2),
};

#define FMB_REG_WR_INDEX		FMB_REG(0x20)
#define FMB_REG_WR_DATA			FMB_REG(0x24)
#define FMB_REG_WR_LEN			FMB_REG(0x28)

#define FMB_REG_DEPTH			FMB_REG(0x2c)

/** WR Depth register bit definitions */
enum {
	/** Read only */ 
	FMB_WR_DEPTH_MASK = BIT(16) - 1,
	/** Trigger RAM init, cleared by HW when done */
	FMB_WR_RAM_INIT_EN = BIT(31), 
};

#define FMB_REG_RD_INDEX		FMB_REG(0x30)
#define FMB_REG_RD_DATA			FMB_REG(0x34)
#define FMB_REG_RD_LEN			FMB_REG(0x38)

