/**
 * Copyright (C) 2015 Xilinx, Inc.  All rights reserved.
 * Based on Xilinx AR 64761
 * Register definition for MCAP IP
 */

#ifndef __MCAP_REGISTERS_H__
#define __MCAP_REGISTERS_H__


#define MCAP_EXT_CAP_HEADER	0x00
#define MCAP_VEND_SPEC_HEADER	0x04
#define MCAP_FPGA_JTAG_ID	0x08
#define MCAP_FPGA_BIT_VERSION	0x0C
#define MCAP_STATUS		0x10
#define MCAP_CONTROL		0x14
#define MCAP_DATA		0x18
#define MCAP_READ_DATA_0	0x1C
#define MCAP_READ_DATA_1	0x20
#define MCAP_READ_DATA_2	0x24
#define MCAP_READ_DATA_3	0x28

#define MCAP_CTRL_MODE_MASK		(1 << 0)
#define MCAP_CTRL_REG_READ_MASK		(1 << 1)
#define MCAP_CTRL_RESET_MASK		(1 << 4)
#define MCAP_CTRL_MOD_RESET_MASK	(1 << 5)
#define MCAP_CTRL_IN_USE_MASK		(1 << 8)
#define MCAP_CTRL_DESIGN_SWITCH_MASK	(1 << 12)
#define MCAP_CTRL_DATA_REG_PROT_MASK	(1 << 16)

#define MCAP_STS_ERR_MASK		(1 << 0)
#define MCAP_STS_EOS_MASK		(1 << 1)
#define MCAP_STS_REG_READ_CMP_MASK	(1 << 4)
#define MCAP_STS_REG_READ_COUNT_MASK	(7 << 5)
#define MCAP_STS_FIFO_OVERFLOW_MASK	(1 << 8)
#define MCAP_STS_FIFO_OCCUPANCY_MASK	(15 << 12)
#define MCAP_STS_CFG_MCAP_REQ_MASK	(1 << 24)

/* Maximum FIFO Depth */
#define MCAP_FIFO_DEPTH		16

/* PCIe Extended Capability Id */
#define MCAP_EXT_CAP_ID		0xB

#define MCAP_LOOP_COUNT	1000000

#define EMCAP_EOS_RETRY_COUNT 10
#define EMCAP_EOS_LOOP_COUNT 100
#define EMCAP_NOOP_VAL	0x2000000

#endif

// XSIP watermark, do not delete 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
