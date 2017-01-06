// Copyright Xilinx, Inc 2014-2016
// Author: Sonal Santan
// Register definition for the XDMA

#ifndef __XDMA_SYS_PARAMETERS_H__
#define __XDMA_SYS_PARAMETERS_H__

#include "perfmon_parameters.h"

#define XILINX_VENDOR_ID 0x10EE

//parameters for HWICAP, Flash and APM on PCIe BAR
#define OCL_CTLR_OFFSET         0x000000
#define HWICAP_OFFSET           0x020000
#define AXI_GATE_OFFSET         0x030000
#define AXI_GATE_OFFSET_READ    0x030008

#define FEATURE_ID              0x031000

#define GENERAL_STATUS          0x032000

#define BPI_FLASH_OFFSET        0x040000

#define AXI_I2C_OFFSET          0x041000
#define PERFMON0_OFFSET         0x100000
#define PERFMON1_OFFSET         0x120000
#define PERFMON2_OFFSET         0x010000

#define OCL_CLKWIZ_OFFSET       0x050000
#define OCL_CLKWIZ_BASEADDR     0x050000
#define OCL_CLKWIZ_BASEADDR2    0x051000

#define OCL_CLKWIZ_STATUS_OFFSET      0x4
#define OCL_CLKWIZ_CONFIG_OFFSET(n)   (0x200 + 4 * (n))

// These are kept only for backwards compatipility. These macros should
// not be used anymore.
#define OCL_CLKWIZ_STATUS     (OCL_CLKWIZ_BASEADDR + OCL_CLKWIZ_STATUS_OFFSET)
#define OCL_CLKWIZ_CONFIG(n)  (OCL_CLKWIZ_BASEADDR + OCL_CLKWIZ_CONFIG_OFFSET(n))

#define HWICAP_BAR             0
#define BPI_FLASH_BAR          0
#define ACCELERATOR_BAR        0
#define PERFMON_BAR            0
#define HWICAP_WRITE_FIFO_SIZE 64
#define MMAP_SIZE_USER         0x400000
#define MMAP_SIZE_CTRL         0x8000
#define DDR_BUFFER_ALIGNMENT   0x40
#define DMA_HWICAP_BITFILE_BUFFER_SIZE 1024
#define OCL_CU_CTRL_RANGE      0x1000

#define ULTRASCALE_MCAP_CONFIG_BASE 0x340

/************************** Constant Definitions ****************************/

/* Input frequency */
#define XDMA_7V3_INPUT_FREQ 100
#define XDMA_KU3_INPUT_FREQ 100

#define XDMA_7V3_CLKWIZ_CONFIG0 0x04000a01
#define XDMA_KU3_CLKWIZ_CONFIG0 0x04000a01

/* Used for parsing bitstream header */
#define XHI_EVEN_MAGIC_BYTE     0x0f
#define XHI_ODD_MAGIC_BYTE      0xf0

/* Extra mode for IDLE */
#define XHI_OP_IDLE  -1

#define XHI_BIT_HEADER_FAILURE -1

/* The imaginary module length register */
#define XHI_MLR                  15

/**
 * AXI IIC Bus Interface v2.0
 * http://www.xilinx.com/support/documentation/ip_documentation/axi_iic/v2_0/pg090-axi-iic.pdf
 */
#define AXI_I2C_SOFT_RESET      AXI_I2C_OFFSET+0x040
#define AXI_I2C_CR              AXI_I2C_OFFSET+0x100
#define AXI_I2C_TX_FIFO         AXI_I2C_OFFSET+0x108
#define AXI_I2C_RX_FIFO         AXI_I2C_OFFSET+0x10c
#define AXI_I2C_RX_FIFO_PIRQ    AXI_I2C_OFFSET+0x120


/** ICAP register definition **/
#define XHWICAP_GIER            HWICAP_OFFSET+0x1c
#define XHWICAP_ISR             HWICAP_OFFSET+0x20
#define XHWICAP_IER             HWICAP_OFFSET+0x28
#define XHWICAP_WF              HWICAP_OFFSET+0x100
#define XHWICAP_RF              HWICAP_OFFSET+0x104
#define XHWICAP_SZ              HWICAP_OFFSET+0x108
#define XHWICAP_CR              HWICAP_OFFSET+0x10c
#define XHWICAP_SR              HWICAP_OFFSET+0x110
#define XHWICAP_WFV             HWICAP_OFFSET+0x114
#define XHWICAP_RFO             HWICAP_OFFSET+0x118
#define XHWICAP_ASR             HWICAP_OFFSET+0x11c

/**
* Bitstream header information.
*/
typedef struct {
  unsigned int HeaderLength;     /* Length of header in 32 bit words */
  unsigned int BitstreamLength;  /* Length of bitstream to read in bytes*/
  unsigned char *DesignName;     /* Design name read from bitstream header */
  unsigned char *PartName;       /* Part name read from bitstream header */
  unsigned char *Date;           /* Date read from bitstream header */
  unsigned char *Time;           /* Bitstream creation time read from header */
  unsigned int MagicLength;      /* Length of the magic numbers in header */
} XHwIcap_Bit_Header;

/*
 * Flash programming constants
 * XAPP 518
 * http://www.xilinx.com/support/documentation/application_notes/xapp518-isp-bpi-prom-virtex-6-pcie.pdf
 * Table 1
 */

#define START_ADDR_CMD 0x53410000
#define END_ADDR_CMD   0x45000000
#define UNLOCK_CMD     0x556E6C6B
#define ERASE_CMD      0x45726173
#define PROGRAM_CMD    0x50726F67

#define READY_STAT     0x00008000
#define ERASE_STAT     0x00000000
#define PROGRAM_STAT   0x00000080

/*
 * Booting FPGA from PROM
 * http://www.xilinx.com/support/documentation/user_guides/ug470_7Series_Config.pdf
 * Table 7.1
 */

#define DUMMY_WORD         0xFFFFFFFF
#define SYNC_WORD          0xAA995566
#define TYPE1_NOOP         0x20000000
#define TYPE1_WRITE_WBSTAR 0x30020001
#define WBSTAR_ADD10       0x00000000
#define WBSTAR_ADD11       0x01000000
#define TYPE1_WRITE_CMD    0x30008001
#define IPROG_CMD          0x0000000F

#endif

// XSIP watermark, do not delete 67d7842dbbe25473c3c32b93c0da8047785f30d78e8a024de1b57352245f9689
