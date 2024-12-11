`ifndef DMA_DEFINES_VH
`define DMA_DEFINES_VH

`include "dma_soft_defines.vh"

`define CPLI_WIDTH 80

`define DAT_WIDTH 512
`define ADR_WIDTH 64
`define ALN_WIDTH 4	// Bits used for subbeat dword alignment 
`define LEN_WIDTH 28
`define RID_WIDTH 10 
`define DID_WIDTH 10 
`define QID_WIDTH 8	// Support for 128 H2C and 128 C2H queues
`define DSC_RID_WIDTH 16
`define DSC_DID_WIDTH 16

`define H2C_TAR_ID 0
`define C2H_TAR_ID 1
`define IRQ_TAR_ID 2
`define CFG_TAR_ID 3
`define DSC_H2C_TAR_ID 4
`define DSC_C2H_TAR_ID 5
`define DSC_TAR_ID 6
//`define MSIX_TAR_ID 8
//`define PF1_MSIX_TAR_ID 9

`define MSIX_PBA_OFFSET 12'hfe0

`define MULTQ_C2H_TUSER_WIDTH   64
`define MULTQ_H2C_TUSER_WIDTH   64 

// CR-1119825
`define UNC_ERR_HDR_POISON        1
`define UNC_ERR_HDR_UR_CA         2
`define UNC_ERR_HDR_BCNT          3
`define UNC_ERR_HDR_PARAM         4
`define UNC_ERR_HDR_ADDR          5
`define UNC_ERR_HDR_TAG           6
`define UNC_ERR_HDR_FLR           8
`define UNC_ERR_HDR_TIMEOUT       9

`endif
