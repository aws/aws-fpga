
//-----------------------------------------------------------------------------
//
// (c) Copyright 2020-2024 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : The Xilinx PCI Express DMA 
// File       : pcie_bridge_rc_core_top.sv
// Version    : 4.1
//-----------------------------------------------------------------------------

`timescale 1ps/1ps
`include "xdma_axi4mm_axi_bridge.vh"
`include "dma_defines.vh"
`include "dma_defines.svh"
module pcie_bridge_rc_core_top 
#(
  parameter       COMPONENT_NAME               = "xdma_0", 
  parameter       VERSION                      = 6,
  parameter       C_DEVICE_NUMBER              = 0, // Device number for Root Port configurations only
  parameter       VCU1262                      = "FALSE",
  parameter       xlnx_ref_board               = "None",
  parameter       GTWIZ_IN_CORE                = 1,
  parameter       INS_LOSS_PROFILE             = "Add-in_Card",
  parameter       PL_UPSTREAM_FACING           = "TRUE",
  parameter       TL_LEGACY_MODE_ENABLE        = "FALSE",
  parameter       PCIE_BLK_LOCN                = 0,
  parameter       PL_LINK_CAP_MAX_LINK_WIDTH   = 1,
  parameter       PL_LINK_CAP_MAX_LINK_SPEED   = 1,
  parameter       REF_CLK_FREQ                 = 0,
  parameter       FREE_RUN_FREQ                = 1,
  parameter       DRP_CLK_SEL                  = 0,
  parameter       AXI_ADDR_WIDTH               = 32,
  parameter       AXI_DATA_WIDTH               = 64,
  parameter       CORE_CLK_FREQ                = 2,
  parameter       PLL_TYPE                     = 0,
  parameter       USER_CLK_FREQ                = 1,
  parameter       PIPE_DEBUG_EN                = "FALSE",
  parameter       SILICON_REV                  = "Production",
  parameter       PIPE_SIM                     = "FALSE",
  parameter       EXT_CH_GT_DRP                = "FALSE",
  parameter       PCIE3_DRP                    = "FALSE",
  parameter       DEDICATE_PERST               = "TRUE",
  parameter       SYS_RESET_POLARITY           = 0,
  parameter       MCAP_ENABLEMENT              = "NONE",
  parameter       MCAP_FPGA_BITSTREAM_VERSION = 32'h00000000,
  parameter       EXT_STARTUP_PRIMITIVE        = "FALSE",
  parameter       PF0_VENDOR_ID                = 16'h10EE,
  parameter       PF0_DEVICE_ID                = 16'h9011,
  parameter       PF0_REVISION_ID              = 8'h00,
  parameter       PF0_SUBSYSTEM_VENDOR_ID      = 16'h10EE,
  parameter       PF0_SUBSYSTEM_ID             = 16'h0007,
  parameter       PF0_CLASS_CODE               = 24'h058000,
  parameter       PF1_VENDOR_ID                = 16'h10EE,
  parameter       PF1_DEVICE_ID                = 16'h9111,
  parameter       PF1_REVISION_ID              = 8'h00,
  parameter       PF1_SUBSYSTEM_VENDOR_ID      = 16'h10EE,
  parameter       PF1_SUBSYSTEM_ID             = 16'h0007,
  parameter       PF1_CLASS_CODE               = 24'h058000,
  parameter       PF2_DEVICE_ID                = 16'h9211,
  parameter       PF2_REVISION_ID              = 8'h00,
  parameter       PF2_SUBSYSTEM_ID             = 16'h0007,
  parameter       PF3_DEVICE_ID                = 16'h9311,
  parameter       PF3_REVISION_ID              = 8'h00,
  parameter       PF3_SUBSYSTEM_ID             = 16'h0007,
  parameter       AXILITE_MASTER_APERTURE_SIZE = 5'b00101,
  parameter       AXILITE_MASTER_CONTROL       = 3'b100,
  parameter       XDMA_APERTURE_SIZE           = 5'b00101,
  parameter       XDMA_CONTROL                 = 3'b000,
  parameter       AXIST_BYPASS_APERTURE_SIZE   = 5'b00101,
  parameter       AXIST_BYPASS_CONTROL         = 3'b000,
  parameter [63:0]C_PCIEBAR2AXIBAR_0           = 64'h0000000000000000,
  parameter [63:0]C_PCIEBAR2AXIBAR_1           = 64'h0000000000000000,
  parameter [63:0]C_PCIEBAR2AXIBAR_2           = 64'h0000000000000000,
  parameter       PF0_INTERRUPT_PIN            = 3'b001,
  parameter       PF0_MSI_CAP_MULTIMSGCAP      = 0,
  parameter       C_COMP_TIMEOUT               = 0,
  parameter       SHARED_LOGIC                 = 1,
  parameter       SHARED_LOGIC_CLK             = "FALSE",
  parameter       SHARED_LOGIC_CLK_7XG2        = "FALSE",
  parameter       SHARED_LOGIC_BOTH            = "FALSE",
  parameter       SHARED_LOGIC_BOTH_7XG2       = "FALSE",
  parameter       SHARED_LOGIC_GTC             = "FALSE",
  parameter       SHARED_LOGIC_GTC_7XG2        = "FALSE",
  parameter       EN_TRANSCEIVER_STATUS_PORTS  = "FALSE",
  parameter       IS_BOARD_PROJECT             = 0,
  parameter       EN_GT_SELECTION              = "FALSE",
  parameter       SELECT_QUAD                  = "GTH_Quad_224",
  parameter       ULTRASCALE                   = "FALSE",
  parameter       ULTRASCALE_PLUS              = "FALSE",
  parameter       V7_GEN3                      = "FALSE",
  parameter       MSI_ENABLED                  = "TRUE",
  parameter       DEV_PORT_TYPE                = 0,
  parameter       XDMA_PCIE_64BIT_EN           = "FALSE",
  parameter       XDMA_AXI_INTF_MM             = 1,
  parameter       XDMA_AXILITE_MASTER          = "FALSE",
  parameter       XDMA_AXIST_BYPASS            = "FALSE",
  parameter       XDMA_RNUM_CHNL               = 1,
  parameter       XDMA_WNUM_CHNL               = 1,
  parameter       XDMA_AXILITE_SLAVE           = "FALSE",
  parameter       XDMA_NUM_USR_IRQ             = 1,
  parameter       XDMA_RNUM_RIDS               = 32,
  parameter       XDMA_WNUM_RIDS               = 16,
  parameter       C_M_AXI_ID_WIDTH             = 4,
  parameter       C_FAMILY                     = "virtex7",
  parameter       XDMA_NUM_PCIE_TAG            = 64,
  parameter       EN_WCHNL_0                   = "TRUE",
  parameter       EN_WCHNL_1                   = "FALSE",
  parameter       EN_WCHNL_2                   = "FALSE",
  parameter       EN_WCHNL_3                   = "FALSE",
  parameter       EN_WCHNL_4                   = "FALSE",
  parameter       EN_WCHNL_5                   = "FALSE",
  parameter       EN_WCHNL_6                   = "FALSE",
  parameter       EN_WCHNL_7                   = "FALSE",
  parameter       EN_RCHNL_0                   = "TRUE",
  parameter       EN_RCHNL_1                   = "FALSE",
  parameter       EN_RCHNL_2                   = "FALSE",
  parameter       EN_RCHNL_3                   = "FALSE",
  parameter       EN_RCHNL_4                   = "FALSE",
  parameter       EN_RCHNL_5                   = "FALSE",
  parameter       EN_RCHNL_6                   = "FALSE",
  parameter       EN_RCHNL_7                   = "FALSE",
  parameter       XDMA_DSC_BYPASS              = "FALSE",
  parameter       C_METERING_ON                = 1,
  parameter       RX_DETECT                    = 0,
  parameter       DSC_BYPASS_RD                = 0,
  parameter       DSC_BYPASS_WR                = 0,
  parameter       XDMA_STS_PORTS               = "FALSE",
  parameter       MSIX_ENABLED                 = "FALSE",
  parameter       WR_CH0_ENABLED               = "FALSE",
  parameter       WR_CH1_ENABLED               = "FALSE",
  parameter       WR_CH2_ENABLED               = "FALSE",
  parameter       WR_CH3_ENABLED               = "FALSE",
  parameter       RD_CH0_ENABLED               = "FALSE",
  parameter       RD_CH1_ENABLED               = "FALSE",
  parameter       RD_CH2_ENABLED               = "FALSE",
  parameter       RD_CH3_ENABLED               = "FALSE",
  parameter       CFG_MGMT_IF                  = "TRUE",
  parameter       RQ_SEQ_NUM_IGNORE            = 0,
  parameter       CFG_EXT_IF                   = "TRUE",
  parameter       LEGACY_CFG_EXT_IF            = "TRUE",
  parameter       C_PARITY_CHECK               = 1,
  parameter       C_PARITY_GEN                 = 1,
  parameter       C_PARITY_PROP                = 0,
  parameter       EN_DEBUG_PORTS               = "FALSE",
  parameter       VU9P_BOARD                   = "FALSE",
  parameter       ENABLE_JTAG_DBG              = "FALSE",
  parameter       ENABLE_LTSSM_DBG              = "FALSE",
  parameter       ENABLE_IBERT                 = "FALSE",
  parameter       MM_SLAVE_EN                  = 0,
  parameter       DMA_EN                       = 1,
  parameter       SHELL_BRIDGE                 = 1,
  parameter       MSIX_PCIE_INTERNAL           = 0,
  parameter       FUNC_MODE                    = 1,
  parameter       INTERRUPT_OUT_WIDTH          = 1,
  parameter       C_MSI_RX_PIN_EN              = 0,
  parameter       C_MSIX_RX_PIN_EN             = 1,
  parameter       C_INTX_RX_PIN_EN             = 1,
  parameter       MSIX_RX_DECODE_EN            = "FALSE",
  parameter       MSIX_VEC_NUM                 = 1024,
  parameter       PF1_ENABLED                  = 0,
  parameter       PF2_ENABLED                  = 0,
  parameter       PF3_ENABLED                  = 0,
  parameter       C_AXIBAR_NUM                 = 1,
  parameter [63:0]C_AXIBAR_0                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_0          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR_1                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_1          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR_2                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_2          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR_3                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_3          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR_4                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_4          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR_5                   = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR_HIGHADDR_5          = 64'hffff_ffff_ffff_ffff,
  parameter [63:0]C_AXIBAR2PCIEBAR_0           = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR2PCIEBAR_1           = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR2PCIEBAR_2           = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR2PCIEBAR_3           = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR2PCIEBAR_4           = 64'h0000_0000_0000_0000,
  parameter [63:0]C_AXIBAR2PCIEBAR_5           = 64'h0000_0000_0000_0000,
  parameter       EN_AXI_SLAVE_IF              = "TRUE",
  parameter       EN_AXI_MASTER_IF             = "TRUE",
  parameter       C_INCLUDE_BAROFFSET_REG      = 1,
  parameter [31:0]C_BASEADDR                   = 32'hFFFF_FFFF,
  parameter [31:0]C_HIGHADDR                   = 32'h0000_0000,
  parameter       C_S_AXI_NUM_READ             = 8,
  parameter       C_M_AXI_NUM_READ             = 8,
  parameter       C_S_AXI_NUM_WRITE            = 8,
  parameter       C_M_AXI_NUM_WRITE            = 8,
  parameter       C_M_AXI_NUM_WRITE_SCALE      = 1,
  parameter       MSIX_IMPL_EXT                = "TRUE",
  parameter       AXI_ACLK_LOOPBACK            = "FALSE",
  parameter       PL_DISABLE_UPCONFIG_CAPABLE  = "FALSE",
  parameter       PF0_BAR0_APERTURE_SIZE       = 5'b00011,
  parameter       PF0_BAR0_CONTROL             = 3'b100,
  parameter       PF0_BAR1_APERTURE_SIZE       = 5'b00000,
  parameter       PF0_BAR1_CONTROL             = 3'b000,
  parameter       PF0_BAR2_APERTURE_SIZE       = 5'b00011,
  parameter       PF0_BAR2_CONTROL             = 3'b100,
  parameter       PF0_BAR3_APERTURE_SIZE       = 5'b00011,
  parameter       PF0_BAR3_CONTROL             = 3'b000,
  parameter       PF0_BAR4_APERTURE_SIZE       = 5'b00011,
  parameter       PF0_BAR4_CONTROL             = 3'b100,
  parameter       PF0_BAR5_APERTURE_SIZE       = 5'b00011,
  parameter       PF0_BAR5_CONTROL             = 3'b000,
  parameter       PF0_EXPANSION_ROM_ENABLE     = "FALSE",
  parameter [4:0] PF0_EXPANSION_ROM_APERTURE_SIZE = 5'b00011,
  parameter       PF1_BAR0_APERTURE_SIZE       = 5'b00011,
  parameter       PF1_BAR0_CONTROL             = 3'b100,
  parameter       PF1_BAR1_APERTURE_SIZE       = 5'b00000,
  parameter       PF1_BAR1_CONTROL             = 3'b000,
  parameter       PF1_BAR2_APERTURE_SIZE       = 5'b00011,
  parameter       PF1_BAR2_CONTROL             = 3'b100,
  parameter       PF1_BAR3_APERTURE_SIZE       = 5'b00011,
  parameter       PF1_BAR3_CONTROL             = 3'b000,
  parameter       PF1_BAR4_APERTURE_SIZE       = 5'b00011,
  parameter       PF1_BAR4_CONTROL             = 3'b100,
  parameter       PF1_BAR5_APERTURE_SIZE       = 5'b00011,
  parameter       PF1_BAR5_CONTROL             = 3'b000,
  parameter       PF1_EXPANSION_ROM_ENABLE     = "FALSE",
  parameter [4:0] PF1_EXPANSION_ROM_APERTURE_SIZE = 5'b00011,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_0         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_1         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_2         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_3         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_4         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_5         = 64'h0000000000000000,
  parameter [63:0]PF1_PCIEBAR2AXIBAR_6         = 64'h0000000000000000,
  parameter       PCIEBAR_NUM                  = 6,
  parameter [63:0]C_PCIEBAR2AXIBAR_3           = 64'h00000000,
  parameter [63:0]C_PCIEBAR2AXIBAR_4           = 64'h00000000,
  parameter [63:0]C_PCIEBAR2AXIBAR_5           = 64'h00000000,
  parameter [63:0]C_PCIEBAR2AXIBAR_6           = 64'h00000000,
  parameter       BARLITE1                     = 0,
  parameter       BARLITE2                     = 0,
  parameter       C_MSIX_INT_TABLE_EN          = 1,
  parameter       VCU118_BOARD                 = "FALSE",
  parameter       TCQ                          = 1,
  parameter       C_AXIBAR_AS_0                = 1,
  parameter       C_AXIBAR_AS_1                = 1,
  parameter       C_AXIBAR_AS_2                = 1,
  parameter       C_AXIBAR_AS_3                = 1,
  parameter       C_AXIBAR_AS_4                = 1,
  parameter       C_AXIBAR_AS_5                = 1,
  parameter       C_MSI_ENABLED                = MSI_ENABLED,
  parameter       C_NUM_DSC_PCIE_RID           = 32,
  parameter       C_NUM_PCIE_DSC_CPL_DID       = 256,
  parameter       C_NUM_AXI_DSC_CPL_DID        = 64,
  parameter [7:0] MULTQ_CHNL                   = 8'h00,
  parameter       IMPL_TARGET                  = "SOFT",
  parameter       C_M_AXI_DATA_WIDTH           = AXI_DATA_WIDTH,
  parameter       C_M_AXI_WUSER_WIDTH          = C_M_AXI_DATA_WIDTH/8,
  parameter       C_M_AXI_BUSER_WIDTH          = 1,
  parameter       C_M_AXI_RUSER_WIDTH          = C_M_AXI_DATA_WIDTH/8,
  parameter       USE_ATTR                     = 0,  // dont want to use Attribute
  parameter       XDMA_DSC_ENG                 = 1,  // Use XDMA dsc format
  parameter       C_H2C_TUSER_WIDTH            = 48,
  parameter       C_C2H_TUSER_WIDTH            = 64,
  parameter       C_AXIBAR_REGIONEN            = 0,
  parameter       C_AXIBAR_NOXLATE             = 0,
  parameter       C_AXIBAR2PCIEATTR_0          = 3'b000,
  parameter       C_AXIBAR2PCIEATTR_1          = 3'b000,
  parameter       C_AXIBAR2PCIEATTR_2          = 3'b000,
  parameter       C_AXIBAR2PCIEATTR_3          = 3'b000,
  parameter       C_AXIBAR2PCIEATTR_4          = 3'b000,
  parameter       C_AXIBAR2PCIEATTR_5          = 3'b000,
  parameter       C_IGNORE_SIZE_AXI_SLAVE      = 1,
  parameter       C_TIMEOUT0_SEL               = 4'hE,
  parameter       C_TIMEOUT1_SEL               = 4'hF,
  parameter       C_TIMEOUT_MULT               = 3'h3,
  parameter       C_OLD_BRIDGE_TIMEOUT         = 0,
  parameter       C_LAST_CORE_CAP_ADDR         = 12'h100,     // DWORD address of last enabled block capability
  parameter       C_VSEC_CAP_ADDR              = 12'h128,     // DWORD address of start of VSEC Header
  parameter       C_VSEC_CAP_LAST              = "FALSE",     // VSEC next capability offset control
  parameter       C_VSEC_ID                    = 16'h0000,
  parameter       C_NUM_USER_INTR              = 9,           // Number of user interrupts in User interrupt vector
  parameter       C_NUM_USER_NEW_INTR          = 6,           // Number of user interrupts in User interrupt vector
  parameter       C_USER_PTR                   = 16'h00D8,    // Address pointer to User Space
  parameter       C_S_AXI_SUPPORTS_NARROW_BURST= 0,
  parameter       C_S_AXI_ID_WIDTH             = 4,
  parameter       C_S_AXI_ADDR_WIDTH           = 64,
  parameter       C_S_AXI_DATA_WIDTH           = AXI_DATA_WIDTH,
  parameter       C_M_AXI_ADDR_WIDTH           = 64,
  parameter       C_S_AXIS_DATA_WIDTH          = AXI_DATA_WIDTH,
  parameter       C_M_AXIS_DATA_WIDTH          = AXI_DATA_WIDTH,
  parameter       C_M_AXIS_RQ_USER_WIDTH       = 137,
  parameter       C_S_AXIS_CQP_USER_WIDTH      = 183,
  parameter       C_S_AXIS_CQ_USER_WIDTH       = 183,
  parameter       C_M_AXIS_RC_USER_WIDTH       = 161,
  parameter       C_S_AXIS_CC_USER_WIDTH       = 81,
  parameter       C_M_AXIL_AWUSER_WIDTH        = 11,
  parameter       C_M_AXIL_ARUSER_WIDTH        = 11,
  parameter       C_M_AXI_AWUSER_WIDTH         = 8,
  parameter       C_M_AXI_ARUSER_WIDTH         = 8,
  parameter       C_S_KEEP_WIDTH               = C_S_AXI_DATA_WIDTH / 32,
  parameter       C_M_KEEP_WIDTH               = C_M_AXI_DATA_WIDTH / 32,
  parameter       C_KEEP_WIDTH                 = AXI_DATA_WIDTH/8,
  parameter       C_S_AXIS_USER_WIDTH          = 64,
  parameter       C_M_AXIS_USER_WIDTH          = 64,
  parameter       C_ADDR_ALGN                  = 1, // Bytes
  parameter       C_ECC_ENABLE                 = 0,
  parameter       C_DSC_MAGIC_EN               = 1,
  parameter       C_NUMQ_PER_CHNL              = 256,
  parameter       C_SLAVE_READ_64OS_EN         = 0,
  parameter       C_RD_BUFFER_ADDR_SIZE        = C_SLAVE_READ_64OS_EN ? 10 : 9,
  parameter       C_RD_BUFFER_SIZE_BITS        = C_SLAVE_READ_64OS_EN ?  6 : 5,
  parameter       C_PCIEBAR_NUM                = PCIEBAR_NUM,
  parameter       C_PCIEBAR_AS                 = 1,
  parameter       C_NUM_MSIX_VECTORS           = 32,
  parameter       DMA_SP                       = 0,
  parameter       DMA_MM                       = 1,
  parameter       DMA_ST                       = 0,
  parameter       DMA_RESET_SOURCE_SEL         = 0,
  parameter       C_ADDR_BITS                  = 64,
  parameter       STS_WIDTH                    = 8,
  parameter       BACKPRESSURE                 = 0,
  parameter       USR_MPL_SIZE                 = 4096,
  parameter       USR_MRS_SIZE                 = 4096,
  parameter       PMON_EN                      = 1,
  parameter       MULT_PF_DES                  = "FALSE",
  parameter       SPLIT_DMA                    = "FALSE",
  parameter       SPLIT_DMA_SINGLE_PF          = "FALSE",
  parameter       FLR_ENABLE                   = "FALSE",
  parameter       PIPE_LINE_STAGE              = 2,
  parameter       AXIS_PIPE_LINE_STAGE         = 2,
  parameter       VU9P_TUL_EX                  = "FALSE",
  parameter       PCIE_BLK_TYPE                = 0,
  parameter       GEN4_EIEOS_0S7               = "FALSE",
  parameter       CCIX_ENABLE                  = "FALSE",
  parameter       CCIX_DVSEC	                 = "FALSE",
  parameter       ENABLE_ATS_SWITCH            = "FALSE",
  parameter       CDC_WB_EN                    = 1,
  parameter       AXIS_CCIX_RX_TDATA_WIDTH     = (AXI_DATA_WIDTH == 512 ? 512 : 256),
  parameter       AXIS_CCIX_TX_TDATA_WIDTH     = (AXI_DATA_WIDTH == 512 ? 512 : 256),
  parameter       AXIS_CCIX_RX_TUSER_WIDTH     = (AXI_DATA_WIDTH == 512 ? 101 : 47),
  parameter       AXIS_CCIX_TX_TUSER_WIDTH     = (AXI_DATA_WIDTH == 512 ? 101 : 47),
  parameter       C_ATS_DATA_WIDTH             = AXI_DATA_WIDTH,
  parameter       C_ATS_CQ_TUSER_WIDTH         = C_S_AXIS_CQ_USER_WIDTH,
  parameter       C_ATS_CC_TUSER_WIDTH         = C_S_AXIS_CC_USER_WIDTH,
  parameter       C_ATS_RQ_TUSER_WIDTH         = C_M_AXIS_RQ_USER_WIDTH,
  parameter       C_ATS_RC_TUSER_WIDTH         = C_M_AXIS_RC_USER_WIDTH,
  parameter       C_ATS_SWITCH_UNIQUE_BDF      = 1,
  parameter       EXT_SYS_CLK_BUFG             = "FALSE",
  parameter       GTCOM_IN_CORE                = 1,
  parameter       C_NUM_OF_SC                  = 1,
  parameter       USR_IRQ_EXDES                = "FALSE",
  parameter       AXI_VIP_IN_EXDES             = "FALSE",
  parameter       XDMA_NON_INCREMENTAL_EXDES   = "FALSE",
  parameter       XDMA_ST_INFINITE_DESC_EXDES  = "FALSE",
  parameter       ACS_EXT_CAP_ENABLE           = "FALSE",
  parameter       EXT_XVC_VSEC_ENABLE          = "FALSE",
  parameter       EN_PCIE_DEBUG_PORTS          = "FALSE",
  parameter       MULTQ_EN                     = 0,
  parameter       C_PCIE_PFS_SUPPORTED         = 0,
  parameter       C_SRIOV_EN                   = 0,
  parameter       BARLITE_EXT_PF0              = 6'h00,
  parameter       BARLITE_EXT_PF1              = 6'h00,
  parameter       BARLITE_EXT_PF2              = 6'h00,
  parameter       BARLITE_EXT_PF3              = 6'h00,
  parameter       BARLITE_INT_PF0              = 6'h01,
  parameter       BARLITE_INT_PF1              = 6'h00,
  parameter       BARLITE_INT_PF2              = 6'h00,
  parameter       BARLITE_INT_PF3              = 6'h00,
  parameter       NUM_VFS_PF0                  = 4,
  parameter       NUM_VFS_PF1                  = 0,
  parameter       NUM_VFS_PF2                  = 0,
  parameter       NUM_VFS_PF3                  = 0,
  parameter       FIRSTVF_OFFSET_PF0           = 0,
  parameter       FIRSTVF_OFFSET_PF1           = 0,
  parameter       FIRSTVF_OFFSET_PF2           = 0,
  parameter       FIRSTVF_OFFSET_PF3           = 0,
  parameter       VF_BARLITE_EXT_PF0           = 6'h00,
  parameter       VF_BARLITE_EXT_PF1           = 6'h00,
  parameter       VF_BARLITE_EXT_PF2           = 6'h00,
  parameter       VF_BARLITE_EXT_PF3           = 6'h00,
  parameter       VF_BARLITE_INT_PF0           = 6'h01,
  parameter       VF_BARLITE_INT_PF1           = 6'h00,
  parameter       VF_BARLITE_INT_PF2           = 6'h00,
  parameter       VF_BARLITE_INT_PF3           = 6'h00,
  parameter       C_C2H_NUM_CHNL               = 4,
  parameter       C_H2C_NUM_CHNL               = 4,
  parameter       H2C_XDMA_CHNL                = 8'h0F,
  parameter       C2H_XDMA_CHNL                = 8'h0F,
  parameter[17:0] AXISTEN_IF_ENABLE_MSG_ROUTE  =18'h0,
  parameter       ENABLE_MORE                  ="FALSE",
  parameter       DISABLE_BRAM_PIPELINE        ="FALSE",
  parameter       DISABLE_EQ_SYNCHRONIZER      ="FALSE",
  parameter       C_ENABLE_RESOURCE_REDUCTION  ="FALSE",
  parameter       C_ATS_ENABLE                 ="FALSE",
  parameter       C_PRI_ENABLE                 ="FALSE",
  parameter       C_FF_ON_INT_IF               ="FALSE",
  parameter       SOFT_RESET_EN                ="FALSE",
  parameter[29:0] C_ATS_OFFSET                 = 30'h120, // In DW offset; << 2 bits for Byte offset
  parameter[29:0] C_PR_OFFSET                  = 30'h124, // In DW offset; << 2 bits for Byte offset
  parameter[11:0] C_ATS_CAP_NEXTPTR            = 12'h000,
  parameter[11:0] C_PR_CAP_NEXTPTR             = 12'h000,
  parameter[4:0]  C_INV_QUEUE_DEPTH            = 5'h00,
  parameter[1:0]  TL_PF_ENABLE_REG             = 2'h0,
  parameter       PCIE_ID_IF                   = "FALSE",
  parameter[31:0] C_OST_PR_CAP                 = 32'h0,
  parameter       AXSIZE_BYTE_ACCESS_EN        = "FALSE",
  parameter       PF_SWAP                      = "FALSE",
  parameter    [5:0]PF0_MSIX_TAR_ID            = 6'h8,
  parameter    [5:0]PF1_MSIX_TAR_ID            = 6'h9,
  parameter       RUNBIT_FIX                   = "FALSE",
  parameter       RBAR_ENABLE                  = "FALSE",
  parameter       C_SMMU_EN                    = 0,
  parameter       C_M_AXI_NUM_READQ            = 2,
  parameter       USE_STANDARD_INTERFACES      = "FALSE",
  parameter       DMA_2RP                      = "FALSE",
  parameter       SRIOV_ACTIVE_VFS             = 252,
  parameter       ENABLE_ERROR_INJECTION       = "FALSE",
  parameter       VERSAL                       = "FALSE",
  parameter       CFG_SPACE_ENABLE             = "FALSE",
  parameter       VERSAL_PART_TYPE             = "VPT",
  parameter       TANDEM_RFSOC                 = "FALSE",
  parameter       VDM_EN                       = "FALSE",
  parameter       BRIDGE_BURST                 = "FALSE",
  parameter       EGW_IS_PARENT_IP             = 1,
  parameter       USRINT_EXPN                  = "FALSE",
  parameter       ERRC_DEC_EN                  = "FALSE"
)
(
  sys_clk,
  sys_clk_ce_out,
  sys_clk_gt,
  sys_rst_n,
  dma_bridge_resetn,
  user_lnk_up,
  cfg_ltssm_state,
  config_space_enable,

  pci_exp_txp,
  pci_exp_txn,
  pci_exp_rxp,
  pci_exp_rxn,

  free_run_clock,

  gt_drp_clk,
  axi_aclk,
  axi_aresetn,

  axi_ctl_aclk,
  axi_ctl_aresetn,

  usr_irq_req,
  usr_irq_ack,
  usr_irq_function_number,
  msi_enable,
  msix_enable,
  msi_vector_width,

  // AXI MM interface
  m_axi_awid,
  m_axi_awaddr,
  m_axi_awlen,
  m_axi_awsize,
  m_axi_awburst,
  m_axi_awprot,
  m_axi_awvalid,
  m_axi_awready,
  m_axi_awlock,
  m_axi_awcache,
  m_axi_wdata,
  m_axi_wuser,
  m_axi_wstrb,
  m_axi_wlast,
  m_axi_wvalid,
  m_axi_wready,
  m_axi_bid,
  m_axi_bresp,
  m_axi_bvalid,
  m_axi_bready,
  m_axi_arid,
  m_axi_araddr,
  m_axi_arlen,
  m_axi_arsize,
  m_axi_arburst,
  m_axi_arprot,
  m_axi_arvalid,
  m_axi_arready,
  m_axi_arlock,
  m_axi_arcache,
  m_axi_rid,
  m_axi_rdata,
  m_axi_ruser,
  m_axi_rresp,
  m_axi_rlast,
  m_axi_rvalid,
  m_axi_rready,

  // AXI BYPASS interface
  m_axib_awid,
  m_axib_awaddr,
  m_axib_awuser,
  m_axib_awlen,
  m_axib_awsize,
  m_axib_awburst,
  m_axib_awprot,
  m_axib_awvalid,
  m_axib_awready,
  m_axib_awlock,
  m_axib_awcache,
  m_axib_wdata,
  m_axib_wuser,
  m_axib_wstrb,
  m_axib_wlast,
  m_axib_wvalid,
  m_axib_wready,
  m_axib_bid,
  m_axib_bresp,
  m_axib_bvalid,
  m_axib_bready,
  m_axib_arid,
  m_axib_araddr,
  m_axib_aruser,
  m_axib_arlen,
  m_axib_arsize,
  m_axib_arburst,
  m_axib_arprot,
  m_axib_arvalid,
  m_axib_arready,
  m_axib_arlock,
  m_axib_arcache,
  m_axib_rid,
  m_axib_rdata,
  m_axib_ruser,
  m_axib_rresp,
  m_axib_rlast,
  m_axib_rvalid,
  m_axib_rready,

// AXI-Slave Interface (BRIDGE)
  s_axib_awid,
  s_axib_awaddr,
  s_axib_awregion,
  s_axib_awlen,
  s_axib_awsize,
  s_axib_awburst,
  s_axib_awvalid,
  s_axib_awready,
  s_axib_wdata,
  s_axib_wstrb,
  s_axib_wlast,
  s_axib_wvalid,
  s_axib_wready,
  s_axib_bid,
  s_axib_bresp,
  s_axib_bvalid,
  s_axib_bready,
  s_axib_arid,
  s_axib_araddr,
  s_axib_arregion,
  s_axib_arlen,
  s_axib_arsize,
  s_axib_arburst,
  s_axib_arvalid,
  s_axib_arready,
  s_axib_rid,
  s_axib_rresp,
  s_axib_rlast,
  s_axib_rvalid,
  s_axib_rdata,
  s_axib_wuser,
  s_axib_ruser,
  s_axib_rready,
  interrupt_out,
  interrupt_out_msi_vec0to31,
  interrupt_out_msi_vec32to63,
  interrupt_out_msix_0,
  interrupt_out_msix_1,
  interrupt_out_msix_2,
  interrupt_out_msix_3,
  s_axis_c2h_tdata_0,
  s_axis_c2h_tlast_0,
  s_axis_c2h_tuser_0,
  s_axis_c2h_tkeep_0,
  s_axis_c2h_tvalid_0,
  s_axis_c2h_tready_0,

  m_axis_h2c_tdata_0,
  m_axis_h2c_tlast_0,
  m_axis_h2c_tuser_0,
  m_axis_h2c_tkeep_0,
  m_axis_h2c_tvalid_0,
  m_axis_h2c_tready_0,

  s_axis_c2h_tdata_1,
  s_axis_c2h_tlast_1,
  s_axis_c2h_tuser_1,
  s_axis_c2h_tkeep_1,
  s_axis_c2h_tvalid_1,
  s_axis_c2h_tready_1,

  m_axis_h2c_tdata_1,
  m_axis_h2c_tlast_1,
  m_axis_h2c_tuser_1,
  m_axis_h2c_tkeep_1,
  m_axis_h2c_tvalid_1,
  m_axis_h2c_tready_1,

  s_axis_c2h_tdata_2,
  s_axis_c2h_tlast_2,
  s_axis_c2h_tuser_2,
  s_axis_c2h_tkeep_2,
  s_axis_c2h_tvalid_2,
  s_axis_c2h_tready_2,

  m_axis_h2c_tdata_2,
  m_axis_h2c_tlast_2,
  m_axis_h2c_tuser_2,
  m_axis_h2c_tkeep_2,
  m_axis_h2c_tvalid_2,
  m_axis_h2c_tready_2,

  s_axis_c2h_tdata_3,
  s_axis_c2h_tlast_3,
  s_axis_c2h_tuser_3,
  s_axis_c2h_tkeep_3,
  s_axis_c2h_tvalid_3,
  s_axis_c2h_tready_3,

  m_axis_h2c_tdata_3,
  m_axis_h2c_tlast_3,
  m_axis_h2c_tuser_3,
  m_axis_h2c_tkeep_3,
  m_axis_h2c_tvalid_3,
  m_axis_h2c_tready_3,

  // AXI-Lite Interface
  m_axil_awaddr,
  m_axil_awuser,
  m_axil_awprot,
  m_axil_awvalid,
  m_axil_awready,
  m_axil_wdata,
  m_axil_wstrb,
  m_axil_wvalid,
  m_axil_wready,
  m_axil_bvalid,
  m_axil_bresp,
  m_axil_bready,
  m_axil_araddr,
  m_axil_aruser,
  m_axil_arprot,
  m_axil_arvalid,
  m_axil_arready,
  m_axil_rdata,
  m_axil_rresp,
  m_axil_rvalid,
  m_axil_rready,

  // AXI-Lite Interface
  s_axil_awaddr,
  s_axil_awprot,
  s_axil_awvalid,
  s_axil_awready,
  s_axil_wdata,
  s_axil_wstrb,
  s_axil_wvalid,
  s_axil_wready,
  s_axil_bvalid,
  s_axil_bresp,
  s_axil_bready,
  s_axil_araddr,
  s_axil_arprot,
  s_axil_arvalid,
  s_axil_arready,
  s_axil_rdata,
  s_axil_rresp,
  s_axil_rvalid,
  s_axil_rready,

  // Descriptor Bypass
  c2h_dsc_byp_ready_0,
  c2h_dsc_byp_src_addr_0,
  c2h_dsc_byp_dst_addr_0,
  c2h_dsc_byp_len_0,
  c2h_dsc_byp_ctl_0,
  c2h_dsc_byp_load_0,

  c2h_dsc_byp_ready_1,
  c2h_dsc_byp_src_addr_1,
  c2h_dsc_byp_dst_addr_1,
  c2h_dsc_byp_len_1,
  c2h_dsc_byp_ctl_1,
  c2h_dsc_byp_load_1,

  c2h_dsc_byp_ready_2,
  c2h_dsc_byp_src_addr_2,
  c2h_dsc_byp_dst_addr_2,
  c2h_dsc_byp_len_2,
  c2h_dsc_byp_ctl_2,
  c2h_dsc_byp_load_2,

  c2h_dsc_byp_ready_3,
  c2h_dsc_byp_src_addr_3,
  c2h_dsc_byp_dst_addr_3,
  c2h_dsc_byp_len_3,
  c2h_dsc_byp_ctl_3,
  c2h_dsc_byp_load_3,

  h2c_dsc_byp_ready_0,
  h2c_dsc_byp_src_addr_0,
  h2c_dsc_byp_dst_addr_0,
  h2c_dsc_byp_len_0,
  h2c_dsc_byp_ctl_0,
  h2c_dsc_byp_load_0,

  h2c_dsc_byp_ready_1,
  h2c_dsc_byp_src_addr_1,
  h2c_dsc_byp_dst_addr_1,
  h2c_dsc_byp_len_1,
  h2c_dsc_byp_ctl_1,
  h2c_dsc_byp_load_1,

  h2c_dsc_byp_ready_2,
  h2c_dsc_byp_src_addr_2,
  h2c_dsc_byp_dst_addr_2,
  h2c_dsc_byp_len_2,
  h2c_dsc_byp_ctl_2,
  h2c_dsc_byp_load_2,

  h2c_dsc_byp_ready_3,
  h2c_dsc_byp_src_addr_3,
  h2c_dsc_byp_dst_addr_3,
  h2c_dsc_byp_len_3,
  h2c_dsc_byp_ctl_3,
  h2c_dsc_byp_load_3,

  c2h_sts_0,
  h2c_sts_0,
  c2h_sts_1,
  h2c_sts_1,
  c2h_sts_2,
  h2c_sts_2,
  c2h_sts_3,
  h2c_sts_3,

  pipe_debug_ctl_in_tx0,
  pipe_debug_ctl_in_tx1,
  pipe_debug_ctl_in_rx0,
  pipe_debug_ctl_in_rx1,
  pipe_debug_ltssm_rec_spd_1,
  pipe_debug_ltssm_pol_act,
  pipe_debug_ctl_vec4,
  pipe_debug_mux_ctl,
  pipe_debug_debug_out_128_0,
  pipe_debug_debug_out_ext_16_0,
  pipe_debug_debug_out_128_1,
  pipe_debug_debug_out_ext_16_1,
  pipe_debug_debug_out_128_2,
  pipe_debug_debug_out_ext_16_2,
  pipe_debug_debug_out_128_3,
  pipe_debug_debug_out_ext_16_3,
  pipe_debug_inject_tx_status,
  pipe_debug_inject_rx_status,


  cfg_vend_id,
  cfg_subsys_vend_id,
  cfg_dev_id_pf0,
  cfg_rev_id_pf0,
  cfg_subsys_id_pf0,
  cfg_dev_id_pf1,
  cfg_rev_id_pf1,
  cfg_subsys_id_pf1,
  cfg_dev_id_pf2,
  cfg_rev_id_pf2,
  cfg_subsys_id_pf2,
  cfg_dev_id_pf3,
  cfg_rev_id_pf3,
  cfg_subsys_id_pf3,
  common_commands_in,
  pipe_rx_0_sigs,
  pipe_rx_1_sigs,
  pipe_rx_2_sigs,
  pipe_rx_3_sigs,
  pipe_rx_4_sigs,
  pipe_rx_5_sigs,
  pipe_rx_6_sigs,
  pipe_rx_7_sigs,
  pipe_rx_8_sigs,
  pipe_rx_9_sigs,
  pipe_rx_10_sigs,
  pipe_rx_11_sigs,
  pipe_rx_12_sigs,
  pipe_rx_13_sigs,
  pipe_rx_14_sigs,
  pipe_rx_15_sigs,
  common_commands_out,
  pipe_tx_0_sigs,
  pipe_tx_1_sigs,
  pipe_tx_2_sigs,
  pipe_tx_3_sigs,
  pipe_tx_4_sigs,
  pipe_tx_5_sigs,
  pipe_tx_6_sigs,
  pipe_tx_7_sigs,
  pipe_tx_8_sigs,
  pipe_tx_9_sigs,
  pipe_tx_10_sigs,
  pipe_tx_11_sigs,
  pipe_tx_12_sigs,
  pipe_tx_13_sigs,
  pipe_tx_14_sigs,
  pipe_tx_15_sigs,

  cfg_mgmt_addr,
  cfg_mgmt_write,
  cfg_mgmt_write_data,
  cfg_mgmt_byte_enable,
  cfg_mgmt_read,
  cfg_mgmt_read_data,
  cfg_mgmt_read_write_done,
  cfg_mgmt_type1_cfg_reg_access,

  pipe_txprbssel,
  pipe_rxprbssel,
  pipe_txprbsforceerr,
  pipe_rxprbscntreset,
  pipe_loopback,
  pipe_rxprbserr,
  pipe_txinhibit,
  pipe_rst_fsm,
  pipe_qrst_fsm,
  pipe_rate_fsm,
  pipe_sync_fsm_tx,
  pipe_sync_fsm_rx,
  pipe_drp_fsm,
  pipe_rst_idle,
  pipe_qrst_idle,
  pipe_rate_idle,
  pipe_eyescandataerror,
  pipe_rxstatus,
  pipe_dmonitorout,
  pipe_cpll_lock,
  pipe_qpll_lock,
  pipe_rxpmaresetdone,
  pipe_rxbufstatus,
  pipe_txphaligndone,
  pipe_txphinitdone,
  pipe_txdlysresetdone,
  pipe_rxphaligndone,
  pipe_rxdlysresetdone,
  pipe_rxsyncdone,
  pipe_rxdisperr,
  pipe_rxnotintable,
  pipe_rxcommadet,
  gt_ch_drp_rdy,
  pipe_debug_0,
  pipe_debug_1,
  pipe_debug_2,
  pipe_debug_3,
  pipe_debug_4,
  pipe_debug_5,
  pipe_debug_6,
  pipe_debug_7,
  pipe_debug_8,
  pipe_debug_9,
  pipe_debug,

  gt_pcieuserratedone,
  gt_loopback,
  gt_txprbsforceerr,
  gt_txinhibit,
  gt_txprbssel,
  gt_rxprbssel,
  gt_rxprbscntreset,
  gt_dmonitorclk,
  gt_dmonfiforeset,
  gt_txelecidle,
  gt_txresetdone,
  gt_rxresetdone,
  gt_rxpmaresetdone,
  gt_txphaligndone,
  gt_txphinitdone,
  gt_txdlysresetdone,
  gt_rxphaligndone,
  gt_rxdlysresetdone,
  gt_rxsyncdone,
  gt_eyescandataerror,
  gt_rxprbserr,
  gt_dmonitorout,
  gt_rxcommadet,
  gt_phystatus,
  gt_rxvalid,
  gt_rxcdrlock,
  gt_pcierateidle,
  gt_pcieuserratestart,
  gt_gtpowergood,
  gt_cplllock,
  gt_rxoutclk,
  gt_rxrecclkout,
  gt_qpll1lock,
  gt_rxstatus,
  gt_rxbufstatus,
  gt_bufgtdiv,
  phy_txeq_ctrl,
  phy_txeq_preset,
  phy_rst_fsm,
  phy_txeq_fsm,
  phy_rxeq_fsm,
  phy_rst_idle,
  phy_rrst_n,
  phy_prst_n,

  ext_ch_gt_drpclk,
  ext_ch_gt_drpaddr,
  ext_ch_gt_drpen,
  ext_ch_gt_drpwe,
  ext_ch_gt_drpdi,
  ext_ch_gt_drprdy,
  ext_ch_gt_drpdo,
  //--------------------------------------------------------------------------------------//
  //  MCAP Design Switch signal                                                           //
  //   - This signal goes high once the tandem stage2 bitstream is loaded.                //
  //   - This signal may be asserted high by SW after the first PR programming sequence   //
  //     has completed.                                                                   //
  //   - After going high, this signal should not be written back to zero by SW.          //
  //--------------------------------------------------------------------------------------//
  mcap_design_switch,
  //--------------------------------------------------------------------------------------//
  //  Configuration Arbitration Signals                                                   //
  //    - These signals should be used to arbitrate for control of the underlying FPGA    //
  //      Configuration logic. Request, Grant, and Release signals should be connected in //
  //      the user design.                                                                //
  //--------------------------------------------------------------------------------------//
  cap_req,
  cap_gnt,
  cap_rel,
  //--------------------------------------------------------------------------------------//
  //  End of Startup (EOS) Signal                                                         //
  //    - This signal should be driven directly by the End of Startup (EOS) output of     //
  //      the STARTUP primitive                                                           //
  //--------------------------------------------------------------------------------------//
  mcap_eos_in,
  //--------------------------------------------------------------------------------------//
  //  Startup Signals                                                                     //
  //    - The startup interface is exposed to the external user for connectivity to other //
  //      IPs                                                                             //
  //--------------------------------------------------------------------------------------//
  startup_cfgclk,
  startup_cfgmclk,
  startup_di,
  startup_eos,
  startup_preq,
  startup_do,
  startup_dts,
  startup_fcsbo,
  startup_fcsbts,
  startup_gsr,
  startup_gts,
  startup_keyclearb,
  startup_pack,
  startup_usrcclko,
  startup_usrcclkts,
  startup_usrdoneo,
  startup_usrdonets,

  drp_rdy,
  drp_do,
  drp_clk,
  drp_en,
  drp_we,
  drp_addr,
  drp_di,

  cfg_ext_read_received,
  cfg_ext_write_received,
  cfg_ext_register_number,
  cfg_ext_function_number,
  cfg_ext_write_data,
  cfg_ext_write_byte_enable,
  cfg_ext_read_data,
  cfg_ext_read_data_valid,

  // --- Shared Logic Clock Internal Interface for pcie3_7x
  int_pclk_out_slave,
  int_pipe_rxusrclk_out,
  int_rxoutclk_out,
  int_dclk_out,
  int_userclk1_out,
  int_userclk2_out,
  int_oobclk_out,
  int_qplllock_out,
  int_qplloutclk_out,
  int_qplloutrefclk_out,
  int_pclk_sel_slave,

  // --- Shared Logic Clock External Interface for pcie3_7x
  pipe_pclk_in,
  pipe_rxusrclk_in,
  pipe_rxoutclk_in,
  pipe_dclk_in,
  pipe_userclk1_in,
  pipe_userclk2_in,
  pipe_oobclk_in,
  pipe_mmcm_rst_n,
  pipe_mmcm_lock_in,
  pipe_txoutclk_out,
  pipe_rxoutclk_out,
  pipe_pclk_sel_out,
  pipe_gen3_out,

  // --- Shared Logic External GT COMMON for pcie3_7x
  qpll_drp_crscode,
  qpll_drp_fsm,
  qpll_drp_done,
  qpll_drp_reset,
  qpll_qplllock,
  qpll_qplloutclk,
  qpll_qplloutrefclk,
  qpll_qplld,
  qpll_qpllreset,
  qpll_drp_clk,
  qpll_drp_rst_n,
  qpll_drp_ovrd,
  qpll_drp_gen3,
  qpll_drp_start,

  // --- Shared Logic GT_COMMON Internal Interface for pcie3_us
  int_qpll1lock_out,
  int_qpll1outclk_out,
  int_qpll1outrefclk_out,

  // --- Shared Logic GT_COMMON External Interface for pcie3_us
  ext_qpll1refclk,
  ext_qpll1pd,
  ext_qpll1rate,
  ext_qpll1reset,
  ext_qpll1lock_out,
  ext_qpll1outclk_out,
  ext_qpll1outrefclk_out,

  m_axis_rq_tdata_out,
  m_axis_rq_tlast_out,
  m_axis_rq_tuser_out,
  m_axis_rq_tkeep_out,
  m_axis_rq_tready_out,
  m_axis_rq_tvalid_out,

  s_axis_rc_tdata_out,
  s_axis_rc_tuser_out,
  s_axis_rc_tlast_out,
  s_axis_rc_tkeep_out,
  s_axis_rc_tvalid_out,
  s_axis_rc_tready_out,

  s_axis_cq_tdata_out,
  s_axis_cq_tuser_out,
  s_axis_cq_tlast_out,
  s_axis_cq_tkeep_out,
  s_axis_cq_tvalid_out,
  s_axis_cq_tready_out,

  m_axis_cc_tdata_out,
  m_axis_cc_tuser_out,
  m_axis_cc_tlast_out,
  m_axis_cc_tkeep_out,
  m_axis_cc_tvalid_out,
  m_axis_cc_tready_out,

  gt_qpll0lock,
  gt_gen34_eios_det,
  gt_txoutclk,
  gt_txoutclkfabric,
  gt_rxoutclkfabric,
  gt_txoutclkpcs,
  gt_rxoutclkpcs,
  gt_txpmareset,
  gt_rxpmareset,
  gt_txpcsreset,
  gt_rxpcsreset,
  gt_rxbufreset,
  gt_rxcdrreset,
  gt_rxdfelpmreset,
  gt_txprogdivresetdone,
  gt_txpmaresetdone,
  gt_txsyncdone,
  gt_rxprbslocked,

  //--------------------------------------------------------------------------
  //  GT WIZARD IP is not in the US PCIe core
  //--------------------------------------------------------------------------
  bufgtce_us_out ,
  bufgtcemask_us_out ,
  bufgtdiv_us_out ,
  bufgtreset_us_out ,
  bufgtrstmask_us_out ,
  cplllock_us_out,
  dmonitorout_us_out,
  drpdo_us_out,
  drprdy_us_out,
  eyescandataerror_us_out,
  gthtxn_us_out,
  gthtxp_us_out,
  gtpowergood_us_out,
  pcierategen3_us_out,
  pcierateidle_us_out,
  pcierateqpllpd_us_out,
  pcierateqpllreset_us_out,
  pciesynctxsyncdone_us_out,
  pcieusergen3rdy_us_out,
  pcieuserphystatusrst_us_out,
  pcieuserratestart_us_out,
  pcsrsvdout_us_out,
  phystatus_us_out,
  rxbufstatus_us_out,
  rxbyteisaligned_us_out,
  rxbyterealign_us_out,
  rxcdrlock_us_out,
  rxclkcorcnt_us_out,
  rxcommadet_us_out,
  rxctrl0_us_out,
  rxctrl1_us_out,
  rxctrl2_us_out,
  rxctrl3_us_out,
  rxdata_us_out,
  rxdlysresetdone_us_out,
  rxelecidle_us_out,
  rxoutclk_us_out,
  rxphaligndone_us_out,
  rxpmaresetdone_us_out,
  rxprbserr_us_out,
  rxprbslocked_us_out,
  rxprgdivresetdone_us_out,
  rxratedone_us_out,
  rxresetdone_us_out,
  rxstatus_us_out,
  rxsyncdone_us_out,
  rxvalid_us_out,
  txdlysresetdone_us_out,
  txoutclk_us_out,
  txphaligndone_us_out,
  txphinitdone_us_out,
  txpmaresetdone_us_out,
  txprgdivresetdone_us_out,
  txresetdone_us_out,
  txsyncout_us_out,
  txsyncdone_us_out,

  cpllpd_us_in,
  rxdfeagchold_us_in ,
  rxdfecfokhold_us_in,
  rxdfelfhold_us_in  ,
  rxdfekhhold_us_in  ,
  rxdfetap2hold_us_in,
  rxdfetap3hold_us_in,
  rxdfetap4hold_us_in,
  rxdfetap5hold_us_in,
  rxdfetap6hold_us_in,
  rxdfetap7hold_us_in,
  rxdfetap8hold_us_in,
  rxdfetap9hold_us_in,
  rxdfetap10hold_us_in,
  rxdfetap11hold_us_in,
  rxdfetap12hold_us_in,
  rxdfetap13hold_us_in,
  rxdfetap14hold_us_in,
  rxdfetap15hold_us_in,
  rxdfeuthold_us_in,
  rxdfevphold_us_in,
  rxoshold_us_in   ,
  rxlpmgchold_us_in,
  rxlpmhfhold_us_in,
  rxlpmlfhold_us_in,
  rxlpmoshold_us_in,
  cpllreset_us_in,
  dmonfiforeset_us_in,
  dmonitorclk_us_in,
  drpclk_us_in,
  drpaddr_us_in,
  drpdi_us_in,
  drpen_us_in,
  drpwe_us_in,
  eyescanreset_us_in,
  gthrxn_us_in,
  gthrxp_us_in,
  gtrefclk0_us_in,
  gtrxreset_us_in,
  gttxreset_us_in,
  gtwiz_reset_rx_done_us_in,
  gtwiz_reset_tx_done_us_in,
  gtwiz_userclk_rx_active_us_in ,
  gtwiz_userclk_tx_active_us_in ,
  gtwiz_userclk_tx_reset_us_in,
  loopback_us_in,
  pcieeqrxeqadaptdone_us_in ,
  pcierstidle_us_in,
  pciersttxsyncstart_us_in,
  pcieuserratedone_us_in,
  pcsrsvdin_us_in,
  rx8b10ben_us_in,
  rxbufreset_us_in,
  rxcdrhold_us_in,
  rxcommadeten_us_in,
  rxlpmen_us_in,
  rxmcommaalignen_us_in,
  rxpcommaalignen_us_in,
  rxpd_us_in,
  rxpolarity_us_in,
  rxprbscntreset_us_in,
  rxprbssel_us_in,
  rxprogdivreset_us_in,
  rxrate_us_in,
  rxratemode_us_in,
  rxslide_us_in,
  rxuserrdy_us_in,
  rxusrclk2_us_in,
  rxusrclk_us_in,
  tx8b10ben_us_in,
  txctrl0_us_in,
  txctrl1_us_in,
  txctrl2_us_in,
  txdata_us_in,
  txdeemph_us_in,
  txdetectrx_us_in,
  txdiffctrl_us_in,
  txdlybypass_us_in,
  txdlyen_us_in,
  txdlyhold_us_in,
  txdlyovrden_us_in,
  txdlysreset_us_in,
  txdlyupdown_us_in,
  txelecidle_us_in,
  txinhibit_us_in,
  txmaincursor_us_in,
  txmargin_us_in,
  txoutclksel_us_in,
  txpd_us_in,
  txphalign_us_in,
  txphalignen_us_in,
  txphdlypd_us_in,
  txphdlyreset_us_in,
  txphdlytstclk_us_in ,
  txphinit_us_in,
  txphovrden_us_in,
  txpostcursor_us_in,
  txprbsforceerr_us_in,
  txprbssel_us_in,
  txprecursor_us_in,
  txprogdivreset_us_in,
  txrate_us_in,
  txswing_us_in,
  txsyncallin_us_in,
  txsyncin_us_in,
  txsyncmode_us_in,
  txuserrdy_us_in,
  txusrclk2_us_in,
  txusrclk_us_in,

  qpll0clk_us_in,
  qpll0refclk_us_in,
  qpll1clk_us_in,
  qpll1refclk_us_in,

  gtrefclk01_us_in,
  qpll1pd_us_in,
  qpll1reset_us_in,
  qpllrsvd2_us_in,
  qpllrsvd3_us_in,
  qpll1lock_us_out,
  qpll1outclk_us_out,
  qpll1outrefclk_us_out,

  //--------------------------------------------------------------------------
  //  GT WIZARD IP is not in the US+ PCIe core
  //--------------------------------------------------------------------------
  gtrefclk01_usp_in,
  gtrefclk00_usp_in,
  pcierateqpll0_usp_in,
  pcierateqpll1_usp_in,
  qpll0pd_usp_in,
  qpll0reset_usp_in,
  qpll1pd_usp_in,
  qpll1reset_usp_in,
  qpll0lock_usp_out,
  qpll0outclk_usp_out,
  qpll0outrefclk_usp_out,
  qpll1lock_usp_out,
  qpll1outclk_usp_out,
  qpll1outrefclk_usp_out,
  qpll0freqlock_usp_in,
  qpll1freqlock_usp_in,
  pcierateqpllpd_usp_out,
  pcierateqpllreset_usp_out,

  rcalenb_usp_in,
  txpisopd_usp_in,
  bufgtce_usp_out,
  bufgtcemask_usp_out,
  bufgtdiv_usp_out,
  bufgtreset_usp_out,
  bufgtrstmask_usp_out,
  cpllfreqlock_usp_in,
  cplllock_usp_out,
  cpllpd_usp_in,
  cpllreset_usp_in,
  dmonfiforeset_usp_in,
  dmonitorclk_usp_in,
  dmonitorout_usp_out,
  eyescanreset_usp_in,
  gtpowergood_usp_out,
  gtrefclk0_usp_in,
  gtrxreset_usp_in,
  gttxreset_usp_in,
  gtwiz_reset_rx_done_usp_in,
  gtwiz_reset_tx_done_usp_in,
  gtwiz_userclk_rx_active_usp_in,
  gtwiz_userclk_tx_active_usp_in,

  loopback_usp_in,
  pcieeqrxeqadaptdone_usp_in,
  pcierategen3_usp_out,
  pcierateidle_usp_out,
  pcierstidle_usp_in,
  pciersttxsyncstart_usp_in,
  pciesynctxsyncdone_usp_out,
  pcieusergen3rdy_usp_out,
  pcieuserphystatusrst_usp_out,
  pcieuserratedone_usp_in,
  pcieuserratestart_usp_out,
  phystatus_usp_out,
  resetovrd_usp_in,
  rx8b10ben_usp_in,
  rxbufreset_usp_in,
  rxbufstatus_usp_out,
  rxbyteisaligned_usp_out,
  rxbyterealign_usp_out,
  rxcdrfreqreset_usp_in,
  rxcdrhold_usp_in,
  rxcdrlock_usp_out,
  rxcdrreset_usp_in,
  rxclkcorcnt_usp_out,
  rxcommadet_usp_out,
  rxcommadeten_usp_in,
  rxctrl0_usp_out,
  rxctrl1_usp_out,
  rxctrl2_usp_out,
  rxctrl3_usp_out,
  rxdata_usp_out,
  rxdfeagchold_usp_in,
  rxdfecfokhold_usp_in,
  rxdfekhhold_usp_in,
  rxdfelfhold_usp_in,
  rxdfelpmreset_usp_in,
  rxdfetap10hold_usp_in,
  rxdfetap11hold_usp_in,
  rxdfetap12hold_usp_in,
  rxdfetap13hold_usp_in,
  rxdfetap14hold_usp_in,
  rxdfetap15hold_usp_in,
  rxdfetap2hold_usp_in,
  rxdfetap3hold_usp_in,
  rxdfetap4hold_usp_in,
  rxdfetap5hold_usp_in,
  rxdfetap6hold_usp_in,
  rxdfetap7hold_usp_in,
  rxdfetap8hold_usp_in,
  rxdfetap9hold_usp_in,
  rxdfeuthold_usp_in,
  rxdfevphold_usp_in,
  rxdlysresetdone_usp_out,
  rxelecidle_usp_out,
  rxlpmen_usp_in,
  rxlpmgchold_usp_in,
  rxlpmhfhold_usp_in,
  rxlpmlfhold_usp_in,
  rxlpmoshold_usp_in,
  rxmcommaalignen_usp_in,
  rxoshold_usp_in,
  rxoutclk_usp_out,
  rxoutclkfabric_usp_out,
  rxoutclkpcs_usp_out,
  rxpcommaalignen_usp_in,
  rxpcsreset_usp_in,
  rxpd_usp_in,
  rxphaligndone_usp_out,
  rxpmareset_usp_in,
  rxpmaresetdone_usp_out,
  rxpolarity_usp_in,
  rxprbscntreset_usp_in,
  rxprbserr_usp_out,
  rxprbslocked_usp_out,
  rxprbssel_usp_in,
  rxprogdivreset_usp_in,
  rxrate_usp_in,
  rxratedone_usp_out,
  rxrecclkout_usp_out,
  rxresetdone_usp_out,
  rxslide_usp_in,
  rxstatus_usp_out,
  rxsyncdone_usp_out,
  rxtermination_usp_in,
  rxuserrdy_usp_in,
  rxusrclk2_usp_in,
  rxusrclk_usp_in,
  rxvalid_usp_out,
  tx8b10ben_usp_in,
  txctrl0_usp_in,
  txctrl1_usp_in,
  txctrl2_usp_in,
  txdata_usp_in,
  txdeemph_usp_in,
  txdetectrx_usp_in,
  txdiffctrl_usp_in,
  txdlybypass_usp_in,
  txdlyen_usp_in,
  txdlyhold_usp_in,
  txdlyovrden_usp_in,
  txdlysreset_usp_in,
  txdlysresetdone_usp_out,
  txdlyupdown_usp_in,
  txelecidle_usp_in,
  txmaincursor_usp_in,
  txmargin_usp_in,
  txoutclk_usp_out,
  txoutclkfabric_usp_out,
  txoutclkpcs_usp_out,
  txoutclksel_usp_in,
  txpcsreset_usp_in,
  txpd_usp_in,
  txphalign_usp_in,
  txphaligndone_usp_out,
  txphalignen_usp_in,
  txphdlypd_usp_in,
  txphdlyreset_usp_in,
  txphdlytstclk_usp_in,
  txphinit_usp_in,
  txphinitdone_usp_out,
  txphovrden_usp_in,
  rxratemode_usp_in,
  txpmareset_usp_in,
  txpmaresetdone_usp_out,
  txpostcursor_usp_in,
  txprbsforceerr_usp_in,
  txprbssel_usp_in,
  txprecursor_usp_in,
  txprgdivresetdone_usp_out,
  txprogdivreset_usp_in,
  txpdelecidlemode_usp_in,
  txrate_usp_in,
  txresetdone_usp_out,
  txswing_usp_in,
  txsyncallin_usp_in,
  txsyncdone_usp_out,
  txsyncin_usp_in,
  txsyncmode_usp_in,
  txsyncout_usp_out,
  txuserrdy_usp_in,
  txusrclk2_usp_in,
  txusrclk_usp_in,
  drpclk_usp_in,
  drpaddr_usp_in,
  drpen_usp_in,
  drprst_usp_in,
  drpwe_usp_in,
  drpdi_usp_in,
  drprdy_usp_out,
  drpdo_usp_out,

  ext_phy_clk_pclk2_gt,
  ext_phy_clk_int_clock,
  ext_phy_clk_pclk,
  ext_phy_clk_phy_pclk2,
  ext_phy_clk_phy_coreclk,
  ext_phy_clk_phy_userclk,
  ext_phy_clk_phy_mcapclk,

  ext_phy_clk_bufg_gt_ce,
  ext_phy_clk_bufg_gt_reset,
  ext_phy_clk_rst_idle,
  ext_phy_clk_txoutclk,
  ext_phy_clk_bufgtcemask,
  ext_phy_clk_gt_bufgtrstmask,
  ext_phy_clk_bufgtdiv,

  //---------- Internal GT COMMON Ports US+ ----------------------
  int_usp_qpll0lock_out,
  int_usp_qpll0outrefclk_out,
  int_usp_qpll0outclk_out,
  int_usp_qpll1lock_out,
  int_usp_qpll1outrefclk_out,
  int_usp_qpll1outclk_out,

  //---------- External GT COMMON Ports US+ ----------------------
  ext_usp_qpllxrefclk,
  ext_usp_qpllxrate,
  ext_usp_qpllxrcalenb,

  ext_usp_qpll0pd,
  ext_usp_qpll0reset,
  ext_usp_qpll0lock_out,
  ext_usp_qpll0outclk_out,
  ext_usp_qpll0outrefclk_out,
  ext_usp_qpll1pd,
  ext_usp_qpll1reset,
  ext_usp_qpll1lock_out,
  ext_usp_qpll1outclk_out,
  ext_usp_qpll1outrefclk_out,

  //--------------------------------------------------------------------------
  cfg_negotiated_width_o,
  cfg_current_speed_o,
  cfg_ltssm_state_o,
  cfg_err_cor_o,
  cfg_err_fatal_o,
  cfg_err_nonfatal_o,
  cfg_local_error_o,
  cfg_local_error_valid_o,
  pipe_tx0_rcvr_det,
  pipe_clk,
  sys_clk_bufg,
  pipe_tx0_powerdown,
  cfg_function_status,
  cfg_max_read_req,
  cfg_max_payload,
  cfg_flr_done,
  cfg_flr_in_process,
  cfg_vf_flr_in_process,
  cfg_vf_flr_func_num,
  cfg_vf_flr_done,
  cfg_interrupt_msi_enable,
  cfg_interrupt_msix_enable,
  cfg_interrupt_msix_mask,
  cfg_interrupt_msix_data,
  cfg_interrupt_msix_address,
  cfg_interrupt_msix_int,
  cfg_interrupt_msi_sent,
  cfg_interrupt_msi_fail,
  cfg_interrupt_msix_sent,
  cfg_interrupt_msix_fail,

  phy_rdy_out_sd,
  cfg_err_cor_in_sd,
  cfg_link_training_enable_sd,
  cfg_config_space_enable_sd,
  cfg_ltssm_state_sd,
  user_lnk_up_sd,
  s_axis_rq_tdata_sd,
  s_axis_rq_tlast_sd,
  s_axis_rq_tuser_sd,
  s_axis_rq_tkeep_sd,
  s_axis_rq_tvalid_sd,
  s_axis_rq_tready_sd,

  m_axis_rc_tdata_sd,
  m_axis_rc_tuser_sd,
  m_axis_rc_tlast_sd,
  m_axis_rc_tkeep_sd,
  m_axis_rc_tvalid_sd,
  m_axis_rc_tready_sd,

  m_axis_cq_tdata_sd,
  m_axis_cq_tuser_sd,
  m_axis_cq_tlast_sd,
  m_axis_cq_tkeep_sd,
  m_axis_cq_tvalid_sd,
  m_axis_cq_tready_sd,

  s_axis_cc_tdata_sd,
  s_axis_cc_tuser_sd,
  s_axis_cc_tlast_sd,
  s_axis_cc_tkeep_sd,
  s_axis_cc_tvalid_sd,
  s_axis_cc_tready_sd,

  rbar_bar_size_sd,
  rbar_function_number_sd,
  rbar_write_enable_bar0_sd,
  rbar_write_enable_bar1_sd,
  rbar_write_enable_bar2_sd,
  rbar_write_enable_bar3_sd,
  rbar_write_enable_bar4_sd,
  rbar_write_enable_bar5_sd,
  user_clk_sd,
  user_reset_sd,
  pcie_cq_np_req_sd,
  pcie_cq_np_req_count_sd,
  pcie_tfc_nph_av_sd,
  pcie_tfc_npd_av_sd,
  pcie_rq_seq_num_vld0_sd,
  pcie_rq_seq_num0_sd,
  pcie_rq_seq_num_vld1_sd,
  pcie_rq_seq_num1_sd,
  cfg_fc_nph_sd,
  cfg_fc_sel_sd,
  cfg_phy_link_down_sd,
  cfg_phy_link_status_sd,
  cfg_negotiated_width_sd,
  cfg_current_speed_sd,
  cfg_pl_status_change_sd,
  cfg_hot_reset_out_sd,
  cfg_ds_port_number_sd,
  cfg_ds_bus_number_sd,
  cfg_ds_device_number_sd,
  cfg_ds_function_number_sd,
  cfg_dsn_sd,
  cfg_function_status_sd,
  cfg_max_read_req_sd,
  cfg_max_payload_sd,
  cfg_err_uncor_in_sd,
  cfg_flr_done_sd,
  cfg_flr_in_process_sd,
  cfg_vf_flr_in_process_sd,

  usr_flr_fnc,     
  usr_flr_set,     
  usr_flr_clr,     
  usr_flr_done_fnc,
  usr_flr_done_vld,

  cfg_err_cor_out_sd,
  cfg_err_nonfatal_out_sd,
  cfg_err_fatal_out_sd,
  cfg_local_error_out_sd,

  cfg_msg_received_sd,
  cfg_msg_received_data_sd,
  cfg_msg_received_type_sd,
  cfg_msg_transmit_sd,
  cfg_msg_transmit_type_sd,
  cfg_msg_transmit_data_sd,
  cfg_msg_transmit_done_sd,

  cfg_mgmt_addr_sd,
  cfg_mgmt_write_sd,
  cfg_mgmt_write_data_sd,
  cfg_mgmt_byte_enable_sd,
  cfg_mgmt_read_sd,
  cfg_mgmt_type1_cfg_reg_access_sd,
  cfg_mgmt_read_data_sd,
  cfg_mgmt_read_write_done_sd,
  cfg_mgmt_function_number_sd,

  cfg_interrupt_int_sd,
  cfg_interrupt_sent_sd,
  cfg_interrupt_pending_sd,

  cfg_interrupt_msi_enable_sd,
  cfg_interrupt_msi_mask_update_sd,
  cfg_interrupt_msi_data_sd,
  cfg_interrupt_msi_int_sd,
  cfg_interrupt_msi_pending_status_sd,
  cfg_interrupt_msi_pending_status_data_enable_sd,
  cfg_interrupt_msi_pending_status_function_num_sd,
  cfg_interrupt_msi_attr_sd,
  cfg_interrupt_msi_tph_present_sd,
  cfg_interrupt_msi_tph_type_sd,
  cfg_interrupt_msi_tph_st_tag_sd,
  cfg_interrupt_msi_function_number_sd,

  cfg_interrupt_msi_sent_sd,
  cfg_interrupt_msi_fail_sd,

  cfg_interrupt_msix_enable_sd,
  cfg_interrupt_msix_mask_sd,
  cfg_interrupt_msix_data_sd,
  cfg_interrupt_msix_address_sd,
  cfg_interrupt_msix_int_sd,
  cfg_interrupt_msix_vf_enable_sd,
  cfg_interrupt_msix_vf_mask_sd,
  cfg_interrupt_msix_vec_pending_sd,
  cfg_interrupt_msix_vec_pending_status_sd,

  rd_interrupt,
  wr_interrupt,
  ats_pri_en,
  cfg_fc_vc_sel,
  core_clk,

  // CXS interface
  cxs0_active_req_tx,
  cxs0_active_ack_tx,
  cxs0_deact_hint_tx,
  cxs0_valid_tx,
  cxs0_crdgnt_tx,
  cxs0_crdrtn_tx,
  cxs0_cntl_tx,
  cxs0_data_tx,
  cxs0_valid_chk_tx,
  cxs0_crdgnt_chk_tx,
  cxs0_crdrtn_chk_tx,
  cxs0_cntl_chk_tx,
  cxs0_data_chk_tx,
  cxs0_active_req_rx,
  cxs0_active_ack_rx,
  cxs0_deact_hint_rx,
  cxs0_valid_rx,
  cxs0_crdgnt_rx,
  cxs0_crdrtn_rx,
  cxs0_cntl_rx,
  cxs0_data_rx,
  cxs0_valid_chk_rx,
  cxs0_crdgnt_chk_rx,
  cxs0_crdrtn_chk_rx,
  cxs0_cntl_chk_rx,
  cxs0_data_chk_rx,

  // CXS interface
  pcie4_cxs0_active_req_tx_sd,
  pcie4_cxs0_active_ack_tx_sd,
  pcie4_cxs0_deact_hint_tx_sd,
  pcie4_cxs0_valid_tx_sd,
  pcie4_cxs0_crdgnt_tx_sd,
  pcie4_cxs0_crdrtn_tx_sd,
  pcie4_cxs0_cntl_tx_sd,
  pcie4_cxs0_data_tx_sd,
  pcie4_cxs0_valid_chk_tx_sd,
  pcie4_cxs0_crdgnt_chk_tx_sd,
  pcie4_cxs0_crdrtn_chk_tx_sd,
  pcie4_cxs0_cntl_chk_tx_sd,
  pcie4_cxs0_data_chk_tx_sd,
  pcie4_cxs0_active_req_rx_sd,
  pcie4_cxs0_active_ack_rx_sd,
  pcie4_cxs0_deact_hint_rx_sd,
  pcie4_cxs0_valid_rx_sd,
  pcie4_cxs0_crdgnt_rx_sd,
  pcie4_cxs0_crdrtn_rx_sd,
  pcie4_cxs0_cntl_rx_sd,
  pcie4_cxs0_data_rx_sd,
  pcie4_cxs0_valid_chk_rx_sd,
  pcie4_cxs0_crdgnt_chk_rx_sd,
  pcie4_cxs0_crdrtn_chk_rx_sd,
  pcie4_cxs0_cntl_chk_rx_sd,
  pcie4_cxs0_data_chk_rx_sd,

  ccix_optimized_tlp_tx_and_rx_enable_in,

  sc0_ats_s_axis_rq_tvalid,
  sc0_ats_s_axis_rq_tready,
  sc0_ats_s_axis_rq_tdata,
  sc0_ats_s_axis_rq_tkeep,
  sc0_ats_s_axis_rq_tlast,
  sc0_ats_s_axis_rq_tuser,

  sc0_ats_m_axis_rc_tvalid,
  sc0_ats_m_axis_rc_tready,
  sc0_ats_m_axis_rc_tdata,
  sc0_ats_m_axis_rc_tkeep,
  sc0_ats_m_axis_rc_tlast,
  sc0_ats_m_axis_rc_tuser,

  sc0_ats_s_axis_cc_tvalid,
  sc0_ats_s_axis_cc_tready,
  sc0_ats_s_axis_cc_tdata,
  sc0_ats_s_axis_cc_tkeep,
  sc0_ats_s_axis_cc_tlast,
  sc0_ats_s_axis_cc_tuser,

  sc0_ats_m_axis_cq_tvalid,
  sc0_ats_m_axis_cq_tready,
  sc0_ats_m_axis_cq_tdata,
  sc0_ats_m_axis_cq_tkeep,
  sc0_ats_m_axis_cq_tlast,
  sc0_ats_m_axis_cq_tuser,

  sc1_ats_s_axis_rq_tvalid,
  sc1_ats_s_axis_rq_tready,
  sc1_ats_s_axis_rq_tdata,
  sc1_ats_s_axis_rq_tkeep,
  sc1_ats_s_axis_rq_tlast,
  sc1_ats_s_axis_rq_tuser,

  sc1_ats_m_axis_rc_tvalid,
  sc1_ats_m_axis_rc_tready,
  sc1_ats_m_axis_rc_tdata,
  sc1_ats_m_axis_rc_tkeep,
  sc1_ats_m_axis_rc_tlast,
  sc1_ats_m_axis_rc_tuser,

  sc1_ats_s_axis_cc_tvalid,
  sc1_ats_s_axis_cc_tready,
  sc1_ats_s_axis_cc_tdata,
  sc1_ats_s_axis_cc_tkeep,
  sc1_ats_s_axis_cc_tlast,
  sc1_ats_s_axis_cc_tuser,

  sc1_ats_m_axis_cq_tvalid,
  sc1_ats_m_axis_cq_tready,
  sc1_ats_m_axis_cq_tdata,
  sc1_ats_m_axis_cq_tkeep,
  sc1_ats_m_axis_cq_tlast,
  sc1_ats_m_axis_cq_tuser,

  // AXI SLAVE Interface to MicroProcessor
  s_aclk,
  s_aresetn,
  s_axi_araddr,
  s_axi_arburst,
  s_axi_arcache,
  s_axi_arid,
  s_axi_arlen,
  s_axi_arlock,
  s_axi_arprot,
  s_axi_arqos,
  s_axi_arready,
  s_axi_arsize,
  s_axi_aruser,
  s_axi_arvalid,
  s_axi_awaddr,
  s_axi_awburst,
  s_axi_awcache,
  s_axi_awid,
  s_axi_awlen,
  s_axi_awlock,
  s_axi_awprot,
  s_axi_awqos,
  s_axi_awready,
  s_axi_awsize,
  s_axi_awuser,
  s_axi_awvalid,
  s_axi_bid,
  s_axi_bready,
  s_axi_bresp,
  s_axi_bvalid,
  s_axi_rdata,
  s_axi_rid,
  s_axi_rlast,
  s_axi_rready,
  s_axi_rresp,
  s_axi_rvalid,
  s_axi_wdata,
  s_axi_wlast,
  s_axi_wready,
  s_axi_wstrb,
  s_axi_wvalid,

  // ATS Signals - Start
  atspri_m_axis_cq_tdata,
  atspri_m_axis_cq_tuser,
  atspri_m_axis_cq_tlast,
  atspri_m_axis_cq_tkeep,
  atspri_m_axis_cq_tvalid,
  atspri_m_axis_cq_tready,
  atspri_s_axis_rq_tdata,
  atspri_s_axis_rq_tuser,
  atspri_s_axis_rq_tlast,
  atspri_s_axis_rq_tkeep,
  atspri_s_axis_rq_tvalid,
  atspri_s_axis_rq_tready,
  cfg_status_ats_stu,
  cfg_status_ats_en,
  cfg_status_pr_en,
  cfg_status_pr_rst,
  cfg_status_pr_uprgi,
  cfg_status_set_uprgi,
  cfg_status_pr_rf,
  cfg_status_set_rf,
  cfg_status_set_s,
  cfg_status_clr_s,
  cfg_status_ost_pr_alloc
  // ATS Signals - End
);
  //--------------------------------------------------------------------------
  //  GT WIZARD IP is not in the US+ PCIe core
  //--------------------------------------------------------------------------
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]      gtrefclk01_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]      gtrefclk00_usp_in;
  output  [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] pcierateqpll0_usp_in;
  output  [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] pcierateqpll1_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]   qpll0pd_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]   qpll0reset_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]   qpll1pd_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]   qpll1reset_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll0lock_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll0outclk_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll0outrefclk_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1lock_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1outclk_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1outrefclk_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          qpll0freqlock_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]          qpll1freqlock_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]      pcierateqpllpd_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]      pcierateqpllreset_usp_out;

  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2 : 0]   rcalenb_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      txpisopd_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      bufgtce_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0] bufgtcemask_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH* 9)-1:0] bufgtdiv_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      bufgtreset_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0] bufgtrstmask_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      cpllfreqlock_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      cplllock_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      cpllpd_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      cpllreset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      dmonfiforeset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      dmonitorclk_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0] dmonitorout_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      eyescanreset_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gtpowergood_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gtrefclk0_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gtrxreset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gttxreset_usp_in;
  output  gtwiz_reset_rx_done_usp_in;
  output  gtwiz_reset_tx_done_usp_in;
  output  gtwiz_userclk_rx_active_usp_in;
  output  gtwiz_userclk_tx_active_usp_in;

  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0] loopback_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcieeqrxeqadaptdone_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcierategen3_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcierateidle_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcierstidle_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pciersttxsyncstart_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pciesynctxsyncdone_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcieusergen3rdy_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcieuserphystatusrst_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcieuserratedone_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pcieuserratestart_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] phystatus_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] resetovrd_usp_in;

  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rx8b10ben_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxbufreset_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]     rxbufstatus_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyteisaligned_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyterealign_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrfreqreset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrhold_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrlock_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrreset_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH * 2)-1 : 0] rxclkcorcnt_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadet_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadeten_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl0_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl1_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl2_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl3_usp_out;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0]   rxdata_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfeagchold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfecfokhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfekhhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfelfhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxdfelpmreset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap10hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap11hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap12hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap13hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap14hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap15hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap2hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap3hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap4hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap5hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap6hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap7hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap8hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfetap9hold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfeuthold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxdfevphold_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxdlysresetdone_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxelecidle_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxlpmen_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmgchold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmhfhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmlfhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxlpmoshold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxmcommaalignen_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxoshold_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxoutclk_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxoutclkfabric_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxoutclkpcs_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpcommaalignen_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpcsreset_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]    rxpd_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxphaligndone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpmareset_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpmaresetdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpolarity_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbscntreset_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbserr_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbslocked_usp_out;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]    rxprbssel_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprogdivreset_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxrate_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxratedone_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxrecclkout_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxresetdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxslide_usp_in;
  input   [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxstatus_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxsyncdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxtermination_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxuserrdy_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk2_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxvalid_usp_out;

  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       tx8b10ben_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]  txctrl0_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]  txctrl1_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 8)-1:0]  txctrl2_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0] txdata_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]  txdeemph_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdetectrx_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*5)-1:0]   txdiffctrl_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlybypass_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyen_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyhold_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyovrden_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlysreset_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlysresetdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txdlyupdown_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txelecidle_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 7)-1:0]  txmaincursor_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txmargin_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclk_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclkfabric_usp_out;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txoutclkpcs_usp_out;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txoutclksel_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpcsreset_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]  txpd_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphalign_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphaligndone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphalignen_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlypd_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlyreset_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphdlytstclk_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphinit_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphinitdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txphovrden_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       rxratemode_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpmareset_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]     txpmaresetdone_usp_out;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]  txpostcursor_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprbsforceerr_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]  txprbssel_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]  txprecursor_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprgdivresetdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txpdelecidlemode_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txprogdivreset_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]  txrate_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txresetdone_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txswing_usp_in;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]   txsyncallin_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]     txsyncdone_usp_out;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]   txsyncin_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txsyncmode_usp_in;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txsyncout_usp_out;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txuserrdy_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txusrclk2_usp_in;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       txusrclk_usp_in;

  output                                            drpclk_usp_in;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH * 10)-1):0] drpaddr_usp_in;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drpen_usp_in;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drprst_usp_in;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drpwe_usp_in;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] drpdi_usp_in;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] drprdy_usp_out;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] drpdo_usp_out;

  input        ext_phy_clk_pclk2_gt;
  input        ext_phy_clk_int_clock;
  input        ext_phy_clk_pclk;
  input        ext_phy_clk_phy_pclk2;
  input        ext_phy_clk_phy_coreclk;
  input        ext_phy_clk_phy_userclk;
  input        ext_phy_clk_phy_mcapclk;

  output       ext_phy_clk_bufg_gt_ce;
  output       ext_phy_clk_bufg_gt_reset;
  output       ext_phy_clk_rst_idle;
  output       ext_phy_clk_txoutclk;
  output       ext_phy_clk_bufgtcemask;
  output       ext_phy_clk_gt_bufgtrstmask;
  output [8:0] ext_phy_clk_bufgtdiv;

//----- Internal GT COMMON Ports US+ ----------------------
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll0lock_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll0outrefclk_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll0outclk_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll1lock_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll1outrefclk_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] int_usp_qpll1outclk_out;

//----- External GT COMMON Ports US+ ----------------------
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpllxrefclk;
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] ext_usp_qpllxrate;
  output                                                   ext_usp_qpllxrcalenb;

  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll0pd;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll0reset;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll0lock_out;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll0outclk_out;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll0outrefclk_out;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll1pd;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll1reset;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll1lock_out;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll1outclk_out;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_usp_qpll1outrefclk_out;

 //--------------------------------------------------------------------------
 //  GT WIZARD IP is not in the US PCIe core
 //--------------------------------------------------------------------------

  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtce_us_out ;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtcemask_us_out ;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 9)-1:0]    bufgtdiv_us_out ;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtreset_us_out ;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    bufgtrstmask_us_out ;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cplllock_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*17)-1:0]    dmonitorout_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 16)-1:0]   drpdo_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 1)-1:0]    drprdy_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         eyescandataerror_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gthtxn_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gthtxp_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtpowergood_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierategen3_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierateidle_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]     pcierateqpllpd_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*2)-1:0]     pcierateqpllreset_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pciesynctxsyncdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieusergen3rdy_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserphystatusrst_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserratestart_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*12)-1:0]    pcsrsvdout_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         phystatus_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]     rxbufstatus_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyteisaligned_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxbyterealign_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrlock_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH * 2)-1 : 0] rxclkcorcnt_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadet_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl0_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    rxctrl1_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl2_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]     rxctrl3_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0]   rxdata_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxdlysresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxelecidle_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       rxoutclk_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxphaligndone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpmaresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbserr_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbslocked_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprgdivresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxratedone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxresetdone_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxstatus_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxsyncdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxvalid_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlysresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txoutclk_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphaligndone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphinitdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       txpmaresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txprgdivresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txresetdone_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txsyncout_us_out;
  input [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       txsyncdone_us_out;

  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]    cpllpd_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfeagchold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfecfokhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfelfhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfekhhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap2hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap3hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap4hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap5hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap6hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap7hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap8hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap9hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap10hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap11hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap12hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap13hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap14hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfetap15hold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfeuthold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxdfevphold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxoshold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxlpmgchold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxlpmhfhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxlpmlfhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]  rxlpmoshold_us_in;

  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         cpllreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         dmonfiforeset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         dmonitorclk_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         drpclk_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 9)-1:0]    drpaddr_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 16)-1:0]   drpdi_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 1)-1:0]    drpen_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 1)-1:0]    drpwe_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         eyescanreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gthrxn_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gthrxp_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtrefclk0_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gtrxreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         gttxreset_us_in;
  output   gtwiz_reset_rx_done_us_in;
  output   gtwiz_reset_tx_done_us_in;
  output   gtwiz_userclk_rx_active_us_in ;
  output   gtwiz_userclk_tx_active_us_in ;
  output   gtwiz_userclk_tx_reset_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    loopback_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieeqrxeqadaptdone_us_in ;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcierstidle_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pciersttxsyncstart_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         pcieuserratedone_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    pcsrsvdin_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rx8b10ben_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxbufreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcdrhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxcommadeten_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxlpmen_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxmcommaalignen_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpcommaalignen_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]    rxpd_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxpolarity_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprbscntreset_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]    rxprbssel_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxprogdivreset_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    rxrate_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxratemode_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxslide_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxuserrdy_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk2_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         rxusrclk_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         tx8b10ben_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    txctrl0_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*16)-1:0]    txctrl1_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 8)-1:0]    txctrl2_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*128)-1:0]   txdata_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdeemph_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdetectrx_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH*4)-1:0]     txdiffctrl_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlybypass_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlyen_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlyhold_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlyovrden_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlysreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txdlyupdown_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txelecidle_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txinhibit_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 7)-1:0]    txmaincursor_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    txmargin_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    txoutclksel_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 2)-1:0]    txpd_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphalign_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphalignen_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphdlypd_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphdlyreset_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphdlytstclk_us_in ;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphinit_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txphovrden_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]    txpostcursor_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txprbsforceerr_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 4)-1:0]    txprbssel_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 5)-1:0]    txprecursor_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txprogdivreset_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH* 3)-1:0]    txrate_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txswing_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]     txsyncallin_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1) : 0]     txsyncin_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txsyncmode_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txuserrdy_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txusrclk2_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]         txusrclk_us_in;

  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       qpll0clk_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       qpll0refclk_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       qpll1clk_us_in;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]       qpll1refclk_us_in;

  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    gtrefclk01_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll1pd_us_in;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]    qpll1reset_us_in;
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)* 5)-1:0] qpllrsvd2_us_in;
  output [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)* 5)-1:0] qpllrsvd3_us_in;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1lock_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1outclk_us_out;
  input [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0]     qpll1outrefclk_us_out;

  input  [31:0]			pipe_debug_ctl_in_tx0;
  input	 [31:0]		  pipe_debug_ctl_in_tx1;
  input	 [31:0]		  pipe_debug_ctl_in_rx0;
  input  [31:0]			pipe_debug_ctl_in_rx1;
  input					    pipe_debug_ltssm_rec_spd_1;
  input					    pipe_debug_ltssm_pol_act;
  input  [3:0] 			pipe_debug_ctl_vec4;
  input  [31:0] 		pipe_debug_mux_ctl;
  output [127:0]		pipe_debug_debug_out_128_0;
  output [15:0]			pipe_debug_debug_out_ext_16_0;
  output [127:0]		pipe_debug_debug_out_128_1;
  output [15:0]			pipe_debug_debug_out_ext_16_1;
  output [127:0]		pipe_debug_debug_out_128_2;
  output [15:0]			pipe_debug_debug_out_ext_16_2;
  output [127:0]		pipe_debug_debug_out_128_3;
  output [15:0]			pipe_debug_debug_out_ext_16_3;
  output [7:0] 			pipe_debug_inject_tx_status;
  output [7:0] 			pipe_debug_inject_rx_status;

  input  [15:0]    cfg_vend_id;
  input  [15:0]    cfg_subsys_vend_id;
  input  [15:0]    cfg_dev_id_pf0;
  input  [15:0]    cfg_dev_id_pf1;
  input  [15:0]    cfg_dev_id_pf2;
  input  [15:0]    cfg_dev_id_pf3;
  input  [7:0]     cfg_rev_id_pf0;
  input  [7:0]     cfg_rev_id_pf1;
  input  [7:0]     cfg_rev_id_pf2;
  input  [7:0]     cfg_rev_id_pf3;
  input  [15:0]    cfg_subsys_id_pf0;
  input  [15:0]    cfg_subsys_id_pf1;
  input  [15:0]    cfg_subsys_id_pf2;
  input  [15:0]    cfg_subsys_id_pf3;

  input  [25:0] common_commands_in;
  input  [83:0] pipe_rx_0_sigs;
  input  [83:0] pipe_rx_1_sigs;
  input  [83:0] pipe_rx_2_sigs;
  input  [83:0] pipe_rx_3_sigs;
  input  [83:0] pipe_rx_4_sigs;
  input  [83:0] pipe_rx_5_sigs;
  input  [83:0] pipe_rx_6_sigs;
  input  [83:0] pipe_rx_7_sigs;
  input  [83:0] pipe_rx_8_sigs;
  input  [83:0] pipe_rx_9_sigs;
  input  [83:0] pipe_rx_10_sigs;
  input  [83:0] pipe_rx_11_sigs;
  input  [83:0] pipe_rx_12_sigs;
  input  [83:0] pipe_rx_13_sigs;
  input  [83:0] pipe_rx_14_sigs;
  input  [83:0] pipe_rx_15_sigs;

  output [25:0] common_commands_out;
  output [83:0] pipe_tx_0_sigs;
  output [83:0] pipe_tx_1_sigs;
  output [83:0] pipe_tx_2_sigs;
  output [83:0] pipe_tx_3_sigs;
  output [83:0] pipe_tx_4_sigs;
  output [83:0] pipe_tx_5_sigs;
  output [83:0] pipe_tx_6_sigs;
  output [83:0] pipe_tx_7_sigs;
  output [83:0] pipe_tx_8_sigs;
  output [83:0] pipe_tx_9_sigs;
  output [83:0] pipe_tx_10_sigs;
  output [83:0] pipe_tx_11_sigs;
  output [83:0] pipe_tx_12_sigs;
  output [83:0] pipe_tx_13_sigs;
  output [83:0] pipe_tx_14_sigs;
  output [83:0] pipe_tx_15_sigs;

  input  [18:0] cfg_mgmt_addr;
  input         cfg_mgmt_write;
  input  [31:0] cfg_mgmt_write_data;
  input  [3:0]  cfg_mgmt_byte_enable;
  input         cfg_mgmt_read;
  output [31:0] cfg_mgmt_read_data;
  output        cfg_mgmt_read_write_done;
  input         cfg_mgmt_type1_cfg_reg_access;

  output gt_drp_clk ;
  output axi_aclk;
  output axi_aresetn;

  input        axi_ctl_aclk;
  output       axi_ctl_aresetn;
  output [5:0] cfg_ltssm_state;
  input              config_space_enable;
  input  [XDMA_NUM_USR_IRQ-1:0]   usr_irq_req;
  output [XDMA_NUM_USR_IRQ-1:0]   usr_irq_ack;

  input  [2*XDMA_NUM_USR_IRQ-1:0] usr_irq_function_number;
  output                          msi_enable;
  output                          msix_enable;
  output [2:0]                    msi_vector_width;

  output  [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_awid;
  output  [AXI_ADDR_WIDTH-1 : 0]       m_axi_awaddr;
  output  [7 : 0]                      m_axi_awlen;
  output  [2 : 0]                      m_axi_awsize;
  output  [1 : 0]                      m_axi_awburst;
  output  [2 : 0]                      m_axi_awprot;
  output                               m_axi_awvalid;
  input                                m_axi_awready;
  output                               m_axi_awlock;
  output  [3 : 0]                      m_axi_awcache;
  output  [C_M_AXI_DATA_WIDTH-1 : 0]   m_axi_wdata;
  output  [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axi_wuser;
  output  [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axi_wstrb;
  output                               m_axi_wlast;
  output                               m_axi_wvalid;
  input                                m_axi_wready;
  input  [C_M_AXI_ID_WIDTH-1 : 0]      m_axi_bid;
  input  [1 : 0]                       m_axi_bresp;
  input                                m_axi_bvalid;
  output                               m_axi_bready;
  output  [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_arid;
  output  [AXI_ADDR_WIDTH-1 : 0]       m_axi_araddr;
  output  [7 : 0]                      m_axi_arlen;
  output  [2 : 0]                      m_axi_arsize;
  output  [1 : 0]                      m_axi_arburst;
  output  [2 : 0]                      m_axi_arprot;
  output                               m_axi_arvalid;
  input                                m_axi_arready;
  output                               m_axi_arlock;
  output  [3 : 0]                      m_axi_arcache;
  input  [C_M_AXI_ID_WIDTH-1 : 0]      m_axi_rid;
  input  [C_M_AXI_DATA_WIDTH-1 : 0]    m_axi_rdata;
  input  [C_M_AXI_DATA_WIDTH/8-1 : 0]  m_axi_ruser;
  input  [1 : 0]                       m_axi_rresp;
  input                                m_axi_rlast;
  input                                m_axi_rvalid;
  output                               m_axi_rready;
  // Axi bypass
  output  [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_awid;
  output  [AXI_ADDR_WIDTH-1 : 0]       m_axib_awaddr;
  output  [C_M_AXI_AWUSER_WIDTH-1 : 0] m_axib_awuser;
  output  [7 : 0]                      m_axib_awlen;
  output  [2 : 0]                      m_axib_awsize;
  output  [1 : 0]                      m_axib_awburst;
  output  [2 : 0]                      m_axib_awprot;
  output                               m_axib_awvalid;
  input                                m_axib_awready;
  output                               m_axib_awlock;
  output  [3 : 0]                      m_axib_awcache;
  output  [C_M_AXI_DATA_WIDTH-1 : 0]   m_axib_wdata ;
  output  [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axib_wuser;
  output  [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axib_wstrb ;
  output                               m_axib_wlast ;
  output                               m_axib_wvalid ;
  input                                m_axib_wready ;
  input  [C_M_AXI_ID_WIDTH-1 : 0]      m_axib_bid ;
  input  [1 : 0]                       m_axib_bresp ;
  input                                m_axib_bvalid ;
  output                               m_axib_bready ;
  output  [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_arid ;
  output  [AXI_ADDR_WIDTH-1 : 0]       m_axib_araddr ;
  output  [C_M_AXI_ARUSER_WIDTH-1 : 0] m_axib_aruser ;
  output  [7 : 0]                      m_axib_arlen ;
  output  [2 : 0]                      m_axib_arsize ;
  output  [1 : 0]                      m_axib_arburst ;
  output  [2 : 0]                      m_axib_arprot ;
  output                               m_axib_arvalid ;
  input                                m_axib_arready ;
  output                               m_axib_arlock;
  output  [3 : 0]                      m_axib_arcache;
  input  [C_M_AXI_ID_WIDTH-1 : 0]      m_axib_rid ;
  input  [C_M_AXI_DATA_WIDTH-1 : 0]    m_axib_rdata ;
  input  [C_M_AXI_DATA_WIDTH/8-1 : 0]  m_axib_ruser;
  input  [1 : 0]                       m_axib_rresp ;
  input                                m_axib_rlast ;
  input                                m_axib_rvalid ;
  output                               m_axib_rready ;

  // C2H AXI ST interface to user Channle 0
  input    [C_S_AXIS_DATA_WIDTH-1:0]   s_axis_c2h_tdata_0;
  input                                s_axis_c2h_tlast_0;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tuser_0;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tkeep_0;
  input                                s_axis_c2h_tvalid_0;
  output                               s_axis_c2h_tready_0;
  // C2H AXI ST interface to user Channle 1
  input    [C_S_AXIS_DATA_WIDTH-1:0]   s_axis_c2h_tdata_1;
  input                                s_axis_c2h_tlast_1;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tuser_1;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tkeep_1;
  input                                s_axis_c2h_tvalid_1;
  output                               s_axis_c2h_tready_1;
  // C2H AXI ST interface to user Channle 2
  input    [C_S_AXIS_DATA_WIDTH-1:0]   s_axis_c2h_tdata_2;
  input                                s_axis_c2h_tlast_2;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tuser_2;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tkeep_2;
  input                                s_axis_c2h_tvalid_2;
  output                               s_axis_c2h_tready_2;
  // C2H AXI ST interface to user Channle 3
  input    [C_S_AXIS_DATA_WIDTH-1:0]   s_axis_c2h_tdata_3;
  input                                s_axis_c2h_tlast_3;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tuser_3;
  input    [C_S_AXIS_DATA_WIDTH/8-1:0] s_axis_c2h_tkeep_3;
  input                                s_axis_c2h_tvalid_3;
  output                               s_axis_c2h_tready_3;

  // H2C AXI ST interface to user Channel 0
  output   [C_M_AXIS_DATA_WIDTH-1:0]   m_axis_h2c_tdata_0;
  output                               m_axis_h2c_tlast_0;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tuser_0;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tkeep_0;
  output                               m_axis_h2c_tvalid_0;
  input                                m_axis_h2c_tready_0;
  // H2C AXI ST interface to user Channel 1
  output   [C_M_AXIS_DATA_WIDTH-1:0]   m_axis_h2c_tdata_1;
  output                               m_axis_h2c_tlast_1;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tuser_1;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tkeep_1;
  output                               m_axis_h2c_tvalid_1;
  input                                m_axis_h2c_tready_1;
  // H2C AXI ST interface to user Channel 2
  output   [C_M_AXIS_DATA_WIDTH-1:0]   m_axis_h2c_tdata_2;
  output                               m_axis_h2c_tlast_2;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tuser_2;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tkeep_2;
  output                               m_axis_h2c_tvalid_2;
  input                                m_axis_h2c_tready_2;
  // H2C AXI ST interface to user Channel 3
  output   [C_M_AXIS_DATA_WIDTH-1:0]   m_axis_h2c_tdata_3;
  output                               m_axis_h2c_tlast_3;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tuser_3;
  output   [C_M_AXIS_DATA_WIDTH/8-1:0] m_axis_h2c_tkeep_3;
  output                               m_axis_h2c_tvalid_3;
  input                                m_axis_h2c_tready_3;

  output  [31 : 0]                     m_axil_awaddr;
  output  [C_M_AXIL_AWUSER_WIDTH-1: 0] m_axil_awuser;
  output  [2 : 0]                      m_axil_awprot;
  output                               m_axil_awvalid;
  input                                m_axil_awready;
  output  [31 : 0]                     m_axil_wdata;
  output  [3 : 0]                      m_axil_wstrb;
  output                               m_axil_wvalid;
  input                                m_axil_wready;
  input                                m_axil_bvalid;
  input  [1:0]                         m_axil_bresp;
  output                               m_axil_bready;
  output  [31 : 0]                     m_axil_araddr;
  output  [C_M_AXIL_ARUSER_WIDTH-1: 0] m_axil_aruser;
  output  [2 : 0]                      m_axil_arprot;
  output                               m_axil_arvalid;
  input                                m_axil_arready;
  input  [31 : 0]                      m_axil_rdata ;
  input  [1 : 0]                       m_axil_rresp ;
  input                                m_axil_rvalid;
  output                               m_axil_rready;
  input  [31 : 0]                      s_axil_awaddr;
  input  [2 : 0]                       s_axil_awprot;
  input                                s_axil_awvalid;
  output                               s_axil_awready;
  input  [31 : 0]                      s_axil_wdata ;
  input  [3 : 0]                       s_axil_wstrb ;
  input                                s_axil_wvalid;
  output                               s_axil_wready;
  output                               s_axil_bvalid;
  output  [1:0]                        s_axil_bresp;
  input                                s_axil_bready;
  input  [31 : 0]                      s_axil_araddr;
  input  [2 : 0]                       s_axil_arprot;
  input                                s_axil_arvalid;
  output                               s_axil_arready;
  output  [31 : 0]                     s_axil_rdata ;
  output  [1 : 0]                      s_axil_rresp;
  output                               s_axil_rvalid;
  input                                s_axil_rready;
  //-- AXI Slave Write Address Channel
  input [C_S_AXI_ID_WIDTH-1:0]         s_axib_awid;
  input [AXI_ADDR_WIDTH-1:0]           s_axib_awaddr;
  input [3:0]                          s_axib_awregion;
  input [7:0]                          s_axib_awlen;
  input [2:0]                          s_axib_awsize;
  input [1:0]                          s_axib_awburst;
  input                                s_axib_awvalid;
  output                               s_axib_awready;
  //-- AXI Slave Write Data Channel
  input [C_S_AXI_DATA_WIDTH-1:0]       s_axib_wdata;
  input [C_S_AXI_DATA_WIDTH/8-1:0]     s_axib_wuser;
  input [C_S_AXI_DATA_WIDTH/8-1:0]     s_axib_wstrb;
  input                                s_axib_wlast;
  input                                s_axib_wvalid;
  output                               s_axib_wready;
  //-- AXI Slave Write Response Channel
  output [C_S_AXI_ID_WIDTH-1:0]        s_axib_bid;
  output [1:0]                         s_axib_bresp;
  output                               s_axib_bvalid;
  input                                s_axib_bready;
  //-- AXI Slave Read Address Channel
  input  [C_S_AXI_ID_WIDTH-1:0]        s_axib_arid;
  input  [AXI_ADDR_WIDTH-1:0]          s_axib_araddr;
  input  [3:0]                         s_axib_arregion;
  input  [7:0]                         s_axib_arlen;
  input  [2:0]                         s_axib_arsize;
  input  [1:0]                         s_axib_arburst;
  input                                s_axib_arvalid;
  output                               s_axib_arready;
  //-- AXI Slave Read Data Channel
  output [C_S_AXI_ID_WIDTH-1:0]        s_axib_rid;
  output [1:0]                         s_axib_rresp;
  output                               s_axib_rlast;
  output                               s_axib_rvalid;
  output [C_S_AXI_DATA_WIDTH-1:0]      s_axib_rdata;
  output [(C_S_AXI_DATA_WIDTH/8)-1:0]  s_axib_ruser;
  input                                s_axib_rready;
  // Descriptor Bypass channel 0
  output         c2h_dsc_byp_ready_0;
  input  [63:0]  c2h_dsc_byp_src_addr_0;
  input  [63:0]  c2h_dsc_byp_dst_addr_0;
  input  [27:0]  c2h_dsc_byp_len_0;
  input  [15:0]  c2h_dsc_byp_ctl_0;
  input          c2h_dsc_byp_load_0;

  output         h2c_dsc_byp_ready_0;
  input  [63:0]  h2c_dsc_byp_src_addr_0;
  input  [63:0]  h2c_dsc_byp_dst_addr_0;
  input  [27:0]  h2c_dsc_byp_len_0;
  input  [15:0]  h2c_dsc_byp_ctl_0;
  input          h2c_dsc_byp_load_0;

  // Descriptor Bypass channel 1
  output         c2h_dsc_byp_ready_1;
  input  [63:0]  c2h_dsc_byp_src_addr_1;
  input  [63:0]  c2h_dsc_byp_dst_addr_1;
  input  [27:0]  c2h_dsc_byp_len_1;
  input  [15:0]  c2h_dsc_byp_ctl_1;
  input          c2h_dsc_byp_load_1;

  output          h2c_dsc_byp_ready_1;
  input   [63:0]  h2c_dsc_byp_src_addr_1;
  input   [63:0]  h2c_dsc_byp_dst_addr_1;
  input   [27:0]  h2c_dsc_byp_len_1;
  input   [15:0]  h2c_dsc_byp_ctl_1;
  input           h2c_dsc_byp_load_1;

  // Descriptor Bypass channel 2
  output         c2h_dsc_byp_ready_2;
  input  [63:0]  c2h_dsc_byp_src_addr_2;
  input  [63:0]  c2h_dsc_byp_dst_addr_2;
  input  [27:0]  c2h_dsc_byp_len_2;
  input  [15:0]  c2h_dsc_byp_ctl_2;
  input          c2h_dsc_byp_load_2;

  output         h2c_dsc_byp_ready_2;
  input  [63:0]  h2c_dsc_byp_src_addr_2;
  input  [63:0]  h2c_dsc_byp_dst_addr_2;
  input  [27:0]  h2c_dsc_byp_len_2;
  input  [15:0]  h2c_dsc_byp_ctl_2;
  input          h2c_dsc_byp_load_2;

  // Descriptor Bypass channel 3
  output         c2h_dsc_byp_ready_3;
  input  [63:0]  c2h_dsc_byp_src_addr_3;
  input  [63:0]  c2h_dsc_byp_dst_addr_3;
  input  [27:0]  c2h_dsc_byp_len_3;
  input  [15:0]  c2h_dsc_byp_ctl_3;
  input          c2h_dsc_byp_load_3;

  output         h2c_dsc_byp_ready_3;
  input  [63:0]  h2c_dsc_byp_src_addr_3;
  input  [63:0]  h2c_dsc_byp_dst_addr_3;
  input  [27:0]  h2c_dsc_byp_len_3;
  input  [15:0]  h2c_dsc_byp_ctl_3;
  input          h2c_dsc_byp_load_3;

  // Status Channel 0
  output   [STS_WIDTH-1:0] c2h_sts_0;
  output   [STS_WIDTH-1:0] h2c_sts_0;

  // Status Channel 1
  output   [STS_WIDTH-1:0] c2h_sts_1;
  output   [STS_WIDTH-1:0] h2c_sts_1;

  // Status Channel 2
  output   [STS_WIDTH-1:0] c2h_sts_2;
  output   [STS_WIDTH-1:0] h2c_sts_2;

  // Status Channel 3
  output   [STS_WIDTH-1:0] c2h_sts_3;
  output   [STS_WIDTH-1:0] h2c_sts_3;

  output  rd_interrupt;
  output  wr_interrupt;
  output  ats_pri_en;

  // AXI SLAVE Interface to MicroProcessor
  // AXI Lite Slave interface to DVSEC block;
  input   s_aclk;
  input   s_aresetn;

  input   [13:0]  s_axi_araddr;
  input   [1:0]   s_axi_arburst;
  input   [3:0]   s_axi_arcache;
  input   [15:0]  s_axi_arid;
  input   [7:0]   s_axi_arlen;
  input   [0:0]   s_axi_arlock;
  input   [2:0]   s_axi_arprot;
  input   [3:0]   s_axi_arqos;
  output          s_axi_arready;
  input   [2:0]   s_axi_arsize;
  input   [15:0]  s_axi_aruser;
  input           s_axi_arvalid;
  input   [13:0]  s_axi_awaddr;
  input   [1:0]   s_axi_awburst;
  input   [3:0]   s_axi_awcache;
  input   [15:0]  s_axi_awid;
  input   [7:0]   s_axi_awlen;
  input   [0:0]   s_axi_awlock;
  input   [2:0]   s_axi_awprot;
  input   [3:0]   s_axi_awqos;
  output          s_axi_awready;
  input   [2:0]   s_axi_awsize;
  input   [15:0]  s_axi_awuser;
  input           s_axi_awvalid;
  output   [15:0] s_axi_bid;
  input           s_axi_bready;
  output   [1:0]  s_axi_bresp;
  output          s_axi_bvalid;
  output   [31:0] s_axi_rdata;
  output   [15:0] s_axi_rid;
  output          s_axi_rlast;
  input           s_axi_rready;
  output   [1:0]  s_axi_rresp;
  output          s_axi_rvalid;
  input   [31:0]  s_axi_wdata;
  input           s_axi_wlast;
  output          s_axi_wready;
  input   [3:0]   s_axi_wstrb;
  input           s_axi_wvalid;

  input           cfg_fc_vc_sel;
  output          core_clk;

  // CXS interface
  input           cxs0_active_req_tx;
  output          cxs0_active_ack_tx;
  output          cxs0_deact_hint_tx;
  input           cxs0_valid_tx;
  output          cxs0_crdgnt_tx;
  input           cxs0_crdrtn_tx;
  input  [AXIS_CCIX_TX_TUSER_WIDTH-(AXIS_CCIX_TX_TDATA_WIDTH/8)-2:0]   cxs0_cntl_tx;
  input  [AXIS_CCIX_TX_TDATA_WIDTH-1:0]  cxs0_data_tx;
  input           cxs0_valid_chk_tx;
  output          cxs0_crdgnt_chk_tx;
  input           cxs0_crdrtn_chk_tx;
  input           cxs0_cntl_chk_tx;
  input  [AXIS_CCIX_TX_TDATA_WIDTH/8-1:0]   cxs0_data_chk_tx;
  output          cxs0_active_req_rx;
  input           cxs0_active_ack_rx;
  input           cxs0_deact_hint_rx;
  output          cxs0_valid_rx;
  input           cxs0_crdgnt_rx;
  output          cxs0_crdrtn_rx;
  output [AXIS_CCIX_RX_TUSER_WIDTH-(AXIS_CCIX_RX_TDATA_WIDTH/8)-2:0]   cxs0_cntl_rx;
  output [AXIS_CCIX_RX_TDATA_WIDTH-1:0]  cxs0_data_rx;
  output          cxs0_valid_chk_rx;
  input           cxs0_crdgnt_chk_rx;
  output          cxs0_crdrtn_chk_rx;
  output          cxs0_cntl_chk_rx;
  output [AXIS_CCIX_RX_TDATA_WIDTH/8-1:0]   cxs0_data_chk_rx;

  input           ccix_optimized_tlp_tx_and_rx_enable_in;

  // CXS interface
  output    pcie4_cxs0_active_req_tx_sd;
  input     pcie4_cxs0_active_ack_tx_sd;
  input     pcie4_cxs0_deact_hint_tx_sd;
  output    pcie4_cxs0_valid_tx_sd;
  input     pcie4_cxs0_crdgnt_tx_sd;
  output    pcie4_cxs0_crdrtn_tx_sd;
  output [AXIS_CCIX_TX_TUSER_WIDTH-(AXIS_CCIX_TX_TDATA_WIDTH/8)-2:0]   pcie4_cxs0_cntl_tx_sd;
  output [AXIS_CCIX_TX_TDATA_WIDTH-1:0]  pcie4_cxs0_data_tx_sd;
  output    pcie4_cxs0_valid_chk_tx_sd;
  input     pcie4_cxs0_crdgnt_chk_tx_sd;
  output    pcie4_cxs0_crdrtn_chk_tx_sd;
  output    pcie4_cxs0_cntl_chk_tx_sd;
  output [AXIS_CCIX_TX_TDATA_WIDTH/8-1:0]   pcie4_cxs0_data_chk_tx_sd;
  input     pcie4_cxs0_active_req_rx_sd;
  output    pcie4_cxs0_active_ack_rx_sd;
  output    pcie4_cxs0_deact_hint_rx_sd;
  input     pcie4_cxs0_valid_rx_sd;
  output    pcie4_cxs0_crdgnt_rx_sd;
  input     pcie4_cxs0_crdrtn_rx_sd;
  input  [AXIS_CCIX_RX_TUSER_WIDTH-(AXIS_CCIX_RX_TDATA_WIDTH/8)-2:0]   pcie4_cxs0_cntl_rx_sd;
  input  [AXIS_CCIX_RX_TDATA_WIDTH-1:0]  pcie4_cxs0_data_rx_sd;
  input     pcie4_cxs0_valid_chk_rx_sd;
  output    pcie4_cxs0_crdgnt_chk_rx_sd;
  input     pcie4_cxs0_crdrtn_chk_rx_sd;
  input     pcie4_cxs0_cntl_chk_rx_sd;
  input  [AXIS_CCIX_RX_TDATA_WIDTH/8-1:0]   pcie4_cxs0_data_chk_rx_sd;

  // System Cache1 Interface
  //RQ Interface
  input                             sc0_ats_s_axis_rq_tvalid;
  output                            sc0_ats_s_axis_rq_tready;
  input [C_ATS_DATA_WIDTH-1:0]      sc0_ats_s_axis_rq_tdata;
  input [C_ATS_DATA_WIDTH/8-1:0]    sc0_ats_s_axis_rq_tkeep;
  input                             sc0_ats_s_axis_rq_tlast;
  input [C_ATS_RQ_TUSER_WIDTH-1:0]  sc0_ats_s_axis_rq_tuser;

  //RC Interface
  output                            sc0_ats_m_axis_rc_tvalid;
  input                             sc0_ats_m_axis_rc_tready;
  output [C_ATS_DATA_WIDTH-1:0]     sc0_ats_m_axis_rc_tdata;
  output [C_ATS_DATA_WIDTH/8-1:0]   sc0_ats_m_axis_rc_tkeep;
  output                            sc0_ats_m_axis_rc_tlast;
  output [C_ATS_RC_TUSER_WIDTH-1:0] sc0_ats_m_axis_rc_tuser;

  //CC Interface
  input                             sc0_ats_s_axis_cc_tvalid;
  output                            sc0_ats_s_axis_cc_tready;
  input [C_ATS_DATA_WIDTH-1:0]      sc0_ats_s_axis_cc_tdata;
  input [C_ATS_DATA_WIDTH/8-1:0]    sc0_ats_s_axis_cc_tkeep;
  input                             sc0_ats_s_axis_cc_tlast;
  input [C_ATS_CC_TUSER_WIDTH-1:0]  sc0_ats_s_axis_cc_tuser;

  //CQ Interface
  output                            sc0_ats_m_axis_cq_tvalid;
  input                             sc0_ats_m_axis_cq_tready;
  output [C_ATS_DATA_WIDTH-1:0]     sc0_ats_m_axis_cq_tdata;
  output [C_ATS_DATA_WIDTH/8-1:0]   sc0_ats_m_axis_cq_tkeep;
  output                            sc0_ats_m_axis_cq_tlast;
  output [C_ATS_CQ_TUSER_WIDTH-1:0] sc0_ats_m_axis_cq_tuser;


  // System Cache2 Interface
  //RQ Interface
  input                             sc1_ats_s_axis_rq_tvalid;
  output                            sc1_ats_s_axis_rq_tready;
  input [C_ATS_DATA_WIDTH-1:0]      sc1_ats_s_axis_rq_tdata;
  input [C_ATS_DATA_WIDTH/8-1:0]    sc1_ats_s_axis_rq_tkeep;
  input                             sc1_ats_s_axis_rq_tlast;
  input [C_ATS_RQ_TUSER_WIDTH-1:0]  sc1_ats_s_axis_rq_tuser;

  //RC Interface
  output                            sc1_ats_m_axis_rc_tvalid;
  input                             sc1_ats_m_axis_rc_tready;
  output [C_ATS_DATA_WIDTH-1:0]     sc1_ats_m_axis_rc_tdata;
  output [C_ATS_DATA_WIDTH/8-1:0]   sc1_ats_m_axis_rc_tkeep;
  output                            sc1_ats_m_axis_rc_tlast;
  output [C_ATS_RC_TUSER_WIDTH-1:0] sc1_ats_m_axis_rc_tuser;

  //CC Interface
  input                             sc1_ats_s_axis_cc_tvalid;
  output                            sc1_ats_s_axis_cc_tready;
  input [C_ATS_DATA_WIDTH-1:0]      sc1_ats_s_axis_cc_tdata;
  input [C_ATS_DATA_WIDTH/8-1:0]    sc1_ats_s_axis_cc_tkeep;
  input                             sc1_ats_s_axis_cc_tlast;
  input [C_ATS_CC_TUSER_WIDTH-1:0]  sc1_ats_s_axis_cc_tuser;

  //CQ Interface
  output                            sc1_ats_m_axis_cq_tvalid;
  input                             sc1_ats_m_axis_cq_tready;
  output [C_ATS_DATA_WIDTH-1:0]     sc1_ats_m_axis_cq_tdata;
  output [C_ATS_DATA_WIDTH/8-1:0]   sc1_ats_m_axis_cq_tkeep;
  output                            sc1_ats_m_axis_cq_tlast;
  output [C_ATS_CQ_TUSER_WIDTH-1:0] sc1_ats_m_axis_cq_tuser;

  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_txp;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_txn;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_rxp;
  input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_rxn;

  input    sys_clk;
  output   sys_clk_ce_out;
  input    sys_clk_gt;
  input    sys_rst_n;
  input    dma_bridge_resetn;
  output   user_lnk_up;
  input    free_run_clock;

  //----------------------------------------------------------------------------------------------------------------//
  //  Connectivity for external clocking                                                                            //
  //----------------------------------------------------------------------------------------------------------------//
  output          drp_rdy;
  output   [15:0] drp_do;
  input           drp_clk ;
  input           drp_en ;
  input           drp_we ;
  input    [10:0] drp_addr ;
  input    [15:0] drp_di ;

  output          cfg_ext_read_received;
  output          cfg_ext_write_received;
  output  [9:0]   cfg_ext_register_number;
  output  [7:0]   cfg_ext_function_number;
  output  [31:0]  cfg_ext_write_data;
  output  [3:0]   cfg_ext_write_byte_enable;
  input   [31:0]  cfg_ext_read_data;
  input           cfg_ext_read_data_valid;
  output     interrupt_out;
  output     interrupt_out_msi_vec0to31;
  output     interrupt_out_msi_vec32to63;
  output     interrupt_out_msix_0;
  output     interrupt_out_msix_1;
  output     interrupt_out_msix_2;
  output     interrupt_out_msix_3;

  output                                            ext_ch_gt_drpclk ;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH * 10)-1):0] ext_ch_gt_drpaddr ;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpen ;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpwe ;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdi ;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drprdy ;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdo ;

  // -----------------------------------------------------------------------
  // Transceiver debug ports for 7 series PCIE gen3 core
  // -----------------------------------------------------------------------
  input   [ 2:0]                                pipe_txprbssel;
  input   [ 2:0]                                pipe_rxprbssel;
  input                                         pipe_txprbsforceerr;
  input                                         pipe_rxprbscntreset;
  input   [ 2:0]                                pipe_loopback;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_rxprbserr;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]       pipe_txinhibit;
  output  [4:0]                                 pipe_rst_fsm;
  output  [11:0]                                pipe_qrst_fsm;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*5)-1:0]  pipe_rate_fsm;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*6)-1:0]  pipe_sync_fsm_tx;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*7)-1:0]  pipe_sync_fsm_rx;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*7)-1:0]  pipe_drp_fsm;
  output                                        pipe_rst_idle;
  output                                        pipe_qrst_idle;
  output                                        pipe_rate_idle;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_eyescandataerror;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH*3-1:0]    pipe_rxstatus;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH*15-1:0]   pipe_dmonitorout;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_cpll_lock;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2:0] pipe_qpll_lock;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_rxpmaresetdone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*3)-1:0]  pipe_rxbufstatus;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_txphaligndone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_txphinitdone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_txdlysresetdone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_rxphaligndone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_rxdlysresetdone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_rxsyncdone;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]  pipe_rxdisperr;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH*8)-1:0]  pipe_rxnotintable;
  output  [(PL_LINK_CAP_MAX_LINK_WIDTH)-1:0]    pipe_rxcommadet;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      gt_ch_drp_rdy;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_0;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_1;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_2;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_3;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_4;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_5;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_6;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_7;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_8;
  output  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]      pipe_debug_9;
  output  [31:0]                                pipe_debug;

  // -----------------------------------------------------------------------
  // Transceiver debug ports for Ultrascale PCIE gen3 core
  // -----------------------------------------------------------------------
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcieuserratedone;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_loopback;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txprbsforceerr;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txinhibit;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  gt_txprbssel;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  gt_rxprbssel;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxprbscntreset;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_dmonitorclk;
  input  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_dmonfiforeset;

  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txelecidle;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txresetdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxresetdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxpmaresetdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txphaligndone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txphinitdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txdlysresetdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxphaligndone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxdlysresetdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxsyncdone;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_eyescandataerror;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxprbserr;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*16)-1):0] gt_dmonitorout;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxcommadet;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_phystatus;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxvalid;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxcdrlock;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcierateidle;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcieuserratestart;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_gtpowergood;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_cplllock;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxoutclk;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxrecclkout;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll1lock;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_rxstatus;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_rxbufstatus;
  output [8:0]                                   gt_bufgtdiv;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*2)-1):0]  phy_txeq_ctrl;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  phy_txeq_preset;
  output [3:0]                                   phy_rst_fsm;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  phy_txeq_fsm;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  phy_rxeq_fsm;
  output                                         phy_rst_idle;
  output                                         phy_rrst_n;
  output                                         phy_prst_n;
  output [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll0lock;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_gen34_eios_det;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclk;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclkfabric;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxoutclkfabric;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclkpcs;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxoutclkpcs;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpmareset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxpmareset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpcsreset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxpcsreset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxbufreset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxcdrreset;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxdfelpmreset;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txprogdivresetdone;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpmaresetdone;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txsyncdone;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxprbslocked;

  // mcap and startup signals.
  output       mcap_design_switch;
  input        mcap_eos_in;
  output       cap_req;
  input        cap_gnt;
  input        cap_rel;
  output       startup_cfgclk;
  output       startup_cfgmclk;
  output [3:0] startup_di;
  output       startup_eos;
  output       startup_preq;
  input  [3:0] startup_do;
  input  [3:0] startup_dts;
  input        startup_fcsbo;
  input        startup_fcsbts;
  input        startup_gsr;
  input        startup_gts;
  input        startup_keyclearb;
  input        startup_pack;
  input        startup_usrcclko;
  input        startup_usrcclkts;
  input        startup_usrdoneo;
  input        startup_usrdonets;

  // Shared Logic Internal
  output                                     int_pclk_out_slave;
  output                                     int_pipe_rxusrclk_out;
  output [(PL_LINK_CAP_MAX_LINK_WIDTH-1):0]  int_rxoutclk_out;
  output                                     int_dclk_out;
  output                                     int_userclk1_out;
  output                                     int_userclk2_out;
  output                                     int_oobclk_out;
  output  [1:0]                              int_qplllock_out;
  output  [1:0]                              int_qplloutclk_out;
  output  [1:0]                              int_qplloutrefclk_out;
  input  [(PL_LINK_CAP_MAX_LINK_WIDTH-1):0]  int_pclk_sel_slave;

  // Shared Logic External Clock
  input                                   pipe_pclk_in;
  input                                   pipe_rxusrclk_in;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pipe_rxoutclk_in;
  input                                   pipe_dclk_in;
  input                                   pipe_userclk1_in;
  input                                   pipe_userclk2_in;
  input                                   pipe_oobclk_in;
  input                                   pipe_mmcm_lock_in;
  input                                   pipe_mmcm_rst_n;
  output                                  pipe_txoutclk_out;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pipe_rxoutclk_out;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0] pipe_pclk_sel_out;
  output                                  pipe_gen3_out;

  // Shared Logic External GT COMMON pcie3_7x
  input  [11:0]   qpll_drp_crscode;
  input  [17:0]   qpll_drp_fsm;
  input  [1:0]    qpll_drp_done;
  input  [1:0]    qpll_drp_reset;
  input  [1:0]    qpll_qplllock;
  input  [1:0]    qpll_qplloutclk;
  input  [1:0]    qpll_qplloutrefclk;
  output          qpll_qplld;
  output [1:0]    qpll_qpllreset;
  output          qpll_drp_clk;
  output          qpll_drp_rst_n;
  output          qpll_drp_ovrd;
  output          qpll_drp_gen3;
  output          qpll_drp_start;

  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           int_qpll1lock_out;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           int_qpll1outclk_out;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           int_qpll1outrefclk_out;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1refclk;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1pd;
  output  [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] ext_qpll1rate;
  output  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1reset;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1lock_out;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1outclk_out;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0]           ext_qpll1outrefclk_out;

  output [C_S_AXIS_DATA_WIDTH-1:0]     m_axis_rq_tdata_out;
  output                               m_axis_rq_tlast_out;
  output [C_M_AXIS_RQ_USER_WIDTH-1:0]  m_axis_rq_tuser_out;
  output [C_S_KEEP_WIDTH-1:0]          m_axis_rq_tkeep_out;
  output [3:0]                         m_axis_rq_tready_out;
  output                               m_axis_rq_tvalid_out;

  output [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_rc_tdata_out;
  output [C_M_AXIS_RC_USER_WIDTH-1:0]  s_axis_rc_tuser_out;
  output                               s_axis_rc_tlast_out;
  output [C_M_KEEP_WIDTH-1:0]          s_axis_rc_tkeep_out;
  output                               s_axis_rc_tvalid_out;
  output                               s_axis_rc_tready_out;

  output [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_cq_tdata_out;
  output [C_S_AXIS_CQP_USER_WIDTH-1:0] s_axis_cq_tuser_out;
  output                               s_axis_cq_tlast_out;
  output [C_M_KEEP_WIDTH-1:0]          s_axis_cq_tkeep_out;
  output                               s_axis_cq_tvalid_out;
  output                               s_axis_cq_tready_out;

  output [C_S_AXIS_DATA_WIDTH-1:0]     m_axis_cc_tdata_out;
  output [C_S_AXIS_CC_USER_WIDTH-1:0]  m_axis_cc_tuser_out;
  output                               m_axis_cc_tlast_out;
  output [C_S_KEEP_WIDTH-1:0]          m_axis_cc_tkeep_out;
  output                               m_axis_cc_tvalid_out;
  output [3:0]                         m_axis_cc_tready_out;

  output [3:0]    cfg_negotiated_width_o;
  output [2:0]    cfg_current_speed_o;
  output [5:0]    cfg_ltssm_state_o;
  output          cfg_err_cor_o;
  output          cfg_err_fatal_o;
  output          cfg_err_nonfatal_o;
  output [4:0]    cfg_local_error_o;
  output          cfg_local_error_valid_o;
  output          pipe_tx0_rcvr_det;
  output [1:0]    pipe_tx0_powerdown;
  output          pipe_clk;
  output          sys_clk_bufg;
  output [15:0]   cfg_function_status;
  output [2:0]    cfg_max_read_req;
  output [1:0]    cfg_max_payload;
  input  [3:0]    cfg_flr_done;
  output [3:0]    cfg_flr_in_process;
  output [251:0]  cfg_vf_flr_in_process;
  input  [7:0]    cfg_vf_flr_func_num;
  input           cfg_vf_flr_done;

  output [3:0]    cfg_interrupt_msi_enable;

  output          cfg_interrupt_msi_sent;
  output          cfg_interrupt_msi_fail;
  output          cfg_interrupt_msix_sent;
  output          cfg_interrupt_msix_fail;
  input  [63:0]   cfg_interrupt_msix_address;
  input  [31:0]   cfg_interrupt_msix_data;
  input           cfg_interrupt_msix_int;
  output [3:0]    cfg_interrupt_msix_enable;
  output [3:0]    cfg_interrupt_msix_mask;


  //******************************************************************
  //    New ports for split IP
  //******************************************************************
  input  [5:0]                         cfg_ltssm_state_sd;
  input                                user_lnk_up_sd;
  input                                phy_rdy_out_sd ;
  output                               cfg_config_space_enable_sd;
  output                               cfg_link_training_enable_sd;
  output [C_S_AXIS_DATA_WIDTH-1:0]     s_axis_rq_tdata_sd;
  output                               s_axis_rq_tlast_sd;
  output [C_M_AXIS_RQ_USER_WIDTH-1:0]  s_axis_rq_tuser_sd;
  output [C_S_KEEP_WIDTH-1:0]          s_axis_rq_tkeep_sd;
  output                               s_axis_rq_tvalid_sd;
  input  [3:0]                         s_axis_rq_tready_sd;

  input  [C_M_AXIS_DATA_WIDTH-1:0]     m_axis_rc_tdata_sd;
  input  [C_M_AXIS_RC_USER_WIDTH-1:0]  m_axis_rc_tuser_sd;
  input                                m_axis_rc_tlast_sd;
  input  [C_M_KEEP_WIDTH-1:0]          m_axis_rc_tkeep_sd;
  input                                m_axis_rc_tvalid_sd;
  output                               m_axis_rc_tready_sd;

  input  [C_M_AXIS_DATA_WIDTH-1:0]     m_axis_cq_tdata_sd;
  input  [C_S_AXIS_CQP_USER_WIDTH-1:0] m_axis_cq_tuser_sd;
  input                                m_axis_cq_tlast_sd;
  input  [C_M_KEEP_WIDTH-1:0]          m_axis_cq_tkeep_sd;
  input                                m_axis_cq_tvalid_sd;
  output                               m_axis_cq_tready_sd;

  output [C_S_AXIS_DATA_WIDTH-1:0]     s_axis_cc_tdata_sd;
  output [C_S_AXIS_CC_USER_WIDTH-1:0]  s_axis_cc_tuser_sd;
  output                               s_axis_cc_tlast_sd;
  output [C_S_KEEP_WIDTH-1:0]          s_axis_cc_tkeep_sd;
  output                               s_axis_cc_tvalid_sd;
  input  [3:0]                         s_axis_cc_tready_sd;

  input  [5:0]   rbar_bar_size_sd;
  input  [7:0]   rbar_function_number_sd;
  input          rbar_write_enable_bar0_sd;
  input          rbar_write_enable_bar1_sd;
  input          rbar_write_enable_bar2_sd;
  input          rbar_write_enable_bar3_sd;
  input          rbar_write_enable_bar4_sd;
  input          rbar_write_enable_bar5_sd;
  input          user_clk_sd;
  input          user_reset_sd;
  output [1:0]   pcie_cq_np_req_sd;
  input  [5:0]   pcie_cq_np_req_count_sd;
  input  [3:0]   pcie_tfc_nph_av_sd;
  input  [3:0]   pcie_tfc_npd_av_sd;
  input          pcie_rq_seq_num_vld0_sd;
  input  [5:0]   pcie_rq_seq_num0_sd;
  input          pcie_rq_seq_num_vld1_sd;
  input  [5:0]   pcie_rq_seq_num1_sd;
  input  [7:0]   cfg_fc_nph_sd;
  output [2:0]   cfg_fc_sel_sd;
  input          cfg_phy_link_down_sd;
  input  [1:0]   cfg_phy_link_status_sd;
  input  [2:0]   cfg_negotiated_width_sd;
  input  [1:0]   cfg_current_speed_sd;
  input          cfg_pl_status_change_sd;
  input          cfg_hot_reset_out_sd;
  output [7:0]   cfg_ds_port_number_sd;
  output [7:0]   cfg_ds_bus_number_sd;
  output [4:0]   cfg_ds_device_number_sd;
  output [2:0]   cfg_ds_function_number_sd;
  output [63:0]  cfg_dsn_sd;
  input  [15:0]  cfg_function_status_sd;
  input  [2:0]   cfg_max_read_req_sd;
  input  [1:0]   cfg_max_payload_sd;
  output         cfg_err_cor_in_sd;
  output         cfg_err_uncor_in_sd;
  output [3:0]   cfg_flr_done_sd;
  input  [3:0]   cfg_flr_in_process_sd;
  input  [251:0] cfg_vf_flr_in_process_sd;

  output [7:0]   usr_flr_fnc;           // FLR
  output         usr_flr_set;           // FLR
  output         usr_flr_clr;           // FLR
  input  [7:0]   usr_flr_done_fnc;      // FLR
  input          usr_flr_done_vld;      // FLR

  // Interrupt Interface Signals
  output [3:0]   cfg_interrupt_int_sd;
  input          cfg_interrupt_sent_sd;
  output [3:0]   cfg_interrupt_pending_sd;

  input  [3:0]   cfg_interrupt_msi_enable_sd;
  input          cfg_interrupt_msi_mask_update_sd;
  input  [31:0]  cfg_interrupt_msi_data_sd;
  output [31:0]  cfg_interrupt_msi_int_sd;
  output [31:0]  cfg_interrupt_msi_pending_status_sd;
  output         cfg_interrupt_msi_pending_status_data_enable_sd;
  output [3:0]   cfg_interrupt_msi_pending_status_function_num_sd;
  output [2:0]   cfg_interrupt_msi_attr_sd;
  output         cfg_interrupt_msi_tph_present_sd;
  output [1:0]   cfg_interrupt_msi_tph_type_sd;
  output [8:0]   cfg_interrupt_msi_tph_st_tag_sd;
  output [7:0]   cfg_interrupt_msi_function_number_sd;

  input          cfg_interrupt_msi_sent_sd;
  input          cfg_interrupt_msi_fail_sd;

  output         cfg_interrupt_msix_int_sd;       // Configuration Interrupt MSI-X Data Valid.
  output [31:0]  cfg_interrupt_msix_data_sd;      // Configuration Interrupt MSI-X Data.
  output [63:0]  cfg_interrupt_msix_address_sd;   // Configuration Interrupt MSI-X Address.
  input  [3:0]   cfg_interrupt_msix_enable_sd;    // Configuration Interrupt MSI-X Function Enabled.
  input  [3:0]   cfg_interrupt_msix_mask_sd;      // Configuration Interrupt MSI-X Function Mask.

  input  [251:0] cfg_interrupt_msix_vf_enable_sd; // Configuration Interrupt MSI-X on VF Enabled.
  input  [251:0] cfg_interrupt_msix_vf_mask_sd;   // Configuration Interrupt MSI-X VF Mask.
  output [1:0]   cfg_interrupt_msix_vec_pending_sd;
  input          cfg_interrupt_msix_vec_pending_status_sd;

  // Error Reporting Interface
  input          cfg_err_cor_out_sd;
  input          cfg_err_nonfatal_out_sd;
  input          cfg_err_fatal_out_sd;
  input  [4:0]   cfg_local_error_out_sd;

  input          cfg_msg_received_sd;
  input  [7:0]   cfg_msg_received_data_sd;
  input  [4:0]   cfg_msg_received_type_sd;
  output         cfg_msg_transmit_sd;
  output [2:0]   cfg_msg_transmit_type_sd;
  output [31:0]  cfg_msg_transmit_data_sd;
  input          cfg_msg_transmit_done_sd;

  output  [9:0]  cfg_mgmt_addr_sd;
  output         cfg_mgmt_write_sd;
  output  [31:0] cfg_mgmt_write_data_sd;
  output  [3:0]  cfg_mgmt_byte_enable_sd;
  output         cfg_mgmt_read_sd;
  output  [7:0]  cfg_mgmt_function_number_sd;
  output         cfg_mgmt_type1_cfg_reg_access_sd;
  input  [31:0]  cfg_mgmt_read_data_sd;
  input          cfg_mgmt_read_write_done_sd;

  //-- AXIS RQ Request Inbound Channel for ATS/PRI messages
  input [C_M_AXIS_DATA_WIDTH-1:0]     atspri_s_axis_rq_tdata;
  input [C_M_AXIS_DATA_WIDTH/32-1:0]  atspri_s_axis_rq_tkeep;
  input [C_M_AXIS_RQ_USER_WIDTH-1:0]  atspri_s_axis_rq_tuser;
  input                               atspri_s_axis_rq_tlast;
  input                               atspri_s_axis_rq_tvalid;
  output                              atspri_s_axis_rq_tready;

  //-- AXIS Completer Request Outbound Channel for ATS/PRI messages
  output [C_S_AXIS_DATA_WIDTH-1:0]    atspri_m_axis_cq_tdata;
  output [C_S_AXIS_DATA_WIDTH/32-1:0] atspri_m_axis_cq_tkeep;
  output [C_S_AXIS_CQ_USER_WIDTH-1:0] atspri_m_axis_cq_tuser;
  output                              atspri_m_axis_cq_tlast;
  output                              atspri_m_axis_cq_tvalid;
  input                               atspri_m_axis_cq_tready;

  //--PCIe CFG Status Interface for ATS/PRI messages
  output [4:0]   cfg_status_ats_stu;
  output         cfg_status_ats_en;
  output         cfg_status_pr_en;
  output         cfg_status_pr_rst;
  output         cfg_status_pr_uprgi;
  input          cfg_status_set_uprgi;
  output         cfg_status_pr_rf;
  input          cfg_status_set_rf;
  input          cfg_status_set_s;
  input          cfg_status_clr_s;
  output [31:0]  cfg_status_ost_pr_alloc;

  wire [251:0]                       cfg_interrupt_msix_vf_enable;
  wire [251:0]                       cfg_interrupt_msix_vf_mask;

  (* keep = "true" *) wire          blk_cfg_ext_read_received;
  (* keep = "true" *) wire          blk_cfg_ext_write_received;
  (* keep = "true" *) wire [9:0]    blk_cfg_ext_register_number;
  (* keep = "true" *) wire [7:0]    blk_cfg_ext_function_number;
  (* keep = "true" *) wire [31:0]   blk_cfg_ext_write_data;
  (* keep = "true" *) wire [3:0]    blk_cfg_ext_write_byte_enable;
  (* keep = "true" *) wire [31:0]   blk_cfg_ext_read_data;
  (* keep = "true" *) wire          blk_cfg_ext_read_data_valid;
  (* keep = "true" *) wire [18:0]   cfg_mgmt_addr;
  (* keep = "true" *) wire          cfg_mgmt_write;
  (* keep = "true" *) wire [31:0]   cfg_mgmt_write_data;
  (* keep = "true" *) wire [3:0]    cfg_mgmt_byte_enable;
  (* keep = "true" *) wire          cfg_mgmt_read;
  (* keep = "true" *) wire [31:0]   cfg_mgmt_read_data;
  (* keep = "true" *) wire          cfg_mgmt_read_write_done;
  (* keep = "true" *) wire          cfg_mgmt_type1_cfg_reg_access;

  (* keep = "true" *) wire          axi_aclk;
  (* keep = "true" *) wire          axi_aresetn;
  (* keep = "true" *) wire          axi_ctl_aclk;
  (* keep = "true" *) wire          axi_ctl_aresetn;
  wire                              axi_aresetn_int;
  (* keep = "true" *) wire  [XDMA_NUM_USR_IRQ-1:0]  usr_irq_req;
  (* keep = "true" *) wire  [XDMA_NUM_USR_IRQ-1:0]  usr_irq_ack;
  (* keep = "true" *) wire  [2*XDMA_NUM_USR_IRQ-1:0] usr_irq_function_number;
  (* keep = "true" *) wire                          msi_enable;
  (* keep = "true" *) wire                          msix_enable;
  (* keep = "true" *) wire [2 : 0]                  msi_vector_width;

  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_awid;
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_awaddr_temp;
  (* keep = "true" *) wire [AXI_ADDR_WIDTH-1 : 0]       m_axi_awaddr;
  (* keep = "true" *) wire [7 : 0]                      m_axi_awlen;
  (* keep = "true" *) wire [2 : 0]                      m_axi_awsize;
  (* keep = "true" *) wire [1 : 0]                      m_axi_awburst;
  (* keep = "true" *) wire [2 : 0]                      m_axi_awprot;
  (* keep = "true" *) wire                              m_axi_awvalid;
  (* keep = "true" *) wire                              m_axi_awready;
  (* keep = "true" *) wire                              m_axi_awlock;
  (* keep = "true" *) wire [3 : 0]                      m_axi_awcache;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH-1 : 0]   m_axi_wdata ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axi_wuser;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axi_wstrb ;
  (* keep = "true" *) wire                              m_axi_wlast ;
  (* keep = "true" *) wire                              m_axi_wvalid ;
  (* keep = "true" *) wire                              m_axi_wready ;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_bid ;
  (* keep = "true" *) wire [1 : 0]                      m_axi_bresp ;
  (* keep = "true" *) wire                              m_axi_bvalid ;
  (* keep = "true" *) wire                              m_axi_bready ;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_arid ;
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_araddr_temp;
  (* keep = "true" *) wire [AXI_ADDR_WIDTH-1 : 0]       m_axi_araddr;
  (* keep = "true" *) wire [7 : 0]                      m_axi_arlen ;
  (* keep = "true" *) wire [2 : 0]                      m_axi_arsize ;
  (* keep = "true" *) wire [1 : 0]                      m_axi_arburst ;
  (* keep = "true" *) wire [2 : 0]                      m_axi_arprot ;
  (* keep = "true" *) wire                              m_axi_arvalid ;
  (* keep = "true" *) wire                              m_axi_arready ;
  (* keep = "true" *) wire                              m_axi_arlock;
  (* keep = "true" *) wire [3 : 0]                      m_axi_arcache;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_rid ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH-1 : 0]   m_axi_rdata ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axi_ruser;
  (* keep = "true" *) wire [1 : 0]                      m_axi_rresp ;
  (* keep = "true" *) wire                              m_axi_rlast ;
  (* keep = "true" *) wire                              m_axi_rvalid ;
  (* keep = "true" *) wire                              m_axi_rready ;
  // Axi bypass
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_awid ;
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_awaddr_temp;
  (* keep = "true" *) wire [AXI_ADDR_WIDTH-1 : 0]       m_axib_awaddr;
  (* keep = "true" *) wire [C_M_AXI_AWUSER_WIDTH-1 : 0] m_axib_awuser ;
  (* keep = "true" *) wire [7 : 0]                      m_axib_awlen ;
  (* keep = "true" *) wire [2 : 0]                      m_axib_awsize ;
  (* keep = "true" *) wire [1 : 0]                      m_axib_awburst ;
  (* keep = "true" *) wire [2 : 0]                      m_axib_awprot ;
  (* keep = "true" *) wire                              m_axib_awvalid ;
  (* keep = "true" *) wire                              m_axib_awready ;
  wire                                                  m_axib_awlock ;
  (* keep = "true" *) wire [3 : 0]                      m_axib_awcache ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH-1 : 0]   m_axib_wdata ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axib_wuser;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axib_wstrb ;
  (* keep = "true" *) wire                              m_axib_wlast ;
  (* keep = "true" *) wire                              m_axib_wvalid ;
  (* keep = "true" *) wire                              m_axib_wready ;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_bid ;
  (* keep = "true" *) wire [1 : 0]                      m_axib_bresp ;
  (* keep = "true" *) wire                              m_axib_bvalid ;
  (* keep = "true" *) wire                              m_axib_bready ;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_arid ;
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_araddr_temp;
  (* keep = "true" *) wire [AXI_ADDR_WIDTH-1 : 0]       m_axib_araddr;
  (* keep = "true" *) wire [C_M_AXI_ARUSER_WIDTH-1: 0]  m_axib_aruser ;
  (* keep = "true" *) wire [7 : 0]                      m_axib_arlen ;
  (* keep = "true" *) wire [2 : 0]                      m_axib_arsize ;
  (* keep = "true" *) wire [1 : 0]                      m_axib_arburst ;
  (* keep = "true" *) wire [2 : 0]                      m_axib_arprot ;
  (* keep = "true" *) wire                              m_axib_arvalid ;
  (* keep = "true" *) wire                              m_axib_arready ;
  wire                                                  m_axib_arlock;
  (* keep = "true" *) wire [3 : 0]                      m_axib_arcache;
  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axib_rid ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH-1 : 0]   m_axib_rdata ;
  (* keep = "true" *) wire [C_M_AXI_DATA_WIDTH/8-1 : 0] m_axib_ruser;

  (* keep = "true" *) wire [1 : 0]                      m_axib_rresp ;
  (* keep = "true" *) wire                              m_axib_rlast ;
  (* keep = "true" *) wire                              m_axib_rvalid ;
  (* keep = "true" *) wire                              m_axib_rready ;

  (* keep = "true" *) wire [31 : 0]                     m_axil_awaddr ;
  (* keep = "true" *) wire [C_M_AXIL_AWUSER_WIDTH-1: 0] m_axil_awuser ;
  wire [2 : 0]                                          m_axil_awprot ;
  (* keep = "true" *) wire                              m_axil_awvalid ;
  (* keep = "true" *) wire                              m_axil_awready ;
  (* keep = "true" *) wire [31 : 0]                     m_axil_wdata ;
  (* keep = "true" *) wire [3 : 0]                      m_axil_wstrb ;
  (* keep = "true" *) wire                              m_axil_wvalid ;
  (* keep = "true" *) wire                              m_axil_wready ;
  (* keep = "true" *) wire                              m_axil_bvalid ;
  (* keep = "true" *) wire [1:0]                        m_axil_bresp ;
  (* keep = "true" *) wire                              m_axil_bready ;
  (* keep = "true" *) wire [31 : 0]                     m_axil_araddr ;
  (* keep = "true" *) wire [C_M_AXIL_ARUSER_WIDTH-1: 0] m_axil_aruser ;
  wire [2 : 0]                                          m_axil_arprot;
  (* keep = "true" *) wire                              m_axil_arvalid ;
  (* keep = "true" *) wire                              m_axil_arready ;
  (* keep = "true" *) wire [31 : 0]                     m_axil_rdata ;
  (* keep = "true" *) wire [1 : 0]                      m_axil_rresp ;
  (* keep = "true" *) wire                              m_axil_rvalid ;
  (* keep = "true" *) wire                              m_axil_rready ;
  (* keep = "true" *) wire [31 : 0]                     s_axil_awaddr ;
  wire [2 : 0]                                          s_axil_awprot ;
  (* keep = "true" *) wire                              s_axil_awvalid ;
  (* keep = "true" *) wire                              s_axil_awready ;
  (* keep = "true" *) wire [31 : 0]                     s_axil_wdata ;
  (* keep = "true" *) wire [3 : 0]                      s_axil_wstrb ;
  (* keep = "true" *) wire                              s_axil_wvalid ;
  (* keep = "true" *) wire              s_axil_wready ;
  (* keep = "true" *) wire              s_axil_bvalid ;
  (* keep = "true" *) wire [1:0]            s_axil_bresp ;
  (* keep = "true" *) wire              s_axil_bready ;
  (* keep = "true" *) wire [31 : 0]         s_axil_araddr ;
   wire [2 : 0]                                 s_axil_arprot;
  (* keep = "true" *) wire              s_axil_arvalid ;
  (* keep = "true" *) wire              s_axil_arready ;
  (* keep = "true" *) wire [31 : 0]                     s_axil_rdata ;
  (* keep = "true" *) wire [1 : 0]          s_axil_rresp ;
  (* keep = "true" *) wire              s_axil_rvalid ;
  (* keep = "true" *) wire              s_axil_rready ;

  wire [C_S_AXI_ID_WIDTH-1 : 0]   s_axib_awid ;
  wire [AXI_ADDR_WIDTH-1 : 0]     s_axib_awaddr ;
  wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axib_awaddr_temp ;
  wire [3 : 0]                    s_axib_awregion ;
  wire [7 : 0]                    s_axib_awlen ;
  wire [2 : 0]                    s_axib_awsize ;
  wire [1 : 0]                    s_axib_awburst ;
  wire                            s_axib_awvalid ;
  wire                            s_axib_awready ;
  wire [AXI_DATA_WIDTH-1 : 0]     s_axib_wdata ;
  wire [(AXI_DATA_WIDTH/8)-1 : 0] s_axib_wuser ;
  wire [AXI_DATA_WIDTH/8-1 : 0]   s_axib_wstrb ;
  wire                            s_axib_wlast ;
  wire                            s_axib_wvalid ;
  wire                            s_axib_wready ;
  wire [C_S_AXI_ID_WIDTH-1 : 0]   s_axib_bid ;
  wire [1 : 0]                    s_axib_bresp;
  wire                            s_axib_bvalid;
  wire                            s_axib_bready;
  wire [C_S_AXI_ID_WIDTH-1 : 0]   s_axib_arid;
  wire [AXI_ADDR_WIDTH-1 : 0]     s_axib_araddr;
  wire [C_S_AXI_ADDR_WIDTH-1 : 0] s_axib_araddr_temp;
  wire [3 : 0]                    s_axib_arregion;
  wire [7 : 0]                    s_axib_arlen;
  wire [2 : 0]                    s_axib_arsize;
  wire [1 : 0]                    s_axib_arburst;
  wire                            s_axib_arvalid;
  wire                            s_axib_arready;
  wire [C_S_AXI_ID_WIDTH-1 : 0]   s_axib_rid;
  wire [AXI_DATA_WIDTH-1 : 0]     s_axib_rdata;
  wire [(AXI_DATA_WIDTH/8)-1 : 0] s_axib_ruser;
  wire [1 : 0]                    s_axib_rresp;
  wire                            s_axib_rlast;
  wire                            s_axib_rvalid;
  wire                            s_axib_rready;

  wire [14:0]   s_axil_awaddr_bram;
  wire [2:0]    s_axil_awprot_bram;
  wire          s_axil_awvalid_bram;
  wire          s_axil_awready_bram;
  wire [31:0]   s_axil_wdata_bram;
  wire [3:0]    s_axil_wstrb_bram;
  wire          s_axil_wvalid_bram;
  wire          s_axil_wready_bram;
  wire [1:0]    s_axil_bresp_bram;
  wire          s_axil_bvalid_bram;
  wire          s_axil_bready_bram;
  wire [31:0]   s_axil_araddr_bram;
  wire [2:0]    s_axil_arprot_bram;
  wire          s_axil_arvalid_bram;
  wire          s_axil_arready_bram;
  wire [31:0]   s_axil_rdata_bram;
  wire [1:0]    s_axil_rresp_bram;
  wire          s_axil_rvalid_bram;
  wire          s_axil_rready_bram;

  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_txp ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_txn ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_rxp ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0]   pci_exp_rxn ;

  (* keep = "true" *) wire      sys_clk ;
  (* keep = "true" *) wire      sys_clk_ce_out;
  (* keep = "true" *) wire      sys_clk_gt ;
  (* keep = "true" *) wire      sys_rst_n  ;
  (* keep = "true" *) wire      user_lnk_up ;

  wire                          free_run_clock;
  (* keep = "true" *) wire          drp_clk ;
  (* keep = "true" *) wire          drp_en ;
  (* keep = "true" *) wire          drp_we ;
  (* keep = "true" *) wire   [10:0] drp_addr ;
  (* keep = "true" *) wire   [15:0] drp_di ;

  (* keep = "true" *) wire                                           ext_ch_gt_drpclk ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  10)-1):0] ext_ch_gt_drpaddr ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpen ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drpwe ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdi ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  1)-1):0] ext_ch_gt_drprdy ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH * 16)-1):0] ext_ch_gt_drpdo ;

  wire           cfg_ext_read_received;
  wire           cfg_ext_write_received;
  wire [9:0]     cfg_ext_register_number;
  wire [7:0]     cfg_ext_function_number;
  wire [31:0]    cfg_ext_write_data;
  wire [3:0]     cfg_ext_write_byte_enable;
  wire [31:0]    cfg_ext_read_data;
  wire           cfg_ext_read_data_valid;
  wire [18:0]   cfg_mgmt_addr_int;
  wire      cfg_mgmt_write_int;
  wire [31:0]   cfg_mgmt_write_data_int;
  wire [3:0]        cfg_mgmt_byte_enable_int;
  wire      cfg_mgmt_read_int;
  wire [31:0]   cfg_mgmt_read_data_int;
  wire      cfg_mgmt_read_write_done_int;
  wire      cfg_mgmt_type1_cfg_reg_access_int;
  wire [7:0]     cfg_mgmt_function_number;
  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1refclk;
  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1pd;
  wire [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] ext_qpll1rate;
  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1reset;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1lock_out;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outclk_out;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outrefclk_out;

  localparam AXI4MM_ULTRA = (C_FAMILY=="kintexu" || C_FAMILY=="virtexu" || C_FAMILY=="virtexuplus" || C_FAMILY=="kintexuplus" || C_FAMILY=="zyncuplus" || C_FAMILY=="zyncuplusrfsoc") ? 1 : 0;
  localparam DAT_WIDTH = C_M_AXIS_DATA_WIDTH;
  localparam DIFF_AXI_ADDR_WIDTH = 64 - AXI_ADDR_WIDTH;
  //localparam C_H2C_NUM_CHNL = XDMA_RNUM_CHNL;
  //localparam C_C2H_NUM_CHNL = XDMA_WNUM_CHNL;
  localparam C_H2C_NUM_RIDS = XDMA_RNUM_RIDS;
  localparam C_C2H_NUM_RIDS = XDMA_WNUM_RIDS;

  localparam C_NUM_USR_IRQ = XDMA_NUM_USR_IRQ;

  localparam C_GEN2_DEVICES = (ULTRASCALE == "FALSE") && (V7_GEN3 == "FALSE");   // Indicates Gen2 PCIe Hard Block
  localparam C_LEGACY_INT_EN = (PF0_INTERRUPT_PIN == 3'b000) ? "FALSE" : "TRUE"; // Indicates Legacy Interrupt Enabled/Disabled

  localparam RUN_BIT_FIX = 0;    // uses ctl_run_re to clear the rresp_cnt

  localparam USR_INT_EXPN = 0;    // used to increase num of vectors to 24

  localparam C_ERRC_DEC_EN = 0;    // Generates OKAY response on S_AXI_RRESP when select AXIS_RC Error Code is set 
  
  attr_dma_t                    attr_dma;
  attr_dma_pf_t        [3:0]        attr_dma_pf;
  attr_dma_pciebar2axibar_pf_t    [3:0][6:0]    attr_dma_pciebar2axibar_pf;
  attr_dma_axibar2pciebar_t    [5:0]        attr_dma_axibar2pciebar;
  
    dma_pcie_axis_rq_if  #(.DATA_WIDTH(C_M_AXIS_DATA_WIDTH), .USER_WIDTH(C_M_AXIS_RQ_USER_WIDTH))    axis_rq();
    dma_pcie_axis_cc_if  #(.DATA_WIDTH(C_S_AXIS_DATA_WIDTH), .USER_WIDTH(C_S_AXIS_CC_USER_WIDTH))    axis_cc();
    dma_pcie_axis_rc_if  #(.DATA_WIDTH(C_M_AXIS_DATA_WIDTH), .USER_WIDTH(C_M_AXIS_RC_USER_WIDTH))    axis_rc();
    dma_pcie_axis_cq_if  #(.DATA_WIDTH(C_S_AXIS_DATA_WIDTH), .USER_WIDTH(C_S_AXIS_CQ_USER_WIDTH))    axis_cq();

    dma_pcie_misc_output_if     pcie_dma_out();
    dma_pcie_misc_input_if      pcie_dma_in();
    dma_pcie_gic_if             pcie_dma_gic();

    dma_pcie_fabric_output_if   fabric_out();
    dma_pcie_fabric_input_if    fabric_in();

    dma_pcie_mi_4Bx2048_4Bwe_ram_if      mi_hw_ctxt();
    dma_pcie_mi_16Bx2048_4Bwe_ram_if     mi_sw_ctxt();
    dma_pcie_mi_2Bx2048_ram_if           mi_dsc_crd_rcv();
    dma_pcie_mi_8Bx2048_4Bwe_ram_if      mi_wb_base_ctxt();

    dma_pcie_mi_dsc_cpli_if              mi_h2c_pcie_dsc_cpli();
    dma_pcie_mi_dsc_cpld_if              mi_h2c_pcie_dsc_cpld();

    dma_pcie_mi_dsc_cpli_if              mi_h2c_axi_dsc_cpli();
    dma_pcie_mi_dsc_cpld_if              mi_h2c_axi_dsc_cpld();

    dma_pcie_mi_dsc_cpli_if              mi_c2h_pcie_dsc_cpli();
    dma_pcie_mi_dsc_cpld_if              mi_c2h_pcie_dsc_cpld();

    dma_pcie_mi_dsc_cpli_if              mi_c2h_axi_dsc_cpli();
    dma_pcie_mi_dsc_cpld_if              mi_c2h_axi_dsc_cpld();

    dma_pcie_dsc_in_if          dsc_in();
    dma_pcie_dsc_out_if         dsc_out();

          
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_h2c0_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_h2c1_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_h2c2_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_h2c3_dat();

    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_c2h0_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_c2h1_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_c2h2_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_c2h3_dat();

    dma_pcie_mi_64Bx512_32Bwe_ram_if     mi_h2c_rd_brg_dat();
    //dma_pcie_mi_64Bx512_32Bwe_ram_if     mi_h2c_wr_brg_dat();
    dma_pcie_mi_64Bx2048_32Bwe_ram_if     mi_h2c_wr_brg_dat();

    dma_pcie_mi_64Bx1024_32Bwe_ram_if    mi_c2h_rd_brg_dat();
    //dma_pcie_mi_64Bx512_32Bwe_ram_if     mi_c2h_rd_brg_dat();
    dma_pcie_mi_64Bx256_32Bwe_ram_if     mi_c2h_wr_brg_dat();

  localparam MULT_PF_DESIGN = 0;
  localparam PROG_USR_IRQ_VEC_MAP = 0;



  wire [2:0] axist_sz;
  wire [2:0] aximm_sz;

  

  // Configuration outputs ?? hope all of them are outputs....

  wire           cfg_phy_link_down;
  wire    [1:0]  cfg_phy_link_status;
  wire    [2:0]  cfg_max_read_req;

  wire    [1:0]  cfg_link_power_state;

  // Error Reporting Interface
  wire           cfg_err_cor_out;
  wire           cfg_err_nonfatal_out;
  wire           cfg_err_fatal_out;
  wire   [4:0]   cfg_local_error;
  wire           cfg_local_error_valid;
  wire           cfg_req_pm_transition_l23_ready = 0;

  wire           cfg_ltr_enable;
  wire   [5:0]   cfg_ltssm_state;
  wire   [3:0]   cfg_interrupt_pending;
  wire           cfg_dbe;
  wire    [2:0]  cfg_negotiated_width;
  wire    [1:0]  cfg_current_speed;
  wire    [1:0]  cfg_max_payload;
  assign  cfg_negotiated_width_o = {1'b0,cfg_negotiated_width};
  assign  cfg_current_speed_o = {1'b0,cfg_current_speed};
  assign cfg_ltssm_state_o = cfg_ltssm_state;
  assign cfg_err_cor_o           = cfg_err_cor_out;
  assign cfg_err_fatal_o         = cfg_err_fatal_out;
  assign cfg_err_nonfatal_o      = cfg_err_nonfatal_out;
  assign cfg_local_error_o       = cfg_local_error;
  assign cfg_local_error_valid_o = cfg_local_error_valid;

  wire   [3:0]   cfg_rcb_status;
  wire   [3:0]   cfg_dpa_substate_change;
  wire   [11:0]  cfg_function_power_state;
  wire   [3:0]   cfg_per_function_number;
  wire   [3:0]   cfg_interrupt_msi_enable_int;
  wire   [11:0]  cfg_interrupt_msi_mmenable;
  wire   [15:0]  cfg_function_status;
  assign cfg_interrupt_msi_enable = cfg_interrupt_msi_enable_int;
  wire    [1:0]  cfg_obff_enable;
  wire           cfg_pl_status_change;

  wire           cfg_msg_received;
  wire    [7:0]  cfg_msg_received_data;
  wire    [4:0]  cfg_msg_received_type;


  wire           cfg_msg_transmit;
  wire     [2:0] cfg_msg_transmit_type;
  wire    [31:0] cfg_msg_transmit_data;
  wire           cfg_msg_transmit_done;

  wire    [7:0]  cfg_fc_ph;
  wire   [11:0]  cfg_fc_pd;
  wire    [7:0]  cfg_fc_nph;
  wire   [11:0]  cfg_fc_npd;
  wire    [7:0]  cfg_fc_cplh;
  wire   [11:0]  cfg_fc_cpld;
  wire    [2:0]  cfg_fc_sel;

  wire   [15:0]  cfg_per_func_status_data;
  wire           cfg_per_function_update_done;

  wire    [63:0] cfg_dsn;
  wire           cfg_err_cor_in;
  wire           cfg_err_uncor_in;
  wire           cfg_power_state_change_ack;
  wire           cfg_power_state_change_interrupt;

  //----------------------------------------------------------------------------------------------------------------//
  // EP Only                                                                                                        //
  //----------------------------------------------------------------------------------------------------------------//

  // Interrupt Interface Signals
  wire [3:0]    cfg_interrupt_int;
  wire          cfg_interrupt_sent;

  wire          cfg_interrupt_msi_mask_update;
  wire [31:0]   cfg_interrupt_msi_data;
  wire [31:0]   cfg_interrupt_msi_int;
  wire          cfg_interrupt_msi_sent;
  wire          cfg_interrupt_msi_fail;
  wire          cfg_hot_reset_out;
  wire [7:0]    cfg_ds_port_number;
  wire [7:0]    cfg_ds_bus_number;
  wire [4:0]    cfg_ds_device_number;
  wire [2:0]    cfg_ds_function_number;

  wire          cfg_interrupt_msix_sent_int;      // Configuration Interrupt MSI-X Interrupt Sent.
  wire          cfg_interrupt_msix_fail_int;      // Configuration Interrupt MSI-X Interrupt Operation Failed.
  wire          cfg_interrupt_msix_int_int;       // Configuration Interrupt MSI-X Data Valid.
  wire  [31:0]  cfg_interrupt_msix_data_int;      // Configuration Interrupt MSI-X Data.
  wire  [63:0]  cfg_interrupt_msix_address_int;   // Configuration Interrupt MSI-X Address.
  wire  [3:0]   cfg_interrupt_msix_enable_int;    // Configuration Interrupt MSI-X Function Enabled.
  wire  [3:0]   cfg_interrupt_msix_mask_int;      // Configuration Interrupt MSI-X Function Mask.
  wire  [251:0] cfg_interrupt_msix_vf_enable_int; // Configuration Interrupt MSI-X on VF Enabled.
  wire  [251:0] cfg_interrupt_msix_vf_mask_int;   // Configuration Interrupt MSI-X VF Mask.
  wire [3:0]                axis_rq_tready;
  wire [3:0]                s_axis_cc_tready;
  wire [3:0]                s_axis_rq_tready_ats;
  wire [3:0]                s_axis_cc_tready_ats;

  wire                      m_axis_rc_tready_rst;

  wire            user_clk;
  wire            user_reset;
  wire [1:0]              pcie_cq_np_req;
  wire [5:0]          pcie_cq_np_req_count;
  wire [3:0]          pcie_tfc_nph_av;
  wire [3:0]          pcie_tfc_npd_av;
  wire                pcie_rq_seq_num_vld0;
  wire [5:0]              pcie_rq_seq_num0;
  wire                pcie_rq_seq_num_vld1;
  wire [5:0]              pcie_rq_seq_num1;

  wire  [C_S_AXIS_DATA_WIDTH-1:0]    m_axis_rq_tdata_out;
  wire                           m_axis_rq_tlast_out;
  wire [C_M_AXIS_RQ_USER_WIDTH-1:0]  m_axis_rq_tuser_out;
  wire [C_S_KEEP_WIDTH-1:0]          m_axis_rq_tkeep_out;
  wire [3:0]                 m_axis_rq_tready_out;
  wire                       m_axis_rq_tvalid_out;

  wire [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_rc_tdata_out;
  wire [C_M_AXIS_RC_USER_WIDTH-1:0]  s_axis_rc_tuser_out;
  wire                       s_axis_rc_tlast_out;
  wire [C_M_KEEP_WIDTH-1:0]          s_axis_rc_tkeep_out;
  wire                       s_axis_rc_tvalid_out;
  wire                       s_axis_rc_tready_out;

  wire [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_cq_tdata_out;
  wire [C_S_AXIS_CQP_USER_WIDTH-1:0] s_axis_cq_tuser_out;
  wire                       s_axis_cq_tlast_out;
  wire [C_M_KEEP_WIDTH-1:0]          s_axis_cq_tkeep_out;
  wire                       s_axis_cq_tvalid_out;
  wire                   s_axis_cq_tready_out;

  wire [C_S_AXIS_DATA_WIDTH-1:0]     m_axis_cc_tdata_out;
  wire [C_S_AXIS_CC_USER_WIDTH-1:0]  m_axis_cc_tuser_out;
  wire                       m_axis_cc_tlast_out;
  wire [C_S_KEEP_WIDTH-1:0]          m_axis_cc_tkeep_out;
  wire                       m_axis_cc_tvalid_out;
  wire [3:0]                 m_axis_cc_tready_out;

  wire                               pipe_tx0_rcvr_det;
  wire [1:0]                         pipe_tx0_powerdown;
  wire                               pipe_clk;
  wire                               sys_clk_bufg;
  wire cfg_link_training_enable;
  wire  [2:0]  cfg_per_func_status_control;
  wire cfg_per_function_output_request;
  wire cfg_per_function_logic_request;
  wire  [31:0] cfg_interrupt_msi_pending_status;
  wire cfg_interrupt_msi_pending_status_data_enable;
  wire [3:0] cfg_interrupt_msi_pending_status_function_num;
  wire [2:0] cfg_interrupt_msi_attr;
  wire cfg_interrupt_msi_tph_present;
  wire [1:0] cfg_interrupt_msi_tph_type;
  wire [8:0] cfg_interrupt_msi_tph_st_tag;
  wire [3:0] cfg_interrupt_msi_function_number;
  wire [5:0] pf1_lite_ext;
  wire dma_reset;
  wire dma_soft_reset;
  wire phy_ready;
  wire [3:0]                         cfg_flr_done_int;
  wire [3:0]                         cfg_flr_in_process_int;
  wire [251:0]                       cfg_vf_flr_in_process_int;
  wire [7:0]                         cfg_vf_flr_func_num_int;
  wire                               cfg_vf_flr_done_int;

  // CCIX Interface signals connected from pcie4c block to cxs_remap block
  wire [AXIS_CCIX_TX_TDATA_WIDTH-1:0]   s_axis_ccix_tx_tdata;
  wire                                  s_axis_ccix_tx_tvalid;
  wire [AXIS_CCIX_TX_TUSER_WIDTH-1:0]   s_axis_ccix_tx_tuser;
  wire                                  ccix_tx_credit;
  wire [AXIS_CCIX_RX_TDATA_WIDTH-1:0]   m_axis_ccix_rx_tdata;
  wire                                  m_axis_ccix_rx_tvalid;
  wire [AXIS_CCIX_RX_TUSER_WIDTH-1:0]   m_axis_ccix_rx_tuser;
  wire                                  ccix_rx_credit;
  wire [7:0]                            ccix_rx_credit_av;

  // AXI Lite interface signals connected from pcie4c block to ATS Switch block
  wire                                s_axis_rq_tvalid;
  wire [C_ATS_DATA_WIDTH-1:0]         s_axis_rq_tdata;
  wire [C_ATS_DATA_WIDTH/32-1:0]      s_axis_rq_tkeep;
  wire                                s_axis_rq_tlast;
  wire [C_ATS_RQ_TUSER_WIDTH-1:0]     s_axis_rq_tuser;

  wire                                m_axis_rc_tvalid;
  wire                                m_axis_rc_tready;
  wire [C_ATS_DATA_WIDTH-1:0]         m_axis_rc_tdata;
  wire [C_ATS_DATA_WIDTH/32-1:0]      m_axis_rc_tkeep;
  wire                                m_axis_rc_tlast;
  wire [C_ATS_RC_TUSER_WIDTH-1:0]     m_axis_rc_tuser;

  wire                                s_axis_cc_tvalid;
  wire [C_ATS_DATA_WIDTH-1:0]         s_axis_cc_tdata;
  wire [C_ATS_DATA_WIDTH/32-1:0]      s_axis_cc_tkeep;
  wire                                s_axis_cc_tlast;
  wire [C_ATS_CC_TUSER_WIDTH-1:0]     s_axis_cc_tuser;

  wire                                m_axis_cq_tvalid;
  wire                                m_axis_cq_tready;
  wire [C_ATS_DATA_WIDTH-1:0]         m_axis_cq_tdata;
  wire [C_ATS_DATA_WIDTH/32-1:0]      m_axis_cq_tkeep;
  wire                                m_axis_cq_tlast;
  wire [C_ATS_CQ_TUSER_WIDTH-1:0]     m_axis_cq_tuser;



//assign m_axi_wuser = {C_M_AXI_DATA_WIDTH/8{1'b0}};

reg [C_M_AXI_DATA_WIDTH/8-1:0]  m_axi_rdataeccparity;
reg [C_M_AXI_DATA_WIDTH/8-1:0]  m_axi_wdataeccparity;
reg [C_M_AXI_DATA_WIDTH/8-1:0]  m_axib_rdataeccparity;
reg [C_M_AXI_DATA_WIDTH/8-1:0]  m_axib_wdataeccparity;

assign m_axi_rdataeccparity = {C_M_AXI_DATA_WIDTH/8{1'b0}};
assign m_axib_rdataeccparity = {C_M_AXI_DATA_WIDTH/8{1'b0}};

// When PF1 is enabled all 6 bars from PF1 are assigend to AXI-Lite interface
// Default number of PF's is 1. 
   assign pf1_lite_ext = PF1_ENABLED ? 6'h3F : 6'h0;
   localparam NUM_PFS = PF3_ENABLED ? 4 : PF2_ENABLED ? 3 : PF1_ENABLED ? 2 : 1;
   localparam SRIOV_EN = (PF3_ENABLED | PF2_ENABLED | PF1_ENABLED ) ? 1 : 0;
  //----------------------------------------------------------------------------------------------------------------//
  // BAR Assignments                                                                                                //
  //----------------------------------------------------------------------------------------------------------------//

  // 64 = Max BAR width or BAR disabled
  // BAR hit only on even number BARs for 64-bit BAR type
  // CONTROL = 'h0 (disabled); CONTROL = 'h4 (32-bit); CONTROL = 'h5 (64-bit)
  // SIZE starts at 'h5 (4KB) and +1 for each BAR size selection larger than it
  // For RP AXI Bridge mode with no BAR enabled, C_PCIEBAR_LEN_0 must be 'd64 to disable Address Translation mechanism
  localparam C_PCIEBAR_LEN_0 = (DMA_EN == 1) ? (AXILITE_MASTER_CONTROL != 'h0) ? (AXILITE_MASTER_APERTURE_SIZE + 'h7) : (XDMA_APERTURE_SIZE + 'h7) : ((PF0_BAR0_CONTROL != 'h0) ? (PF0_BAR0_APERTURE_SIZE + 12 - 5) : 64);

  localparam C_PCIEBAR_LEN_1 = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4)) ? (XDMA_APERTURE_SIZE + 'h7) :
                               (((AXILITE_MASTER_CONTROL == 'h0) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
			          (PF0_BAR1_CONTROL == 'h4) ? (PF0_BAR1_APERTURE_SIZE + 12 - 5) : 
                                   64) : (PF0_BAR1_APERTURE_SIZE + 12 - 5);

  localparam C_PCIEBAR_LEN_2 = (DMA_EN == 1) ? (AXILITE_MASTER_CONTROL == 'h5) ? (XDMA_APERTURE_SIZE + 'h7) :
                                 ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h5)) ? (XDMA_APERTURE_SIZE + 'h7) :
                                   ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                     ( ((XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                       ( ((XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h5)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                         64 
                                       )
                                     )
                                   )
                                 ) : (PF0_BAR2_APERTURE_SIZE + 12 - 5);

  localparam C_PCIEBAR_LEN_3 = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL == 'h5) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ?  (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                               64 : (PF0_BAR3_APERTURE_SIZE + 12 - 5);

  localparam C_PCIEBAR_LEN_4 = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL != 'h0) && (XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                               64 : (PF0_BAR4_APERTURE_SIZE + 12 - 5);

  localparam C_PCIEBAR_LEN_5 = (DMA_EN == 1) ? 64 : (PF0_BAR5_APERTURE_SIZE + 12 - 5); // BAR hit on this bar is not used
  localparam C_PCIEBAR_LEN_6 = PF0_EXPANSION_ROM_ENABLE ? (PF0_EXPANSION_ROM_APERTURE_SIZE + 12 - 5) : 64; // BAR hit on EROM

  localparam BARLITE0        = (DMA_EN == 0) ? 7 : (XDMA_AXILITE_MASTER == "TRUE" ) ? 0 : 7;                            // BAR number for AXILite; Always at 0 when enabled
  localparam C_INCLUDE_RC    = (PL_UPSTREAM_FACING == "true") ? 0 : 1;

  //
  // BAR translation assignment based on BAR selection.
  //

  localparam [63:0]C_PCIEBAR2AXIBAR_0_TMP = (DMA_EN == 1) ? (AXILITE_MASTER_CONTROL != 'h0) ? {64'h0 | C_PCIEBAR2AXIBAR_0} : {64'h0 | C_PCIEBAR2AXIBAR_1} : {64'h0 | C_PCIEBAR2AXIBAR_0} ;
  localparam [63:0]C_PCIEBAR2AXIBAR_1_TMP = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4)) ?  {64'h0 | C_PCIEBAR2AXIBAR_1} :
                               (((AXILITE_MASTER_CONTROL == 'h0) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ?  {64'h0 | C_PCIEBAR2AXIBAR_2} :
                                   64'h00) : {64'h0 | C_PCIEBAR2AXIBAR_1};
  localparam [63:0]C_PCIEBAR2AXIBAR_2_TMP = (DMA_EN == 1) ? (AXILITE_MASTER_CONTROL == 'h5) ?  {64'h0 | C_PCIEBAR2AXIBAR_1} :
                                 ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h5)) ? {64'h0 | C_PCIEBAR2AXIBAR_1} :
                                   ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL != 'h0)) ? {64'h0 | C_PCIEBAR2AXIBAR_2} :
                                     ( ((XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ?  {64'h0 | C_PCIEBAR2AXIBAR_2} :
                                       ( ((XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h5)) ? {64'h0 | C_PCIEBAR2AXIBAR_2} :
                                         64'h00 
                                       )
                                     )
                                   )
                                 ) : {64'h0 | C_PCIEBAR2AXIBAR_2};

  localparam [63:0]C_PCIEBAR2AXIBAR_3_TMP = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL == 'h5) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ?   {64'h0 | C_PCIEBAR2AXIBAR_2} :
                               64'h00 : {64'h0 | C_PCIEBAR2AXIBAR_3};

  localparam [63:0]C_PCIEBAR2AXIBAR_4_TMP = (DMA_EN == 1) ? ((AXILITE_MASTER_CONTROL != 'h0) && (XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ?  {64'h0 | C_PCIEBAR2AXIBAR_2} :
                               64'h00 : {64'h0 | C_PCIEBAR2AXIBAR_4};

  localparam [63:0]C_PCIEBAR2AXIBAR_5_TMP = {64'h0 | C_PCIEBAR2AXIBAR_5};
  localparam [63:0]C_PCIEBAR2AXIBAR_6_TMP = {64'h0 | C_PCIEBAR2AXIBAR_6};

  //----------------------------------------------------------------------------------------------------------------//
  wire                          axi_ctl_aclk_sig;
  wire                          mmcm_lock;
  reg                           sys_rst_lock_reg;

  assign m_axi_awaddr = m_axi_awaddr_temp[AXI_ADDR_WIDTH-1:0];
  assign m_axi_araddr = m_axi_araddr_temp[AXI_ADDR_WIDTH-1:0];
  assign m_axib_awaddr = m_axib_awaddr_temp[AXI_ADDR_WIDTH-1:0];
  assign m_axib_araddr = m_axib_araddr_temp[AXI_ADDR_WIDTH-1:0];
generate
  if (DIFF_AXI_ADDR_WIDTH == 0) begin
    assign s_axib_awaddr_temp = s_axib_awaddr;
    assign s_axib_araddr_temp = s_axib_araddr;
  end else begin
    assign s_axib_awaddr_temp = {{DIFF_AXI_ADDR_WIDTH{1'b0}},s_axib_awaddr};
    assign s_axib_araddr_temp = {{DIFF_AXI_ADDR_WIDTH{1'b0}},s_axib_araddr};
  end
endgenerate
generate
  if (AXI_ACLK_LOOPBACK == "TRUE") begin
    assign axi_ctl_aclk_sig = axi_ctl_aclk;
  end else begin
    assign axi_ctl_aclk_sig = user_clk;
  end
endgenerate
generate
  if (DMA_RESET_SOURCE_SEL == 1) begin
    assign dma_reset = ~phy_ready;
  end else if (DMA_RESET_SOURCE_SEL == 2) begin
    assign dma_reset = sys_rst_lock_reg; // CAUTION - Never use this option with US+ CPLL_CAL block, clock instability will occur
  end else begin
    assign dma_reset = user_reset ;
  end
endgenerate
  assign dma_soft_reset = dma_reset | ~dma_bridge_resetn;
  // Synchronize AXI CTL Interface Reset
  assign axi_ctl_aresetn = ~dma_soft_reset;
  (* ASYNC_REG = "TRUE" *)  reg sys_rst_n_reg;
  (* ASYNC_REG = "TRUE" *)  reg sys_rst_n_reg2;
  always @ (posedge axi_ctl_aclk_sig or negedge sys_rst_n) begin
      if (!sys_rst_n) begin
          sys_rst_n_reg  <= #TCQ 1'b0;
          sys_rst_n_reg2 <= #TCQ 1'b0;
      end else begin
          sys_rst_n_reg  <= #TCQ 1'b1;
          sys_rst_n_reg2 <= #TCQ sys_rst_n_reg;  
      end
  end
  always @ (posedge axi_ctl_aclk_sig) begin
      if (sys_rst_n_reg2)
          sys_rst_lock_reg <= #TCQ 1'b0; 
      else
          sys_rst_lock_reg <= #TCQ 1'b1;
  end

  assign m_axis_rc_tready_rst = axis_rc.tready[0] | ~dma_bridge_resetn; // Assert rc_tready when soft reset is asserted to allow pending RX completions to be flused out from HB


  wire [5:0] rbar_bar_size;
  wire [7:0] rbar_function_number;
  wire rbar_write_enable_bar0;
  wire rbar_write_enable_bar1;
  wire rbar_write_enable_bar2;
  wire rbar_write_enable_bar3;
  wire rbar_write_enable_bar4;
  wire rbar_write_enable_bar5;

  wire [3:0] attr_dma_ch_stream;
  assign interrupt_out = pcie_dma_gic.interrupt[0];
  assign interrupt_out_msi_vec0to31 = pcie_dma_gic.interrupt[1];
  assign interrupt_out_msi_vec32to63 = pcie_dma_gic.interrupt[2];
  assign interrupt_out_msix_0 = pcie_dma_gic.interrupt[3];
  assign interrupt_out_msix_1 = pcie_dma_gic.interrupt[4];
  assign interrupt_out_msix_2 = pcie_dma_gic.interrupt[5];
  assign interrupt_out_msix_3 = pcie_dma_gic.interrupt[6];

  assign dsc_in.dsc           = dsc_out.dsc;
  assign attr_dma.msi_rx_decode_en = (C_MSI_ENABLED == "TRUE") ? 1'b1 : 'h0;
  assign attr_dma.axi_slv_brdg_base_addr = 'h0;
  assign attr_dma.axi_slv_multq_base_addr = 'h0;
  assign attr_dma.axi_slv_xdma_base_addr = 'h0;
  assign attr_dma.enable = 'h0;
  assign attr_dma.data_width    =    
                    ((C_S_AXIS_DATA_WIDTH == 256) ? 3'h2 :
                    ((C_S_AXIS_DATA_WIDTH == 128) ?  3'h1 :
                    ((C_S_AXIS_DATA_WIDTH == 64) ?  3'h0 : 3'h3)));
  assign attr_dma.mask50       = 
                    (C_S_AXIS_DATA_WIDTH == 64)  ? 6'b000111 : 
                    (C_S_AXIS_DATA_WIDTH == 128) ? 6'b001111 : 
                    (C_S_AXIS_DATA_WIDTH == 256) ? 6'b011111 : 6'b111111;
  
  assign attr_dma_ch_stream = DMA_ST ? 4'hF : 4'h0;
  assign attr_dma.ch_stream    = {4'h0, attr_dma_ch_stream};
  assign attr_dma.metering_enable = C_METERING_ON ? 1'b1 : 'h0;
  assign attr_dma.root_port = C_INCLUDE_RC ? 1'b1 : 'h0;
  assign attr_dma.barlite0 = BARLITE0;
  assign attr_dma.barlite1 = BARLITE1;
  
  assign attr_dma.pcie_if_parity_check = 'h0;
  assign attr_dma.slvlite_base0 = 'h0;
  assign attr_dma.slvlite_base1 = 'h0;
  assign attr_dma.axibar_num = 'h0;
  assign attr_dma.pciebar_num = 'h0;
  assign attr_dma.ch_en        = 'h0;
  assign attr_dma.ch_pfid        = 'h0;
  assign attr_dma.ch_h2c_axi_dsc = 'h0;
  assign attr_dma.ch_c2h_axi_dsc = 'h0;
  assign attr_dma.ch_multq_ll  = 'h0;
  assign attr_dma.ch_multq_max = 'h0;
  assign attr_dma.ch_multq     = 'h0;
  assign attr_dma.cq_rcfg_en   = 1'b1;
  assign attr_dma.spare.bdg_mst_rw_rlx_dis = 1'd0;
  
  assign attr_dma.rq_rcfg_en   = 1'b0;
  // PCIE to AXI BAR information. assign bar length for PF0.
  
  assign attr_dma_pciebar2axibar_pf[0][0].len = (PF_SWAP == "TRUE") ?  (PF0_BAR0_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_0;
  assign attr_dma_pciebar2axibar_pf[0][1].len = (PF_SWAP == "TRUE") ?  (PF0_BAR1_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_1;
  assign attr_dma_pciebar2axibar_pf[0][2].len = (PF_SWAP == "TRUE") ?  (PF0_BAR2_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_2;
  assign attr_dma_pciebar2axibar_pf[0][3].len = (PF_SWAP == "TRUE") ?  (PF0_BAR3_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_3;
  assign attr_dma_pciebar2axibar_pf[0][4].len = (PF_SWAP == "TRUE") ?  (PF0_BAR4_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_4;
  assign attr_dma_pciebar2axibar_pf[0][5].len = (PF_SWAP == "TRUE") ?  (PF0_BAR5_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_5;
  assign attr_dma_pciebar2axibar_pf[0][6].len = (PF_SWAP == "TRUE") ?  (PF0_EXPANSION_ROM_APERTURE_SIZE + 7) :  C_PCIEBAR_LEN_6;
  
  assign attr_dma_pciebar2axibar_pf[0][0].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_0[63:12]*/ :  C_PCIEBAR2AXIBAR_0_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][1].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_1[63:12]*/ :  C_PCIEBAR2AXIBAR_1_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][2].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_2[63:12]*/ :  C_PCIEBAR2AXIBAR_2_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][3].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_3[63:12]*/ :  C_PCIEBAR2AXIBAR_3_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][4].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_4[63:12]*/ :  C_PCIEBAR2AXIBAR_4_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][5].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_5[63:12]*/ :  C_PCIEBAR2AXIBAR_5_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][6].bar = (PF_SWAP == "TRUE") ?  52'b0 /*PF0_PCIEBAR2AXIBAR_6[63:12]*/ :  C_PCIEBAR2AXIBAR_6_TMP[63:12];
  assign attr_dma_pciebar2axibar_pf[0][0].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][1].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][2].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][3].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][4].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][5].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][6].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][0].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][1].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][2].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][3].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][4].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][5].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[0][6].cache = 'h0;

  assign attr_dma_pciebar2axibar_pf[1][0].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_0 :  (PF1_BAR0_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][1].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_1 :  (PF1_BAR1_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][2].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_2 :  (PF1_BAR2_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][3].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_3 :  (PF1_BAR3_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][4].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_4 :  (PF1_BAR4_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][5].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_5 :  (PF1_BAR5_APERTURE_SIZE + 7);
  assign attr_dma_pciebar2axibar_pf[1][6].len = (PF_SWAP == "TRUE") ?  C_PCIEBAR_LEN_6 :  (PF1_EXPANSION_ROM_APERTURE_SIZE + 7);
  
  assign attr_dma_pciebar2axibar_pf[1][0].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_0_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_0[63:12];
  assign attr_dma_pciebar2axibar_pf[1][1].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_1_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_1[63:12];
  assign attr_dma_pciebar2axibar_pf[1][2].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_2_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_2[63:12];
  assign attr_dma_pciebar2axibar_pf[1][3].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_3_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_3[63:12];
  assign attr_dma_pciebar2axibar_pf[1][4].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_4_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_4[63:12];
  assign attr_dma_pciebar2axibar_pf[1][5].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_5_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_5[63:12];
  assign attr_dma_pciebar2axibar_pf[1][6].bar = (PF_SWAP == "TRUE") ?  C_PCIEBAR2AXIBAR_6_TMP[63:12] :  PF1_PCIEBAR2AXIBAR_6[63:12];
  assign attr_dma_pciebar2axibar_pf[1][0].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][1].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][2].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][3].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][4].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][5].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][6].sec = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][0].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][1].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][2].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][3].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][4].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][5].cache = 'h0;
  assign attr_dma_pciebar2axibar_pf[1][6].cache = 'h0;

  assign m_axis_rq_tdata_out   = axis_rq.tdata ;
  assign m_axis_rq_tlast_out   = axis_rq.tlast;
  assign m_axis_rq_tuser_out   = axis_rq.tuser;
  assign m_axis_rq_tkeep_out   = axis_rq.tkeep;
  assign m_axis_rq_tready_out  = axis_rq_tready;
  assign m_axis_rq_tvalid_out  = axis_rq.tvalid;

  assign s_axis_rc_tdata_out   = axis_rc.tdata;
  assign s_axis_rc_tuser_out   = axis_rc.tuser ;
  assign s_axis_rc_tlast_out   = axis_rc.tlast ;
  assign s_axis_rc_tkeep_out   = axis_rc.tkeep;
  assign s_axis_rc_tvalid_out  = axis_rc.tvalid;
  assign s_axis_rc_tready_out  = m_axis_rc_tready_rst;

  assign s_axis_cq_tdata_out   = axis_cq.tdata ;
  assign s_axis_cq_tuser_out   = axis_cq.tuser ;
  assign s_axis_cq_tlast_out   = axis_cq.tlast;
  assign s_axis_cq_tkeep_out   = axis_cq.tkeep;
  assign s_axis_cq_tvalid_out  = axis_cq.tvalid;
  assign s_axis_cq_tready_out  = axis_cq.tready[0];

  assign m_axis_cc_tdata_out   = axis_cc.tdata;
  assign m_axis_cc_tuser_out   = axis_cc.tuser;
  assign m_axis_cc_tlast_out   = axis_cc.tlast ;
  assign m_axis_cc_tkeep_out   = axis_cc.tkeep;
  assign m_axis_cc_tvalid_out  = axis_cc.tvalid;
  assign m_axis_cc_tready_out  = s_axis_cc_tready;

assign aximm_sz =   ((C_S_AXIS_DATA_WIDTH == 256) ? 3'h2 :
            ((C_S_AXIS_DATA_WIDTH == 128) ?  3'h1 :
            ((C_S_AXIS_DATA_WIDTH == 64) ?  3'h0 : 3'h3)));
assign axist_sz = aximm_sz;

assign axi_aresetn = ~dma_soft_reset;
assign axi_aclk = user_clk;

assign msi_vector_width = cfg_interrupt_msi_mmenable[2:0];
assign msi_enable = cfg_interrupt_msi_enable_int[0];
assign msix_enable = cfg_interrupt_msix_enable_int[0];

assign axis_rq.tready = axis_rq_tready[0];
assign axis_cc.tready = s_axis_cc_tready[0];

assign pcie_dma_in.pcie_cq_np_req_count           = pcie_cq_np_req_count; 
assign pcie_dma_in.cfg_interrupt_msi_mask_update  = cfg_interrupt_msi_mask_update;
assign pcie_dma_in.cfg_err_cor_out                = cfg_err_cor_out;
assign pcie_dma_in.cfg_err_fatal_out              = cfg_err_fatal_out;
assign pcie_dma_in.cfg_err_nonfatal_out           = cfg_err_nonfatal_out;
assign pcie_dma_in.cfg_hot_reset_out              = cfg_hot_reset_out;

   assign pcie_dma_in.cfg_interrupt_msi_enable       = 'h0;
assign pcie_dma_in.cfg_interrupt_msi_fail         = cfg_interrupt_msi_fail;
assign pcie_dma_in.cfg_interrupt_msi_sent         = cfg_interrupt_msi_sent;

assign pcie_dma_in.cfg_negotiated_width           = {1'b0,cfg_negotiated_width};
assign pcie_dma_in.cfg_current_speed              = {1'b0,cfg_current_speed};

assign pcie_dma_in.cfg_interrupt_msix_sent = 1'b0;
assign pcie_dma_in.cfg_interrupt_msix_fail = 1'b0;
assign pcie_dma_in.cfg_interrupt_msix_enable = 4'b00;
assign pcie_dma_in.cfg_interrupt_msix_mask = 4'b00;
assign pcie_dma_in.cfg_interrupt_msix_vf_enable = 6'b0;
assign pcie_dma_in.cfg_interrupt_msix_vf_mask = 6'b0;

assign pcie_dma_in.cfg_mgmt_read_data             = cfg_mgmt_read_data_int;
assign pcie_dma_in.cfg_mgmt_read_write_done       = cfg_mgmt_read_write_done_int;
assign pcie_dma_in.cfg_interrupt_sent             = cfg_interrupt_sent;
assign pcie_dma_in.cfg_local_error                = cfg_local_error[0];
assign pcie_dma_in.cfg_msg_received               = cfg_msg_received;
assign pcie_dma_in.cfg_msg_transmit_done          = cfg_msg_transmit_done;
assign pcie_dma_in.cfg_per_function_update_done   = cfg_per_function_update_done;
assign pcie_dma_in.cfg_phy_link_down              = cfg_phy_link_down;
assign pcie_dma_in.cfg_function_status            = cfg_function_status;
assign pcie_dma_in.cfg_per_func_status_data       = cfg_per_func_status_data;
assign pcie_dma_in.cfg_phy_link_status            = cfg_phy_link_status;
assign pcie_dma_in.cfg_vf_flr_in_process          = 252'b0 | cfg_vf_flr_in_process_int;
assign pcie_dma_in.cfg_max_payload                = {1'b0,cfg_max_payload};
assign pcie_dma_in.cfg_max_read_req               = cfg_max_read_req;

//assign pcie_dma_in.cfg_ext_write_data             = cfg_ext_write_data;
//assign pcie_dma_in.cfg_ext_write_byte_enable      = cfg_ext_write_byte_enable;
//assign pcie_dma_in.cfg_ext_read_received          = cfg_ext_read_received;
//assign pcie_dma_in.cfg_ext_write_received         = cfg_ext_write_received;
//assign pcie_dma_in.cfg_ext_function_number        = cfg_ext_function_number;
//assign pcie_dma_in.cfg_ext_register_number        = cfg_ext_register_number;

assign pcie_dma_in.cfg_ext_write_data             = 32'h0;
assign pcie_dma_in.cfg_ext_write_byte_enable      = 4'h0;
assign pcie_dma_in.cfg_ext_read_received          = 1'b0;
assign pcie_dma_in.cfg_ext_write_received         = 1'b0;
assign pcie_dma_in.cfg_ext_function_number        = 8'h0;
assign pcie_dma_in.cfg_ext_register_number        = 10'h0;

assign pcie_dma_in.cfg_flr_in_process             = 4'h0;
assign pcie_dma_in.pcie_rq_seq_num0               = pcie_rq_seq_num0[3:0];
assign pcie_dma_in.pcie_rq_seq_num1               = pcie_rq_seq_num1[3:0];
assign pcie_dma_in.pcie_rq_seq_num_vld0           = pcie_rq_seq_num_vld0;
assign pcie_dma_in.pcie_rq_seq_num_vld1           = pcie_rq_seq_num_vld1;
assign pcie_dma_in.pcie_tfc_nph_av                = pcie_tfc_nph_av;
assign pcie_dma_in.cfg_msg_received_type          = cfg_msg_received_type;
assign pcie_dma_in.cfg_ltssm_state                = cfg_ltssm_state;
assign pcie_dma_in.cfg_pl_status_change           = cfg_pl_status_change;
assign pcie_dma_in.cfg_msg_received_data          = cfg_msg_received_data;
assign pcie_dma_in.cfg_fc_nph                     = cfg_fc_nph;

assign cfg_fc_sel                                        = pcie_dma_out.cfg_fc_sel;
assign pcie_cq_np_req                                    = pcie_dma_out.pcie_cq_np_req;
assign cfg_mgmt_addr_int                                     = pcie_dma_out.cfg_mgmt_addr;
assign cfg_mgmt_write_int                                    = pcie_dma_out.cfg_mgmt_write;
assign cfg_mgmt_write_data_int                               = pcie_dma_out.cfg_mgmt_write_data;
assign cfg_mgmt_byte_enable_int                              = pcie_dma_out.cfg_mgmt_byte_enable;
assign cfg_mgmt_read_int                                     = pcie_dma_out.cfg_mgmt_read;
assign cfg_mgmt_type1_cfg_reg_access_int                     = pcie_dma_out.cfg_mgmt_type1_cfg_reg_access;
assign cfg_mgmt_function_number                          = pcie_dma_out.cfg_mgmt_function_number;
assign cfg_ds_port_number                                = pcie_dma_out.cfg_ds_port_number;
assign cfg_ds_bus_number                                 = pcie_dma_out.cfg_ds_bus_number;
assign cfg_ds_device_number                              = pcie_dma_out.cfg_ds_device_number;
assign cfg_ds_function_number                            = pcie_dma_out.cfg_ds_function_number;
assign cfg_per_func_status_control                       = pcie_dma_out.cfg_per_func_status_control;
assign cfg_per_function_number                           = pcie_dma_out.cfg_per_function_number;
assign cfg_per_function_output_request                   = pcie_dma_out.cfg_per_function_output_request;
assign cfg_per_function_logic_request                    = pcie_dma_out.cfg_per_function_logic_request;
assign cfg_msg_transmit                                  = pcie_dma_out.cfg_msg_transmit;
assign cfg_msg_transmit_type                             = pcie_dma_out.cfg_msg_transmit_type;
assign cfg_msg_transmit_data                             = pcie_dma_out.cfg_msg_transmit_data;
//assign cfg_subsys_id                                   = pcie_dma_out.cfg_subsys_id;
//assign cfg_subsys_vend_id                              = pcie_dma_out.cfg_subsys_vend_id;
//assign cfg_vend_id                                     = pcie_dma_out.cfg_vend_id;
assign cfg_dsn                                           = pcie_dma_out.cfg_dsn;
assign cfg_err_cor_in                                    = pcie_dma_out.cfg_err_cor_in;
assign cfg_err_uncor_in                                  = pcie_dma_out.cfg_err_uncor_in;
assign cfg_link_training_enable                          = pcie_dma_out.cfg_link_training_enable;
//assign cfg_ext_read_data                               = pcie_dma_out.cfg_ext_read_data;
//assign cfg_ext_read_data_valid                         = pcie_dma_out.cfg_ext_read_data_valid;
assign cfg_flr_done_int                                  = pcie_dma_out.cfg_flr_done;
//assign cfg_vf_flr_done_int                             = pcie_dma_out.cfg_vf_flr_done;
//assign cfg_vf_flr_func_num_int                         = pcie_dma_out.cfg_vf_flr_func_num;
assign cfg_config_space_enable                           = pcie_dma_out.cfg_config_space_enable;
assign cfg_hot_reset_in                                  = pcie_dma_out.cfg_hot_reset_in;
assign cfg_interrupt_msi_int                             = pcie_dma_out.cfg_interrupt_msi_int;
assign cfg_interrupt_msi_pending_status                  = pcie_dma_out.cfg_interrupt_msi_pending_status;
assign cfg_interrupt_msi_pending_status_data_enable      = pcie_dma_out.cfg_interrupt_msi_pending_status_data_enable;
assign cfg_interrupt_msi_pending_status_function_num     = pcie_dma_out.cfg_interrupt_msi_pending_status_function_num;
assign cfg_interrupt_msi_attr                            = pcie_dma_out.cfg_interrupt_msi_attr;
assign cfg_interrupt_msi_tph_present                     = pcie_dma_out.cfg_interrupt_msi_tph_present;
assign cfg_interrupt_msi_tph_type                        = pcie_dma_out.cfg_interrupt_msi_tph_type;
assign cfg_interrupt_msi_tph_st_tag                      = pcie_dma_out.cfg_interrupt_msi_tph_st_tag;
assign cfg_interrupt_msi_function_number                 = pcie_dma_out.cfg_interrupt_msi_function_number;
assign cfg_interrupt_int                                 = pcie_dma_out.cfg_interrupt_int;
assign cfg_interrupt_pending                             = pcie_dma_out.cfg_interrupt_pending;

    xdma_v4_1_29_udma_wrapper #(
      .C_PARITY_CHECK              (C_PARITY_CHECK),
      .C_PARITY_GEN                (C_PARITY_GEN),
      .C_PARITY_PROP               (C_PARITY_PROP),
      .RQ_SEQ_NUM_IGNORE           (RQ_SEQ_NUM_IGNORE),
      .C_MSI_RX_PIN_EN             (C_MSI_RX_PIN_EN),
      .C_MSIX_RX_PIN_EN            (C_MSIX_RX_PIN_EN),
      .C_INTX_RX_PIN_EN            (C_INTX_RX_PIN_EN),
      .MSIX_RX_DECODE_EN           (MSIX_RX_DECODE_EN),
      .MSIX_VEC_NUM                (MSIX_VEC_NUM),
      .VERSION                     (VERSION),
      .TCQ                         (TCQ),
      .USE_ATTR                    (USE_ATTR),
      .IMPL_TARGET                 (IMPL_TARGET),
      .XDMA_DSC_ENG                (XDMA_DSC_ENG),
      .C_FAMILY                    (C_FAMILY),
      .C_M_AXI_ID_WIDTH            (C_M_AXI_ID_WIDTH),
      .C_M_AXI_ADDR_WIDTH          (C_M_AXI_ADDR_WIDTH),
      .C_M_AXI_DATA_WIDTH          (C_M_AXI_DATA_WIDTH),
      .C_S_AXI_SUPPORTS_NARROW_BURST(C_S_AXI_SUPPORTS_NARROW_BURST),
      .C_S_AXIS_DATA_WIDTH         (C_S_AXIS_DATA_WIDTH),
      .C_S_AXI_ID_WIDTH            (C_S_AXI_ID_WIDTH),
      .C_S_AXI_ADDR_WIDTH          (C_S_AXI_ADDR_WIDTH),
      .C_S_AXI_DATA_WIDTH          (C_S_AXI_DATA_WIDTH),
      .C_M_AXIS_DATA_WIDTH         (C_M_AXIS_DATA_WIDTH),
      .C_M_AXIS_RQ_USER_WIDTH      (C_M_AXIS_RQ_USER_WIDTH),
      .C_M_AXIS_RC_USER_WIDTH      (C_M_AXIS_RC_USER_WIDTH),
      .C_S_AXIS_CQ_USER_WIDTH      (C_S_AXIS_CQ_USER_WIDTH),
      .C_S_AXIS_CC_USER_WIDTH      (C_S_AXIS_CC_USER_WIDTH),
      .C_H2C_TUSER_WIDTH           (C_H2C_TUSER_WIDTH),
      .C_C2H_TUSER_WIDTH           (C_C2H_TUSER_WIDTH),

      .C_M_AXI_AWUSER_WIDTH        (C_M_AXI_AWUSER_WIDTH),
//    .C_M_AXI_WUSER_WIDTH         (C_M_AXI_WUSER_WIDTH),
//    .C_M_AXI_BUSER_WIDTH         (C_M_AXI_BUSER_WIDTH),
      .C_M_AXI_ARUSER_WIDTH        (C_M_AXI_ARUSER_WIDTH),
//    .C_M_AXI_RUSER_WIDTH         (C_M_AXI_RUSER_WIDTH),

      .C_PCIEBAR_LEN_0             (C_PCIEBAR_LEN_0),
      .C_PCIEBAR_LEN_1             (C_PCIEBAR_LEN_1),
      .C_PCIEBAR_LEN_2             (C_PCIEBAR_LEN_2),
      .C_PCIEBAR_LEN_3             (C_PCIEBAR_LEN_3),
      .C_PCIEBAR_LEN_4             (C_PCIEBAR_LEN_4),
      .C_PCIEBAR_LEN_5             (C_PCIEBAR_LEN_5),
      .C_PCIEBAR_LEN_6             (C_PCIEBAR_LEN_6),
      .C_PCIEBAR2AXIBAR_0          (C_PCIEBAR2AXIBAR_0_TMP),
      .C_PCIEBAR2AXIBAR_1          (C_PCIEBAR2AXIBAR_1_TMP),
      .C_PCIEBAR2AXIBAR_2          (C_PCIEBAR2AXIBAR_2_TMP),
      .C_PCIEBAR2AXIBAR_3          (C_PCIEBAR2AXIBAR_3_TMP),
      .C_PCIEBAR2AXIBAR_4          (C_PCIEBAR2AXIBAR_4_TMP),
      .C_PCIEBAR2AXIBAR_5          (C_PCIEBAR2AXIBAR_5_TMP),
      .C_ADDR_ALGN                 (C_ADDR_ALGN),
      .C_ADDR_BITS                 (C_ADDR_BITS),
      .C_DSC_MAGIC_EN              (C_DSC_MAGIC_EN),
      .C_H2C_NUM_CHNL              (C_H2C_NUM_CHNL),
      .C_C2H_NUM_CHNL              (C_C2H_NUM_CHNL),
      .C_H2C_NUM_RIDS              (C_H2C_NUM_RIDS),
      .C_C2H_NUM_RIDS              (C_C2H_NUM_RIDS),
      .C_NUMQ_PER_CHNL             (C_NUMQ_PER_CHNL),
      .C_NUM_DSC_PCIE_RID          (C_NUM_DSC_PCIE_RID),
      .C_NUM_PCIE_DSC_CPL_DID      (C_NUM_PCIE_DSC_CPL_DID),
      .C_NUM_AXI_DSC_CPL_DID       (C_NUM_AXI_DSC_CPL_DID),
      .H2C_XDMA_CHNL               (8'b00001111),
      .C2H_XDMA_CHNL               (8'b00001111),
      .MULTQ_CHNL                  (MULTQ_CHNL),
      .MULTQ_MAX_CHNL              ({8{6'h20}}),
      .C_M_NUM_AXI_READ            (C_C2H_NUM_RIDS),
      .C_NUM_USR_IRQ               (C_NUM_USR_IRQ),
      .C_NUM_PCIE_TAGS             (XDMA_NUM_PCIE_TAG),
//    .C_METERING_ON               (C_METERING_ON),
      .C_ECC_ENABLE                (C_ECC_ENABLE),
      .C_SLAVE_READ_64OS_EN        (C_SLAVE_READ_64OS_EN),
      .C_RD_BUFFER_ADDR_SIZE       (C_RD_BUFFER_ADDR_SIZE),
      .C_RD_BUFFER_SIZE_BITS       (C_RD_BUFFER_SIZE_BITS),
      .C_PCIEBAR_NUM               (C_PCIEBAR_NUM),
      .C_PCIEBAR_AS                (C_PCIEBAR_AS),
      .AXI_DSC_ENG_EN              (0),
      .AXI_WBK_ENG_EN              (0),
      .PCIE_DSC_ENG_EN             (1),
      .PCIE_WBK_ENG_EN             (1),
      .BARLITE0                    (BARLITE0),
      .BARLITE1                    (BARLITE1),
      .BARLITE2                    (BARLITE2),
      .MM_SLAVE_EN                 (MM_SLAVE_EN),
      .C_M_NUM_CQ_AXI_READ         (C_M_AXI_NUM_READ),
      .C_M_NUM_CQ_AXI_READQ        (C_M_AXI_NUM_READQ),
      .C_M_NUM_CQ_AXI_WRITE        (C_M_AXI_NUM_WRITE),
      .C_M_NUM_CQ_AXI_WRITE_SCALE  (C_M_AXI_NUM_WRITE_SCALE),
      .C_S_NUM_AXI_READ            (C_S_AXI_NUM_READ),
      .C_S_NUM_AXI_WRITE           (C_S_AXI_NUM_WRITE),
      .C_AXIBAR_NOXLATE            (C_AXIBAR_NOXLATE),
      .C_INCLUDE_BAROFFSET_REG     (C_INCLUDE_BAROFFSET_REG),
      .C_AXIBAR_0                  (C_AXIBAR_0),
      .C_AXIBAR_HIGHADDR_0         (C_AXIBAR_HIGHADDR_0),
      .C_AXIBAR_1                  (C_AXIBAR_1),
      .C_AXIBAR_HIGHADDR_1         (C_AXIBAR_HIGHADDR_1),
      .C_AXIBAR_2                  (C_AXIBAR_2),
      .C_AXIBAR_HIGHADDR_2         (C_AXIBAR_HIGHADDR_2),
      .C_AXIBAR_3                  (C_AXIBAR_3),
      .C_AXIBAR_HIGHADDR_3         (C_AXIBAR_HIGHADDR_3),
      .C_AXIBAR_4                  (C_AXIBAR_4),
      .C_AXIBAR_HIGHADDR_4         (C_AXIBAR_HIGHADDR_4),
      .C_AXIBAR_5                  (C_AXIBAR_5),
      .C_AXIBAR_HIGHADDR_5         (C_AXIBAR_HIGHADDR_5),
      .C_AXIBAR_AS_0               (C_AXIBAR_AS_0),
      .C_AXIBAR_AS_1               (C_AXIBAR_AS_1),
      .C_AXIBAR_AS_2               (C_AXIBAR_AS_2),
      .C_AXIBAR_AS_3               (C_AXIBAR_AS_3),
      .C_AXIBAR_AS_4               (C_AXIBAR_AS_4),
      .C_AXIBAR_AS_5               (C_AXIBAR_AS_5),
      .C_AXIBAR2PCIEBAR_0          (C_AXIBAR2PCIEBAR_0),
      .C_AXIBAR2PCIEBAR_1          (C_AXIBAR2PCIEBAR_1),
      .C_AXIBAR2PCIEBAR_2          (C_AXIBAR2PCIEBAR_2),
      .C_AXIBAR2PCIEBAR_3          (C_AXIBAR2PCIEBAR_3),
      .C_AXIBAR2PCIEBAR_4          (C_AXIBAR2PCIEBAR_4),
      .C_AXIBAR2PCIEBAR_5          (C_AXIBAR2PCIEBAR_5),
      .C_AXIBAR2PCIEATTR_0         (C_AXIBAR2PCIEATTR_0),
      .C_AXIBAR2PCIEATTR_1         (C_AXIBAR2PCIEATTR_1),
      .C_AXIBAR2PCIEATTR_2         (C_AXIBAR2PCIEATTR_2),
      .C_AXIBAR2PCIEATTR_3         (C_AXIBAR2PCIEATTR_3),
      .C_AXIBAR2PCIEATTR_4         (C_AXIBAR2PCIEATTR_4),
      .C_AXIBAR2PCIEATTR_5         (C_AXIBAR2PCIEATTR_5),   
      .C_IGNORE_SIZE_AXI_SLAVE     (C_IGNORE_SIZE_AXI_SLAVE),
      .C_TIMEOUT0_SEL              (C_TIMEOUT0_SEL),
      .C_TIMEOUT1_SEL              (C_TIMEOUT1_SEL),
      .C_TIMEOUT_MULT              (C_TIMEOUT_MULT),
      .C_OLD_BRIDGE_TIMEOUT        (C_OLD_BRIDGE_TIMEOUT),
      .C_S_AXI_REG_ENABLE          (1),
      .DMA_EN                      (DMA_EN),
      .SHELL_BRIDGE                (SHELL_BRIDGE),
      .MSIX_PCIE_INTERNAL          (MSIX_PCIE_INTERNAL),
      .C_MSIX_INT_TABLE_EN         (C_MSIX_INT_TABLE_EN),
      .C_AXIBAR_REGIONEN           (C_AXIBAR_REGIONEN),
      .C_INCLUDE_RC                (C_INCLUDE_RC),
      .C_BASEADDR                  (C_BASEADDR),
      .C_HIGHADDR                  (C_HIGHADDR),
      .C_LAST_CORE_CAP_ADDR        (C_LAST_CORE_CAP_ADDR),
      .C_VSEC_CAP_ADDR             (C_VSEC_CAP_ADDR),
      .C_VSEC_CAP_LAST             (C_VSEC_CAP_LAST),
      .C_VSEC_ID                   (C_VSEC_ID),
      .C_DEVICE_NUMBER             (C_DEVICE_NUMBER),
      .C_NUM_USER_INTR             (C_NUM_USER_INTR),
      .C_NUM_USER_NEW_INTR         (C_NUM_USER_NEW_INTR),
      .C_USER_PTR                  (C_USER_PTR),
      .C_COMP_TIMEOUT              (C_COMP_TIMEOUT),
      .C_MSI_ENABLED               (C_MSI_ENABLED),
      .PL_LINK_CAP_MAX_LINK_SPEED  (PL_LINK_CAP_MAX_LINK_SPEED),
      .PL_DISABLE_UPCONFIG_CAPABLE (PL_DISABLE_UPCONFIG_CAPABLE),
   
      .C_PCIE_PFS_SUPPORTED        (NUM_PFS),
      .C_PCIE_PFS_ENABLED          (NUM_PFS),
      .C_PCIE_VFS_SUPPORTED        (0),
      .C_PCIE_VFS_ENABLED          (0),
      .C_SRIOV_EN                  (SRIOV_EN),
      .USR_MPL_SIZE                (USR_MPL_SIZE),
      .USR_MRS_SIZE                (USR_MRS_SIZE),
      .STS_WIDTH                   (STS_WIDTH),
      .BACKPRESSURE                (BACKPRESSURE),
      .DSC_BYPASS_RD               (DSC_BYPASS_RD),
      .DSC_BYPASS_WR               (DSC_BYPASS_WR),
      .PMON_EN                     (PMON_EN),
      .DMA_ST                      (DMA_ST),
      .C_ENABLE_RESOURCE_REDUCTION (C_ENABLE_RESOURCE_REDUCTION),
      .MULT_PF_DESIGN(MULT_PF_DESIGN),
      .PROG_USR_IRQ_VEC_MAP (PROG_USR_IRQ_VEC_MAP),
      .DMA_MM                      (DMA_MM),
      .FUNC_MODE                   (FUNC_MODE),
      .C_ATS_ENABLE(C_ATS_ENABLE),
      .C_PRI_ENABLE(C_PRI_ENABLE),
      .C_FF_ON_INT_IF(C_FF_ON_INT_IF),
      .C_ATS_OFFSET(C_ATS_OFFSET),
      .C_PR_OFFSET(C_PR_OFFSET),
      .C_ATS_CAP_NEXTPTR(C_ATS_CAP_NEXTPTR),
      .C_PR_CAP_NEXTPTR(C_PR_CAP_NEXTPTR),
      .C_INV_QUEUE_DEPTH(C_INV_QUEUE_DEPTH),
      .C_OST_PR_CAP(C_OST_PR_CAP),
      .C_M_INT_W_ORDER_EN(C_INCLUDE_RC ? 1 : 0),
      .AXSIZE_BYTE_ACCESS_EN(AXSIZE_BYTE_ACCESS_EN),
      .PF_SWAP(PF_SWAP),
      .PF0_MSIX_TAR_ID(PF0_MSIX_TAR_ID),
      .PF1_MSIX_TAR_ID(PF1_MSIX_TAR_ID),
      .DMA_2RP(DMA_2RP),
      .RBAR_ENABLE    (RBAR_ENABLE),
      .RUN_BIT_FIX(RUN_BIT_FIX),
      .C_SMMU_EN(C_SMMU_EN),
      .USR_INT_EXPN(USR_INT_EXPN),
      .C_ERRC_DEC_EN(C_ERRC_DEC_EN)
    )
   udma_wrapper (
     //-- AXI Global
     .user_clk  (user_clk),
     .sys_reset (dma_soft_reset),
     .link_up   ( user_lnk_up ),
     .axi_aresetn(),

     .usr_flr_fnc                  ( usr_flr_fnc),
     .usr_flr_set                  ( usr_flr_set),
     .usr_flr_clr                  ( usr_flr_clr),
     .usr_flr_done_fnc             ( usr_flr_done_fnc ),
     .usr_flr_done_vld             ( usr_flr_done_vld ),

    .rbar_bar_size                                  ( 6'h0 ),
    .rbar_function_number                           ( 8'h0 ),
    .rbar_write_enable_bar0                         ( 1'b0 ),
    .rbar_write_enable_bar1                         ( 1'b0 ),
    .rbar_write_enable_bar2                         ( 1'b0 ),
    .rbar_write_enable_bar3                         ( 1'b0 ),
    .rbar_write_enable_bar4                         ( 1'b0 ),
    .rbar_write_enable_bar5                         ( 1'b0 ),

     .pf1_lite_ext    (pf1_lite_ext),
     // Attribute
     .attr_dma                     (attr_dma),
     .attr_dma_pf                  (attr_dma_pf),
     .attr_dma_pciebar2axibar_pf   (attr_dma_pciebar2axibar_pf),
     .attr_dma_axibar2pciebar      (attr_dma_axibar2pciebar),

     .mi_hw_ctxt                (mi_hw_ctxt),
     .mi_sw_ctxt                (mi_sw_ctxt),
     .mi_dsc_crd_rcv            (mi_dsc_crd_rcv),
     .mi_wb_base_ctxt           (mi_wb_base_ctxt),

    // BRAM interface
     .mi_h2c_pcie_dsc_cpli      (mi_h2c_pcie_dsc_cpli),                       
     .mi_h2c_pcie_dsc_cpld      (mi_h2c_pcie_dsc_cpld),               
     .mi_h2c_axi_dsc_cpli       (mi_h2c_axi_dsc_cpli),                      
     .mi_h2c_axi_dsc_cpld       (mi_h2c_axi_dsc_cpld), 

     .mi_c2h_pcie_dsc_cpli      (mi_c2h_pcie_dsc_cpli),                       
     .mi_c2h_pcie_dsc_cpld      (mi_c2h_pcie_dsc_cpld),               
     .mi_c2h_axi_dsc_cpli       (mi_c2h_axi_dsc_cpli),                      
     .mi_c2h_axi_dsc_cpld       (mi_c2h_axi_dsc_cpld), 
    
     .dsc_in                    (dsc_in),
     .dsc_out                   (dsc_out),
                 
     .mi_h2c0_dat               (mi_h2c0_dat),
     .mi_h2c1_dat               (mi_h2c1_dat),
     .mi_h2c2_dat               (mi_h2c2_dat),
     .mi_h2c3_dat               (mi_h2c3_dat),

     .mi_c2h0_dat               (mi_c2h0_dat),
     .mi_c2h1_dat               (mi_c2h1_dat),
     .mi_c2h2_dat               (mi_c2h2_dat),
     .mi_c2h3_dat               (mi_c2h3_dat),

     .mi_h2c_rd_brg_dat        (mi_h2c_rd_brg_dat),
     .mi_h2c_wr_brg_dat        (mi_h2c_wr_brg_dat),

     .mi_c2h_rd_brg_dat        (mi_c2h_rd_brg_dat),
     .mi_c2h_wr_brg_dat     (mi_c2h_wr_brg_dat),

    //-- AXIS RQ Request Channel
    .m_axis_rq              (axis_rq),
    .m_axis_cc              (axis_cc),
    .s_axis_rc              (axis_rc),
    .s_axis_cq              (axis_cq),

    .pcie_dma_out           (pcie_dma_out),
    .pcie_dma_in            (pcie_dma_in),

    .pcie_dma_gic           (pcie_dma_gic),
    .fabric_out             (fabric_out),
    .fabric_in              (fabric_in),

    // AXI-Lite Master interface
    .m_axil_awaddr          (m_axil_awaddr),
     .m_axil_awuser     (m_axil_awuser[7:0]),
    .m_axil_awprot          (m_axil_awprot),
    .m_axil_awvalid         (m_axil_awvalid),
    .m_axil_awready         (m_axil_awready),
                                         
    .m_axil_wdata           (m_axil_wdata),
    .m_axil_wstrb           (m_axil_wstrb),
    .m_axil_wvalid          (m_axil_wvalid),
    .m_axil_wready          (m_axil_wready),
                                         
    .m_axil_bvalid          (m_axil_bvalid),
    .m_axil_bresp           (m_axil_bresp),
    .m_axil_bready          (m_axil_bready),
                                         
    .m_axil_araddr          (m_axil_araddr),
     .m_axil_aruser     (m_axil_aruser[7:0]),
    .m_axil_arprot          (m_axil_arprot),
    .m_axil_arvalid         (m_axil_arvalid),
    .m_axil_arready         (m_axil_arready),
                                         
    .m_axil_rdata           (m_axil_rdata),
    .m_axil_rresp           (m_axil_rresp),
    .m_axil_rvalid          (m_axil_rvalid),
    .m_axil_rready          (m_axil_rready),

    // AXI-Lite Slave interface 
    .s_axil_awaddr          (s_axil_awaddr),
    .s_axil_awprot          (s_axil_awprot),
    .s_axil_awvalid         (s_axil_awvalid),
    .s_axil_awready         (s_axil_awready),
                                         
    .s_axil_wdata           (s_axil_wdata),
    .s_axil_wstrb           (s_axil_wstrb),
    .s_axil_wvalid          (s_axil_wvalid),
    .s_axil_wready          (s_axil_wready),
                                         
    .s_axil_bvalid          (s_axil_bvalid),
    .s_axil_bresp           (s_axil_bresp),
    .s_axil_bready          (s_axil_bready),
                                         
    .s_axil_araddr          (s_axil_araddr),
    .s_axil_arprot          (s_axil_arprot),
    .s_axil_arvalid         (s_axil_arvalid),
    .s_axil_arready         (s_axil_arready),
                                         
    .s_axil_rdata           (s_axil_rdata),
    .s_axil_rresp           (s_axil_rresp),
    .s_axil_rvalid          (s_axil_rvalid),
    .s_axil_rready          (s_axil_rready),

    //--AXI Master Read Address Channel
    .m_axi_arid             (m_axi_arid),
    .m_axi_araddr           (m_axi_araddr_temp),
    .m_axi_arlen            (m_axi_arlen),
    .m_axi_arsize           (m_axi_arsize),
    .m_axi_arburst          (m_axi_arburst),
    .m_axi_arprot           (m_axi_arprot),
    .m_axi_arvalid          (m_axi_arvalid),
    .m_axi_arready          (m_axi_arready),
    .m_axi_arlock           (m_axi_arlock),
    .m_axi_arcache          (m_axi_arcache),
    //--AXI Master Read Data Channel
    .m_axi_rid              (m_axi_rid),
    .m_axi_rdata            (m_axi_rdata),
    .m_axi_rdataeccparity   (m_axi_ruser),
    .m_axi_rresp            (m_axi_rresp),
    .m_axi_rlast            (m_axi_rlast),
    .m_axi_rvalid           (m_axi_rvalid),
    .m_axi_rready           (m_axi_rready),

        //--AXI master Write Address Channel
    .m_axi_awaddr           (m_axi_awaddr_temp),
    .m_axi_awid             (m_axi_awid),
    .m_axi_awlen            (m_axi_awlen),
    .m_axi_awsize           (m_axi_awsize),
    .m_axi_awburst          (m_axi_awburst),
    .m_axi_awprot           (m_axi_awprot),
    .m_axi_awvalid          (m_axi_awvalid),
    .m_axi_awready          (m_axi_awready),
    .m_axi_awlock           (m_axi_awlock),
    .m_axi_awcache          (m_axi_awcache),

        //--AXI master Write Data Channel
    .m_axi_wdata            (m_axi_wdata),
    .m_axi_wdataeccparity   (m_axi_wuser),
    .m_axi_wstrb            (m_axi_wstrb),
    .m_axi_wlast            (m_axi_wlast),
    .m_axi_wvalid           (m_axi_wvalid),
    .m_axi_wready           (m_axi_wready),

    //--AXI master Response Channel
    .m_axi_bresp            (m_axi_bresp),
    .m_axi_bid              (m_axi_bid),
    .m_axi_bvalid           (m_axi_bvalid),
    .m_axi_bready           (m_axi_bready),



    //--AXI Master Read Address Channel
    .m_axib_arid            (m_axib_arid),
    .m_axib_araddr          (m_axib_araddr_temp),
    .m_axib_aruser          (m_axib_aruser),
    .m_axib_arlen           (m_axib_arlen),
    .m_axib_arsize          (m_axib_arsize),
    .m_axib_arburst         (m_axib_arburst),
    .m_axib_arprot          (m_axib_arprot),
    .m_axib_arvalid         (m_axib_arvalid),
    .m_axib_arready         (m_axib_arready),
    .m_axib_arlock          (m_axib_arlock),
    .m_axib_arcache         (m_axib_arcache),
    //--AXI Master Read Data Channel
    .m_axib_rid             (m_axib_rid),
    .m_axib_rdata           (m_axib_rdata),
    .m_axib_rdataeccparity  (m_axib_ruser),
    .m_axib_rresp           (m_axib_rresp),
    .m_axib_rlast           (m_axib_rlast),
    .m_axib_rvalid          (m_axib_rvalid),
    .m_axib_rready          (m_axib_rready),
        //--AXI master Write Address Channel
    .m_axib_awaddr          (m_axib_awaddr_temp),
    .m_axib_awuser          (m_axib_awuser),
    .m_axib_awid            (m_axib_awid),
    .m_axib_awlen           (m_axib_awlen),
    .m_axib_awsize          (m_axib_awsize),
    .m_axib_awburst         (m_axib_awburst),
    .m_axib_awprot          (m_axib_awprot),
    .m_axib_awvalid         (m_axib_awvalid),
    .m_axib_awready         (m_axib_awready),
    .m_axib_awlock          (m_axib_awlock),
    .m_axib_awcache         (m_axib_awcache),

        //--AXI master Write Data Channel
    .m_axib_wdata           (m_axib_wdata),
    .m_axib_wdataeccparity  (m_axib_wuser),
    .m_axib_wstrb           (m_axib_wstrb),
    .m_axib_wlast           (m_axib_wlast),
    .m_axib_wvalid          (m_axib_wvalid),
    .m_axib_wready          (m_axib_wready),

    //--AXI master Response Channel
    .m_axib_bresp           (m_axib_bresp),
    .m_axib_bid             (m_axib_bid),
    .m_axib_bvalid          (m_axib_bvalid),
    .m_axib_bready          (m_axib_bready),

   //-- AXI Slave Write Address Channel
   .s_axi_awid(s_axib_awid),
   .s_axi_awaddr(s_axib_awaddr_temp),
   .s_axi_awregion(s_axib_awregion),
   .s_axi_awlen(s_axib_awlen),
   .s_axi_awsize(s_axib_awsize),
   .s_axi_awburst(s_axib_awburst),
   .s_axi_awvalid(s_axib_awvalid),
   .s_axi_awready(s_axib_awready),

   //-- AXI Slave Write Data Channel
   .s_axi_wdata(s_axib_wdata),
   .s_axi_wdataeccparity(s_axib_wuser),
   .s_axi_wstrb(s_axib_wstrb),
   .s_axi_wlast(s_axib_wlast),
   .s_axi_wvalid(s_axib_wvalid),
   .s_axi_wready(s_axib_wready),

   //-- AXI Slave Write Response Channel
   .s_axi_bid(s_axib_bid),
   .s_axi_bresp(s_axib_bresp),
   .s_axi_bvalid(s_axib_bvalid),
   .s_axi_bready(s_axib_bready),

   //-- AXI Slave Read Address Channel
   .s_axi_arid(s_axib_arid),
   .s_axi_araddr(s_axib_araddr_temp),
   .s_axi_arregion(s_axib_arregion),
   .s_axi_arlen(s_axib_arlen),
   .s_axi_arsize(s_axib_arsize),
   .s_axi_arburst(s_axib_arburst),
   .s_axi_arvalid(s_axib_arvalid),
   .s_axi_arready(s_axib_arready),

   //-- AXI Slave Read Data Channel
   .s_axi_rid(s_axib_rid),
   .s_axi_rresp(s_axib_rresp),
   .s_axi_rlast(s_axib_rlast),
   .s_axi_rvalid(s_axib_rvalid),
   .s_axi_rdata(s_axib_rdata),
   .s_axi_rdataeccparity(s_axib_ruser),
   .s_axi_rready(s_axib_rready),
   
     .s_axis_c2h_tdata         (s_axis_c2h_tdata_0),
     .s_axis_c2h_tlast         (s_axis_c2h_tlast_0),
     .s_axis_c2h_tvalid        (s_axis_c2h_tvalid_0),
     .s_axis_c2h_tready        (s_axis_c2h_tready_0),
     .s_axis_c2h_tkeep         (s_axis_c2h_tkeep_0),
     .s_axis_c2h_tparity       (s_axis_c2h_tuser_0),
    .s_axis_c2h_tuser   (64'h0),
     .m_axis_h2c_tdata         (m_axis_h2c_tdata_0),
     .m_axis_h2c_tlast         (m_axis_h2c_tlast_0),
     .m_axis_h2c_tvalid        (m_axis_h2c_tvalid_0),
     .m_axis_h2c_tkeep         (m_axis_h2c_tkeep_0),
     .m_axis_h2c_tready        (m_axis_h2c_tready_0),
     .m_axis_h2c_tparity       (m_axis_h2c_tuser_0),
    .m_axis_h2c_tuser   (),

    .usr_irq_req        (usr_irq_req),
    .usr_irq_ack        (usr_irq_ack),
    .usr_irq_function_number (usr_irq_function_number),
    .usr_irq_fail       (usr_irq_fail),


     .c2h_dsc_byp_ready (c2h_dsc_byp_ready_0),
     .c2h_dsc_byp_src_addr   (c2h_dsc_byp_src_addr_0),
     .c2h_dsc_byp_dst_addr   (c2h_dsc_byp_dst_addr_0),
     .c2h_dsc_byp_len        (c2h_dsc_byp_len_0),
     .c2h_dsc_byp_ctl        (c2h_dsc_byp_ctl_0),
     .c2h_dsc_byp_load       (c2h_dsc_byp_load_0),

     .h2c_dsc_byp_ready (h2c_dsc_byp_ready_0),
     .h2c_dsc_byp_src_addr   (h2c_dsc_byp_src_addr_0),
     .h2c_dsc_byp_dst_addr   (h2c_dsc_byp_dst_addr_0),
     .h2c_dsc_byp_len        (h2c_dsc_byp_len_0),
     .h2c_dsc_byp_ctl        (h2c_dsc_byp_ctl_0),
     .h2c_dsc_byp_load       (h2c_dsc_byp_load_0),

    // H2C Descriptor Output Interface
    .h2c_desc_cmd_out_rdy              (1'b0),
    .h2c_desc_cmd_out_qrdy             (32'hFFFFFFFF),
    .h2c_desc_cmd_out_vld              (),
    .h2c_desc_cmd_out_qid              (),
    .h2c_desc_cmd_out_data             (),

    // H2C Descriptor Input Interface
    .h2c_desc_cmd_in_rdy               (),
    .h2c_desc_cmd_in_vld               (1'b0),
    .h2c_desc_cmd_in_qid               (5'h0),
    .h2c_desc_cmd_in_data              (128'h0),

      .c2h_pktin_accept                  (),
      .c2h_pktin_drop                    (),
      .c2h_desc_avail_inc_vld            (),
      .c2h_desc_avail_inc_qid            (),
      .c2h_desc_avail_inc_num            (),

/////////////////////////////////////////////
/*
    .cfg_dbe            (cfg_dbe),
*/

    .m_axis_cq_tdata                                ( atspri_m_axis_cq_tdata ),
    .m_axis_cq_tvalid                               ( atspri_m_axis_cq_tvalid ),
    .m_axis_cq_tready                               ( atspri_m_axis_cq_tready ),
    .m_axis_cq_tkeep                                ( atspri_m_axis_cq_tkeep ),
    .m_axis_cq_tlast                                ( atspri_m_axis_cq_tlast ),
    .m_axis_cq_tuser                                ( atspri_m_axis_cq_tuser ),

    .s_axis_rq_tdata                                ( atspri_s_axis_rq_tdata ),
    .s_axis_rq_tvalid                               ( atspri_s_axis_rq_tvalid ),
    .s_axis_rq_tready                               ( atspri_s_axis_rq_tready ),
    .s_axis_rq_tkeep                                ( atspri_s_axis_rq_tkeep ),
    .s_axis_rq_tlast                                ( atspri_s_axis_rq_tlast ),
    .s_axis_rq_tuser                                ( atspri_s_axis_rq_tuser ),

    .cfg_status_ats_stu                             ( cfg_status_ats_stu ),
    .cfg_status_ats_en                              ( cfg_status_ats_en ),
    .cfg_status_pr_en                               ( cfg_status_pr_en ),
    .cfg_status_pr_rst                              ( cfg_status_pr_rst ),
    .cfg_status_pr_uprgi                            ( cfg_status_pr_uprgi ),
    .cfg_status_set_uprgi                           ( cfg_status_set_uprgi ),
    .cfg_status_pr_rf                               ( cfg_status_pr_rf ),
    .cfg_status_set_rf                              ( cfg_status_set_rf ),
    .cfg_status_set_s                               ( cfg_status_set_s ),
    .cfg_status_clr_s                               ( cfg_status_clr_s ),
    .cfg_status_ost_pr_alloc                        ( cfg_status_ost_pr_alloc ),

    //.cfg_flr_in_process                            ( cfg_flr_in_process_int ),
	
    .user_cfg_ext_read_received_o                  ( cfg_ext_read_received ),
    .user_cfg_ext_write_received_o                 ( cfg_ext_write_received ),
    .user_cfg_ext_register_number_o                ( cfg_ext_register_number ),
    .user_cfg_ext_function_number_o                ( cfg_ext_function_number ),
    .user_cfg_ext_write_data_o                     ( cfg_ext_write_data ),
    .user_cfg_ext_write_byte_enable_o              ( cfg_ext_write_byte_enable ),
    .user_cfg_ext_read_data_i                      ( cfg_ext_read_data ),
    .user_cfg_ext_read_data_valid_i                ( cfg_ext_read_data_valid ),

    .blk_cfg_ext_read_received_i                   ( blk_cfg_ext_read_received ),
    .blk_cfg_ext_write_received_i                  ( blk_cfg_ext_write_received ),
    .blk_cfg_ext_register_number_i                 ( blk_cfg_ext_register_number ),
    .blk_cfg_ext_function_number_i                 ( blk_cfg_ext_function_number ),
    .blk_cfg_ext_write_data_i                      ( blk_cfg_ext_write_data ),
    .blk_cfg_ext_write_byte_enable_i               ( blk_cfg_ext_write_byte_enable ),
    .blk_cfg_ext_read_data_o                       ( blk_cfg_ext_read_data ),
    .blk_cfg_ext_read_data_valid_o                 ( blk_cfg_ext_read_data_valid )
	
   );
xdma_v4_1_29_udma_ram_top
   #(
    .TCQ                (TCQ),
    .IMPL_TARGET        (IMPL_TARGET),
    .SHELL_BRIDGE          (SHELL_BRIDGE),
    .MM_SLAVE_EN        (MM_SLAVE_EN),
    .AXI4MM_ULTRA       (AXI4MM_ULTRA),
    .C_DATA_WIDTH       (DAT_WIDTH),
    .C_H2C_NUM_CHNL     (C_H2C_NUM_CHNL),
    .C_C2H_NUM_CHNL     (C_C2H_NUM_CHNL),
    .C_NUMQ_PER_CHNL    (C_NUMQ_PER_CHNL),
    .C_SLAVE_READ_64OS_EN      (C_SLAVE_READ_64OS_EN),
    .C_NUM_PCIE_DSC_CPL_DID    (C_NUM_PCIE_DSC_CPL_DID),
    .C_NUM_AXI_DSC_CPL_DID     (C_NUM_AXI_DSC_CPL_DID),
    .H2C_DAT_DEPTH      (512),
    .C2H_DAT_DEPTH      (512),
    .MASTER_RD_DEPTH    (512),
    .ECC_ENABLE         (C_ECC_ENABLE),
    .ENABLE_ERROR_INJECTION(ENABLE_ERROR_INJECTION)
) ram_top (

    .user_clk                     (user_clk),
    .user_reset                   (user_reset),

    .mi_hw_ctxt                   (mi_hw_ctxt),
    .mi_sw_ctxt                   (mi_sw_ctxt),
    .mi_dsc_crd_rcv               (mi_dsc_crd_rcv),
    .mi_wb_base_ctxt              (mi_wb_base_ctxt),
                                                                
    .mi_h2c_pcie_dsc_cpli         (mi_h2c_pcie_dsc_cpli),
    .mi_h2c_pcie_dsc_cpld         (mi_h2c_pcie_dsc_cpld),
                                                                
    .mi_h2c_axi_dsc_cpli          (mi_h2c_axi_dsc_cpli),
    .mi_h2c_axi_dsc_cpld          (mi_h2c_axi_dsc_cpld),
                                                                
    .mi_c2h_pcie_dsc_cpli         (mi_c2h_pcie_dsc_cpli),
    .mi_c2h_pcie_dsc_cpld         (mi_c2h_pcie_dsc_cpld),
                                                                
    .mi_c2h_axi_dsc_cpli          (mi_c2h_axi_dsc_cpli),
    .mi_c2h_axi_dsc_cpld          (mi_c2h_axi_dsc_cpld),
                                  
    .mi_h2c0_dat                  (mi_h2c0_dat),
    .mi_h2c1_dat                  (mi_h2c1_dat),
    .mi_h2c2_dat                  (mi_h2c2_dat),
    .mi_h2c3_dat                  (mi_h2c3_dat),
                                                                
    .mi_c2h0_dat                  (mi_c2h0_dat),
    .mi_c2h1_dat                  (mi_c2h1_dat),
    .mi_c2h2_dat                  (mi_c2h2_dat),
    .mi_c2h3_dat                  (mi_c2h3_dat),

    .mi_h2c_rd_brg_dat            (mi_h2c_rd_brg_dat),
    .mi_h2c_wr_brg_dat            (mi_h2c_wr_brg_dat),

    .mi_c2h_rd_brg_dat            (mi_c2h_rd_brg_dat),
    .mi_c2h_wr_brg_dat            (mi_c2h_wr_brg_dat)
);

   assign s_axis_c2h_tready_1 = 1'b0;
   assign s_axis_c2h_tready_2 = 1'b0;
   assign s_axis_c2h_tready_3 = 1'b0;
//   assign s_axis_c2h_tuser_1 = 1'b0;
//   assign s_axis_c2h_tuser_2 = 1'b0;
//   assign s_axis_c2h_tuser_3 = 1'b0;
//   assign s_axis_c2h_tkeep_1 = 1'b0;
//   assign s_axis_c2h_tkeep_2 = 1'b0;
//   assign s_axis_c2h_tkeep_3 = 1'b0;
   assign c2h_dsc_byp_ready_1 = 1'b0;
   assign c2h_dsc_byp_ready_2 = 1'b0;
   assign c2h_dsc_byp_ready_3 = 1'b0;

   assign m_axis_h2c_tdata_1 = {C_M_AXIS_DATA_WIDTH{1'h0}};
   assign m_axis_h2c_tlast_1 = 1'b0;
   assign m_axis_h2c_tvalid_1 = 1'b0;
   assign m_axis_h2c_tdata_2 = {C_M_AXIS_DATA_WIDTH{1'h0}};
   assign m_axis_h2c_tlast_2 = 1'b0;
   assign m_axis_h2c_tvalid_2 = 1'b0;
   assign m_axis_h2c_tdata_3 = {C_M_AXIS_DATA_WIDTH{1'h0}};
   assign m_axis_h2c_tlast_3 = 1'b0;
   assign m_axis_h2c_tvalid_3 = 1'b0;
   assign h2c_dsc_byp_ready_1 = 1'b0;
   assign h2c_dsc_byp_ready_2 = 1'b0;
   assign h2c_dsc_byp_ready_3 = 1'b0;

  pcie_bridge_rc_pcie4c_ip  pcie4c_ip_i (


    //---------------------------------------------------------------------------------------//
    //  PCI Express (pci_exp) Interface                                                      //
    //---------------------------------------------------------------------------------------//

    // Tx
    .pci_exp_txn                                    ( pci_exp_txn ),
    .pci_exp_txp                                    ( pci_exp_txp ),

    // Rx
    .pci_exp_rxn                                    ( pci_exp_rxn ),
    .pci_exp_rxp                                    ( pci_exp_rxp ),

    //---------------------------------------------------------------------------------------//
    //  AXI Interface                                                                        //
    //---------------------------------------------------------------------------------------//
    .user_clk                                       ( user_clk),
    .user_reset                                     ( user_reset ),
    .user_lnk_up                                    ( user_lnk_up ),
    .phy_rdy_out                                    ( phy_ready ),
    .s_axis_rq_tlast                                ( axis_rq.tlast ),
    .s_axis_rq_tdata                                ( axis_rq.tdata ),
    .s_axis_rq_tuser                                ( axis_rq.tuser ),
    .s_axis_rq_tkeep                                ( axis_rq.tkeep ),
    .s_axis_rq_tready                               ( axis_rq_tready ),
    .s_axis_rq_tvalid                               ( axis_rq.tvalid ),

    .m_axis_rc_tdata                                ( axis_rc.tdata ),
    .m_axis_rc_tuser                                ( axis_rc.tuser ),
    .m_axis_rc_tlast                                ( axis_rc.tlast ),
    .m_axis_rc_tkeep                                ( axis_rc.tkeep ),
    .m_axis_rc_tvalid                               ( axis_rc.tvalid ),
    .m_axis_rc_tready                               ( m_axis_rc_tready_rst ),

    .m_axis_cq_tdata                                ( axis_cq.tdata ),
    .m_axis_cq_tuser                                ( axis_cq.tuser ),
    .m_axis_cq_tlast                                ( axis_cq.tlast ),
    .m_axis_cq_tkeep                                ( axis_cq.tkeep ),
    .m_axis_cq_tvalid                               ( axis_cq.tvalid ),
    .m_axis_cq_tready                               ( axis_cq.tready[0] ),

    .s_axis_cc_tdata                                ( axis_cc.tdata ),
    .s_axis_cc_tuser                                ( axis_cc.tuser ),
    .s_axis_cc_tlast                                ( axis_cc.tlast ),
    .s_axis_cc_tkeep                                ( axis_cc.tkeep ),
    .s_axis_cc_tvalid                               ( axis_cc.tvalid ),
    .s_axis_cc_tready                               ( s_axis_cc_tready ),
    .pcie_rq_seq_num0                               ( pcie_rq_seq_num0 ), //N
    .pcie_rq_seq_num_vld0                           ( pcie_rq_seq_num_vld0 ),//N
    .pcie_rq_seq_num1                               ( pcie_rq_seq_num1 ),//N
    .pcie_rq_seq_num_vld1                           ( pcie_rq_seq_num_vld1 ),//N
    .pcie_rq_tag0                                   ( ),//N
    .pcie_rq_tag1                                   ( ),//N
    .pcie_rq_tag_av                                 ( ),
    .pcie_rq_tag_vld0                               ( ),//N
    .pcie_rq_tag_vld1                               ( ),//N

    .pcie_tfc_nph_av                                ( pcie_tfc_nph_av ),
    .pcie_tfc_npd_av                                ( pcie_tfc_npd_av ),
    .pcie_cq_np_req                                 ( pcie_cq_np_req ),
    .pcie_cq_np_req_count                           ( pcie_cq_np_req_count ),

    //---------------------------------------------------------------------------------------//
    //  Configuration (CFG) Interface                                                        //
    //---------------------------------------------------------------------------------------//

    //-------------------------------------------------------------------------------//
    // EP and RP                                                                     //
    //-------------------------------------------------------------------------------//

    .cfg_phy_link_down                              ( cfg_phy_link_down ),
    .cfg_phy_link_status                            ( cfg_phy_link_status ),
    .cfg_negotiated_width                           ( cfg_negotiated_width ),
    .cfg_current_speed                              ( cfg_current_speed ),
    .cfg_max_payload                                ( cfg_max_payload ),
    .cfg_max_read_req                               ( cfg_max_read_req ),
    .cfg_function_status                            ( cfg_function_status ),
    .cfg_function_power_state                       ( cfg_function_power_state ),
    .cfg_vf_status                                  (),
    .cfg_vf_power_state                             (),
    .cfg_link_power_state                           ( cfg_link_power_state ),

    // Management Interface
     .cfg_mgmt_read_data           ( cfg_mgmt_read_data_int ),
     .cfg_mgmt_read_write_done     ( cfg_mgmt_read_write_done_int ),
     .cfg_mgmt_addr                ( cfg_mgmt_addr_int[9:0] ),
     .cfg_mgmt_write               ( cfg_mgmt_write_int ),
     .cfg_mgmt_write_data          ( cfg_mgmt_write_data_int ),
     .cfg_mgmt_byte_enable         ( cfg_mgmt_byte_enable_int ),
     .cfg_mgmt_read                ( cfg_mgmt_read_int ),
     .cfg_mgmt_debug_access        ( cfg_mgmt_type1_cfg_reg_access_int ),
     .cfg_mgmt_function_number     ( cfg_mgmt_function_number ),
    // Error Reporting Interface
    .cfg_err_cor_out                                ( cfg_err_cor_out ),
    .cfg_err_nonfatal_out                           ( cfg_err_nonfatal_out ),
    .cfg_err_fatal_out                              ( cfg_err_fatal_out ),
    .cfg_local_error_valid                          ( cfg_local_error_valid ), //N
    .cfg_local_error_out                            ( cfg_local_error ), //N

    .cfg_ltssm_state                                ( cfg_ltssm_state ),
    .cfg_rx_pm_state                                (  ), //N
    .cfg_tx_pm_state                                (  ), //N
    .cfg_rcb_status                                 ( cfg_rcb_status ),
    .cfg_obff_enable                                ( cfg_obff_enable ),
    .cfg_pl_status_change                           ( cfg_pl_status_change ),

    .cfg_msg_received                               ( cfg_msg_received ),
    .cfg_msg_received_data                          ( cfg_msg_received_data ),
    .cfg_msg_received_type                          ( cfg_msg_received_type ),

    .cfg_msg_transmit                               ( cfg_msg_transmit ),
    .cfg_msg_transmit_type                          ( cfg_msg_transmit_type ),
    .cfg_msg_transmit_data                          ( cfg_msg_transmit_data ),
    .cfg_msg_transmit_done                          ( cfg_msg_transmit_done ),

    .cfg_fc_ph                                      ( cfg_fc_ph ),
    .cfg_fc_pd                                      ( cfg_fc_pd ),
    .cfg_fc_nph                                     ( cfg_fc_nph ),
    .cfg_fc_npd                                     ( cfg_fc_npd ),
    .cfg_fc_cplh                                    ( cfg_fc_cplh ),
    .cfg_fc_cpld                                    ( cfg_fc_cpld ),
    .cfg_fc_sel                                     ( cfg_fc_sel ),

    .cfg_bus_number                                 (  ), //N
    .cfg_dsn                                        ( cfg_dsn ),
    .cfg_power_state_change_ack                     ( cfg_power_state_change_interrupt ),
    .cfg_power_state_change_interrupt               ( cfg_power_state_change_interrupt ),
    .cfg_err_cor_in                                 ( cfg_err_cor_in ),
    .cfg_err_uncor_in                               ( cfg_err_uncor_in ),

    .cfg_link_training_enable                       ( cfg_link_training_enable ),
    .cfg_tph_requester_enable                       (),
    .cfg_tph_st_mode                                (),
    .cfg_vf_tph_requester_enable                    (),
    .cfg_vf_tph_st_mode                             (),
    .cfg_flr_in_process                             (),
    .cfg_vf_flr_in_process                          (),
    .cfg_vf_flr_func_num                            ( 8'b0 ), //N
    .cfg_pm_aspm_l1_entry_reject                    ( 1'b0 ), //N
    .cfg_pm_aspm_tx_l0s_entry_disable               ( 1'b0 ), //N
    //-------------------------------------------------------------------------------//
    // EP Only                                                                       //
    //-------------------------------------------------------------------------------//

    // Interrupt Interface Signals
    .cfg_interrupt_int                              ( cfg_interrupt_int ),
    .cfg_interrupt_pending                          ( cfg_interrupt_pending ),
    .cfg_interrupt_sent                             ( cfg_interrupt_sent ),

     // EP only
    .cfg_flr_done                                   ( 4'b0 ),
    .cfg_vf_flr_done                                ( 1'b0 ),
    .cfg_hot_reset_out                              ( cfg_hot_reset_out ),
    .cfg_config_space_enable                        ( 1'b1 ),
    .cfg_req_pm_transition_l23_ready                ( cfg_req_pm_transition_l23_ready ),

    // RP only
    .cfg_hot_reset_in                               ( 1'b0 ),

    .cfg_ds_bus_number                              ( cfg_ds_bus_number ),
    .cfg_ds_device_number                           ( cfg_ds_device_number ),
    .cfg_ds_port_number                             ( cfg_ds_port_number ),

    .common_commands_in                        (common_commands_in ),
    .pipe_rx_0_sigs                            (pipe_rx_0_sigs     ),
    .pipe_rx_1_sigs                            (pipe_rx_1_sigs     ),
    .pipe_rx_2_sigs                            (pipe_rx_2_sigs     ),
    .pipe_rx_3_sigs                            (pipe_rx_3_sigs     ),
    .pipe_rx_4_sigs                            (pipe_rx_4_sigs     ),
    .pipe_rx_5_sigs                            (pipe_rx_5_sigs     ),
    .pipe_rx_6_sigs                            (pipe_rx_6_sigs     ),
    .pipe_rx_7_sigs                            (pipe_rx_7_sigs     ),
    .pipe_rx_8_sigs                            (pipe_rx_8_sigs     ),
    .pipe_rx_9_sigs                            (pipe_rx_9_sigs     ),
    .pipe_rx_10_sigs                           (pipe_rx_10_sigs     ),
    .pipe_rx_11_sigs                           (pipe_rx_11_sigs     ),
    .pipe_rx_12_sigs                           (pipe_rx_12_sigs     ),
    .pipe_rx_13_sigs                           (pipe_rx_13_sigs     ),
    .pipe_rx_14_sigs                           (pipe_rx_14_sigs     ),
    .pipe_rx_15_sigs                           (pipe_rx_15_sigs     ),

    .common_commands_out                       (common_commands_out),
    .pipe_tx_0_sigs                            (pipe_tx_0_sigs     ),
    .pipe_tx_1_sigs                            (pipe_tx_1_sigs     ),
    .pipe_tx_2_sigs                            (pipe_tx_2_sigs     ),
    .pipe_tx_3_sigs                            (pipe_tx_3_sigs     ),
    .pipe_tx_4_sigs                            (pipe_tx_4_sigs     ),
    .pipe_tx_5_sigs                            (pipe_tx_5_sigs     ),
    .pipe_tx_6_sigs                            (pipe_tx_6_sigs     ),
    .pipe_tx_7_sigs                            (pipe_tx_7_sigs     ),
    .pipe_tx_8_sigs                            (pipe_tx_8_sigs     ),
    .pipe_tx_9_sigs                            (pipe_tx_9_sigs     ),
    .pipe_tx_10_sigs                           (pipe_tx_10_sigs     ),
    .pipe_tx_11_sigs                           (pipe_tx_11_sigs     ),
    .pipe_tx_12_sigs                           (pipe_tx_12_sigs     ),
    .pipe_tx_13_sigs                           (pipe_tx_13_sigs     ),
    .pipe_tx_14_sigs                           (pipe_tx_14_sigs     ),
    .pipe_tx_15_sigs                           (pipe_tx_15_sigs     ),






    //--------------------------------------------------------------------------------------//
    //  System(SYS) Interface                                                               //
    //--------------------------------------------------------------------------------------//
    .sys_clk                                  (sys_clk),
    .sys_clk_gt                               (sys_clk_gt),
    .sys_reset                                (sys_rst_n)    // despite of postfix "_n" in its name - this signal can be active high/low depending on GUI selection
  );

// Instantiation of the AXI BRAM Controller block interfaced with PCIE4C IP 



   //assign m_axib_wuser = {C_M_AXI_DATA_WIDTH/8{1'b0}};

   assign ext_ch_gt_drpclk = 1'b0;
   assign ext_ch_gt_drprdy = {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
   assign ext_ch_gt_drpdo  = {PL_LINK_CAP_MAX_LINK_WIDTH*16{1'b0}};

   assign drp_rdy = 1'b0;
   assign drp_do  = 16'b0;
   assign  blk_cfg_ext_read_received = 1'b0;
   assign  blk_cfg_ext_write_received = 1'b0;
   assign  blk_cfg_ext_register_number = 10'b0;
   assign  blk_cfg_ext_function_number = 8'b0;
   assign  blk_cfg_ext_write_data = 32'b0;
   assign  blk_cfg_ext_write_byte_enable = 4'b0;
   //  Tie-off unused mcap outputs
   assign mcap_design_switch = 1'b1;
   assign cap_req = 1'b0;

   //  Tie-off unused Startup Signals
   assign startup_cfgclk = 1'b0;
   assign startup_cfgmclk = 1'b0;
   assign startup_di = 4'b0000;
   assign startup_eos = 1'b0;
   assign startup_preq = 1'b0;



endmodule
