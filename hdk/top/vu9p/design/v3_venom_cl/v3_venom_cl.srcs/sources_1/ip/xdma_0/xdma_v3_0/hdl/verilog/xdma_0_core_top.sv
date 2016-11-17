//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : The Xilinx PCI Express DMA 
// File       : xdma_0_core_top.sv
// Version    : $IpVersion 
//-----------------------------------------------------------------------------

`timescale 1ns/1ps
`include "xdma_axi4mm_axi_bridge.vh"
`include "dma_defines.vh"
`include "dma_defines.svh"
module xdma_0_core_top #(
        parameter       COMPONENT_NAME               = "xdma_0",
        parameter       PL_UPSTREAM_FACING           = "TRUE",
        parameter       TL_LEGACY_MODE_ENABLE        = "FALSE",
        parameter       PCIE_BLK_LOCN                = 0,
        parameter       PL_LINK_CAP_MAX_LINK_WIDTH   = 1,
        parameter       PL_LINK_CAP_MAX_LINK_SPEED   = 1,
        parameter       REF_CLK_FREQ                 = 0,
        parameter       AXI_ADDR_WIDTH               = 32,
        parameter       AXI_DATA_WIDTH               = 64,
        parameter       CORE_CLK_FREQ                = 2,
        parameter       PLL_TYPE                     = 0,
        parameter       USER_CLK_FREQ                = 1,
        parameter       SILICON_REV                  = "Production",
        parameter       PIPE_SIM                     = "FALSE",
        parameter       EXT_CH_GT_DRP                = "FALSE",
        parameter       PCIE3_DRP                    = "FALSE",
        parameter       DEDICATE_PERST               = "TRUE",
        parameter       SYS_RESET_POLARITY           = 0,
        parameter       MCAP_ENABLEMENT              = "NONE",
        parameter       EXT_STARTUP_PRIMITIVE        = "FALSE",
        parameter       PF0_VENDOR_ID                = 16'h10EE,
        parameter       PF0_DEVICE_ID                = 16'h7011,
        parameter       PF0_REVISION_ID              = 8'h00,
        parameter       PF0_SUBSYSTEM_VENDOR_ID      = 16'h10EE,
        parameter       PF0_SUBSYSTEM_ID             = 16'h0007,
        parameter       PF0_CLASS_CODE               = 24'h058000,
        parameter       AXILITE_MASTER_APERTURE_SIZE = 5'b00101,
        parameter       AXILITE_MASTER_CONTROL       = 3'b100,
        parameter       XDMA_APERTURE_SIZE           = 5'b00101,
        parameter       XDMA_CONTROL                 = 3'b000,
        parameter       AXIST_BYPASS_APERTURE_SIZE   = 5'b00101,
        parameter       AXIST_BYPASS_CONTROL         = 3'b000,
        parameter       C_PCIEBAR2AXIBAR_0           = 64'h0000000000000000,
        parameter       C_PCIEBAR2AXIBAR_1           = 64'h0000000000000000,
        parameter       C_PCIEBAR2AXIBAR_2           = 64'h0000000000000000,
        parameter       PF0_INTERRUPT_PIN            = 3'b001,
        parameter       PF0_MSI_CAP_MULTIMSGCAP      = 0,
        parameter       C_COMP_TIMEOUT               = 0,
        parameter       SHARED_LOGIC                 = 1,
        parameter       SHARED_LOGIC_CLK             = "FALSE",
        parameter       SHARED_LOGIC_BOTH            = "FALSE",
        parameter       SHARED_LOGIC_GTC             = "FALSE",
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
	parameter	C_FAMILY	             = "virtex7",
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
	parameter	DSC_BYPASS_RD	             = 0,
	parameter	DSC_BYPASS_WR		     = 0,
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
	parameter	C_PARITY_CHECK 		     = 1,
        parameter	C_PARITY_GEN	             = 1,
	parameter	C_PARITY_PROP		     = 0,
        parameter       EN_DEBUG_PORTS               = "FALSE",
        parameter       VU9P_BOARD                   = "FALSE",
        parameter       ENABLE_JTAG_DBG              = "FALSE",
        parameter       MM_SLAVE_EN                  = 0,
        parameter       DMA_EN                       = 1,
        parameter       C_AXIBAR_NUM                 = 1,
        parameter       C_AXIBAR_0                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_0          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR_1                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_1          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR_2                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_2          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR_3                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_3          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR_4                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_4          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR_5                   = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR_HIGHADDR_5          = 64'hffff_ffff_ffff_ffff,
        parameter       C_AXIBAR2PCIEBAR_0           = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR2PCIEBAR_1           = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR2PCIEBAR_2           = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR2PCIEBAR_3           = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR2PCIEBAR_4           = 64'h0000_0000_0000_0000,
        parameter       C_AXIBAR2PCIEBAR_5           = 64'h0000_0000_0000_0000,
        parameter       EN_AXI_SLAVE_IF              = "TRUE",
        parameter       EN_AXI_MASTER_IF             = "TRUE",
        parameter       C_INCLUDE_BAROFFSET_REG      = 1,
        parameter [31:0]  C_BASEADDR                 = 32'hFFFF_FFFF,  
        parameter [31:0]  C_HIGHADDR                 = 32'h0000_0000,   
        parameter       C_S_AXI_NUM_READ             = 32,
        parameter       C_M_AXI_NUM_READ             = 8,
        parameter       C_S_AXI_NUM_WRITE            = 8,
        parameter       C_M_AXI_NUM_WRITE            = 8,
        parameter       MSIX_IMPL_EXT                = "TRUE",
        parameter       AXI_ACLK_LOOPBACK            = "FALSE",
        parameter       PL_DISABLE_UPCONFIG_CAPABLE  = "FALSE",
        parameter       C_INCLUDE_RC                 = 0,
	parameter	TCQ			     = 1,
        parameter       C_AXIBAR_AS_0                = 0,
        parameter       C_AXIBAR_AS_1                = 0,
        parameter       C_AXIBAR_AS_2                = 0,
        parameter       C_AXIBAR_AS_3                = 0,
        parameter       C_AXIBAR_AS_4                = 0,
        parameter       C_AXIBAR_AS_5                = 0,
        parameter       C_MSI_ENABLED                = MSI_ENABLED,
	parameter	C_DEVICE_NUMBER		     = 0, //Device number for Root Port configurations only
	parameter	C_S_AXI_ID_WIDTH	     = 4,
	parameter	C_S_AXI_ADDR_WIDTH           = AXI_ADDR_WIDTH,
	parameter	C_S_AXI_DATA_WIDTH	     = AXI_DATA_WIDTH,
	parameter	C_M_AXI_ADDR_WIDTH           = AXI_ADDR_WIDTH,
	parameter	C_M_AXI_DATA_WIDTH	     = AXI_DATA_WIDTH,
	parameter	C_S_AXIS_DATA_WIDTH	     = AXI_DATA_WIDTH,
	parameter	C_M_AXIS_DATA_WIDTH	     = AXI_DATA_WIDTH,
	parameter	C_M_AXIS_RQ_USER_WIDTH	     = 137,
        parameter	C_S_AXIS_CQP_USER_WIDTH	     = 183,
	parameter	C_S_AXIS_CQ_USER_WIDTH	     = 183,
	parameter	C_M_AXIS_RC_USER_WIDTH       = 161,
	parameter	C_S_AXIS_CC_USER_WIDTH	     = 81,
	parameter	C_M_AXIL_AWUSER_WIDTH	     = 11,
	parameter	C_M_AXIL_ARUSER_WIDTH	     = 11,
	parameter	C_M_AXI_AWUSER_WIDTH	     = 8,
	parameter	C_M_AXI_ARUSER_WIDTH	     = 8,
	parameter	C_S_KEEP_WIDTH		     = C_S_AXI_DATA_WIDTH / 32,
	parameter	C_M_KEEP_WIDTH		     = C_M_AXI_DATA_WIDTH / 32,
        parameter       C_KEEP_WIDTH                 = AXI_DATA_WIDTH/8,
	parameter	C_S_AXIS_USER_WIDTH	     = 64,
	parameter	C_M_AXIS_USER_WIDTH	     = 64,
	parameter	C_ADDR_ALGN      	     = 1, // Bytes
	parameter	C_ECC_ENABLE	             = 0,
	parameter	C_DSC_MAGIC_EN		     = 1,
	parameter	C_RD_BUFFER_ADDR_SIZE	     = 9,
	parameter	C_RD_BUFFER_SIZE_BITS	     = 5,
	parameter	C_PCIEBAR_NUM		     = 6,
	parameter	C_PCIEBAR_AS		     = 1,
        parameter	C_NUM_MSIX_VECTORS           = 32,
	parameter	DMA_SP 		             = 0,
	parameter	DMA_MM 			     = 1,
	parameter	DMA_ST 			     = 0,
	parameter	C_ADDR_BITS		     = 64,
	parameter	STS_WIDTH	             = 8,
	parameter       BACKPRESSURE                 = 0,
	parameter       USR_MPL_SIZE                 = 4096,
	parameter       USR_MRS_SIZE                 = 4096,
	parameter       PMON_EN                      = 1,
	parameter	CDC_WB_EN	             = 1
)
(
  sys_clk,
  sys_clk_gt,
  sys_rst_n,
  user_lnk_up,

  pci_exp_txp,
  pci_exp_txn,
  pci_exp_rxp,
  pci_exp_rxn,

  axi_aclk,
  axi_aresetn,

  axi_ctl_aclk,
  axi_ctl_aresetn,

  usr_irq_req,
  usr_irq_ack,
  msi_enable,
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
  s_axi_awid,
  s_axi_awaddr,
  s_axi_awregion,
  s_axi_awlen,
  s_axi_awsize,
  s_axi_awburst,
  s_axi_awvalid,
  s_axi_awready,
  s_axi_wdata,
  s_axi_wdataeccparity,
  s_axi_wstrb,
  s_axi_wlast,
  s_axi_wvalid,
  s_axi_wready,
  s_axi_bid,
  s_axi_bresp,
  s_axi_bvalid,
  s_axi_bready,
  s_axi_arid,
  s_axi_araddr,
  s_axi_arregion,
  s_axi_arlen,
  s_axi_arsize,
  s_axi_arburst,
  s_axi_arvalid,
  s_axi_arready,
  s_axi_rid,
  s_axi_rresp,
  s_axi_rlast,
  s_axi_rvalid,
  s_axi_rdata,
  s_axi_rdataeccparity,
  s_axi_rready,
  interrupt_out,

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
  //    - This singal should be driven directly by the End of Startup (EOS) output of     //
  //      the STARTUP primitive                                                           //
  //--------------------------------------------------------------------------------------//
  mcap_eos_in,
  //--------------------------------------------------------------------------------------//
  //  Startup Signals                                                                     //
  //    - The startup interface is exposed to the external user for connectifity to other //
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
    
  pipe_tx0_rcvr_det,
  pipe_clk,
  sys_clk_bufg,
  pipe_tx0_powerdown,
  cfg_ltssm_state,
  cfg_function_status,
  cfg_max_read_req,
  cfg_max_payload,
  cfg_err_uncor_in,
  cfg_flr_done,
  cfg_flr_in_process,
  cfg_vf_flr_in_process,
  cfg_vf_flr_func_num,
  cfg_vf_flr_done,
  cfg_interrupt_msi_enable,
  cfg_interrupt_msix_enable

);

output  wire   [3:0]   cfg_interrupt_msi_enable;
output  wire   [3:0]   cfg_interrupt_msix_enable;

   input  wire [25:0] common_commands_in;
   input  wire [83:0] pipe_rx_0_sigs;
   input  wire [83:0] pipe_rx_1_sigs;
   input  wire [83:0] pipe_rx_2_sigs;
   input  wire [83:0] pipe_rx_3_sigs;
   input  wire [83:0] pipe_rx_4_sigs;
   input  wire [83:0] pipe_rx_5_sigs;
   input  wire [83:0] pipe_rx_6_sigs;
   input  wire [83:0] pipe_rx_7_sigs;
   input  wire [83:0] pipe_rx_8_sigs;
   input  wire [83:0] pipe_rx_9_sigs;
   input  wire [83:0] pipe_rx_10_sigs;
   input  wire [83:0] pipe_rx_11_sigs;
   input  wire [83:0] pipe_rx_12_sigs;
   input  wire [83:0] pipe_rx_13_sigs;
   input  wire [83:0] pipe_rx_14_sigs;
   input  wire [83:0] pipe_rx_15_sigs;
   output wire [25:0] common_commands_out;
   output wire [83:0] pipe_tx_0_sigs;
   output wire [83:0] pipe_tx_1_sigs;
   output wire [83:0] pipe_tx_2_sigs;
   output wire [83:0] pipe_tx_3_sigs;
   output wire [83:0] pipe_tx_4_sigs;
   output wire [83:0] pipe_tx_5_sigs;
   output wire [83:0] pipe_tx_6_sigs;
   output wire [83:0] pipe_tx_7_sigs;
   output wire [83:0] pipe_tx_8_sigs;
   output wire [83:0] pipe_tx_9_sigs;
   output wire [83:0] pipe_tx_10_sigs;
   output wire [83:0] pipe_tx_11_sigs;
   output wire [83:0] pipe_tx_12_sigs;
   output wire [83:0] pipe_tx_13_sigs;
   output wire [83:0] pipe_tx_14_sigs;
   output wire [83:0] pipe_tx_15_sigs;

   input [18:0]	      cfg_mgmt_addr;
   input	      cfg_mgmt_write;
   input  [31:0]      cfg_mgmt_write_data;
   input  [3:0]       cfg_mgmt_byte_enable;
   input	      cfg_mgmt_read;
   output [31:0]      cfg_mgmt_read_data;
   output 	      cfg_mgmt_read_write_done;
   input	      cfg_mgmt_type1_cfg_reg_access;

   output  	      axi_aclk;
   output  	      axi_aresetn;

   input  	      axi_ctl_aclk;
   output  	      axi_ctl_aresetn;

   input   [XDMA_NUM_USR_IRQ-1:0]	usr_irq_req;
   output  [XDMA_NUM_USR_IRQ-1:0]	usr_irq_ack;
   output  				msi_enable;
   output  [2 : 0] 			msi_vector_width;

   output  [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_awid;
   output  [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_awaddr;
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
   output  [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_araddr;
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
   output  [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_awaddr;
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
   output  [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_araddr ;
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
   input	[C_S_AXIS_DATA_WIDTH-1:0]	s_axis_c2h_tdata_0;
   input					s_axis_c2h_tlast_0;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tuser_0;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tkeep_0;
   input					s_axis_c2h_tvalid_0;
   output					s_axis_c2h_tready_0;
   // C2H AXI ST interface to user Channle 1
   input	[C_S_AXIS_DATA_WIDTH-1:0]	s_axis_c2h_tdata_1;
   input					s_axis_c2h_tlast_1;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tuser_1;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tkeep_1;
   input					s_axis_c2h_tvalid_1;
   output					s_axis_c2h_tready_1;
   // C2H AXI ST interface to user Channle 2
   input	[C_S_AXIS_DATA_WIDTH-1:0]	s_axis_c2h_tdata_2;
   input					s_axis_c2h_tlast_2;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tuser_2;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tkeep_2;
   input					s_axis_c2h_tvalid_2;
   output					s_axis_c2h_tready_2;
   // C2H AXI ST interface to user Channle 3
   input	[C_S_AXIS_DATA_WIDTH-1:0]	s_axis_c2h_tdata_3;
   input					s_axis_c2h_tlast_3;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tuser_3;
   input	[C_S_AXIS_DATA_WIDTH/8-1:0]	s_axis_c2h_tkeep_3;
   input					s_axis_c2h_tvalid_3;
   output					s_axis_c2h_tready_3;

   // H2C AXI ST interface to user Channel 0
   output	[C_M_AXIS_DATA_WIDTH-1:0]	m_axis_h2c_tdata_0;
   output					m_axis_h2c_tlast_0;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tuser_0;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tkeep_0;
   output					m_axis_h2c_tvalid_0;
   input					m_axis_h2c_tready_0;
   // H2C AXI ST interface to user Channel 1
   output	[C_M_AXIS_DATA_WIDTH-1:0]	m_axis_h2c_tdata_1;
   output					m_axis_h2c_tlast_1;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tuser_1;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tkeep_1;
   output					m_axis_h2c_tvalid_1;
   input					m_axis_h2c_tready_1;
   // H2C AXI ST interface to user Channel 2
   output	[C_M_AXIS_DATA_WIDTH-1:0]	m_axis_h2c_tdata_2;
   output					m_axis_h2c_tlast_2;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tuser_2;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tkeep_2;
   output					m_axis_h2c_tvalid_2;
   input					m_axis_h2c_tready_2;
   // H2C AXI ST interface to user Channel 3
   output	[C_M_AXIS_DATA_WIDTH-1:0]	m_axis_h2c_tdata_3;
   output					m_axis_h2c_tlast_3;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tuser_3;
   output	[C_M_AXIS_DATA_WIDTH/8-1:0]	m_axis_h2c_tkeep_3;
   output					m_axis_h2c_tvalid_3;
   input					m_axis_h2c_tready_3;

   output  [31 : 0]			m_axil_awaddr;
   output  [C_M_AXIL_AWUSER_WIDTH-1: 0] m_axil_awuser;
   output  [2 : 0] 			m_axil_awprot;
   output  				m_axil_awvalid;
   input  				m_axil_awready;
   output  [31 : 0]                     m_axil_wdata;
   output  [3 : 0]                      m_axil_wstrb;
   output  				m_axil_wvalid;
   input  				m_axil_wready;
   input  				m_axil_bvalid;
   input  [1:0]			        m_axil_bresp;
   output  				m_axil_bready;
   output  [31 : 0]			m_axil_araddr;
   output  [C_M_AXIL_ARUSER_WIDTH-1: 0] m_axil_aruser;
   output  [2 : 0]			m_axil_arprot;
   output  				m_axil_arvalid;
   input  				m_axil_arready;
   input  [31 : 0] m_axil_rdata ;
   input  [1 : 0] 			m_axil_rresp ;
   input  				m_axil_rvalid;
   output  				m_axil_rready;
   input  [31 : 0]			s_axil_awaddr;
   input  [2 : 0] 			s_axil_awprot;
   input  				s_axil_awvalid;
   output  				s_axil_awready;
   input  [31 : 0] s_axil_wdata ;
   input  [3 : 0] s_axil_wstrb ;
   input  				s_axil_wvalid;
   output  				s_axil_wready;
   output  				s_axil_bvalid;
   output  [1:0]			s_axil_bresp;
   input  				s_axil_bready;
   input  [31 : 0]			s_axil_araddr;
   input  [2 : 0]			s_axil_arprot;
   input  				s_axil_arvalid;
   output  				s_axil_arready;
   output  [31 : 0] s_axil_rdata ;
   output  [1 : 0] 			s_axil_rresp;
   output  				s_axil_rvalid;
   input  				s_axil_rready;
//-- AXI Slave Write Address Channel
   input [C_S_AXI_ID_WIDTH-1:0] 	s_axi_awid;
   input [C_S_AXI_ADDR_WIDTH-1:0] 	s_axi_awaddr;
   input [3:0] 			        s_axi_awregion;
   input [7:0] 			        s_axi_awlen;
   input [2:0] 			        s_axi_awsize;
   input [1:0] 			        s_axi_awburst;
   input 				s_axi_awvalid;
   output 				s_axi_awready;	
   //-- AXI Slave Write Data Channel
   input [C_S_AXI_DATA_WIDTH-1:0] 	s_axi_wdata;
   input [C_S_AXI_DATA_WIDTH/8-1:0] 	s_axi_wdataeccparity;
   input [C_S_AXI_DATA_WIDTH/8-1:0] 	s_axi_wstrb;
   input 				s_axi_wlast;
   input 				s_axi_wvalid;
   output 				s_axi_wready;
   //-- AXI Slave Write Response Channel
   output [C_S_AXI_ID_WIDTH-1:0] 	s_axi_bid;
   output [1:0] 			s_axi_bresp;
   output 				s_axi_bvalid;
   input 				s_axi_bready;
   //-- AXI Slave Read Address Channel
   input  [C_S_AXI_ID_WIDTH-1:0]       s_axi_arid;
   input  [C_S_AXI_ADDR_WIDTH-1:0]     s_axi_araddr;
   input  [3:0]                        s_axi_arregion;
   input  [7:0]                        s_axi_arlen;
   input  [2:0]                        s_axi_arsize;
   input  [1:0]                        s_axi_arburst;
   input                               s_axi_arvalid;
   output                              s_axi_arready;
   //-- AXI Slave Read Data Channel
   output [C_S_AXI_ID_WIDTH-1:0]       s_axi_rid;
   output [1:0]                        s_axi_rresp;
   output                              s_axi_rlast;
   output                              s_axi_rvalid;
   output [C_S_AXI_DATA_WIDTH-1:0]     s_axi_rdata;
   output [(C_S_AXI_DATA_WIDTH/8)-1:0] s_axi_rdataeccparity;
   input                               s_axi_rready;
   // Descriptor Bypass channel 0
   output       wire                    c2h_dsc_byp_ready_0;
   input        wire [63:0]             c2h_dsc_byp_src_addr_0;
   input        wire [63:0]             c2h_dsc_byp_dst_addr_0;
   input        wire [27:0]             c2h_dsc_byp_len_0;
   input        wire [15:0]             c2h_dsc_byp_ctl_0;
   input        wire                    c2h_dsc_byp_load_0;

   output       wire                    h2c_dsc_byp_ready_0;
   input        wire [63:0]             h2c_dsc_byp_src_addr_0;
   input        wire [63:0]             h2c_dsc_byp_dst_addr_0;
   input        wire [27:0]             h2c_dsc_byp_len_0;
   input        wire [15:0]             h2c_dsc_byp_ctl_0;
   input        wire                    h2c_dsc_byp_load_0;

   // Descriptor Bypass channel 1
   output       wire                    c2h_dsc_byp_ready_1;
   input        wire [63:0]             c2h_dsc_byp_src_addr_1;
   input        wire [63:0]             c2h_dsc_byp_dst_addr_1;
   input        wire [27:0]             c2h_dsc_byp_len_1;
   input        wire [15:0]             c2h_dsc_byp_ctl_1;
   input        wire                    c2h_dsc_byp_load_1;

   output       wire                    h2c_dsc_byp_ready_1;
   input        wire [63:0]             h2c_dsc_byp_src_addr_1;
   input        wire [63:0]             h2c_dsc_byp_dst_addr_1;
   input        wire [27:0]             h2c_dsc_byp_len_1;
   input        wire [15:0]             h2c_dsc_byp_ctl_1;
   input        wire                    h2c_dsc_byp_load_1;

   // Descriptor Bypass channel 2
   output       wire                    c2h_dsc_byp_ready_2;
   input        wire [63:0]             c2h_dsc_byp_src_addr_2;
   input        wire [63:0]             c2h_dsc_byp_dst_addr_2;
   input        wire [27:0]             c2h_dsc_byp_len_2;
   input        wire [15:0]             c2h_dsc_byp_ctl_2;
   input        wire                    c2h_dsc_byp_load_2;

   output       wire                    h2c_dsc_byp_ready_2;
   input        wire [63:0]             h2c_dsc_byp_src_addr_2;
   input        wire [63:0]             h2c_dsc_byp_dst_addr_2;
   input        wire [27:0]             h2c_dsc_byp_len_2;
   input        wire [15:0]             h2c_dsc_byp_ctl_2;
   input        wire                    h2c_dsc_byp_load_2;

   // Descriptor Bypass channel 3
   output       wire                    c2h_dsc_byp_ready_3;
   input        wire [63:0]             c2h_dsc_byp_src_addr_3;
   input        wire [63:0]             c2h_dsc_byp_dst_addr_3;
   input        wire [27:0]             c2h_dsc_byp_len_3;
   input        wire [15:0]             c2h_dsc_byp_ctl_3;
   input        wire                    c2h_dsc_byp_load_3;

   output       wire                    h2c_dsc_byp_ready_3;
   input        wire [63:0]             h2c_dsc_byp_src_addr_3;
   input        wire [63:0]             h2c_dsc_byp_dst_addr_3;
   input        wire [27:0]             h2c_dsc_byp_len_3;
   input        wire [15:0]             h2c_dsc_byp_ctl_3;
   input        wire                    h2c_dsc_byp_load_3;

   // Status Channel 0
   output	wire [STS_WIDTH-1:0]	c2h_sts_0;
   output	wire [STS_WIDTH-1:0]	h2c_sts_0;

   // Status Channel 1
   output	wire [STS_WIDTH-1:0]	c2h_sts_1;
   output	wire [STS_WIDTH-1:0]	h2c_sts_1;

   // Status Channel 2
   output	wire [STS_WIDTH-1:0]	c2h_sts_2;
   output	wire [STS_WIDTH-1:0]	h2c_sts_2;

   // Status Channel 3
   output	wire [STS_WIDTH-1:0]	c2h_sts_3;
   output	wire [STS_WIDTH-1:0]	h2c_sts_3;

   output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_txp ;
   output  [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_txn ;
   input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_rxp ;
   input   [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_rxn ;

   input  				sys_clk ;
   input  				sys_clk_gt ;
   input  				sys_rst_n  ;
   output  				user_lnk_up ;

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
  output  wire    interrupt_out;

  output                                            ext_ch_gt_drpclk ;
  input   [((PL_LINK_CAP_MAX_LINK_WIDTH *  9)-1):0] ext_ch_gt_drpaddr ;
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
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcieuserratedone ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_loopback         ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txprbsforceerr   ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txinhibit        ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  gt_txprbssel        ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  gt_rxprbssel        ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxprbscntreset   ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_dmonitorclk      ;
  input wire  [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_dmonfiforeset    ;
 
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txelecidle       ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txresetdone      ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxresetdone      ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxpmaresetdone   ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txphaligndone    ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txphinitdone     ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_txdlysresetdone  ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxphaligndone    ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxdlysresetdone  ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxsyncdone       ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_eyescandataerror ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxprbserr        ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*17)-1):0] gt_dmonitorout      ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxcommadet       ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_phystatus        ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxvalid          ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxcdrlock        ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcierateidle     ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_pcieuserratestart;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_gtpowergood      ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_cplllock         ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxoutclk         ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*1)-1):0]  gt_rxrecclkout      ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll1lock        ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_rxstatus         ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  gt_rxbufstatus      ;
  output wire [8:0]                                   gt_bufgtdiv         ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*2)-1):0]  phy_txeq_ctrl       ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*4)-1):0]  phy_txeq_preset     ;
  output wire [3:0]                                   phy_rst_fsm         ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  phy_txeq_fsm        ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH*3)-1):0]  phy_rxeq_fsm        ;
  output wire                                         phy_rst_idle        ;
  output wire                                         phy_rrst_n          ;
  output wire                                         phy_prst_n          ;
  output wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] gt_qpll0lock        ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_gen34_eios_det   ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclk         ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclkfabric   ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxoutclkfabric   ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txoutclkpcs      ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxoutclkpcs      ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpmareset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxpmareset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpcsreset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxpcsreset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxbufreset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxcdrreset       ;
  input  wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxdfelpmreset     ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txprogdivresetdone;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txpmaresetdone   ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_txsyncdone       ;
  output wire [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]        gt_rxprbslocked     ;

  // mcap and startup signals.
  output wire                                        mcap_design_switch;
  input  wire                                        mcap_eos_in;
  output wire                                        cap_req;
  input  wire                                        cap_gnt;
  input  wire                                        cap_rel;
  output wire                                        startup_cfgclk;
  output wire                                        startup_cfgmclk;
  output wire [3:0]                                  startup_di;
  output wire                                        startup_eos;
  output wire                                        startup_preq;
  input  wire [3:0]                                  startup_do;
  input  wire [3:0]                                  startup_dts;
  input  wire                                        startup_fcsbo;
  input  wire                                        startup_fcsbts;
  input  wire                                        startup_gsr;
  input  wire                                        startup_gts;
  input  wire                                        startup_keyclearb;
  input  wire                                        startup_pack;
  input  wire                                        startup_usrcclko;
  input  wire                                        startup_usrcclkts;
  input  wire                                        startup_usrdoneo;
  input  wire                                        startup_usrdonets;

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
  input                                       pipe_pclk_in;
  input                                       pipe_rxusrclk_in;
  input  [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pipe_rxoutclk_in;
  input                                       pipe_dclk_in;
  input                                       pipe_userclk1_in;
  input                                       pipe_userclk2_in;
  input                                       pipe_oobclk_in;
  input                                       pipe_mmcm_lock_in;
  input                                       pipe_mmcm_rst_n;
  output                                      pipe_txoutclk_out;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pipe_rxoutclk_out;
  output [PL_LINK_CAP_MAX_LINK_WIDTH-1:0]     pipe_pclk_sel_out;
  output                                      pipe_gen3_out;

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

  output [C_S_AXIS_DATA_WIDTH-1:0]    m_axis_rq_tdata_out;
  output 	         	      m_axis_rq_tlast_out;
  output [C_M_AXIS_RQ_USER_WIDTH-1:0] m_axis_rq_tuser_out;
  output [C_S_KEEP_WIDTH-1:0] 	      m_axis_rq_tkeep_out;
  output [3:0] 			      m_axis_rq_tready_out;
  output 			      m_axis_rq_tvalid_out;

  output [C_M_AXIS_DATA_WIDTH-1:0]    s_axis_rc_tdata_out;
  output [C_M_AXIS_RC_USER_WIDTH-1:0] s_axis_rc_tuser_out;
  output 			      s_axis_rc_tlast_out;
  output [C_M_KEEP_WIDTH-1:0] 	      s_axis_rc_tkeep_out;
  output 			      s_axis_rc_tvalid_out;
  output 			      s_axis_rc_tready_out;

  output [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_cq_tdata_out;
  output [C_S_AXIS_CQP_USER_WIDTH-1:0] s_axis_cq_tuser_out;
  output 			       s_axis_cq_tlast_out;
  output [C_M_KEEP_WIDTH-1:0] 	       s_axis_cq_tkeep_out;
  output 			       s_axis_cq_tvalid_out;
  output 			       s_axis_cq_tready_out;

  output [C_S_AXIS_DATA_WIDTH-1:0]     m_axis_cc_tdata_out;
  output [C_S_AXIS_CC_USER_WIDTH-1:0]  m_axis_cc_tuser_out;
  output 			       m_axis_cc_tlast_out;
  output [C_S_KEEP_WIDTH-1:0] 	       m_axis_cc_tkeep_out;
  output 			       m_axis_cc_tvalid_out;
  output [3:0] 			       m_axis_cc_tready_out;

  output                               pipe_tx0_rcvr_det;
  output [1:0]                         pipe_tx0_powerdown;
  output                               pipe_clk;
  output                               sys_clk_bufg;
  output [5:0]                         cfg_ltssm_state;
  output [15:0]                        cfg_function_status;
  output [2:0]                         cfg_max_read_req;
  output [1:0]                         cfg_max_payload;
  input                                cfg_err_uncor_in;
  input  [3:0]                         cfg_flr_done;
  output [3:0]                         cfg_flr_in_process;
  output [251:0]                       cfg_vf_flr_in_process;
  input  [7:0]                         cfg_vf_flr_func_num;
  input                                cfg_vf_flr_done;


  (* keep = "true" *) wire [18:0]	cfg_mgmt_addr;
  (* keep = "true" *) wire 		cfg_mgmt_write;
  (* keep = "true" *) wire [31:0] 	cfg_mgmt_write_data;
  (* keep = "true" *) wire [3:0]        cfg_mgmt_byte_enable;
  (* keep = "true" *) wire 		cfg_mgmt_read;
  (* keep = "true" *) wire [31:0] 	cfg_mgmt_read_data;
  (* keep = "true" *) wire		cfg_mgmt_read_write_done;
  (* keep = "true" *) wire  	        cfg_mgmt_type1_cfg_reg_access;

  (* keep = "true" *) wire 		axi_aclk;
  (* keep = "true" *) wire 		axi_aresetn;
  (* keep = "true" *) wire 		axi_ctl_aclk;
  (* keep = "true" *) wire 		axi_ctl_aresetn;
  wire 		                        axi_aresetn_int;
  (* keep = "true" *) wire  [XDMA_NUM_USR_IRQ-1:0]	usr_irq_req;
  (* keep = "true" *) wire  [XDMA_NUM_USR_IRQ-1:0]	usr_irq_ack;
  (* keep = "true" *) wire 				msi_enable;
  (* keep = "true" *) wire [2 : 0] 			msi_vector_width;

  (* keep = "true" *) wire [C_M_AXI_ID_WIDTH-1 : 0]     m_axi_awid;
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_awaddr;
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
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axi_araddr ;
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
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_awaddr ;
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
  (* keep = "true" *) wire [C_M_AXI_ADDR_WIDTH-1 : 0]   m_axib_araddr ;
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

  (* keep = "true" *) wire [31 : 0]			m_axil_awaddr ;
  (* keep = "true" *) wire [C_M_AXIL_AWUSER_WIDTH-1: 0]	m_axil_awuser ;
  wire [2 : 0] 			                        m_axil_awprot ;
  (* keep = "true" *) wire 				m_axil_awvalid ;
  (* keep = "true" *) wire 				m_axil_awready ;
  (* keep = "true" *) wire [31 : 0]                     m_axil_wdata ;
  (* keep = "true" *) wire [3 : 0]                      m_axil_wstrb ;
  (* keep = "true" *) wire 				m_axil_wvalid ;
  (* keep = "true" *) wire 				m_axil_wready ;
  (* keep = "true" *) wire 				m_axil_bvalid ;
  (* keep = "true" *) wire [1:0]			m_axil_bresp ;
  (* keep = "true" *) wire 				m_axil_bready ;
  (* keep = "true" *) wire [31 : 0]			m_axil_araddr ;
  (* keep = "true" *) wire [C_M_AXIL_ARUSER_WIDTH-1: 0]	m_axil_aruser ;
  wire [2 : 0]			                        m_axil_arprot;
  (* keep = "true" *) wire 				m_axil_arvalid ;
  (* keep = "true" *) wire 				m_axil_arready ;
  (* keep = "true" *) wire [31 : 0]                     m_axil_rdata ;
  (* keep = "true" *) wire [1 : 0] 			m_axil_rresp ;
  (* keep = "true" *) wire 				m_axil_rvalid ;
  (* keep = "true" *) wire 				m_axil_rready ;
  (* keep = "true" *) wire [31 : 0]			s_axil_awaddr ;
  wire [2 : 0] 			                        s_axil_awprot ;
  (* keep = "true" *) wire 				s_axil_awvalid ;
  (* keep = "true" *) wire 				s_axil_awready ;
  (* keep = "true" *) wire [31 : 0]                     s_axil_wdata ;
  (* keep = "true" *) wire [3 : 0]                      s_axil_wstrb ;
  (* keep = "true" *) wire 				s_axil_wvalid ;
  (* keep = "true" *) wire 				s_axil_wready ;
  (* keep = "true" *) wire 				s_axil_bvalid ;
  (* keep = "true" *) wire [1:0]			s_axil_bresp ;
  (* keep = "true" *) wire 				s_axil_bready ;
  (* keep = "true" *) wire [31 : 0]			s_axil_araddr ;
   wire [2 : 0]			                        s_axil_arprot;
  (* keep = "true" *) wire 				s_axil_arvalid ;
  (* keep = "true" *) wire 				s_axil_arready ;
  (* keep = "true" *) wire [31 : 0]                     s_axil_rdata ;
  (* keep = "true" *) wire [1 : 0] 			s_axil_rresp ;
  (* keep = "true" *) wire 				s_axil_rvalid ;
  (* keep = "true" *) wire 				s_axil_rready ;

  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_txp ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_txn ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_rxp ;
  (* keep = "true" *) wire [PL_LINK_CAP_MAX_LINK_WIDTH-1 : 0] 	pci_exp_rxn ;

  (* keep = "true" *) wire 	    sys_clk ;
  (* keep = "true" *) wire 	    sys_clk_gt ;
  (* keep = "true" *) wire 	    sys_rst_n  ;
  (* keep = "true" *) wire 	    user_lnk_up ;

  (* keep = "true" *) wire          drp_clk ;
  (* keep = "true" *) wire          drp_en ;
  (* keep = "true" *) wire          drp_we ;
  (* keep = "true" *) wire   [10:0] drp_addr ;
  (* keep = "true" *) wire   [15:0] drp_di ;

  (* keep = "true" *) wire                                           ext_ch_gt_drpclk ;
  (* keep = "true" *) wire [((PL_LINK_CAP_MAX_LINK_WIDTH *  9)-1):0] ext_ch_gt_drpaddr ;
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

  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1refclk;
  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1pd;
  wire [((((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2)+1)*3)-1:0] ext_qpll1rate;
  wire [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1reset;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1lock_out;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outclk_out;
  wire  [((PL_LINK_CAP_MAX_LINK_WIDTH-1)>>2):0] ext_qpll1outrefclk_out;

  localparam DAT_WIDTH = C_M_AXIS_DATA_WIDTH;
  localparam C_RNUM_CHNL = XDMA_RNUM_CHNL;
  localparam C_WNUM_CHNL = XDMA_WNUM_CHNL;
  localparam C_RNUM_RIDS = XDMA_RNUM_RIDS;
  localparam C_WNUM_RIDS = XDMA_WNUM_RIDS;
  localparam C_NUM_USR_IRQ = XDMA_NUM_USR_IRQ;
  localparam C_GEN2_DEVICES = (ULTRASCALE == "FALSE") && (V7_GEN3 == "FALSE");   // Indicates Gen2 PCIe Hard Block
  localparam C_LEGACY_INT_EN = (PF0_INTERRUPT_PIN == 3'b000) ? "FALSE" : "TRUE"; // Indicates Legacy Interrupt Enabled/Disabled

  wire [2:0] axist_sz;
  wire [2:0] aximm_sz;

  wire [15:0]    cfg_subsys_vend_id = PF0_SUBSYSTEM_VENDOR_ID;

  // Configuration outputs ?? hope all of them are outputs....

  wire           cfg_phy_link_down;
  wire    [1:0]  cfg_phy_link_status;
  wire    [2:0]  cfg_max_read_req;

  wire    [1:0]  cfg_link_power_state;

  // Error Reporting Interface
  wire           cfg_err_cor_out;
  wire           cfg_err_nonfatal_out;
  wire           cfg_err_fatal_out;
  wire           cfg_local_error;
  wire           cfg_req_pm_transition_l23_ready = 0;

  wire           cfg_ltr_enable;
  wire   [3:0]   cfg_interrupt_pending;
  wire           cfg_dbe_int;
  wire           cfg_dbe;
  wire    [2:0]  cfg_negotiated_width;
  wire    [1:0]  cfg_current_speed;
  wire    [1:0]  cfg_max_payload;
  wire   [3:0]   cfg_rcb_status;
  wire   [3:0]   cfg_dpa_substate_change;
  wire   [11:0]  cfg_function_power_state;
  wire   [3:0]   cfg_per_function_number;
//  wire   [3:0]   cfg_interrupt_msi_enable;
  wire   [11:0]  cfg_interrupt_msi_mmenable;
  wire   [15:0]  cfg_function_status;
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
  wire           cfg_power_state_change_ack;
  wire           cfg_power_state_change_interrupt;

  //----------------------------------------------------------------------------------------------------------------//
  // EP Only                                                                                                        //
  //----------------------------------------------------------------------------------------------------------------//

  // Interrupt Interface Signals
  wire [3:0] 	cfg_interrupt_int;
  wire 	        cfg_interrupt_sent;

  wire 	        cfg_interrupt_msi_mask_update;
  wire [31:0] 	cfg_interrupt_msi_data;
  wire [31:0] 	cfg_interrupt_msi_int;
  wire 	        cfg_interrupt_msi_sent;
  wire 	        cfg_interrupt_msi_fail;
  wire 	        cfg_hot_reset_out;
  wire [7:0] 	cfg_ds_port_number;
  wire [7:0] 	cfg_ds_bus_number;
  wire [4:0] 	cfg_ds_device_number;
  wire [2:0] 	cfg_ds_function_number;

  wire	        cfg_interrupt_msix_sent;      // Configuration Interrupt MSI-X Interrupt Sent.
  wire	        cfg_interrupt_msix_fail;      // Configuration Interrupt MSI-X Interrupt Operation Failed.
  wire	        cfg_interrupt_msix_int;       // Configuration Interrupt MSI-X Data Valid.
  wire	[31:0]  cfg_interrupt_msix_data;      // Configuration Interrupt MSI-X Data.
  wire	[63:0]  cfg_interrupt_msix_address;   // Configuration Interrupt MSI-X Address.
//  wire	[3:0]   cfg_interrupt_msix_enable;    // Configuration Interrupt MSI-X Function Enabled.
  wire	[3:0]   cfg_interrupt_msix_mask;      // Configuration Interrupt MSI-X Function Mask.
  wire	[251:0] cfg_interrupt_msix_vf_enable; // Configuration Interrupt MSI-X on VF Enabled.
  wire	[251:0] cfg_interrupt_msix_vf_mask;   // Configuration Interrupt MSI-X VF Mask.
  wire [C_S_AXIS_DATA_WIDTH-1:0]    s_axis_rq_tdata;
  wire 	         		    s_axis_rq_tlast;
  wire [C_M_AXIS_RQ_USER_WIDTH-1:0] s_axis_rq_tuser;
  wire [C_S_KEEP_WIDTH-1:0] 	    s_axis_rq_tkeep;
  wire [3:0] 			    s_axis_rq_tready;
  wire 			            s_axis_rq_tvalid;

  wire [C_M_AXIS_DATA_WIDTH-1:0]    m_axis_rc_tdata;
  wire [C_M_AXIS_RC_USER_WIDTH-1:0] m_axis_rc_tuser;
  wire 			            m_axis_rc_tlast;
  wire [C_M_KEEP_WIDTH-1:0] 	    m_axis_rc_tkeep;
  wire 			            m_axis_rc_tvalid;
  wire 			            m_axis_rc_tready;
  wire 			            m_axis_rc_tready_dma;

  wire [C_M_AXIS_DATA_WIDTH-1:0]     m_axis_cq_tdata;
  wire [C_S_AXIS_CQP_USER_WIDTH-1:0] m_axis_cq_tuser;
  wire 			             m_axis_cq_tlast;
  wire [C_M_KEEP_WIDTH-1:0] 	     m_axis_cq_tkeep;
  wire 			             m_axis_cq_tvalid;
  wire  			     m_axis_cq_tready;
  wire 			             m_axis_cq_tready_dma;

  wire [C_S_AXIS_DATA_WIDTH-1:0]     s_axis_cc_tdata;
  wire [C_S_AXIS_CC_USER_WIDTH-1:0]  s_axis_cc_tuser;
  wire 			             s_axis_cc_tlast;
  wire [C_S_KEEP_WIDTH-1:0] 	     s_axis_cc_tkeep;
  wire 			             s_axis_cc_tvalid;
  wire [3:0] 			     s_axis_cc_tready;

  wire 			  user_clk;
  wire 			  user_reset;
  wire [1:0] 	          pcie_cq_np_req;
  wire [5:0] 		  pcie_cq_np_req_count;
  wire [3:0] 		  pcie_tfc_nph_av;
  wire [3:0] 		  pcie_tfc_npd_av;
  wire 		          pcie_rq_seq_num_vld0;
  wire [5:0] 	          pcie_rq_seq_num0;
  wire 		          pcie_rq_seq_num_vld1;
  wire [5:0] 	          pcie_rq_seq_num1;

  wire  [C_S_AXIS_DATA_WIDTH-1:0]    m_axis_rq_tdata_out;
  wire 	                 	     m_axis_rq_tlast_out;
  wire [C_M_AXIS_RQ_USER_WIDTH-1:0]  m_axis_rq_tuser_out;
  wire [C_S_KEEP_WIDTH-1:0] 	     m_axis_rq_tkeep_out;
  wire [3:0] 			     m_axis_rq_tready_out;
  wire 			             m_axis_rq_tvalid_out;

  wire [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_rc_tdata_out;
  wire [C_M_AXIS_RC_USER_WIDTH-1:0]  s_axis_rc_tuser_out;
  wire 			             s_axis_rc_tlast_out;
  wire [C_M_KEEP_WIDTH-1:0] 	     s_axis_rc_tkeep_out;
  wire 			             s_axis_rc_tvalid_out;
  wire 			             s_axis_rc_tready_out;

  wire [C_M_AXIS_DATA_WIDTH-1:0]     s_axis_cq_tdata_out;
  wire [C_S_AXIS_CQP_USER_WIDTH-1:0] s_axis_cq_tuser_out;
  wire 			             s_axis_cq_tlast_out;
  wire [C_M_KEEP_WIDTH-1:0] 	     s_axis_cq_tkeep_out;
  wire 			             s_axis_cq_tvalid_out;
  wire  			     s_axis_cq_tready_out;

  wire [C_S_AXIS_DATA_WIDTH-1:0]     m_axis_cc_tdata_out;
  wire [C_S_AXIS_CC_USER_WIDTH-1:0]  m_axis_cc_tuser_out;
  wire 			             m_axis_cc_tlast_out;
  wire [C_S_KEEP_WIDTH-1:0] 	     m_axis_cc_tkeep_out;
  wire 			             m_axis_cc_tvalid_out;
  wire [3:0] 			     m_axis_cc_tready_out;

  wire                               pipe_tx0_rcvr_det;
  wire [1:0]                         pipe_tx0_powerdown;
  wire                               pipe_clk;
  wire                               sys_clk_bufg;
  wire [5:0]                         cfg_ltssm_state;
  wire                               cfg_err_uncor_in;
  wire  [3:0]                        cfg_flr_done;
  wire [3:0]                         cfg_flr_in_process;
  wire [251:0]                       cfg_vf_flr_in_process;
  wire  [7:0]                        cfg_vf_flr_func_num;
  wire                               cfg_vf_flr_done;

  assign m_axis_rq_tdata_out   = s_axis_rq_tdata ;
  assign m_axis_rq_tlast_out   = s_axis_rq_tlast;
  assign m_axis_rq_tuser_out   = s_axis_rq_tuser;
  assign m_axis_rq_tkeep_out   = s_axis_rq_tkeep;
  assign m_axis_rq_tready_out  = s_axis_rq_tready;
  assign m_axis_rq_tvalid_out  = s_axis_rq_tvalid;

  assign s_axis_rc_tdata_out   = m_axis_rc_tdata;
  assign s_axis_rc_tuser_out   = m_axis_rc_tuser ;
  assign s_axis_rc_tlast_out   = m_axis_rc_tlast ;
  assign s_axis_rc_tkeep_out   = m_axis_rc_tkeep;
  assign s_axis_rc_tvalid_out  = m_axis_rc_tvalid;
  assign s_axis_rc_tready_out  = m_axis_rc_tready;

  assign s_axis_cq_tdata_out   = m_axis_cq_tdata ;
  assign s_axis_cq_tuser_out   = m_axis_cq_tuser ;
  assign s_axis_cq_tlast_out   = m_axis_cq_tlast;
  assign s_axis_cq_tkeep_out   = m_axis_cq_tkeep;
  assign s_axis_cq_tvalid_out  = m_axis_cq_tvalid;
  assign s_axis_cq_tready_out  = m_axis_cq_tready;

  assign m_axis_cc_tdata_out   = s_axis_cc_tdata;
  assign m_axis_cc_tuser_out   = s_axis_cc_tuser;
  assign m_axis_cc_tlast_out   = s_axis_cc_tlast ;
  assign m_axis_cc_tkeep_out   = s_axis_cc_tkeep;
  assign m_axis_cc_tvalid_out  = s_axis_cc_tvalid;
  assign m_axis_cc_tready_out  = s_axis_cc_tready;

assign aximm_sz =	((C_S_AXIS_DATA_WIDTH == 256) ? 3'h2 :
 			((C_S_AXIS_DATA_WIDTH == 128) ?  3'h1 :
			((C_S_AXIS_DATA_WIDTH == 64) ?  3'h0 : 3'h3)));
assign axist_sz = aximm_sz;

assign axi_aresetn =  axi_aresetn_int ;
assign axi_aclk = user_clk;

assign cfg_msg_data = 16'h0;                     // Message Requester ID
assign cfg_msg_transmit = 1'b0;
assign cfg_msg_transmit_type = 3'b0;
assign cfg_msg_transmit_data = 32'h0;

assign cfg_fc_sel = 3'h5;

assign msi_vector_width = cfg_interrupt_msi_mmenable[2:0];
assign msi_enable = cfg_interrupt_msi_enable[0];

assign m_axis_cq_tready = m_axis_cq_tready_dma;
assign m_axis_rc_tready = m_axis_rc_tready_dma;

//assign m_axi_wuser = {C_M_AXI_DATA_WIDTH/8{1'b0}};

reg	[C_M_AXI_DATA_WIDTH/8-1:0]	m_axi_rdataeccparity;
reg	[C_M_AXI_DATA_WIDTH/8-1:0]	m_axi_wdataeccparity;
reg	[C_M_AXI_DATA_WIDTH/8-1:0]	m_axib_rdataeccparity;
reg	[C_M_AXI_DATA_WIDTH/8-1:0]	m_axib_wdataeccparity;

assign m_axi_rdataeccparity = {C_M_AXI_DATA_WIDTH/8{1'b0}};
assign m_axib_rdataeccparity = {C_M_AXI_DATA_WIDTH/8{1'b0}};

assign cfg_dbe_int = cfg_dbe | cfg_err_uncor_in;

  //----------------------------------------------------------------------------------------------------------------//
  // BAR Assignments                                                                                                //
  //----------------------------------------------------------------------------------------------------------------//

  // 64 = Max BAR width or BAR disabled
  // BAR hit only on even number BARs for 64-bit BAR type
  // CONTROL = 'h0 (disabled); CONTROL = 'h4 (32-bit); CONTROL = 'h5 (64-bit)
  // SIZE starts at 'h5 (4KB) and +1 for each BAR size selection larger than it
  localparam C_PCIEBAR_LEN_0 = (AXILITE_MASTER_CONTROL != 'h0) ? (AXILITE_MASTER_APERTURE_SIZE + 'h7) : (XDMA_APERTURE_SIZE + 'h7);

  localparam C_PCIEBAR_LEN_1 = ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4)) ? (XDMA_APERTURE_SIZE + 'h7) :
                                 ( ((AXILITE_MASTER_CONTROL == 'h0) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                   64 
                                 );

  localparam C_PCIEBAR_LEN_2 = (AXILITE_MASTER_CONTROL == 'h5) ? (XDMA_APERTURE_SIZE + 'h7) :
                                 ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h5)) ? (XDMA_APERTURE_SIZE + 'h7) :
                                   ( ((AXILITE_MASTER_CONTROL == 'h4) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                     ( ((XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                       ( ((XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h5)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                                         64 
                                       )
                                     )
                                   )
                                 );

  localparam C_PCIEBAR_LEN_3 = ((AXILITE_MASTER_CONTROL == 'h5) && (XDMA_CONTROL == 'h4) && (AXIST_BYPASS_CONTROL == 'h4)) ?  (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                               64;

  localparam C_PCIEBAR_LEN_4 = ((AXILITE_MASTER_CONTROL == 'h5) && (XDMA_CONTROL == 'h5) && (AXIST_BYPASS_CONTROL != 'h0)) ? (AXIST_BYPASS_APERTURE_SIZE + 'h7) :
                               64;

  localparam C_PCIEBAR_LEN_5 = 64; // BAR hit on this bar is not used
  localparam C_PCIEBAR_LEN_6 = 64; // BAR hit on this bar is not used

  localparam BARLITE0        = (XDMA_AXILITE_MASTER == "TRUE" ) ? 0 : 7;                            // BAR number for AXILite; Always at 0 when enabled
  localparam BARLITE1        = (XDMA_AXILITE_MASTER == "FALSE") ? 0 : (XDMA_CONTROL == 5) ? 2 : 1;  // BAR number for XDMA Control;

  //----------------------------------------------------------------------------------------------------------------//

   xdma_v3_0_2_dma_top #(
      .C_FAMILY(C_FAMILY),
      .VERSION(4),
      .MM_SLAVE_EN(MM_SLAVE_EN),
      .DMA_EN(DMA_EN),
      .C_INCLUDE_RC(C_INCLUDE_RC),
      .C_MSI_ENABLED(C_MSI_ENABLED),
      .C_COMP_TIMEOUT(C_COMP_TIMEOUT),
      .PL_LINK_CAP_MAX_LINK_SPEED(PL_LINK_CAP_MAX_LINK_SPEED),
      .PL_DISABLE_UPCONFIG_CAPABLE(PL_DISABLE_UPCONFIG_CAPABLE),
      .C_AXIBAR_0(C_AXIBAR_0),
      .C_AXIBAR_1(C_AXIBAR_1),
      .C_AXIBAR_2(C_AXIBAR_2),
      .C_AXIBAR_3(C_AXIBAR_3),
      .C_AXIBAR_4(C_AXIBAR_4),
      .C_AXIBAR_5(C_AXIBAR_5),
      .C_AXIBAR_AS_0(C_AXIBAR_AS_0),
      .C_AXIBAR_AS_1(C_AXIBAR_AS_1),
      .C_AXIBAR_AS_2(C_AXIBAR_AS_2),
      .C_AXIBAR_AS_3(C_AXIBAR_AS_3),
      .C_AXIBAR_AS_4(C_AXIBAR_AS_4),
      .C_AXIBAR_AS_5(C_AXIBAR_AS_5),
      .C_AXIBAR_HIGHADDR_0(C_AXIBAR_HIGHADDR_0),
      .C_AXIBAR_HIGHADDR_1(C_AXIBAR_HIGHADDR_1),
      .C_AXIBAR_HIGHADDR_2(C_AXIBAR_HIGHADDR_2),
      .C_AXIBAR_HIGHADDR_3(C_AXIBAR_HIGHADDR_3),
      .C_AXIBAR_HIGHADDR_4(C_AXIBAR_HIGHADDR_4),
      .C_AXIBAR_HIGHADDR_5(C_AXIBAR_HIGHADDR_5),
      .C_AXIBAR_NUM(C_AXIBAR_NUM),
      .C_M_AXI_ID_WIDTH(C_M_AXI_ID_WIDTH),
      .C_M_AXI_ADDR_WIDTH(C_M_AXI_ADDR_WIDTH),
      .C_M_AXI_DATA_WIDTH(C_M_AXI_DATA_WIDTH),
      .C_S_AXIS_DATA_WIDTH(C_S_AXIS_DATA_WIDTH),
      .C_S_AXI_ID_WIDTH(C_S_AXI_ID_WIDTH),
      .C_S_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
      .C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
      .C_M_AXIS_DATA_WIDTH(C_M_AXIS_DATA_WIDTH),
      .C_M_AXIS_RQ_USER_WIDTH(C_M_AXIS_RQ_USER_WIDTH),
      .C_M_AXIS_RC_USER_WIDTH(C_M_AXIS_RC_USER_WIDTH),
      .C_S_AXIS_CQ_USER_WIDTH(C_S_AXIS_CQ_USER_WIDTH),
      .C_S_AXIS_CC_USER_WIDTH(C_S_AXIS_CC_USER_WIDTH),
      .C_S_NUM_AXI_READ(C_S_AXI_NUM_READ),
      .C_S_NUM_AXI_WRITE(C_S_AXI_NUM_WRITE),
      .C_ADDR_ALGN      (C_ADDR_ALGN),
      .C_ADDR_BITS	(C_ADDR_BITS),
      .C_DSC_MAGIC_EN	(C_DSC_MAGIC_EN),
      .C_RNUM_CHNL  	(C_RNUM_CHNL),
      .C_RNUM_RIDS  	(C_RNUM_RIDS),
      .C_WNUM_CHNL  	(C_WNUM_CHNL),
      .C_WNUM_RIDS  	(C_WNUM_RIDS),
      .C_M_NUM_AXI_READ (C_WNUM_RIDS),
      .C_NUM_MSIX_VECTORS(C_NUM_MSIX_VECTORS),
      .C_NUM_USR_IRQ	(C_NUM_USR_IRQ),
      .C_NUM_PCIE_TAGS	(XDMA_NUM_PCIE_TAG),
      .C_METERING_ON	(C_METERING_ON),
      .C_ECC_ENABLE(C_ECC_ENABLE),
      .C_RD_BUFFER_ADDR_SIZE(C_RD_BUFFER_ADDR_SIZE),
      .C_RD_BUFFER_SIZE_BITS(C_RD_BUFFER_SIZE_BITS),
      .C_PCIEBAR_NUM(C_PCIEBAR_NUM),
      .C_PCIEBAR_AS(C_PCIEBAR_AS),
      .AXI_DSC_ENG_EN	(0),
      .AXI_WBK_ENG_EN	(0),
      .PCIE_DSC_ENG_EN	(1),
      .PCIE_WBK_ENG_EN	(1),
      .C_PCIEBAR_LEN_0(C_PCIEBAR_LEN_0),
      .C_PCIEBAR_LEN_1(C_PCIEBAR_LEN_1),
      .C_PCIEBAR_LEN_2(C_PCIEBAR_LEN_2),
      .C_PCIEBAR_LEN_3(C_PCIEBAR_LEN_3),
      .C_PCIEBAR_LEN_4(C_PCIEBAR_LEN_4),
      .C_PCIEBAR_LEN_5(C_PCIEBAR_LEN_5),
      .C_PCIEBAR_LEN_6(C_PCIEBAR_LEN_5),
      .C_PCIEBAR2AXIBAR_0(C_PCIEBAR2AXIBAR_0),
      .C_PCIEBAR2AXIBAR_1(C_PCIEBAR2AXIBAR_1),
      .C_PCIEBAR2AXIBAR_2(C_PCIEBAR2AXIBAR_2),
      .BARLITE0(BARLITE0),
      .BARLITE1(BARLITE1),
      .USR_MPL_SIZE	(USR_MPL_SIZE),
      .USR_MRS_SIZE	(USR_MRS_SIZE),
      .C_PARITY_CHECK   (C_PARITY_CHECK),
      .C_PARITY_GEN     (C_PARITY_GEN),
      .C_PARITY_PROP    (C_PARITY_PROP),
      .STS_WIDTH	(STS_WIDTH),
      .BACKPRESSURE	(BACKPRESSURE),
      .DSC_BYPASS_RD	(DSC_BYPASS_RD),
      .DSC_BYPASS_WR	(DSC_BYPASS_WR),
      .PMON_EN (PMON_EN),
      .RQ_SEQ_NUM_IGNORE (RQ_SEQ_NUM_IGNORE),
      .DMA_ST(DMA_ST),
      .DMA_SP(DMA_SP),
      .DMA_MM(DMA_MM),
      .C_M_AXIL_AWUSER_WIDTH(C_M_AXIL_AWUSER_WIDTH),
      .C_M_AXIL_ARUSER_WIDTH(C_M_AXIL_ARUSER_WIDTH)
		     )
   dma_top (
     //-- AXI Global
     .user_clk	(user_clk),
     .user_reset (user_reset ),
     .link_up	( user_lnk_up ),
     .sys_rst_n ( sys_rst_n ),
     .axi_aresetn ( axi_aresetn_int ),
     // AXI Streaming Size
     .axist_sz(axist_sz),

     // AXI MM Size
     .aximm_sz(aximm_sz),

      //-- AXIS RQ Request Channel
     .m_axis_rq_tdata(s_axis_rq_tdata),
     .m_axis_rq_tkeep(s_axis_rq_tkeep),
     .m_axis_rq_tuser(s_axis_rq_tuser),
     .m_axis_rq_tlast(s_axis_rq_tlast),
     .m_axis_rq_tvalid(s_axis_rq_tvalid),
     .m_axis_rq_tready(s_axis_rq_tready[1]),
     .pcie_fc_nph( cfg_fc_nph ),
     .pcie_cq_np_req(pcie_cq_np_req),
     .pcie_tfc_nph_av(pcie_tfc_nph_av),  // Use 4 bits for Diablo FIXME
     .pcie_rq_seq_num_vld(pcie_rq_seq_num_vld0),
     .pcie_rq_seq_num(pcie_rq_seq_num0[3:0]),
     .pcie_rq_seq_num_vld_1(pcie_rq_seq_num_vld1),	
     .pcie_rq_seq_num_1(pcie_rq_seq_num1[3:0]),		

      //-- AXIS Completion Requester Channel
     .s_axis_rc_tdata(m_axis_rc_tdata),
     .s_axis_rc_tkeep(m_axis_rc_tkeep),
     .s_axis_rc_tuser(m_axis_rc_tuser),
     .s_axis_rc_tlast(m_axis_rc_tlast),
     .s_axis_rc_tvalid(m_axis_rc_tvalid),
     .s_axis_rc_tready(m_axis_rc_tready_dma),

     //--AXIS Completer Request Channel
     .s_axis_cq_tdata(m_axis_cq_tdata),
     .s_axis_cq_tkeep(m_axis_cq_tkeep),
     .s_axis_cq_tlast(m_axis_cq_tlast),
     .s_axis_cq_tvalid(m_axis_cq_tvalid),
     .s_axis_cq_tready(m_axis_cq_tready_dma),
     .s_axis_cq_tuser(m_axis_cq_tuser),
     //--AXIS Completion Target Channel
     .m_axis_cc_tdata(s_axis_cc_tdata),
     .m_axis_cc_tkeep(s_axis_cc_tkeep),
     .m_axis_cc_tlast(s_axis_cc_tlast),
     .m_axis_cc_tvalid(s_axis_cc_tvalid),
     .m_axis_cc_tready(s_axis_cc_tready),
     .m_axis_cc_tuser(s_axis_cc_tuser),

     // AXI-Lite Master interface
     .m_axil_awaddr		(m_axil_awaddr),
     .m_axil_awuser		(m_axil_awuser),
     .m_axil_awprot		(m_axil_awprot),
     .m_axil_awvalid		(m_axil_awvalid),
     .m_axil_awready		(m_axil_awready),

     .m_axil_wdata		(m_axil_wdata),
     .m_axil_wstrb		(m_axil_wstrb),
     .m_axil_wvalid		(m_axil_wvalid),
     .m_axil_wready		(m_axil_wready),

     .m_axil_bvalid		(m_axil_bvalid),
     .m_axil_bresp		(m_axil_bresp),
     .m_axil_bready		(m_axil_bready),

     .m_axil_araddr		(m_axil_araddr),
     .m_axil_aruser		(m_axil_aruser),
     .m_axil_arprot		(m_axil_arprot),
     .m_axil_arvalid		(m_axil_arvalid),
     .m_axil_arready		(m_axil_arready),

     .m_axil_rdata		(m_axil_rdata),
     .m_axil_rresp		(m_axil_rresp),
     .m_axil_rvalid		(m_axil_rvalid),
     .m_axil_rready		(m_axil_rready),

     // AXI-Lite Slave interface
     .s_axil_awaddr		(s_axil_awaddr),
     .s_axil_awprot		(s_axil_awprot),
     .s_axil_awvalid		(s_axil_awvalid),
     .s_axil_awready		(s_axil_awready),

     .s_axil_wdata		(s_axil_wdata),
     .s_axil_wstrb		(s_axil_wstrb),
     .s_axil_wvalid		(s_axil_wvalid),
     .s_axil_wready		(s_axil_wready),

     .s_axil_bvalid		(s_axil_bvalid),
     .s_axil_bresp		(s_axil_bresp),
     .s_axil_bready		(s_axil_bready),

     .s_axil_araddr		(s_axil_araddr),
     .s_axil_arprot		(s_axil_arprot),
     .s_axil_arvalid		(s_axil_arvalid),
     .s_axil_arready		(s_axil_arready),
     
     .s_axil_rdata		(s_axil_rdata),
     .s_axil_rresp		(s_axil_rresp),
     .s_axil_rvalid		(s_axil_rvalid),
     .s_axil_rready		(s_axil_rready),

     //--AXI Master Read Address Channel
     .m_axi_arid		(m_axi_arid),
     .m_axi_araddr		(m_axi_araddr),
     .m_axi_arlen		(m_axi_arlen),
     .m_axi_arsize		(m_axi_arsize),
     .m_axi_arburst		(m_axi_arburst),
     .m_axi_arprot		(m_axi_arprot),
     .m_axi_arvalid		(m_axi_arvalid),
     .m_axi_arready		(m_axi_arready),
     .m_axi_arlock		(m_axi_arlock),
     .m_axi_arcache		(m_axi_arcache),

     //--AXI Master Read Data Channel
     .m_axi_rid		        (m_axi_rid),
     .m_axi_rdata		(m_axi_rdata),
     .m_axi_rdataeccparity	(m_axi_ruser),
     .m_axi_rresp		(m_axi_rresp),
     .m_axi_rlast		(m_axi_rlast),
     .m_axi_rvalid		(m_axi_rvalid),
     .m_axi_rready		(m_axi_rready),

     //--AXI master Write Address Channel
     .m_axi_awaddr		(m_axi_awaddr),
     .m_axi_awid		(m_axi_awid),
     .m_axi_awlen		(m_axi_awlen),
     .m_axi_awsize		(m_axi_awsize),
     .m_axi_awburst		(m_axi_awburst),
     .m_axi_awprot		(m_axi_awprot),
     .m_axi_awvalid		(m_axi_awvalid),
     .m_axi_awready		(m_axi_awready),
     .m_axi_awlock		(m_axi_awlock),
     .m_axi_awcache		(m_axi_awcache),

     //--AXI master Write Data Channel
     .m_axi_wdata		(m_axi_wdata),
     .m_axi_wdataeccparity	(m_axi_wuser),
     .m_axi_wstrb		(m_axi_wstrb),
     .m_axi_wlast		(m_axi_wlast),
     .m_axi_wvalid		(m_axi_wvalid),
     .m_axi_wready		(m_axi_wready),

     //--AXI master Response Channel
     .m_axi_bresp		(m_axi_bresp),
     .m_axi_bid		        (m_axi_bid),
     .m_axi_bvalid		(m_axi_bvalid),
     .m_axi_bready		(m_axi_bready),

     //--AXI Master Read Address Channel
     .m_axib_arid		(m_axib_arid),
     .m_axib_araddr		(m_axib_araddr),
     .m_axib_aruser		(m_axib_aruser),
     .m_axib_arlen		(m_axib_arlen),
     .m_axib_arsize		(m_axib_arsize),
     .m_axib_arburst		(m_axib_arburst),
     .m_axib_arprot		(m_axib_arprot),
     .m_axib_arvalid		(m_axib_arvalid),
     .m_axib_arready		(m_axib_arready),
     .m_axib_arlock		(m_axib_arlock),
     .m_axib_arcache		(m_axib_arcache),
     //--AXI Master Read Data Channel
     .m_axib_rid		(m_axib_rid),
     .m_axib_rdata		(m_axib_rdata),
     .m_axib_rdataeccparity	(m_axib_ruser),
     .m_axib_rresp		(m_axib_rresp),
     .m_axib_rlast		(m_axib_rlast),
     .m_axib_rvalid		(m_axib_rvalid),
     .m_axib_rready		(m_axib_rready),
     //--AXI master Write Address Channel
     .m_axib_awaddr		(m_axib_awaddr),
     .m_axib_awuser		(m_axib_awuser),
     .m_axib_awid		(m_axib_awid),
     .m_axib_awlen		(m_axib_awlen),
     .m_axib_awsize		(m_axib_awsize),
     .m_axib_awburst		(m_axib_awburst),
     .m_axib_awprot		(m_axib_awprot),
     .m_axib_awvalid		(m_axib_awvalid),
     .m_axib_awready		(m_axib_awready),
     .m_axib_awlock		(m_axib_awlock),
     .m_axib_awcache		(m_axib_awcache),

     //--AXI master Write Data Channel
     .m_axib_wdata		(m_axib_wdata),
     .m_axib_wdataeccparity	(m_axib_wuser),
     .m_axib_wstrb		(m_axib_wstrb),
     .m_axib_wlast		(m_axib_wlast),
     .m_axib_wvalid		(m_axib_wvalid),
     .m_axib_wready		(m_axib_wready),

     //--AXI master Response Channel
     .m_axib_bresp		(m_axib_bresp),
     .m_axib_bid		(m_axib_bid),
     .m_axib_bvalid		(m_axib_bvalid),
     .m_axib_bready		(m_axib_bready),
         
   //-- AXI Slave Write Address Channel
   .s_axi_awid(s_axi_awid),
   .s_axi_awaddr(s_axi_awaddr),
   .s_axi_awregion(s_axi_awregion),
   .s_axi_awlen(s_axi_awlen),
   .s_axi_awsize(s_axi_awsize),
   .s_axi_awburst(s_axi_awburst),
   .s_axi_awvalid(s_axi_awvalid),
   .s_axi_awready(s_axi_awready),

   //-- AXI Slave Write Data Channel
   .s_axi_wdata(s_axi_wdata),
   .s_axi_wdataeccparity(s_axi_wdataeccparity),
   .s_axi_wstrb(s_axi_wstrb),
   .s_axi_wlast(s_axi_wlast),
   .s_axi_wvalid(s_axi_wvalid),
   .s_axi_wready(s_axi_wready),

   //-- AXI Slave Write Response Channel
   .s_axi_bid(s_axi_bid),
   .s_axi_bresp(s_axi_bresp),
   .s_axi_bvalid(s_axi_bvalid),
   .s_axi_bready(s_axi_bready),

   //-- AXI Slave Read Address Channel
   .s_axi_arid(s_axi_arid),
   .s_axi_araddr(s_axi_araddr),
   .s_axi_arregion(s_axi_arregion),
   .s_axi_arlen(s_axi_arlen),
   .s_axi_arsize(s_axi_arsize),
   .s_axi_arburst(s_axi_arburst),
   .s_axi_arvalid(s_axi_arvalid),
   .s_axi_arready(s_axi_arready),

   //-- AXI Slave Read Data Channel
   .s_axi_rid(s_axi_rid),
   .s_axi_rresp(s_axi_rresp),
   .s_axi_rlast(s_axi_rlast),
   .s_axi_rvalid(s_axi_rvalid),
   .s_axi_rready(s_axi_rready),
   .s_axi_rdata(s_axi_rdata),
   .s_axi_rdataeccparity(s_axi_rdataeccparity),
   .interrupt_out(interrupt_out), 
     .s_axis_c2h_tdata	       ({s_axis_c2h_tdata_3,s_axis_c2h_tdata_2,s_axis_c2h_tdata_1,s_axis_c2h_tdata_0}),
     .s_axis_c2h_tlast	       ({s_axis_c2h_tlast_3,s_axis_c2h_tlast_2,s_axis_c2h_tlast_1,s_axis_c2h_tlast_0}),
     .s_axis_c2h_tvalid        ({s_axis_c2h_tvalid_3,s_axis_c2h_tvalid_2,s_axis_c2h_tvalid_1,s_axis_c2h_tvalid_0}),
     .s_axis_c2h_tready        ({s_axis_c2h_tready_3,s_axis_c2h_tready_2,s_axis_c2h_tready_1,s_axis_c2h_tready_0}),
     .s_axis_c2h_tkeep         ({s_axis_c2h_tkeep_3, s_axis_c2h_tkeep_2, s_axis_c2h_tkeep_1, s_axis_c2h_tkeep_0}),
     .s_axis_c2h_tparity       ({s_axis_c2h_tuser_3,s_axis_c2h_tuser_2,s_axis_c2h_tuser_1,s_axis_c2h_tuser_0}),

     .m_axis_h2c_tdata	       ({m_axis_h2c_tdata_3,m_axis_h2c_tdata_2,m_axis_h2c_tdata_1,m_axis_h2c_tdata_0}),
     .m_axis_h2c_tlast	       ({m_axis_h2c_tlast_3,m_axis_h2c_tlast_2,m_axis_h2c_tlast_1,m_axis_h2c_tlast_0}),
     .m_axis_h2c_tvalid        ({m_axis_h2c_tvalid_3,m_axis_h2c_tvalid_2,m_axis_h2c_tvalid_1,m_axis_h2c_tvalid_0}),
     .m_axis_h2c_tkeep	       ({m_axis_h2c_tkeep_3,m_axis_h2c_tkeep_2,m_axis_h2c_tkeep_1,m_axis_h2c_tkeep_0}),
     .m_axis_h2c_tready        ({m_axis_h2c_tready_3,m_axis_h2c_tready_2,m_axis_h2c_tready_1,m_axis_h2c_tready_0}),
     .m_axis_h2c_tparity       ({m_axis_h2c_tuser_3,m_axis_h2c_tuser_2,m_axis_h2c_tuser_1,m_axis_h2c_tuser_0}),
     .usr_irq_req	       (usr_irq_req),
     .usr_irq_ack	       (usr_irq_ack),
     .usr_irq_fail	       (),

     .c2h_sts		({c2h_sts_3,c2h_sts_2,c2h_sts_1,c2h_sts_0}),

     .h2c_sts		({h2c_sts_3,h2c_sts_2,h2c_sts_1,h2c_sts_0}),

     .c2h_dsc_byp_ready	({c2h_dsc_byp_ready_3,c2h_dsc_byp_ready_2,c2h_dsc_byp_ready_1,c2h_dsc_byp_ready_0}),
     .c2h_dsc_byp_src_addr   ({c2h_dsc_byp_src_addr_3,c2h_dsc_byp_src_addr_2,c2h_dsc_byp_src_addr_1,c2h_dsc_byp_src_addr_0}),
     .c2h_dsc_byp_dst_addr   ({c2h_dsc_byp_dst_addr_3,c2h_dsc_byp_dst_addr_2,c2h_dsc_byp_dst_addr_1,c2h_dsc_byp_dst_addr_0}),
     .c2h_dsc_byp_len        ({c2h_dsc_byp_len_3,c2h_dsc_byp_len_2,c2h_dsc_byp_len_1,c2h_dsc_byp_len_0}),
     .c2h_dsc_byp_ctl        ({c2h_dsc_byp_ctl_3,c2h_dsc_byp_ctl_2,c2h_dsc_byp_ctl_1,c2h_dsc_byp_ctl_0}),
     .c2h_dsc_byp_load       ({c2h_dsc_byp_load_3,c2h_dsc_byp_load_2,c2h_dsc_byp_load_1,c2h_dsc_byp_load_0}),

     .h2c_dsc_byp_ready	({h2c_dsc_byp_ready_3,h2c_dsc_byp_ready_2,h2c_dsc_byp_ready_1,h2c_dsc_byp_ready_0}),
     .h2c_dsc_byp_src_addr   ({h2c_dsc_byp_src_addr_3,h2c_dsc_byp_src_addr_2,h2c_dsc_byp_src_addr_1,h2c_dsc_byp_src_addr_0}),
     .h2c_dsc_byp_dst_addr   ({h2c_dsc_byp_dst_addr_3,h2c_dsc_byp_dst_addr_2,h2c_dsc_byp_dst_addr_1,h2c_dsc_byp_dst_addr_0}),
     .h2c_dsc_byp_len        ({h2c_dsc_byp_len_3,h2c_dsc_byp_len_2,h2c_dsc_byp_len_1,h2c_dsc_byp_len_0}),
     .h2c_dsc_byp_ctl        ({h2c_dsc_byp_ctl_3,h2c_dsc_byp_ctl_2,h2c_dsc_byp_ctl_1,h2c_dsc_byp_ctl_0}),
     .h2c_dsc_byp_load       ({h2c_dsc_byp_load_3,h2c_dsc_byp_load_2,h2c_dsc_byp_load_1,h2c_dsc_byp_load_0}),
     .cfg_function_status    (cfg_function_status),
     .cfg_phy_link_down	     (cfg_phy_link_down),
     .cfg_phy_link_status    (cfg_phy_link_status),
     .cfg_max_payload	     ({1'b0,cfg_max_payload}),
     .cfg_max_read_req	     (cfg_max_read_req),
     .cfg_dbe		     (cfg_dbe),
     .cfg_interrupt_msix_data      (cfg_interrupt_msix_data),
     .cfg_interrupt_msix_address   (cfg_interrupt_msix_address),
     .cfg_interrupt_msix_int       (cfg_interrupt_msix_int),
     .cfg_interrupt_msix_enable    (cfg_interrupt_msix_enable),
     .cfg_interrupt_msix_mask      (cfg_interrupt_msix_mask),
     .cfg_interrupt_msix_vf_enable (cfg_interrupt_msix_vf_enable[5:0]),
     .cfg_interrupt_msix_vf_mask   (cfg_interrupt_msix_vf_mask[5:0]),
     .cfg_interrupt_msix_sent      (cfg_interrupt_msi_sent),
     .cfg_interrupt_msix_fail      (cfg_interrupt_msi_fail),
     .cfg_negotiated_width         ({(cfg_negotiated_width[2:0] == 3'd3), (cfg_negotiated_width[2:0] == 3'd2),
                                       (cfg_negotiated_width[2:0] == 3'd1), (cfg_negotiated_width[2:0] == 3'd0)}),
     .cfg_current_speed            ({(cfg_current_speed[1:0] == 2'b10), (cfg_current_speed[1:0] == 2'b01), (cfg_current_speed[1:0] == 2'b00)}),
     .cfg_interrupt_msi_enable	   (cfg_interrupt_msi_enable),
     .cfg_interrupt_msi_int	   (cfg_interrupt_msi_int),
     .cfg_interrupt_msi_sent	   (cfg_interrupt_msi_sent),
     .cfg_interrupt_int	           (cfg_interrupt_int),
     .cfg_interrupt_pending	   (cfg_interrupt_pending),
     .cfg_interrupt_sent	   (cfg_interrupt_sent),
     .cfg_ltssm_state              (cfg_ltssm_state ),     
     .cfg_err_cor_out              (cfg_err_cor_out),
     .cfg_err_fatal_out            (cfg_err_fatal_out),
     .cfg_err_nonfatal_out         (cfg_err_nonfatal_out),
     .cfg_hot_reset_out            (cfg_hot_reset_out),
     .cfg_local_error              (cfg_local_error),
     .cfg_mgmt_read_data           ( cfg_mgmt_read_data ),
     .cfg_mgmt_read_write_done     ( cfg_mgmt_read_write_done ),
     .cfg_msg_received             ( cfg_msg_received ),
     .cfg_msg_received_data        ( cfg_msg_received_data ),
     .cfg_msg_received_type        ( cfg_msg_received_type ),
     .cfg_msg_transmit_done        ( cfg_msg_transmit_done ),
     .cfg_pl_status_change         (cfg_pl_status_change),
     .cfg_ds_port_number(cfg_ds_port_number),
     .cfg_ds_bus_number(cfg_ds_bus_number),
     .cfg_ds_device_number(cfg_ds_device_number),
     .cfg_ds_function_number(cfg_ds_function_number),
     .cfg_hot_reset_in(),
     .cfg_config_space_enable(),
     .cfg_err_cor_in(),
     .cfg_err_uncor_in(),
     .cfg_dsn(cfg_dsn)

   );



  xdma_0_pcie4_ip  pcie4_ip_i (

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

    .s_axis_rq_tlast                                ( s_axis_rq_tlast ),
    .s_axis_rq_tdata                                ( s_axis_rq_tdata ),
    .s_axis_rq_tuser                                ( s_axis_rq_tuser ),
    .s_axis_rq_tkeep                                ( s_axis_rq_tkeep ),
    .s_axis_rq_tready                               ( s_axis_rq_tready ),
    .s_axis_rq_tvalid                               ( s_axis_rq_tvalid ),

    .m_axis_rc_tdata                                ( m_axis_rc_tdata ),
    .m_axis_rc_tuser                                ( m_axis_rc_tuser ),
    .m_axis_rc_tlast                                ( m_axis_rc_tlast ),
    .m_axis_rc_tkeep                                ( m_axis_rc_tkeep ),
    .m_axis_rc_tvalid                               ( m_axis_rc_tvalid ),
    .m_axis_rc_tready                               ( m_axis_rc_tready ),

    .m_axis_cq_tdata                                ( m_axis_cq_tdata ),
    .m_axis_cq_tuser                                ( m_axis_cq_tuser ),
    .m_axis_cq_tlast                                ( m_axis_cq_tlast ),
    .m_axis_cq_tkeep                                ( m_axis_cq_tkeep ),
    .m_axis_cq_tvalid                               ( m_axis_cq_tvalid ),
    .m_axis_cq_tready                               ( m_axis_cq_tready ),

    .s_axis_cc_tdata                                ( s_axis_cc_tdata ),
    .s_axis_cc_tuser                                ( s_axis_cc_tuser ),
    .s_axis_cc_tlast                                ( s_axis_cc_tlast ),
    .s_axis_cc_tkeep                                ( s_axis_cc_tkeep ),
    .s_axis_cc_tvalid                               ( s_axis_cc_tvalid ),
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
    .cfg_mgmt_addr                                  ( cfg_mgmt_addr[9:0] ),
    .cfg_mgmt_write                                 ( cfg_mgmt_write ),
    .cfg_mgmt_write_data                            ( cfg_mgmt_write_data ),
    .cfg_mgmt_byte_enable                           ( cfg_mgmt_byte_enable ),
    .cfg_mgmt_read                                  ( cfg_mgmt_read ),
    .cfg_mgmt_read_data                             ( cfg_mgmt_read_data ),
    .cfg_mgmt_read_write_done                       ( cfg_mgmt_read_write_done ),
    .cfg_mgmt_function_number                       ( 8'b0 ), //N
    .cfg_mgmt_debug_access                          ( 1'b0 ), //N
    .cfg_ext_read_received                          ( cfg_ext_read_received ),
    .cfg_ext_write_received                         ( cfg_ext_write_received ),
    .cfg_ext_register_number                        ( cfg_ext_register_number ),
    .cfg_ext_function_number                        ( cfg_ext_function_number ),
    .cfg_ext_write_data                             ( cfg_ext_write_data ),
    .cfg_ext_write_byte_enable                      ( cfg_ext_write_byte_enable ),
    .cfg_ext_read_data                              ( cfg_ext_read_data ),
    .cfg_ext_read_data_valid                        ( cfg_ext_read_data_valid ),

    // Error Reporting Interface
    .cfg_err_cor_out                                ( cfg_err_cor_out ),
    .cfg_err_nonfatal_out                           ( cfg_err_nonfatal_out ),
    .cfg_err_fatal_out                              ( cfg_err_fatal_out ),
    .cfg_local_error_valid                          (  ), //N
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
    .cfg_err_cor_in                                 ( 1'b0 ),
    .cfg_err_uncor_in                               ( cfg_dbe_int ),

    .cfg_link_training_enable                       ( 1'b1 ),
    .cfg_tph_requester_enable                       (),
    .cfg_tph_st_mode                                (),
    .cfg_vf_tph_requester_enable                    (),
    .cfg_vf_tph_st_mode                             (),
    .cfg_flr_in_process                             (cfg_flr_in_process),
    .cfg_vf_flr_in_process                          (cfg_vf_flr_in_process),
    .cfg_vf_flr_func_num                            (cfg_vf_flr_func_num  ), //N
    .cfg_pm_aspm_l1_entry_reject                    ( 1'b0 ), //N
    .cfg_pm_aspm_tx_l0s_entry_disable               ( 1'b0 ), //N
    //-------------------------------------------------------------------------------//
    // EP Only                                                                       //
    //-------------------------------------------------------------------------------//

    // Interrupt Interface Signals
    .cfg_interrupt_int                              ( cfg_interrupt_int ),
    .cfg_interrupt_pending                          ( cfg_interrupt_pending ),
    .cfg_interrupt_sent                             ( cfg_interrupt_sent ),
    .cfg_interrupt_msi_enable                       ( cfg_interrupt_msi_enable),
    .cfg_interrupt_msi_mmenable                     ( cfg_interrupt_msi_mmenable ),
    .cfg_interrupt_msi_mask_update                  ( cfg_interrupt_msi_mask_update ),
    .cfg_interrupt_msi_data                         ( cfg_interrupt_msi_data ),
    .cfg_interrupt_msi_select                       ( 4'b0000 ),
    .cfg_interrupt_msi_int                          ( cfg_interrupt_msi_int ),
    .cfg_interrupt_msi_pending_status               ( 32'b0 ),
    .cfg_interrupt_msi_pending_status_data_enable   ( 1'b0 ),
    .cfg_interrupt_msi_pending_status_function_num  ( 4'b0 ),
    .cfg_interrupt_msi_sent                         ( cfg_interrupt_msi_sent ),
    .cfg_interrupt_msi_fail                         ( cfg_interrupt_msi_fail ),

    .cfg_interrupt_msi_attr                         ( 3'b0 ),
    .cfg_interrupt_msi_tph_present                  ( 1'b0 ),
    .cfg_interrupt_msi_tph_type                     ( 2'b0 ),
    .cfg_interrupt_msi_tph_st_tag                   ( 9'b0 ),
    .cfg_interrupt_msi_function_number              ( 4'b0 ),
    .cfg_interrupt_msix_data                        ( cfg_interrupt_msix_data ),
    .cfg_interrupt_msix_address                     ( cfg_interrupt_msix_address ),
    .cfg_interrupt_msix_int                         ( cfg_interrupt_msix_int ),
    .cfg_interrupt_msix_enable                      ( cfg_interrupt_msix_enable ),
    .cfg_interrupt_msix_mask                        ( cfg_interrupt_msix_mask ),
    .cfg_interrupt_msix_vf_enable                   ( cfg_interrupt_msix_vf_enable ),
    .cfg_interrupt_msix_vf_mask                     ( cfg_interrupt_msix_vf_mask ),
     // EP only
    .cfg_flr_done                                   ( cfg_flr_done ),  
    .cfg_vf_flr_done                                ( cfg_vf_flr_done ),
    .cfg_hot_reset_out                              ( cfg_hot_reset_out ),
    .cfg_config_space_enable                        ( 1'b1 ),
    .cfg_req_pm_transition_l23_ready                ( cfg_req_pm_transition_l23_ready ),

    // RP only
    .cfg_hot_reset_in                               ( 1'b0 ),

    .cfg_ds_bus_number                              ( cfg_ds_bus_number ),
    .cfg_ds_device_number                           ( cfg_ds_device_number ),
    .cfg_ds_port_number                             ( cfg_ds_port_number ),

    //--------------------------------------------------------------------------
    //  Transceiver Debug And Status Ports
    //--------------------------------------------------------------------------
    .gt_pcieuserratedone                      (gt_pcieuserratedone),
    .gt_loopback                              (gt_loopback),             
    .gt_txprbsforceerr                        (gt_txprbsforceerr),            
    .gt_txinhibit                             (gt_txinhibit),            
    .gt_txprbssel                             (gt_txprbssel),            
    .gt_rxprbssel                             (gt_rxprbssel),          
    .gt_rxprbscntreset                        (gt_rxprbscntreset),             
    .gt_rxcdrlock                             (gt_rxcdrlock),         
    .gt_pcierateidle                          (gt_pcierateidle),
    .gt_pcieuserratestart                     (gt_pcieuserratestart),
    .gt_gtpowergood                           (gt_gtpowergood),  
    .gt_rxoutclk                              (gt_rxoutclk), 
    .gt_rxrecclkout                           (gt_rxrecclkout), 
    .gt_txresetdone                           (gt_txresetdone),    
    .gt_rxpmaresetdone                        (gt_rxpmaresetdone),      
    .gt_rxresetdone                           (gt_rxresetdone),        
    .gt_rxbufstatus                           (gt_rxbufstatus),            
    .gt_txphaligndone                         (gt_txphaligndone),            
    .gt_txphinitdone                          (gt_txphinitdone),         
    .gt_txdlysresetdone                       (gt_txdlysresetdone),         
    .gt_rxphaligndone                         (gt_rxphaligndone),        
    .gt_rxdlysresetdone                       (gt_rxdlysresetdone),          
    .gt_rxsyncdone                            (gt_rxsyncdone),        
    .gt_cplllock                              (gt_cplllock),              
    .gt_qpll0lock                             (gt_qpll0lock),            
    .gt_qpll1lock                             (gt_qpll1lock),            
    .gt_eyescandataerror                      (gt_eyescandataerror),               
    .gt_rxprbserr                             (gt_rxprbserr),           
    .gt_dmonitorout                           (gt_dmonitorout),           
    .gt_dmonfiforeset                         (gt_dmonfiforeset),
    .gt_dmonitorclk                           (gt_dmonitorclk),
    .gt_rxcommadet                            (gt_rxcommadet),                   
    .gt_txelecidle                            (gt_txelecidle),             
    .gt_rxvalid                               (gt_rxvalid),              
    .gt_bufgtdiv                              (gt_bufgtdiv),                 
    .phy_rrst_n                               (phy_rrst_n),
    .phy_txeq_ctrl                            (phy_txeq_ctrl),                  
    .phy_txeq_preset                          (phy_txeq_preset),                   
    .phy_txeq_fsm                             (phy_txeq_fsm),                  
    .phy_rxeq_fsm                             (phy_rxeq_fsm),                 
    .phy_rst_idle                             (phy_rst_idle),                              
    .gt_gen34_eios_det                        (gt_gen34_eios_det),    
    .gt_txoutclk                              (gt_txoutclk),          
    .gt_txoutclkfabric                        (gt_txoutclkfabric),    
    .gt_rxoutclkfabric                        (gt_rxoutclkfabric),    
    .gt_txoutclkpcs                           (gt_txoutclkpcs),       
    .gt_rxoutclkpcs                           (gt_rxoutclkpcs),       
    .gt_txpmareset                            (gt_txpmareset),        
    .gt_rxpmareset                            (gt_rxpmareset),        
    .gt_txpcsreset                            (gt_txpcsreset),        
    .gt_rxpcsreset                            (gt_rxpcsreset),        
    .gt_rxbufreset                            (gt_rxbufreset),        
    .gt_rxcdrreset                            (gt_rxcdrreset),        
    .gt_rxdfelpmreset                         (gt_rxdfelpmreset),     
    .gt_txprogdivresetdone                    (gt_txprogdivresetdone),
    .gt_txpmaresetdone                        (gt_txpmaresetdone),    
    .gt_txsyncdone                            (gt_txsyncdone),        
    .gt_rxprbslocked                          (gt_rxprbslocked),
    .phy_prst_n                               (phy_prst_n),
    .phy_rst_fsm                              (phy_rst_fsm),                 
    .gt_phystatus                             (gt_phystatus),                   
    .gt_rxstatus                              (gt_rxstatus),
    // -------------------------------------------------------------------------------------// 
    // JTAG Signals                                                                         //
    // -------------------------------------------------------------------------------------// 
    .pipe_tx0_rcvr_det                        (pipe_tx0_rcvr_det),
    .pipe_clk                                 (pipe_clk),
    .sys_clk_bufg                             (sys_clk_bufg),
    .pipe_tx0_powerdown                       (pipe_tx0_powerdown),

    //--------------------------------------------------------------------------------------//
    //  DRP Interface                                                                       //
    //--------------------------------------------------------------------------------------//
    .drp_rdy                                   (drp_rdy            ),
    .drp_do                                    (drp_do             ),
    .drp_clk                                   (drp_clk            ),
    .drp_en                                    (drp_en             ),
    .drp_we                                    (drp_we             ),
    .drp_addr                                  (drp_addr[9:0]      ),
    .drp_di                                    (drp_di             ),

    //--------------------------------------------------------------------------------------//
    //  System(SYS) Interface                                                               //
    //--------------------------------------------------------------------------------------//
    .sys_clk                                  (sys_clk),
    .sys_clk_gt                               (sys_clk_gt),
    .sys_reset                                (sys_rst_n)    // despite of postfix "_n" in its name - this signal can be active high/low depending on GUI selection
      ,
    .pipe_rx_0_sigs(pipe_rx_0_sigs),
    .pipe_rx_1_sigs(pipe_rx_1_sigs),
    .pipe_rx_2_sigs(pipe_rx_2_sigs),
    .pipe_rx_3_sigs(pipe_rx_3_sigs),
    .pipe_rx_4_sigs(pipe_rx_4_sigs),
    .pipe_rx_5_sigs(pipe_rx_5_sigs),
    .pipe_rx_6_sigs(pipe_rx_6_sigs),
    .pipe_rx_7_sigs(pipe_rx_7_sigs),
    .pipe_rx_8_sigs(pipe_rx_8_sigs),
    .pipe_rx_9_sigs(pipe_rx_9_sigs),
    .pipe_rx_10_sigs(pipe_rx_10_sigs),
    .pipe_rx_11_sigs(pipe_rx_11_sigs),
    .pipe_rx_12_sigs(pipe_rx_12_sigs),
    .pipe_rx_13_sigs(pipe_rx_13_sigs),
    .pipe_rx_14_sigs(pipe_rx_14_sigs),
    .pipe_rx_15_sigs(pipe_rx_15_sigs),
    .common_commands_out(common_commands_out),
    .pipe_tx_0_sigs(pipe_tx_0_sigs),
    .pipe_tx_1_sigs(pipe_tx_1_sigs),
    .pipe_tx_2_sigs(pipe_tx_2_sigs),
    .pipe_tx_3_sigs(pipe_tx_3_sigs),
    .pipe_tx_4_sigs(pipe_tx_4_sigs),
    .pipe_tx_5_sigs(pipe_tx_5_sigs),
    .pipe_tx_6_sigs(pipe_tx_6_sigs),
    .pipe_tx_7_sigs(pipe_tx_7_sigs),
    .pipe_tx_8_sigs(pipe_tx_8_sigs),
    .pipe_tx_9_sigs(pipe_tx_9_sigs),
    .pipe_tx_10_sigs(pipe_tx_10_sigs),
    .pipe_tx_11_sigs(pipe_tx_11_sigs),
    .pipe_tx_12_sigs(pipe_tx_12_sigs),
    .pipe_tx_13_sigs(pipe_tx_13_sigs),
    .pipe_tx_14_sigs(pipe_tx_14_sigs),
    .pipe_tx_15_sigs(pipe_tx_15_sigs)
  );

//   assign common_commands_out = 26'b0;
//   assign pipe_tx_0_sigs      = 84'b0;
//   assign pipe_tx_1_sigs      = 84'b0;
//   assign pipe_tx_2_sigs      = 84'b0;
//   assign pipe_tx_3_sigs      = 84'b0;
//   assign pipe_tx_4_sigs      = 84'b0;
//   assign pipe_tx_5_sigs      = 84'b0;
//   assign pipe_tx_6_sigs      = 84'b0;
//   assign pipe_tx_7_sigs      = 84'b0;

   //assign m_axib_wuser = {C_M_AXI_DATA_WIDTH/8{1'b0}};

   assign ext_ch_gt_drpclk = 1'b0;
   assign ext_ch_gt_drprdy = {PL_LINK_CAP_MAX_LINK_WIDTH{1'b0}};
   assign ext_ch_gt_drpdo  = {PL_LINK_CAP_MAX_LINK_WIDTH*16{1'b0}};

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
