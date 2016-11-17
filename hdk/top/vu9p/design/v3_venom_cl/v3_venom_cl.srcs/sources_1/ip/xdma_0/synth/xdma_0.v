// (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
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
// DO NOT MODIFY THIS FILE.


// IP VLNV: xilinx.com:ip:xdma:3.0
// IP Revision: 2

(* X_CORE_INFO = "xdma_0_core_top,Vivado 2016.3_AR68069" *)
(* CHECK_LICENSE_TYPE = "xdma_0,xdma_0_core_top,{}" *)
(* CORE_GENERATION_INFO = "xdma_0,xdma_0_core_top,{x_ipProduct=Vivado 2016.3_AR68069,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=xdma,x_ipVersion=3.0,x_ipCoreRevision=2,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,COMPONENT_NAME=xdma_0,PL_UPSTREAM_FACING=true,TL_LEGACY_MODE_ENABLE=false,PCIE_BLK_LOCN=8,PL_LINK_CAP_MAX_LINK_WIDTH=16,PL_LINK_CAP_MAX_LINK_SPEED=4,REF_CLK_FREQ=0,AXI_ADDR_WIDTH=64,AXI_DATA_WIDTH=512,CORE_CLK_FREQ=2,PLL_TYPE=2,USER_CLK_FREQ=3,SILICON_REV=Pre-Production,PIPE_SIM=FALSE,EXT_CH_GT_DRP=false,PCIE3_D\
RP=true,DEDICATE_PERST=false,SYS_RESET_POLARITY=0,MCAP_ENABLEMENT=NONE,EXT_STARTUP_PRIMITIVE=false,PF0_VENDOR_ID=0x1D0F,PF0_DEVICE_ID=0x1042,PF0_REVISION_ID=0x00,PF0_SUBSYSTEM_VENDOR_ID=0x10EE,PF0_SUBSYSTEM_ID=0x0007,PF0_CLASS_CODE=0x058000,AXILITE_MASTER_APERTURE_SIZE=0x12,AXILITE_MASTER_CONTROL=0x5,XDMA_APERTURE_SIZE=0x09,XDMA_CONTROL=0x5,AXIST_BYPASS_APERTURE_SIZE=0x14,AXIST_BYPASS_CONTROL=0x5,C_PCIEBAR2AXIBAR_0=0x0000000000000000,C_PCIEBAR2AXIBAR_1=0x0000000000000000,C_PCIEBAR2AXIBAR_2=0x000\
0000000000000,PF0_INTERRUPT_PIN=000,PF0_MSI_CAP_MULTIMSGCAP=0,C_COMP_TIMEOUT=0,SHARED_LOGIC=0,SHARED_LOGIC_CLK=false,SHARED_LOGIC_BOTH=false,SHARED_LOGIC_GTC=false,EN_TRANSCEIVER_STATUS_PORTS=TRUE,IS_BOARD_PROJECT=0,EN_GT_SELECTION=false,SELECT_QUAD=GTY_Quad_227,ULTRASCALE=FALSE,ULTRASCALE_PLUS=TRUE,V7_GEN3=FALSE,MSI_ENABLED=TRUE,DEV_PORT_TYPE=0,XDMA_AXI_INTF_MM=1,XDMA_PCIE_64BIT_EN=xdma_pcie_64bit_en,XDMA_AXILITE_MASTER=TRUE,XDMA_AXIST_BYPASS=TRUE,XDMA_RNUM_CHNL=4,XDMA_WNUM_CHNL=4,XDMA_AXILITE_\
SLAVE=TRUE,XDMA_NUM_USR_IRQ=16,XDMA_RNUM_RIDS=32,XDMA_WNUM_RIDS=32,C_M_AXI_ID_WIDTH=5,C_AXIBAR_NUM=1,C_FAMILY=virtexuplus,XDMA_NUM_PCIE_TAG=256,EN_AXI_MASTER_IF=TRUE,EN_WCHNL_0=TRUE,EN_WCHNL_1=TRUE,EN_WCHNL_2=TRUE,EN_WCHNL_3=TRUE,EN_WCHNL_4=FALSE,EN_WCHNL_5=FALSE,EN_WCHNL_6=FALSE,EN_WCHNL_7=FALSE,EN_RCHNL_0=TRUE,EN_RCHNL_1=TRUE,EN_RCHNL_2=TRUE,EN_RCHNL_3=TRUE,EN_RCHNL_4=FALSE,EN_RCHNL_5=FALSE,EN_RCHNL_6=FALSE,EN_RCHNL_7=FALSE,XDMA_DSC_BYPASS=FALSE,C_METERING_ON=1,RX_DETECT=0,DSC_BYPASS_RD=0,DSC_\
BYPASS_WR=0,XDMA_STS_PORTS=TRUE,MSIX_ENABLED=TRUE,WR_CH0_ENABLED=FALSE,WR_CH1_ENABLED=FALSE,WR_CH2_ENABLED=FALSE,WR_CH3_ENABLED=FALSE,RD_CH0_ENABLED=FALSE,RD_CH1_ENABLED=FALSE,RD_CH2_ENABLED=FALSE,RD_CH3_ENABLED=FALSE,CFG_MGMT_IF=TRUE,RQ_SEQ_NUM_IGNORE=0,CFG_EXT_IF=TRUE,C_PARITY_CHECK=1,C_PARITY_GEN=1,C_PARITY_PROP=0,EN_DEBUG_PORTS=FALSE,VU9P_BOARD=FALSE,ENABLE_JTAG_DBG=TRUE,MM_SLAVE_EN=1,DMA_EN=1,C_AXIBAR_0=0x0000000000000000,C_AXIBAR_1=0x0000000000000000,C_AXIBAR_2=0x0000000000000000,C_AXIBAR_\
3=0x0000000000000000,C_AXIBAR_4=0x0000000000000000,C_AXIBAR_5=0x0000000000000000,C_AXIBAR_HIGHADDR_0=0xffffffffffffffff,C_AXIBAR_HIGHADDR_1=0x0000000000000000,C_AXIBAR_HIGHADDR_2=0x0000000000000000,C_AXIBAR_HIGHADDR_3=0x0000000000000000,C_AXIBAR_HIGHADDR_4=0x0000000000000000,C_AXIBAR_HIGHADDR_5=0x0000000000000000,C_AXIBAR2PCIEBAR_0=0x0000000000000000,C_AXIBAR2PCIEBAR_1=0x0000000000000000,C_AXIBAR2PCIEBAR_2=0x0000000000000000,C_AXIBAR2PCIEBAR_3=0x0000000000000000,C_AXIBAR2PCIEBAR_4=0x000000000000\
0000,C_AXIBAR2PCIEBAR_5=0x0000000000000000,EN_AXI_SLAVE_IF=TRUE,C_INCLUDE_BAROFFSET_REG=1,C_BASEADDR=0x00000000,C_HIGHADDR=0x00000000,C_S_AXI_ID_WIDTH=5,C_S_AXI_NUM_READ=32,C_M_AXI_NUM_READ=8,C_S_AXI_NUM_WRITE=8,C_M_AXI_NUM_WRITE=8,MSIX_IMPL_EXT=TRUE,AXI_ACLK_LOOPBACK=FALSE,C_INCLUDE_RC=0}" *)
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0 (
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
  usr_irq_req,
  usr_irq_ack,
  msi_enable,
  msi_vector_width,
  m_axi_awready,
  m_axi_wready,
  m_axi_bid,
  m_axi_bresp,
  m_axi_bvalid,
  m_axi_arready,
  m_axi_rid,
  m_axi_rdata,
  m_axi_rresp,
  m_axi_rlast,
  m_axi_rvalid,
  m_axi_awid,
  m_axi_awaddr,
  m_axi_awlen,
  m_axi_awsize,
  m_axi_awburst,
  m_axi_awprot,
  m_axi_awvalid,
  m_axi_awlock,
  m_axi_awcache,
  m_axi_wdata,
  m_axi_wstrb,
  m_axi_wlast,
  m_axi_wvalid,
  m_axi_bready,
  m_axi_arid,
  m_axi_araddr,
  m_axi_arlen,
  m_axi_arsize,
  m_axi_arburst,
  m_axi_arprot,
  m_axi_arvalid,
  m_axi_arlock,
  m_axi_arcache,
  m_axi_rready,
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
  cfg_mgmt_addr,
  cfg_mgmt_write,
  cfg_mgmt_write_data,
  cfg_mgmt_byte_enable,
  cfg_mgmt_read,
  cfg_mgmt_read_data,
  cfg_mgmt_read_write_done,
  drp_rdy,
  drp_do,
  drp_clk,
  drp_en,
  drp_we,
  drp_addr,
  drp_di,
  m_axib_awid,
  m_axib_awaddr,
  m_axib_awlen,
  m_axib_awuser,
  m_axib_awsize,
  m_axib_awburst,
  m_axib_awprot,
  m_axib_awvalid,
  m_axib_awready,
  m_axib_awlock,
  m_axib_awcache,
  m_axib_wdata,
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
  m_axib_arlen,
  m_axib_aruser,
  m_axib_arsize,
  m_axib_arburst,
  m_axib_arprot,
  m_axib_arvalid,
  m_axib_arready,
  m_axib_arlock,
  m_axib_arcache,
  m_axib_rid,
  m_axib_rdata,
  m_axib_rresp,
  m_axib_rlast,
  m_axib_rvalid,
  m_axib_rready,
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
  c2h_sts_0,
  h2c_sts_0,
  c2h_sts_1,
  h2c_sts_1,
  c2h_sts_2,
  h2c_sts_2,
  c2h_sts_3,
  h2c_sts_3,
  gt_pcieuserratedone,
  gt_loopback,
  gt_txprbsforceerr,
  gt_txinhibit,
  gt_txprbssel,
  gt_rxprbssel,
  gt_rxprbscntreset,
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
  gt_dmonfiforeset,
  gt_dmonitorclk,
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
  cfg_ext_read_received,
  cfg_ext_write_received,
  cfg_ext_register_number,
  cfg_ext_function_number,
  cfg_ext_write_data,
  cfg_ext_write_byte_enable,
  cfg_ext_read_data,
  cfg_ext_read_data_valid,
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
  interrupt_out,
  s_axi_awid,
  s_axi_awaddr,
  s_axi_awregion,
  s_axi_awlen,
  s_axi_awsize,
  s_axi_awburst,
  s_axi_awvalid,
  s_axi_wdata,
  s_axi_wstrb,
  s_axi_wlast,
  s_axi_wvalid,
  s_axi_bready,
  s_axi_arid,
  s_axi_araddr,
  s_axi_arregion,
  s_axi_arlen,
  s_axi_arsize,
  s_axi_arburst,
  s_axi_arvalid,
  s_axi_rready,
  s_axi_awready,
  s_axi_wready,
  s_axi_bid,
  s_axi_bresp,
  s_axi_bvalid,
  s_axi_arready,
  s_axi_rid,
  s_axi_rdata,
  s_axi_rresp,
  s_axi_rlast,
  s_axi_rvalid,
  cfg_ltssm_state,
  cfg_function_status,
  cfg_max_read_req,
  cfg_max_payload,
  cfg_err_uncor_in,
  cfg_flr_in_process,
  cfg_flr_done,
  cfg_vf_flr_in_process,
  cfg_vf_flr_func_num,
  cfg_vf_flr_done,
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
  cfg_interrupt_msi_enable,
  cfg_interrupt_msix_enable,
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
  m_axis_cc_tready_out

               
);

   output wire[3:0] cfg_interrupt_msi_enable;
   output wire[3:0] cfg_interrupt_msix_enable;

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



(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.SYS_CLK CLK" *)
input wire sys_clk;
(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.sys_clk_gt CLK" *)
input wire sys_clk_gt;
(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 RST.sys_rst_n RST" *)
input wire sys_rst_n;
output wire user_lnk_up;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_7x_mgt:1.0 pcie_mgt txp" *)
output wire [15 : 0] pci_exp_txp;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_7x_mgt:1.0 pcie_mgt txn" *)
output wire [15 : 0] pci_exp_txn;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_7x_mgt:1.0 pcie_mgt rxp" *)
input wire [15 : 0] pci_exp_rxp;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_7x_mgt:1.0 pcie_mgt rxn" *)
input wire [15 : 0] pci_exp_rxn;
(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.axi_aclk CLK" *)
output wire axi_aclk;
(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 RST.axi_aresetn RST" *)
output wire axi_aresetn;
input wire [15 : 0] usr_irq_req;
output wire [15 : 0] usr_irq_ack;
output wire msi_enable;
output wire [2 : 0] msi_vector_width;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWREADY" *)
input wire m_axi_awready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WREADY" *)
input wire m_axi_wready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BID" *)
input wire [4 : 0] m_axi_bid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BRESP" *)
input wire [1 : 0] m_axi_bresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BVALID" *)
input wire m_axi_bvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARREADY" *)
input wire m_axi_arready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RID" *)
input wire [4 : 0] m_axi_rid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RDATA" *)
input wire [511 : 0] m_axi_rdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RRESP" *)
input wire [1 : 0] m_axi_rresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RLAST" *)
input wire m_axi_rlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RVALID" *)
input wire m_axi_rvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWID" *)
output wire [4 : 0] m_axi_awid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWADDR" *)
output wire [63 : 0] m_axi_awaddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLEN" *)
output wire [7 : 0] m_axi_awlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWSIZE" *)
output wire [2 : 0] m_axi_awsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWBURST" *)
output wire [1 : 0] m_axi_awburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWPROT" *)
output wire [2 : 0] m_axi_awprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWVALID" *)
output wire m_axi_awvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWLOCK" *)
output wire m_axi_awlock;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI AWCACHE" *)
output wire [3 : 0] m_axi_awcache;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WDATA" *)
output wire [511 : 0] m_axi_wdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WSTRB" *)
output wire [63 : 0] m_axi_wstrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WLAST" *)
output wire m_axi_wlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI WVALID" *)
output wire m_axi_wvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI BREADY" *)
output wire m_axi_bready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARID" *)
output wire [4 : 0] m_axi_arid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARADDR" *)
output wire [63 : 0] m_axi_araddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLEN" *)
output wire [7 : 0] m_axi_arlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARSIZE" *)
output wire [2 : 0] m_axi_arsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARBURST" *)
output wire [1 : 0] m_axi_arburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARPROT" *)
output wire [2 : 0] m_axi_arprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARVALID" *)
output wire m_axi_arvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARLOCK" *)
output wire m_axi_arlock;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI ARCACHE" *)
output wire [3 : 0] m_axi_arcache;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI RREADY" *)
output wire m_axi_rready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE AWADDR" *)
output wire [31 : 0] m_axil_awaddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE AWUSER" *)
output wire [10 : 0] m_axil_awuser;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE AWPROT" *)
output wire [2 : 0] m_axil_awprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE AWVALID" *)
output wire m_axil_awvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE AWREADY" *)
input wire m_axil_awready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE WDATA" *)
output wire [31 : 0] m_axil_wdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE WSTRB" *)
output wire [3 : 0] m_axil_wstrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE WVALID" *)
output wire m_axil_wvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE WREADY" *)
input wire m_axil_wready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE BVALID" *)
input wire m_axil_bvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE BRESP" *)
input wire [1 : 0] m_axil_bresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE BREADY" *)
output wire m_axil_bready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE ARADDR" *)
output wire [31 : 0] m_axil_araddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE ARUSER" *)
output wire [10 : 0] m_axil_aruser;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE ARPROT" *)
output wire [2 : 0] m_axil_arprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE ARVALID" *)
output wire m_axil_arvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE ARREADY" *)
input wire m_axil_arready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE RDATA" *)
input wire [31 : 0] m_axil_rdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE RRESP" *)
input wire [1 : 0] m_axil_rresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE RVALID" *)
input wire m_axil_rvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_LITE RREADY" *)
output wire m_axil_rready;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt ADDR" *)
input wire [18 : 0] cfg_mgmt_addr;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt WRITE_EN" *)
input wire cfg_mgmt_write;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt WRITE_DATA" *)
input wire [31 : 0] cfg_mgmt_write_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt BYTE_EN" *)
input wire [3 : 0] cfg_mgmt_byte_enable;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt READ_EN" *)
input wire cfg_mgmt_read;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt READ_DATA" *)
output wire [31 : 0] cfg_mgmt_read_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie_cfg_mgmt:1.0 pcie_cfg_mgmt READ_WRITE_DONE" *)
output wire cfg_mgmt_read_write_done;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DRDY" *)
output wire drp_rdy;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DO" *)
output wire [15 : 0] drp_do;
input wire drp_clk;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DEN" *)
input wire drp_en;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DWE" *)
input wire drp_we;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DADDR" *)
input wire [10 : 0] drp_addr;
(* X_INTERFACE_INFO = "xilinx.com:interface:drp:1.0 drp DI" *)
input wire [15 : 0] drp_di;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWID" *)
output wire [4 : 0] m_axib_awid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWADDR" *)
output wire [63 : 0] m_axib_awaddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWLEN" *)
output wire [7 : 0] m_axib_awlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWUSER" *)
output wire [7 : 0] m_axib_awuser;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWSIZE" *)
output wire [2 : 0] m_axib_awsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWBURST" *)
output wire [1 : 0] m_axib_awburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWPROT" *)
output wire [2 : 0] m_axib_awprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWVALID" *)
output wire m_axib_awvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWREADY" *)
input wire m_axib_awready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWLOCK" *)
output wire m_axib_awlock;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS AWCACHE" *)
output wire [3 : 0] m_axib_awcache;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS WDATA" *)
output wire [511 : 0] m_axib_wdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS WSTRB" *)
output wire [63 : 0] m_axib_wstrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS WLAST" *)
output wire m_axib_wlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS WVALID" *)
output wire m_axib_wvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS WREADY" *)
input wire m_axib_wready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS BID" *)
input wire [4 : 0] m_axib_bid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS BRESP" *)
input wire [1 : 0] m_axib_bresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS BVALID" *)
input wire m_axib_bvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS BREADY" *)
output wire m_axib_bready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARID" *)
output wire [4 : 0] m_axib_arid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARADDR" *)
output wire [63 : 0] m_axib_araddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARLEN" *)
output wire [7 : 0] m_axib_arlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARUSER" *)
output wire [7 : 0] m_axib_aruser;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARSIZE" *)
output wire [2 : 0] m_axib_arsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARBURST" *)
output wire [1 : 0] m_axib_arburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARPROT" *)
output wire [2 : 0] m_axib_arprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARVALID" *)
output wire m_axib_arvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARREADY" *)
input wire m_axib_arready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARLOCK" *)
output wire m_axib_arlock;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS ARCACHE" *)
output wire [3 : 0] m_axib_arcache;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RID" *)
input wire [4 : 0] m_axib_rid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RDATA" *)
input wire [511 : 0] m_axib_rdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RRESP" *)
input wire [1 : 0] m_axib_rresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RLAST" *)
input wire m_axib_rlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RVALID" *)
input wire m_axib_rvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 M_AXI_BYPASS RREADY" *)
output wire m_axib_rready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWADDR" *)
input wire [31 : 0] s_axil_awaddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWPROT" *)
input wire [2 : 0] s_axil_awprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWVALID" *)
input wire s_axil_awvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE AWREADY" *)
output wire s_axil_awready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE WDATA" *)
input wire [31 : 0] s_axil_wdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE WSTRB" *)
input wire [3 : 0] s_axil_wstrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE WVALID" *)
input wire s_axil_wvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE WREADY" *)
output wire s_axil_wready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE BVALID" *)
output wire s_axil_bvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE BRESP" *)
output wire [1 : 0] s_axil_bresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE BREADY" *)
input wire s_axil_bready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARADDR" *)
input wire [31 : 0] s_axil_araddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARPROT" *)
input wire [2 : 0] s_axil_arprot;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARVALID" *)
input wire s_axil_arvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE ARREADY" *)
output wire s_axil_arready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE RDATA" *)
output wire [31 : 0] s_axil_rdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE RRESP" *)
output wire [1 : 0] s_axil_rresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE RVALID" *)
output wire s_axil_rvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI_LITE RREADY" *)
input wire s_axil_rready;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports c2h_sts0" *)
output wire [7 : 0] c2h_sts_0;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports h2c_sts0" *)
output wire [7 : 0] h2c_sts_0;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports c2h_sts1" *)
output wire [7 : 0] c2h_sts_1;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports h2c_sts1" *)
output wire [7 : 0] h2c_sts_1;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports c2h_sts2" *)
output wire [7 : 0] c2h_sts_2;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports h2c_sts2" *)
output wire [7 : 0] h2c_sts_2;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports c2h_sts3" *)
output wire [7 : 0] c2h_sts_3;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:xdma_status_ports:1.0 dma_status_ports h2c_sts3" *)
output wire [7 : 0] h2c_sts_3;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug pcieuserratedone" *)
input wire [15 : 0] gt_pcieuserratedone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug loopback" *)
input wire [47 : 0] gt_loopback;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txprbsforceerr" *)
input wire [15 : 0] gt_txprbsforceerr;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txinhibit" *)
input wire [15 : 0] gt_txinhibit;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txprbssel" *)
input wire [63 : 0] gt_txprbssel;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxprbssel" *)
input wire [63 : 0] gt_rxprbssel;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxprbscntreset" *)
input wire [15 : 0] gt_rxprbscntreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txelecidle" *)
output wire [15 : 0] gt_txelecidle;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txresetdone" *)
output wire [15 : 0] gt_txresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxresetdone" *)
output wire [15 : 0] gt_rxresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxpmaresetdone" *)
output wire [15 : 0] gt_rxpmaresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txphaligndone" *)
output wire [15 : 0] gt_txphaligndone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txphinitdone" *)
output wire [15 : 0] gt_txphinitdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txdlysresetdone" *)
output wire [15 : 0] gt_txdlysresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxphaligndone" *)
output wire [15 : 0] gt_rxphaligndone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxdlysresetdone" *)
output wire [15 : 0] gt_rxdlysresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxsyncdone" *)
output wire [15 : 0] gt_rxsyncdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug eyescandataerror" *)
output wire [15 : 0] gt_eyescandataerror;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxprbserr" *)
output wire [15 : 0] gt_rxprbserr;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug dmonfiforeset" *)
input wire [15 : 0] gt_dmonfiforeset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug dmonitorclk" *)
input wire [15 : 0] gt_dmonitorclk;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug dmonitorout" *)
output wire [271 : 0] gt_dmonitorout;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxcommadet" *)
output wire [15 : 0] gt_rxcommadet;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug phystatus" *)
output wire [15 : 0] gt_phystatus;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxvalid" *)
output wire [15 : 0] gt_rxvalid;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxcdrlock" *)
output wire [15 : 0] gt_rxcdrlock;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rate_idle" *)
output wire [15 : 0] gt_pcierateidle;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug pcieuserratestart" *)
output wire [15 : 0] gt_pcieuserratestart;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug gtpowergood" *)
output wire [15 : 0] gt_gtpowergood;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug cpll_lock" *)
output wire [15 : 0] gt_cplllock;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxoutclk" *)
output wire [15 : 0] gt_rxoutclk;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxrecclkout" *)
output wire [15 : 0] gt_rxrecclkout;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug qpll1_lock" *)
output wire [2 : 0] gt_qpll1lock;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxstatus" *)
output wire [47 : 0] gt_rxstatus;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxbufstatus" *)
output wire [47 : 0] gt_rxbufstatus;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug bufgtdiv" *)
output wire [8 : 0] gt_bufgtdiv;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txeq_ctrl" *)
output wire [31 : 0] phy_txeq_ctrl;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txeq_preset" *)
output wire [63 : 0] phy_txeq_preset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rst_fsm" *)
output wire [3 : 0] phy_rst_fsm;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txeq_fsm" *)
output wire [47 : 0] phy_txeq_fsm;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxeq_fsm" *)
output wire [47 : 0] phy_rxeq_fsm;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rst_idle" *)
output wire phy_rst_idle;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rrst_n" *)
output wire phy_rrst_n;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug prst_n" *)
output wire phy_prst_n;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext read_received" *)
output wire cfg_ext_read_received;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext write_received" *)
output wire cfg_ext_write_received;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext register_number" *)
output wire [9 : 0] cfg_ext_register_number;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext function_number" *)
output wire [7 : 0] cfg_ext_function_number;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext write_data" *)
output wire [31 : 0] cfg_ext_write_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext write_byte_enable" *)
output wire [3 : 0] cfg_ext_write_byte_enable;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext read_data" *)
input wire [31 : 0] cfg_ext_read_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:pcie3_cfg_ext:1.0 pcie_cfg_ext read_data_valid" *)
input wire cfg_ext_read_data_valid;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug qpll0_lock" *)
output wire [3 : 0] gt_qpll0lock;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug gen34_eios_det" *)
output wire [15 : 0] gt_gen34_eios_det;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txoutclk" *)
output wire [15 : 0] gt_txoutclk;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txoutclkfabric" *)
output wire [15 : 0] gt_txoutclkfabric;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxoutclkfabric" *)
output wire [15 : 0] gt_rxoutclkfabric;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txoutclkpcs" *)
output wire [15 : 0] gt_txoutclkpcs;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxoutclkpcs" *)
output wire [15 : 0] gt_rxoutclkpcs;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txpmareset" *)
input wire [15 : 0] gt_txpmareset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxpmareset" *)
input wire [15 : 0] gt_rxpmareset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txpcsreset" *)
input wire [15 : 0] gt_txpcsreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxpcsreset" *)
input wire [15 : 0] gt_rxpcsreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxbufreset" *)
input wire [15 : 0] gt_rxbufreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxcdrreset" *)
input wire [15 : 0] gt_rxcdrreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxdfelpmreset" *)
input wire [15 : 0] gt_rxdfelpmreset;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txprogdivresetdone" *)
output wire [15 : 0] gt_txprogdivresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txpmaresetdone" *)
output wire [15 : 0] gt_txpmaresetdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug txsyncdone" *)
output wire [15 : 0] gt_txsyncdone;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug rxprbslocked" *)
output wire [15 : 0] gt_rxprbslocked;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug pipe_tx0_rcvr_det_o" *)
output wire pipe_tx0_rcvr_det;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug pipe_clk_o" *)
output wire pipe_clk;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug sys_clk_bufg_o" *)
output wire sys_clk_bufg;
(* X_INTERFACE_INFO = "xilinx.com:display_xdma:pcie4_us_plus_transceiver_debug:1.0 pcie4_us_plus_transceiver_debug pipe_tx0_powerdown_o" *)
output wire [1 : 0] pipe_tx0_powerdown;
output wire interrupt_out;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWID" *)
input wire [4 : 0] s_axi_awid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWADDR" *)
input wire [63 : 0] s_axi_awaddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREGION" *)
input wire [3 : 0] s_axi_awregion;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWLEN" *)
input wire [7 : 0] s_axi_awlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWSIZE" *)
input wire [2 : 0] s_axi_awsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWBURST" *)
input wire [1 : 0] s_axi_awburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWVALID" *)
input wire s_axi_awvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WDATA" *)
input wire [511 : 0] s_axi_wdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WSTRB" *)
input wire [63 : 0] s_axi_wstrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WLAST" *)
input wire s_axi_wlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WVALID" *)
input wire s_axi_wvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BREADY" *)
input wire s_axi_bready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARID" *)
input wire [4 : 0] s_axi_arid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARADDR" *)
input wire [63 : 0] s_axi_araddr;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREGION" *)
input wire [3 : 0] s_axi_arregion;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARLEN" *)
input wire [7 : 0] s_axi_arlen;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARSIZE" *)
input wire [2 : 0] s_axi_arsize;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARBURST" *)
input wire [1 : 0] s_axi_arburst;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARVALID" *)
input wire s_axi_arvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RREADY" *)
input wire s_axi_rready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI AWREADY" *)
output wire s_axi_awready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI WREADY" *)
output wire s_axi_wready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BID" *)
output wire [4 : 0] s_axi_bid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BRESP" *)
output wire [1 : 0] s_axi_bresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI BVALID" *)
output wire s_axi_bvalid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI ARREADY" *)
output wire s_axi_arready;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RID" *)
output wire [4 : 0] s_axi_rid;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RDATA" *)
output wire [511 : 0] s_axi_rdata;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RRESP" *)
output wire [1 : 0] s_axi_rresp;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RLAST" *)
output wire s_axi_rlast;
(* X_INTERFACE_INFO = "xilinx.com:interface:aximm:1.0 S_AXI RVALID" *)
output wire s_axi_rvalid;
output wire [5 : 0] cfg_ltssm_state;
output wire [15 : 0] cfg_function_status;
output wire [2 : 0] cfg_max_read_req;
output wire [1 : 0] cfg_max_payload;
input wire cfg_err_uncor_in;
output wire [3 : 0] cfg_flr_in_process;
input wire [3 : 0] cfg_flr_done;
output wire [251 : 0] cfg_vf_flr_in_process;
input wire [7 : 0] cfg_vf_flr_func_num;
input wire [0 : 0] cfg_vf_flr_done;

   output wire [511:0]  s_axis_cq_tdata_out;
   output wire [182:0]  s_axis_cq_tuser_out;
   output wire          s_axis_cq_tlast_out;
   output wire [15:0]   s_axis_cq_tkeep_out;
   output wire          s_axis_cq_tvalid_out;
   output wire          s_axis_cq_tready_out;
   
   output wire [511:0]  m_axis_cc_tdata_out;
   output wire [80:0]   m_axis_cc_tuser_out;
   output wire          m_axis_cc_tlast_out;
   output wire [15:0]   m_axis_cc_tkeep_out;
   output wire          m_axis_cc_tvalid_out;
   output wire [3:0]    m_axis_cc_tready_out;
   
  xdma_0_core_top #(
    .COMPONENT_NAME("xdma_0"),
    .PL_UPSTREAM_FACING("true"),
    .TL_LEGACY_MODE_ENABLE("false"),
    .PCIE_BLK_LOCN(8),
    .PL_LINK_CAP_MAX_LINK_WIDTH(16),
    .PL_LINK_CAP_MAX_LINK_SPEED(4),
    .REF_CLK_FREQ(0),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(512),
    .CORE_CLK_FREQ(2),
    .PLL_TYPE(2),
    .USER_CLK_FREQ(3),
    .SILICON_REV("Pre-Production"),
    .PIPE_SIM("FALSE"),
    .EXT_CH_GT_DRP("false"),
    .PCIE3_DRP("true"),
    .DEDICATE_PERST("false"),
    .SYS_RESET_POLARITY(0),
    .MCAP_ENABLEMENT("NONE"),
    .EXT_STARTUP_PRIMITIVE("false"),
    .PF0_VENDOR_ID('H1D0F),
    .PF0_DEVICE_ID('H1042),
    .PF0_REVISION_ID('H00),
    .PF0_SUBSYSTEM_VENDOR_ID('H10EE),
    .PF0_SUBSYSTEM_ID('H0007),
    .PF0_CLASS_CODE('H058000),
    .AXILITE_MASTER_APERTURE_SIZE('H12),
    .AXILITE_MASTER_CONTROL('H5),
    .XDMA_APERTURE_SIZE('H09),
    .XDMA_CONTROL('H5),
    .AXIST_BYPASS_APERTURE_SIZE('H14),
    .AXIST_BYPASS_CONTROL('H5),
    .C_PCIEBAR2AXIBAR_0('H0000000000000000),
    .C_PCIEBAR2AXIBAR_1('H0000000000000000),
    .C_PCIEBAR2AXIBAR_2('H0000000000000000),
    .PF0_INTERRUPT_PIN('D000),
    .PF0_MSI_CAP_MULTIMSGCAP(0),
    .C_COMP_TIMEOUT(0),
    .SHARED_LOGIC(0),
    .SHARED_LOGIC_CLK("false"),
    .SHARED_LOGIC_BOTH("false"),
    .SHARED_LOGIC_GTC("false"),
    .EN_TRANSCEIVER_STATUS_PORTS("TRUE"),
    .IS_BOARD_PROJECT(0),
    .EN_GT_SELECTION("false"),
    .SELECT_QUAD("GTY_Quad_227"),
    .ULTRASCALE("FALSE"),
    .ULTRASCALE_PLUS("TRUE"),
    .V7_GEN3("FALSE"),
    .MSI_ENABLED("TRUE"),
    .DEV_PORT_TYPE(0),
    .XDMA_AXI_INTF_MM(1),
    .XDMA_PCIE_64BIT_EN("xdma_pcie_64bit_en"),
    .XDMA_AXILITE_MASTER("TRUE"),
    .XDMA_AXIST_BYPASS("TRUE"),
    .XDMA_RNUM_CHNL(4),
    .XDMA_WNUM_CHNL(4),
    .XDMA_AXILITE_SLAVE("TRUE"),
    .XDMA_NUM_USR_IRQ(16),
    .XDMA_RNUM_RIDS(32),
    .XDMA_WNUM_RIDS(32),
    .C_M_AXI_ID_WIDTH(5),
    .C_AXIBAR_NUM(1),
    .C_FAMILY("virtexuplus"),
    .XDMA_NUM_PCIE_TAG(256),
    .EN_AXI_MASTER_IF("TRUE"),
    .EN_WCHNL_0("TRUE"),
    .EN_WCHNL_1("TRUE"),
    .EN_WCHNL_2("TRUE"),
    .EN_WCHNL_3("TRUE"),
    .EN_WCHNL_4("FALSE"),
    .EN_WCHNL_5("FALSE"),
    .EN_WCHNL_6("FALSE"),
    .EN_WCHNL_7("FALSE"),
    .EN_RCHNL_0("TRUE"),
    .EN_RCHNL_1("TRUE"),
    .EN_RCHNL_2("TRUE"),
    .EN_RCHNL_3("TRUE"),
    .EN_RCHNL_4("FALSE"),
    .EN_RCHNL_5("FALSE"),
    .EN_RCHNL_6("FALSE"),
    .EN_RCHNL_7("FALSE"),
    .XDMA_DSC_BYPASS("FALSE"),
    .C_METERING_ON(1),
    .RX_DETECT(0),
    .DSC_BYPASS_RD(0),
    .DSC_BYPASS_WR(0),
    .XDMA_STS_PORTS("TRUE"),
    .MSIX_ENABLED("TRUE"),
    .WR_CH0_ENABLED("FALSE"),
    .WR_CH1_ENABLED("FALSE"),
    .WR_CH2_ENABLED("FALSE"),
    .WR_CH3_ENABLED("FALSE"),
    .RD_CH0_ENABLED("FALSE"),
    .RD_CH1_ENABLED("FALSE"),
    .RD_CH2_ENABLED("FALSE"),
    .RD_CH3_ENABLED("FALSE"),
    .CFG_MGMT_IF("TRUE"),
    .RQ_SEQ_NUM_IGNORE(0),
    .CFG_EXT_IF("TRUE"),
    .C_PARITY_CHECK(1),
    .C_PARITY_GEN(1),
    .C_PARITY_PROP(0),
    .EN_DEBUG_PORTS("FALSE"),
    .VU9P_BOARD("FALSE"),
    .ENABLE_JTAG_DBG("TRUE"),
    .MM_SLAVE_EN(1),
    .DMA_EN(1),
    .C_AXIBAR_0('H0000000000000000),
    .C_AXIBAR_1('H0000000000000000),
    .C_AXIBAR_2('H0000000000000000),
    .C_AXIBAR_3('H0000000000000000),
    .C_AXIBAR_4('H0000000000000000),
    .C_AXIBAR_5('H0000000000000000),
    .C_AXIBAR_HIGHADDR_0('Hffffffffffffffff),
    .C_AXIBAR_HIGHADDR_1('H0000000000000000),
    .C_AXIBAR_HIGHADDR_2('H0000000000000000),
    .C_AXIBAR_HIGHADDR_3('H0000000000000000),
    .C_AXIBAR_HIGHADDR_4('H0000000000000000),
    .C_AXIBAR_HIGHADDR_5('H0000000000000000),
    .C_AXIBAR2PCIEBAR_0('H0000000000000000),
    .C_AXIBAR2PCIEBAR_1('H0000000000000000),
    .C_AXIBAR2PCIEBAR_2('H0000000000000000),
    .C_AXIBAR2PCIEBAR_3('H0000000000000000),
    .C_AXIBAR2PCIEBAR_4('H0000000000000000),
    .C_AXIBAR2PCIEBAR_5('H0000000000000000),
    .EN_AXI_SLAVE_IF("TRUE"),
    .C_INCLUDE_BAROFFSET_REG(1),
    .C_BASEADDR('H00000000),
    .C_HIGHADDR('H00000000),
    .C_S_AXI_ID_WIDTH(5),
    .C_S_AXI_NUM_READ(32),
    .C_M_AXI_NUM_READ(8),
    .C_S_AXI_NUM_WRITE(8),
    .C_M_AXI_NUM_WRITE(8),
    .MSIX_IMPL_EXT("TRUE"),
    .AXI_ACLK_LOOPBACK("FALSE"),
    .C_INCLUDE_RC(0)
  ) inst (
    .sys_clk(sys_clk),
    .sys_clk_gt(sys_clk_gt),
    .sys_rst_n(sys_rst_n),
    .user_lnk_up(user_lnk_up),
    .pci_exp_txp(pci_exp_txp),
    .pci_exp_txn(pci_exp_txn),
    .pci_exp_rxp(pci_exp_rxp),
    .pci_exp_rxn(pci_exp_rxn),
    .axi_aclk(axi_aclk),
    .axi_aresetn(axi_aresetn),
    .axi_ctl_aclk(1'B0),
    .axi_ctl_aresetn(),
    .usr_irq_req(usr_irq_req),
    .usr_irq_ack(usr_irq_ack),
    .msi_enable(msi_enable),
    .msi_vector_width(msi_vector_width),
    .m_axi_awready(m_axi_awready),
    .m_axi_wready(m_axi_wready),
    .m_axi_bid(m_axi_bid),
    .m_axi_bresp(m_axi_bresp),
    .m_axi_bvalid(m_axi_bvalid),
    .m_axi_arready(m_axi_arready),
    .m_axi_rid(m_axi_rid),
    .m_axi_rdata(m_axi_rdata),
    .m_axi_ruser(64'B0),
    .m_axi_rresp(m_axi_rresp),
    .m_axi_rlast(m_axi_rlast),
    .m_axi_rvalid(m_axi_rvalid),
    .m_axi_awid(m_axi_awid),
    .m_axi_awaddr(m_axi_awaddr),
    .m_axi_awlen(m_axi_awlen),
    .m_axi_awsize(m_axi_awsize),
    .m_axi_awburst(m_axi_awburst),
    .m_axi_awprot(m_axi_awprot),
    .m_axi_awvalid(m_axi_awvalid),
    .m_axi_awlock(m_axi_awlock),
    .m_axi_awcache(m_axi_awcache),
    .m_axi_wdata(m_axi_wdata),
    .m_axi_wuser(),
    .m_axi_wstrb(m_axi_wstrb),
    .m_axi_wlast(m_axi_wlast),
    .m_axi_wvalid(m_axi_wvalid),
    .m_axi_bready(m_axi_bready),
    .m_axi_arid(m_axi_arid),
    .m_axi_araddr(m_axi_araddr),
    .m_axi_arlen(m_axi_arlen),
    .m_axi_arsize(m_axi_arsize),
    .m_axi_arburst(m_axi_arburst),
    .m_axi_arprot(m_axi_arprot),
    .m_axi_arvalid(m_axi_arvalid),
    .m_axi_arlock(m_axi_arlock),
    .m_axi_arcache(m_axi_arcache),
    .m_axi_rready(m_axi_rready),
    .m_axil_awaddr(m_axil_awaddr),
    .m_axil_awuser(m_axil_awuser),
    .m_axil_awprot(m_axil_awprot),
    .m_axil_awvalid(m_axil_awvalid),
    .m_axil_awready(m_axil_awready),
    .m_axil_wdata(m_axil_wdata),
    .m_axil_wstrb(m_axil_wstrb),
    .m_axil_wvalid(m_axil_wvalid),
    .m_axil_wready(m_axil_wready),
    .m_axil_bvalid(m_axil_bvalid),
    .m_axil_bresp(m_axil_bresp),
    .m_axil_bready(m_axil_bready),
    .m_axil_araddr(m_axil_araddr),
    .m_axil_aruser(m_axil_aruser),
    .m_axil_arprot(m_axil_arprot),
    .m_axil_arvalid(m_axil_arvalid),
    .m_axil_arready(m_axil_arready),
    .m_axil_rdata(m_axil_rdata),
    .m_axil_rresp(m_axil_rresp),
    .m_axil_rvalid(m_axil_rvalid),
    .m_axil_rready(m_axil_rready),
    .cfg_mgmt_addr(cfg_mgmt_addr),
    .cfg_mgmt_write(cfg_mgmt_write),
    .cfg_mgmt_write_data(cfg_mgmt_write_data),
    .cfg_mgmt_byte_enable(cfg_mgmt_byte_enable),
    .cfg_mgmt_read(cfg_mgmt_read),
    .cfg_mgmt_read_data(cfg_mgmt_read_data),
    .cfg_mgmt_read_write_done(cfg_mgmt_read_write_done),
    .cfg_mgmt_type1_cfg_reg_access(1'B0),
    .drp_rdy(drp_rdy),
    .drp_do(drp_do),
    .drp_clk(drp_clk),
    .drp_en(drp_en),
    .drp_we(drp_we),
    .drp_addr(drp_addr),
    .drp_di(drp_di),
    .common_commands_in(common_commands_in),
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
    .pipe_tx_15_sigs(pipe_tx_15_sigs),

    .m_axib_awid(m_axib_awid),
    .m_axib_awaddr(m_axib_awaddr),
    .m_axib_awlen(m_axib_awlen),
    .m_axib_awuser(m_axib_awuser),
    .m_axib_awsize(m_axib_awsize),
    .m_axib_awburst(m_axib_awburst),
    .m_axib_awprot(m_axib_awprot),
    .m_axib_awvalid(m_axib_awvalid),
    .m_axib_awready(m_axib_awready),
    .m_axib_awlock(m_axib_awlock),
    .m_axib_awcache(m_axib_awcache),
    .m_axib_wdata(m_axib_wdata),
    .m_axib_wstrb(m_axib_wstrb),
    .m_axib_wlast(m_axib_wlast),
    .m_axib_wvalid(m_axib_wvalid),
    .m_axib_wready(m_axib_wready),
    .m_axib_wuser(),
    .m_axib_bid(m_axib_bid),
    .m_axib_bresp(m_axib_bresp),
    .m_axib_bvalid(m_axib_bvalid),
    .m_axib_bready(m_axib_bready),
    .m_axib_arid(m_axib_arid),
    .m_axib_araddr(m_axib_araddr),
    .m_axib_arlen(m_axib_arlen),
    .m_axib_aruser(m_axib_aruser),
    .m_axib_arsize(m_axib_arsize),
    .m_axib_arburst(m_axib_arburst),
    .m_axib_arprot(m_axib_arprot),
    .m_axib_arvalid(m_axib_arvalid),
    .m_axib_arready(m_axib_arready),
    .m_axib_arlock(m_axib_arlock),
    .m_axib_arcache(m_axib_arcache),
    .m_axib_rid(m_axib_rid),
    .m_axib_rdata(m_axib_rdata),
    .m_axib_ruser(64'B0),
    .m_axib_rresp(m_axib_rresp),
    .m_axib_rlast(m_axib_rlast),
    .m_axib_rvalid(m_axib_rvalid),
    .m_axib_rready(m_axib_rready),
    .s_axis_c2h_tdata_0(512'B0),
    .s_axis_c2h_tlast_0(1'B0),
    .s_axis_c2h_tvalid_0(1'B0),
    .s_axis_c2h_tready_0(),
    .s_axis_c2h_tuser_0(64'B0),
    .s_axis_c2h_tkeep_0(64'B0),
    .m_axis_h2c_tdata_0(),
    .m_axis_h2c_tlast_0(),
    .m_axis_h2c_tvalid_0(),
    .m_axis_h2c_tready_0(1'B0),
    .m_axis_h2c_tuser_0(),
    .m_axis_h2c_tkeep_0(),
    .s_axis_c2h_tdata_1(512'B0),
    .s_axis_c2h_tlast_1(1'B0),
    .s_axis_c2h_tvalid_1(1'B0),
    .s_axis_c2h_tready_1(),
    .s_axis_c2h_tuser_1(64'B0),
    .s_axis_c2h_tkeep_1(64'B0),
    .m_axis_h2c_tdata_1(),
    .m_axis_h2c_tlast_1(),
    .m_axis_h2c_tvalid_1(),
    .m_axis_h2c_tready_1(1'B0),
    .m_axis_h2c_tuser_1(),
    .m_axis_h2c_tkeep_1(),
    .s_axis_c2h_tdata_2(512'B0),
    .s_axis_c2h_tlast_2(1'B0),
    .s_axis_c2h_tvalid_2(1'B0),
    .s_axis_c2h_tready_2(),
    .s_axis_c2h_tuser_2(64'B0),
    .s_axis_c2h_tkeep_2(64'B0),
    .m_axis_h2c_tdata_2(),
    .m_axis_h2c_tlast_2(),
    .m_axis_h2c_tvalid_2(),
    .m_axis_h2c_tready_2(1'B0),
    .m_axis_h2c_tuser_2(),
    .m_axis_h2c_tkeep_2(),
    .s_axis_c2h_tdata_3(512'B0),
    .s_axis_c2h_tlast_3(1'B0),
    .s_axis_c2h_tvalid_3(1'B0),
    .s_axis_c2h_tready_3(),
    .s_axis_c2h_tuser_3(64'B0),
    .s_axis_c2h_tkeep_3(64'B0),
    .m_axis_h2c_tdata_3(),
    .m_axis_h2c_tlast_3(),
    .m_axis_h2c_tvalid_3(),
    .m_axis_h2c_tready_3(1'B0),
    .m_axis_h2c_tuser_3(),
    .m_axis_h2c_tkeep_3(),
    .s_axil_awaddr(s_axil_awaddr),
    .s_axil_awprot(s_axil_awprot),
    .s_axil_awvalid(s_axil_awvalid),
    .s_axil_awready(s_axil_awready),
    .s_axil_wdata(s_axil_wdata),
    .s_axil_wstrb(s_axil_wstrb),
    .s_axil_wvalid(s_axil_wvalid),
    .s_axil_wready(s_axil_wready),
    .s_axil_bvalid(s_axil_bvalid),
    .s_axil_bresp(s_axil_bresp),
    .s_axil_bready(s_axil_bready),
    .s_axil_araddr(s_axil_araddr),
    .s_axil_arprot(s_axil_arprot),
    .s_axil_arvalid(s_axil_arvalid),
    .s_axil_arready(s_axil_arready),
    .s_axil_rdata(s_axil_rdata),
    .s_axil_rresp(s_axil_rresp),
    .s_axil_rvalid(s_axil_rvalid),
    .s_axil_rready(s_axil_rready),
    .c2h_dsc_byp_ready_0(),
    .c2h_dsc_byp_src_addr_0(64'B0),
    .c2h_dsc_byp_dst_addr_0(64'B0),
    .c2h_dsc_byp_len_0(28'B0),
    .c2h_dsc_byp_ctl_0(16'B0),
    .c2h_dsc_byp_load_0(1'B0),
    .c2h_dsc_byp_ready_1(),
    .c2h_dsc_byp_src_addr_1(64'B0),
    .c2h_dsc_byp_dst_addr_1(64'B0),
    .c2h_dsc_byp_len_1(28'B0),
    .c2h_dsc_byp_ctl_1(16'B0),
    .c2h_dsc_byp_load_1(1'B0),
    .c2h_dsc_byp_ready_2(),
    .c2h_dsc_byp_src_addr_2(64'B0),
    .c2h_dsc_byp_dst_addr_2(64'B0),
    .c2h_dsc_byp_len_2(28'B0),
    .c2h_dsc_byp_ctl_2(16'B0),
    .c2h_dsc_byp_load_2(1'B0),
    .c2h_dsc_byp_ready_3(),
    .c2h_dsc_byp_src_addr_3(64'B0),
    .c2h_dsc_byp_dst_addr_3(64'B0),
    .c2h_dsc_byp_len_3(28'B0),
    .c2h_dsc_byp_ctl_3(16'B0),
    .c2h_dsc_byp_load_3(1'B0),
    .h2c_dsc_byp_ready_0(),
    .h2c_dsc_byp_src_addr_0(64'B0),
    .h2c_dsc_byp_dst_addr_0(64'B0),
    .h2c_dsc_byp_len_0(28'B0),
    .h2c_dsc_byp_ctl_0(16'B0),
    .h2c_dsc_byp_load_0(1'B0),
    .h2c_dsc_byp_ready_1(),
    .h2c_dsc_byp_src_addr_1(64'B0),
    .h2c_dsc_byp_dst_addr_1(64'B0),
    .h2c_dsc_byp_len_1(28'B0),
    .h2c_dsc_byp_ctl_1(16'B0),
    .h2c_dsc_byp_load_1(1'B0),
    .h2c_dsc_byp_ready_2(),
    .h2c_dsc_byp_src_addr_2(64'B0),
    .h2c_dsc_byp_dst_addr_2(64'B0),
    .h2c_dsc_byp_len_2(28'B0),
    .h2c_dsc_byp_ctl_2(16'B0),
    .h2c_dsc_byp_load_2(1'B0),
    .h2c_dsc_byp_ready_3(),
    .h2c_dsc_byp_src_addr_3(64'B0),
    .h2c_dsc_byp_dst_addr_3(64'B0),
    .h2c_dsc_byp_len_3(28'B0),
    .h2c_dsc_byp_ctl_3(16'B0),
    .h2c_dsc_byp_load_3(1'B0),
    .c2h_sts_0(c2h_sts_0),
    .h2c_sts_0(h2c_sts_0),
    .c2h_sts_1(c2h_sts_1),
    .h2c_sts_1(h2c_sts_1),
    .c2h_sts_2(c2h_sts_2),
    .h2c_sts_2(h2c_sts_2),
    .c2h_sts_3(c2h_sts_3),
    .h2c_sts_3(h2c_sts_3),
    .pipe_txprbssel(3'B0),
    .pipe_rxprbssel(3'B0),
    .pipe_txprbsforceerr(1'B0),
    .pipe_rxprbscntreset(1'B0),
    .pipe_loopback(3'B0),
    .pipe_rxprbserr(),
    .pipe_txinhibit(16'B0),
    .pipe_rst_fsm(),
    .pipe_qrst_fsm(),
    .pipe_rate_fsm(),
    .pipe_sync_fsm_tx(),
    .pipe_sync_fsm_rx(),
    .pipe_drp_fsm(),
    .pipe_rst_idle(),
    .pipe_qrst_idle(),
    .pipe_rate_idle(),
    .pipe_eyescandataerror(),
    .pipe_rxstatus(),
    .pipe_dmonitorout(),
    .pipe_cpll_lock(),
    .pipe_qpll_lock(),
    .pipe_rxpmaresetdone(),
    .pipe_rxbufstatus(),
    .pipe_txphaligndone(),
    .pipe_txphinitdone(),
    .pipe_txdlysresetdone(),
    .pipe_rxphaligndone(),
    .pipe_rxdlysresetdone(),
    .pipe_rxsyncdone(),
    .pipe_rxdisperr(),
    .pipe_rxnotintable(),
    .pipe_rxcommadet(),
    .gt_ch_drp_rdy(),
    .pipe_debug_0(),
    .pipe_debug_1(),
    .pipe_debug_2(),
    .pipe_debug_3(),
    .pipe_debug_4(),
    .pipe_debug_5(),
    .pipe_debug_6(),
    .pipe_debug_7(),
    .pipe_debug_8(),
    .pipe_debug_9(),
    .pipe_debug(),
    .gt_pcieuserratedone(gt_pcieuserratedone),
    .gt_loopback(gt_loopback),
    .gt_txprbsforceerr(gt_txprbsforceerr),
    .gt_txinhibit(gt_txinhibit),
    .gt_txprbssel(gt_txprbssel),
    .gt_rxprbssel(gt_rxprbssel),
    .gt_rxprbscntreset(gt_rxprbscntreset),
    .gt_txelecidle(gt_txelecidle),
    .gt_txresetdone(gt_txresetdone),
    .gt_rxresetdone(gt_rxresetdone),
    .gt_rxpmaresetdone(gt_rxpmaresetdone),
    .gt_txphaligndone(gt_txphaligndone),
    .gt_txphinitdone(gt_txphinitdone),
    .gt_txdlysresetdone(gt_txdlysresetdone),
    .gt_rxphaligndone(gt_rxphaligndone),
    .gt_rxdlysresetdone(gt_rxdlysresetdone),
    .gt_rxsyncdone(gt_rxsyncdone),
    .gt_eyescandataerror(gt_eyescandataerror),
    .gt_rxprbserr(gt_rxprbserr),
    .gt_dmonfiforeset(gt_dmonfiforeset),
    .gt_dmonitorclk(gt_dmonitorclk),
    .gt_dmonitorout(gt_dmonitorout),
    .gt_rxcommadet(gt_rxcommadet),
    .gt_phystatus(gt_phystatus),
    .gt_rxvalid(gt_rxvalid),
    .gt_rxcdrlock(gt_rxcdrlock),
    .gt_pcierateidle(gt_pcierateidle),
    .gt_pcieuserratestart(gt_pcieuserratestart),
    .gt_gtpowergood(gt_gtpowergood),
    .gt_cplllock(gt_cplllock),
    .gt_rxoutclk(gt_rxoutclk),
    .gt_rxrecclkout(gt_rxrecclkout),
    .gt_qpll1lock(gt_qpll1lock),
    .gt_rxstatus(gt_rxstatus),
    .gt_rxbufstatus(gt_rxbufstatus),
    .gt_bufgtdiv(gt_bufgtdiv),
    .phy_txeq_ctrl(phy_txeq_ctrl),
    .phy_txeq_preset(phy_txeq_preset),
    .phy_rst_fsm(phy_rst_fsm),
    .phy_txeq_fsm(phy_txeq_fsm),
    .phy_rxeq_fsm(phy_rxeq_fsm),
    .phy_rst_idle(phy_rst_idle),
    .phy_rrst_n(phy_rrst_n),
    .phy_prst_n(phy_prst_n),
    .ext_ch_gt_drpen(16'B0),
    .ext_ch_gt_drpwe(16'B0),
    .ext_ch_gt_drpaddr(144'B0),
    .ext_ch_gt_drpdi(256'B0),
    .ext_ch_gt_drpclk(),
    .ext_ch_gt_drprdy(),
    .ext_ch_gt_drpdo(),
    .mcap_design_switch(),
    .mcap_eos_in(1'B0),
    .startup_cfgclk(),
    .startup_cfgmclk(),
    .startup_di(),
    .startup_eos(),
    .startup_preq(),
    .startup_do(4'B0),
    .startup_dts(4'B0),
    .startup_fcsbo(1'B0),
    .startup_fcsbts(1'B0),
    .startup_gsr(1'B0),
    .startup_gts(1'B0),
    .startup_keyclearb(1'B1),
    .startup_pack(1'B0),
    .startup_usrcclko(1'B0),
    .startup_usrcclkts(1'B1),
    .startup_usrdoneo(1'B0),
    .startup_usrdonets(1'B1),
    .cap_req(),
    .cap_gnt(1'B1),
    .cap_rel(1'B0),
    .cfg_ext_read_received(cfg_ext_read_received),
    .cfg_ext_write_received(cfg_ext_write_received),
    .cfg_ext_register_number(cfg_ext_register_number),
    .cfg_ext_function_number(cfg_ext_function_number),
    .cfg_ext_write_data(cfg_ext_write_data),
    .cfg_ext_write_byte_enable(cfg_ext_write_byte_enable),
    .cfg_ext_read_data(cfg_ext_read_data),
    .cfg_ext_read_data_valid(cfg_ext_read_data_valid),
    .m_axis_rq_tdata_out(),
    .m_axis_rq_tlast_out(),
    .m_axis_rq_tuser_out(),
    .m_axis_rq_tkeep_out(),
    .m_axis_rq_tready_out(),
    .m_axis_rq_tvalid_out(),
    .s_axis_rc_tdata_out(),
    .s_axis_rc_tuser_out(),
    .s_axis_rc_tlast_out(),
    .s_axis_rc_tkeep_out(),
    .s_axis_rc_tvalid_out(),
    .s_axis_rc_tready_out(),
    .s_axis_cq_tdata_out  (s_axis_cq_tdata_out  ),
    .s_axis_cq_tuser_out  (s_axis_cq_tuser_out  ),
    .s_axis_cq_tlast_out  (s_axis_cq_tlast_out  ),
    .s_axis_cq_tkeep_out  (s_axis_cq_tkeep_out  ),
    .s_axis_cq_tvalid_out (s_axis_cq_tvalid_out ),
    .s_axis_cq_tready_out (s_axis_cq_tready_out ),
    .m_axis_cc_tdata_out  (m_axis_cc_tdata_out  ),
    .m_axis_cc_tuser_out  (m_axis_cc_tuser_out  ),
    .m_axis_cc_tlast_out  (m_axis_cc_tlast_out  ),
    .m_axis_cc_tkeep_out  (m_axis_cc_tkeep_out  ),
    .m_axis_cc_tvalid_out (m_axis_cc_tvalid_out ),
    .m_axis_cc_tready_out (m_axis_cc_tready_out ),
    .pipe_pclk_in(1'B0),
    .pipe_rxusrclk_in(1'B0),
    .pipe_rxoutclk_in(16'B0),
    .pipe_dclk_in(1'B0),
    .pipe_userclk1_in(1'B0),
    .pipe_userclk2_in(1'B0),
    .pipe_oobclk_in(1'B0),
    .pipe_mmcm_lock_in(1'B1),
    .pipe_txoutclk_out(),
    .pipe_rxoutclk_out(),
    .pipe_mmcm_rst_n(1'B1),
    .pipe_pclk_sel_out(),
    .pipe_gen3_out(),
    .ext_qpll1refclk(),
    .ext_qpll1rate(),
    .ext_qpll1pd(),
    .ext_qpll1reset(),
    .ext_qpll1lock_out(3'B0),
    .ext_qpll1outclk_out(3'B0),
    .ext_qpll1outrefclk_out(3'B0),
    .int_qpll1lock_out(),
    .int_qpll1outrefclk_out(),
    .int_qpll1outclk_out(),
    .int_pclk_out_slave(),
    .int_pipe_rxusrclk_out(),
    .int_rxoutclk_out(),
    .int_dclk_out(),
    .int_userclk1_out(),
    .int_userclk2_out(),
    .int_oobclk_out(),
    .int_qplllock_out(),
    .int_qplloutclk_out(),
    .int_qplloutrefclk_out(),
    .int_pclk_sel_slave(16'B0),
    .qpll_drp_crscode(12'B0),
    .qpll_drp_fsm(18'B0),
    .qpll_drp_done(2'B0),
    .qpll_drp_reset(2'B0),
    .qpll_qplllock(2'B0),
    .qpll_qplloutclk(2'B0),
    .qpll_qplloutrefclk(2'B0),
    .qpll_qplld(),
    .qpll_qpllreset(),
    .qpll_drp_clk(),
    .qpll_drp_rst_n(),
    .qpll_drp_ovrd(),
    .qpll_drp_gen3(),
    .qpll_drp_start(),
    .gt_qpll0lock(gt_qpll0lock),
    .gt_gen34_eios_det(gt_gen34_eios_det),
    .gt_txoutclk(gt_txoutclk),
    .gt_txoutclkfabric(gt_txoutclkfabric),
    .gt_rxoutclkfabric(gt_rxoutclkfabric),
    .gt_txoutclkpcs(gt_txoutclkpcs),
    .gt_rxoutclkpcs(gt_rxoutclkpcs),
    .gt_txpmareset(gt_txpmareset),
    .gt_rxpmareset(gt_rxpmareset),
    .gt_txpcsreset(gt_txpcsreset),
    .gt_rxpcsreset(gt_rxpcsreset),
    .gt_rxbufreset(gt_rxbufreset),
    .gt_rxcdrreset(gt_rxcdrreset),
    .gt_rxdfelpmreset(gt_rxdfelpmreset),
    .gt_txprogdivresetdone(gt_txprogdivresetdone),
    .gt_txpmaresetdone(gt_txpmaresetdone),
    .gt_txsyncdone(gt_txsyncdone),
    .gt_rxprbslocked(gt_rxprbslocked),
    .pipe_tx0_rcvr_det(pipe_tx0_rcvr_det),
    .pipe_clk(pipe_clk),
    .sys_clk_bufg(sys_clk_bufg),
    .pipe_tx0_powerdown(pipe_tx0_powerdown),
    .interrupt_out(interrupt_out),
    .s_axi_awid(s_axi_awid),
    .s_axi_awaddr(s_axi_awaddr),
    .s_axi_awregion(s_axi_awregion),
    .s_axi_awlen(s_axi_awlen),
    .s_axi_awsize(s_axi_awsize),
    .s_axi_awburst(s_axi_awburst),
    .s_axi_awvalid(s_axi_awvalid),
    .s_axi_wdata(s_axi_wdata),
    .s_axi_wstrb(s_axi_wstrb),
    .s_axi_wlast(s_axi_wlast),
    .s_axi_wvalid(s_axi_wvalid),
    .s_axi_bready(s_axi_bready),
    .s_axi_arid(s_axi_arid),
    .s_axi_araddr(s_axi_araddr),
    .s_axi_arregion(s_axi_arregion),
    .s_axi_arlen(s_axi_arlen),
    .s_axi_arsize(s_axi_arsize),
    .s_axi_arburst(s_axi_arburst),
    .s_axi_arvalid(s_axi_arvalid),
    .s_axi_rready(s_axi_rready),
    .s_axi_awready(s_axi_awready),
    .s_axi_wready(s_axi_wready),
    .s_axi_bid(s_axi_bid),
    .s_axi_bresp(s_axi_bresp),
    .s_axi_bvalid(s_axi_bvalid),
    .s_axi_arready(s_axi_arready),
    .s_axi_rid(s_axi_rid),
    .s_axi_rdata(s_axi_rdata),
    .s_axi_rresp(s_axi_rresp),
    .s_axi_rlast(s_axi_rlast),
    .s_axi_rvalid(s_axi_rvalid),
    .cfg_ltssm_state(cfg_ltssm_state),
    .cfg_function_status(cfg_function_status),
    .cfg_max_read_req(cfg_max_read_req),
    .cfg_max_payload(cfg_max_payload),
    .cfg_err_uncor_in(cfg_err_uncor_in),
    .cfg_flr_in_process(cfg_flr_in_process),
    .cfg_flr_done(cfg_flr_done),
    .cfg_vf_flr_in_process(cfg_vf_flr_in_process),
    .cfg_vf_flr_func_num(cfg_vf_flr_func_num),
    .cfg_vf_flr_done(cfg_vf_flr_done),
    .cfg_interrupt_msi_enable(cfg_interrupt_msi_enable),
    .cfg_interrupt_msix_enable(cfg_interrupt_msix_enable)
  );
endmodule
