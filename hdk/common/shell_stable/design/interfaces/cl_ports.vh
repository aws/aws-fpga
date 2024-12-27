// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// ============================================================================


  //----------------------------------------
  // Globals
  //----------------------------------------

  input  logic          clk_main_a0,           //Main clock.  This is the clock for all of the interfaces to the SH
  input  logic          rst_main_n,            //Reset sync'ed to main clock.

  input  logic          clk_hbm_ref,           // 100MHz HBM reference clock

  input  logic          sh_cl_flr_assert,      //Function level reset assertion.  Level signal that indicates PCIe function level reset is asserted
  output logic          cl_sh_flr_done,        //Function level reset done indication.  Must be asserted by CL when done processing function level reset.

  output logic  [31:0]  cl_sh_status0,         //Functionality TBD
  output logic  [31:0]  cl_sh_status1,         //Functionality TBD
  output logic  [31:0]  cl_sh_status2,         //Functionality TBD

  output logic  [31:0]  cl_sh_id0,             //15:0 - PCI Vendor ID
                                               //31:16 - PCI Device ID
  output logic  [31:0]  cl_sh_id1,             //15:0 - PCI Subsystem Vendor ID
                                               //31:16 - PCI Subsystem ID

  input  logic  [31:0]  sh_cl_ctl0,            //Functionality TBD
  input  logic  [31:0]  sh_cl_ctl1,            //Functionality TBD
  input  logic  [31:0]  sh_cl_ctl2,            //Functionality TBD

  input  logic  [15:0]  sh_cl_status_vdip,     //Virtual DIP switches.  Controlled through FPGA management PF and tools.
  output logic  [15:0]  cl_sh_status_vled,     //Virtual LEDs, monitored through FPGA management PF and tools

  input  logic   [1:0]  sh_cl_pwr_state,      //Power state, 2'b00: Normal, 2'b11: Critical

  // These signals relate to the dma_pcis interface. They should be
  // asserted when the CL is running out of resources and will not be able
  // to accept certain types of transactions.
  output logic          cl_sh_dma_wr_full,    // Resources low for dma writes  (DMA_PCIS AXI ID: 0x00-0x03)
  output logic          cl_sh_dma_rd_full,    // Resources low for dma reads   (DMA_PCIS AXI ID: 0x00-0x03)


  //-------------------------------------------------------------------------------------------
  // PCIe Master interface from CL
  //
  //    AXI-4 master interface per PCIe interface.  This is for PCIe transactions mastered
  //    from the SH targetting the host (DMA access to host).  Standard AXI-4 interface.
  //-------------------------------------------------------------------------------------------
  output logic  [15:0]  cl_sh_pcim_awid,
  output logic  [63:0]  cl_sh_pcim_awaddr,
  output logic   [7:0]  cl_sh_pcim_awlen,
  output logic   [2:0]  cl_sh_pcim_awsize,
  output logic   [1:0]  cl_sh_pcim_awburst,
  output logic   [3:0]  cl_sh_pcim_awcache,
  output logic          cl_sh_pcim_awlock,
  output logic   [2:0]  cl_sh_pcim_awprot,
  output logic   [3:0]  cl_sh_pcim_awqos,
  output logic  [54:0]  cl_sh_pcim_awuser,
  output logic          cl_sh_pcim_awvalid,
  input  logic          sh_cl_pcim_awready,

  output logic  [15:0]  cl_sh_pcim_wid,
  output logic [511:0]  cl_sh_pcim_wdata,
  output logic  [63:0]  cl_sh_pcim_wstrb,
  output logic          cl_sh_pcim_wlast,
  output logic  [63:0]  cl_sh_pcim_wuser,
  output logic          cl_sh_pcim_wvalid,
  input  logic          sh_cl_pcim_wready,

  input  logic  [15:0]  sh_cl_pcim_bid,
  input  logic   [1:0]  sh_cl_pcim_bresp,
  input  logic          sh_cl_pcim_bvalid,
  output logic          cl_sh_pcim_bready,

  output logic  [15:0]  cl_sh_pcim_arid,
  output logic  [63:0]  cl_sh_pcim_araddr,
  output logic   [7:0]  cl_sh_pcim_arlen,
  output logic   [2:0]  cl_sh_pcim_arsize,
  output logic   [1:0]  cl_sh_pcim_arburst,
  output logic   [3:0]  cl_sh_pcim_arcache,
  output logic          cl_sh_pcim_arlock,
  output logic   [2:0]  cl_sh_pcim_arprot,
  output logic   [3:0]  cl_sh_pcim_arqos,
  output logic  [54:0]  cl_sh_pcim_aruser,
  output logic          cl_sh_pcim_arvalid,
  input  logic          sh_cl_pcim_arready,

  input  logic  [15:0]  sh_cl_pcim_rid,
  input  logic [511:0]  sh_cl_pcim_rdata,
  input  logic   [1:0]  sh_cl_pcim_rresp,
  input  logic          sh_cl_pcim_rlast,
  input  logic  [63:0]  sh_cl_pcim_ruser,
  input  logic          sh_cl_pcim_rvalid,
  output logic          cl_sh_pcim_rready,

  input  logic   [1:0]  cfg_max_payload,   //Max payload size - 00:128B, 01:256B, 10:512B, 11:1024B
  input  logic   [2:0]  cfg_max_read_req,  //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B


  //-----------------------------------------------------------------------------------------------
  // DDR-4 Interface
  //
  //    DDR is instantiated in CL.  This is the physical interface.
  //    These interfaces must be connected to an instantiated sh_ddr in the CL logic.
  //    Note even if DDR interface is not used, sh_ddr must be instantiated and connected
  //    to these interface ports. The sh_ddr block has parameters to control whether the DDR
  //    controller is instantiated.  If the DDR controller is not instantiated it will not
  //    take up FPGA resources.
  //-----------------------------------------------------------------------------------------------


  // ------------------- DDR4 x72 RDIMM Interface  ----------------------------------
  input  logic          CLK_DIMM_DP,
  input  logic          CLK_DIMM_DN,
  output logic          M_ACT_N,
  output logic  [17:0]  M_MA,
  output logic   [1:0]  M_BA,
  output logic   [1:0]  M_BG,
  output logic   [1:0]  M_CKE,
  output logic   [1:0]  M_ODT,
  output logic   [1:0]  M_CS_N,
  output logic   [1:0]  M_CLK_DN,
  output logic   [1:0]  M_CLK_DP,
  output logic          M_PAR,
  inout  wire   [63:0]  M_DQ,
  inout  wire    [7:0]  M_ECC,
  inout  wire   [17:0]  M_DQS_DP,
  inout  wire   [17:0]  M_DQS_DN,
  output logic          RST_DIMM_N,

  //-----------------------------------------------------------------------------
  // DDR Stats interfaces for DDR controllers in the CL.  This must be hooked up
  // to the sh_ddr.sv for the DDR interfaces to function.  If the DDR controller is
  // not used (removed through parameter on the sh_ddr instantiated), then the
  // associated stats interface should not be hooked up and the ddr_sh_stat_ackX signal
  // should be tied high.
  //-----------------------------------------------------------------------------
  input  logic   [7:0]  sh_cl_ddr_stat_addr,
  input  logic  [31:0]  sh_cl_ddr_stat_wdata,
  input  logic          sh_cl_ddr_stat_wr,
  input  logic          sh_cl_ddr_stat_rd,
  input  logic   [2:0]  sh_cl_ddr_stat_user,
  output logic          cl_sh_ddr_stat_ack,
  output logic  [31:0]  cl_sh_ddr_stat_rdata,

  output logic   [7:0]  cl_sh_ddr_stat_int,


  //---------------------------------------------------------------------------------------
  // The user-defined interrupts.  These map to MSI-X vectors through mapping in the SH.
  //---------------------------------------------------------------------------------------
  output logic  [15:0]  cl_sh_apppf_irq_req,  //Interrupt request.  The request (cl_sh_apppf_irq_req[n]) should be pulsed (single clock) to generate
                                              // an interrupt request.  Another request should not be generated until ack'ed by the SH
  input  logic  [15:0]  sh_cl_apppf_irq_ack,  //Interrupt ack.  SH asserts sh_cl_apppf_irq_ack[n] (single clock pulse) to acknowledge the corresponding
                                              // interrupt request (cl_sh_apppf_irq_req[n]) from the CL


  //----------------------------------------------------
  // PCIS AXI-4 interface to master cycles to CL
  //----------------------------------------------------
  input  logic  [15:0]  sh_cl_dma_pcis_awid,
  input  logic  [63:0]  sh_cl_dma_pcis_awaddr,
  input  logic   [7:0]  sh_cl_dma_pcis_awlen,
  input  logic   [2:0]  sh_cl_dma_pcis_awsize,
  input  logic   [1:0]  sh_cl_dma_pcis_awburst,
  input  logic   [3:0]  sh_cl_dma_pcis_awcache,
  input  logic          sh_cl_dma_pcis_awlock,
  input  logic   [2:0]  sh_cl_dma_pcis_awprot,
  input  logic   [3:0]  sh_cl_dma_pcis_awqos,
  input  logic  [54:0]  sh_cl_dma_pcis_awuser,
  input  logic          sh_cl_dma_pcis_awvalid,
  output logic          cl_sh_dma_pcis_awready,

  input  logic  [15:0]  sh_cl_dma_pcis_wid,
  input  logic [511:0]  sh_cl_dma_pcis_wdata,
  input  logic  [63:0]  sh_cl_dma_pcis_wstrb,
  input  logic          sh_cl_dma_pcis_wlast,
  input  logic  [63:0]  sh_cl_dma_pcis_wuser,
  input  logic          sh_cl_dma_pcis_wvalid,
  output logic          cl_sh_dma_pcis_wready,

  output logic  [15:0]  cl_sh_dma_pcis_bid,
  output logic   [1:0]  cl_sh_dma_pcis_bresp,
  output logic          cl_sh_dma_pcis_bvalid,
  input  logic          sh_cl_dma_pcis_bready,

  input  logic  [15:0]  sh_cl_dma_pcis_arid,
  input  logic  [63:0]  sh_cl_dma_pcis_araddr,
  input  logic   [7:0]  sh_cl_dma_pcis_arlen,
  input  logic   [2:0]  sh_cl_dma_pcis_arsize,
  input  logic   [1:0]  sh_cl_dma_pcis_arburst,
  input  logic   [3:0]  sh_cl_dma_pcis_arcache,
  input  logic          sh_cl_dma_pcis_arlock,
  input  logic   [2:0]  sh_cl_dma_pcis_arprot,
  input  logic   [3:0]  sh_cl_dma_pcis_arqos,
  input  logic  [54:0]  sh_cl_dma_pcis_aruser,
  input  logic          sh_cl_dma_pcis_arvalid,
  output logic          cl_sh_dma_pcis_arready,

  output logic  [15:0]  cl_sh_dma_pcis_rid,
  output logic [511:0]  cl_sh_dma_pcis_rdata,
  output logic   [1:0]  cl_sh_dma_pcis_rresp,
  output logic          cl_sh_dma_pcis_rlast,
  output logic  [63:0]  cl_sh_dma_pcis_ruser,
  output logic          cl_sh_dma_pcis_rvalid,
  input  logic          sh_cl_dma_pcis_rready,


  //------------------------------------------------------------------------------------------
  // AXI-L maps to any inbound PCIe access through AppPF BAR0
  // For example, this AXI-L interface can connect to OpenCL Kernels
  // This would connect automatically to the required logic
  // if the CL is created through SDAccel flow
  //------------------------------------------------------------------------------------------
  input  logic  [31:0]  ocl_cl_awaddr,
  input  logic  [54:0]  ocl_cl_awuser,
  input  logic          ocl_cl_awvalid,
  output logic          cl_ocl_awready,

  input  logic  [31:0]  ocl_cl_wdata,
  input  logic   [3:0]  ocl_cl_wstrb,
  input  logic          ocl_cl_wvalid,
  output logic          cl_ocl_wready,

  output logic   [1:0]  cl_ocl_bresp,
  output logic          cl_ocl_bvalid,
  input  logic          ocl_cl_bready,

  input  logic  [31:0]  ocl_cl_araddr,
  input  logic  [54:0]  ocl_cl_aruser,
  input  logic          ocl_cl_arvalid,
  output logic          cl_ocl_arready,

  output logic  [31:0]  cl_ocl_rdata,
  output logic   [1:0]  cl_ocl_rresp,
  output logic          cl_ocl_rvalid,
  input  logic          ocl_cl_rready,


  //------------------------------------------------------------------------------------------
  // ** TBD** AXI-L maps to any inbound PCIe access through ManagementPF BAR4 for developer's use
  // If the CL is created through  Xilinx’s SDAccel, then this configuration bus
  // would be connected automatically to SDAccel generic logic (SmartConnect, APM etc)
  //------------------------------------------------------------------------------------------
  input  logic  [31:0]  sda_cl_awaddr,
  input  logic          sda_cl_awvalid,
  output logic          cl_sda_awready,

  input  logic  [31:0]  sda_cl_wdata,
  input  logic   [3:0]  sda_cl_wstrb,
  input  logic          sda_cl_wvalid,
  output logic          cl_sda_wready,

  output logic   [1:0]  cl_sda_bresp,
  output logic          cl_sda_bvalid,
  input  logic          sda_cl_bready,

  input  logic  [31:0]  sda_cl_araddr,
  input  logic          sda_cl_arvalid,
  output logic          cl_sda_arready,

  output logic  [31:0]  cl_sda_rdata,
  output logic   [1:0]  cl_sda_rresp,
  output logic          cl_sda_rvalid,
  input  logic          sda_cl_rready,

  //-------------------------------------------------------------------------------------------
  // Debug bridge -- This is for Virtual JTAG.   If enabling the CL for
  // Virtual JTAG (chipcope) debug, connect this interface to the debug bridge in the CL
  //-------------------------------------------------------------------------------------------
  input  logic          drck,
  input  logic          shift,
  input  logic          tdi,
  input  logic          update,
  input  logic          sel,
  output logic          tdo,
  input  logic          tms,
  input  logic          tck,
  input  logic          runtest,
  input  logic          reset,
  input  logic          capture,
  input  logic          bscanid_en,


  //-------------------------------------------------------------
  // These are global counters that increment every 4ns.  They
  // are synchronized to clk_main_a0.  Note if clk_main_a0 is
  // slower than 250MHz, the CL will see skips in the counts
  //-------------------------------------------------------------
  input  logic  [63:0]  sh_cl_glcount0,  //Global counter 0
  input  logic  [63:0]  sh_cl_glcount1,  //Global counter 1


  //----------------------------------------------------------------
  // HBM Monitor I/O. These signals are sychronized to clk_hbm_ref.
  //----------------------------------------------------------------
  input  logic          hbm_apb_preset_n_1,
  output logic  [21:0]  hbm_apb_paddr_1,
  output logic   [2:0]  hbm_apb_pprot_1,
  output logic          hbm_apb_psel_1,
  output logic          hbm_apb_penable_1,
  output logic          hbm_apb_pwrite_1,
  output logic  [31:0]  hbm_apb_pwdata_1,
  output logic   [3:0]  hbm_apb_pstrb_1,
  output logic          hbm_apb_pready_1,
  output logic  [31:0]  hbm_apb_prdata_1,
  output logic          hbm_apb_pslverr_1,

  input  logic          hbm_apb_preset_n_0,
  output logic  [21:0]  hbm_apb_paddr_0,
  output logic   [2:0]  hbm_apb_pprot_0,
  output logic          hbm_apb_psel_0,
  output logic          hbm_apb_penable_0,
  output logic          hbm_apb_pwrite_0,
  output logic  [31:0]  hbm_apb_pwdata_0,
  output logic   [3:0]  hbm_apb_pstrb_0,
  output logic          hbm_apb_pready_0,
  output logic  [31:0]  hbm_apb_prdata_0,
  output logic          hbm_apb_pslverr_0,


  //==================================================================
  // C2C Endpoint IOs
  //==================================================================
  input  logic          PCIE_EP_PERSTN,
  input  logic          PCIE_EP_REF_CLK_P,
  input  logic          PCIE_EP_REF_CLK_N,
  output logic [7 : 0]  PCIE_EP_TXP,
  output logic [7 : 0]  PCIE_EP_TXN,
  input  logic [7 : 0]  PCIE_EP_RXP,
  input  logic [7 : 0]  PCIE_EP_RXN,


  //==================================================================
  // C2C Rootport IOs
  //==================================================================
  output logic          PCIE_RP_PERSTN,
  input  logic          PCIE_RP_REF_CLK_P,
  input  logic          PCIE_RP_REF_CLK_N,
  output logic [7 : 0]  PCIE_RP_TXP,
  output logic [7 : 0]  PCIE_RP_TXN,
  input  logic [7 : 0]  PCIE_RP_RXP,
  input  logic [7 : 0]  PCIE_RP_RXN
