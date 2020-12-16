// (c) Copyright 2017 Xilinx, Inc. All rights reserved.
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

(* DowngradeIPIdentifiedWarnings="yes" *)
module aws_v1_0_2_top #
  (
   parameter integer C_MODE = 0,
   // 0 = AWS HLS (IPI) flow: All interfaces are available.
   // 1 = SDx Unified flow Memory-only mode: Only DDR interfaces and related ports are available.
   // 2 = SDx Unified flow Non-memory mode: All interfaces except DDR-related are available.
   parameter integer C_DDR_A_PRESENT = 0,
   parameter integer C_DDR_B_PRESENT = 0,
   parameter integer C_DDR_D_PRESENT = 0,
   parameter integer C_NUM_A_CLOCKS = 1,
   parameter integer C_NUM_B_CLOCKS = 0,
   parameter integer C_NUM_C_CLOCKS = 0,
   parameter [15:0]  C_VENDOR_ID = 16'h1D0F,
   parameter [15:0]  C_DEVICE_ID = 16'hF010,
   parameter [15:0]  C_SUBSYSTEM_VENDOR_ID = 16'hFEDD,
   parameter [15:0]  C_SUBSYSTEM_ID = 16'h1D51,
   parameter C_CLOCK_A0_PERIOD = "4.0",
   parameter C_CLOCK_A1_PERIOD = "8.0",
   parameter C_CLOCK_B0_PERIOD = "4.0",
   parameter C_CLOCK_C0_PERIOD = "3.333333",
   parameter integer C_CLOCK_A_RECIPE = 1,
   parameter integer C_CLOCK_B_RECIPE = 0,
   parameter integer C_CLOCK_C_RECIPE = 0,
   parameter integer C_NUM_STAGES_STATS = 1,
   parameter integer C_PCIM_PRESENT = 0
  ) 
  (
   //--------------------------------
   // S_SH bus-interface ports
   //--------------------------------
   `include "aws_v1_0_2_ports.vh" // Subset of Amazon-provided port definitions (without Debug Bridge)
   ,
   
   //--------------------------------
   // Globals
   //--------------------------------
   output wire clk_main_a0_out,                           //Main clock.  This is the clock for all of the interfaces of AWS
   output wire clk_extra_a1_out,                          //Extra clock A1 (phase aligned to "A" clock group)
   output wire clk_extra_a2_out,                          //Extra clock A2 (phase aligned to "A" clock group)
   output wire clk_extra_a3_out,                          //Extra clock A3 (phase aligned to "A" clock group)
   output wire clk_extra_b0_out,                          //Extra clock B0 (phase aligned to "B" clock group)
   output wire clk_extra_b1_out,                          //Extra clock B1 (phase aligned to "B" clock group)
   output wire clk_extra_c0_out,                          //Extra clock C0 (phase aligned to "C" clock group)
   output wire clk_extra_c1_out,                          //Extra clock C1 (phase aligned to "C" clock group)
   
   output wire rst_main_n_out,                            //Reset sync to main clock.
   output wire kernel_rst_n_out,                          //Kernel_reset.

   output wire flr_assert,                            //Function level reset assertion.
   input  wire flr_done,                              //Function level reset done acknowledge
         
   output wire [15:0] status_vdip,                    //Virtual DIP switches.
   input  wire [15:0] status_vled,                    //Virtual LEDs
   
   input  wire [15:0] irq_req,                        // User-defined interrupt request
   output wire [15:0] irq_ack,                        // User-defined interrupt acknowledge
   
   output wire [63:0] glcount0,                       //Global counter 0
   output wire [63:0] glcount1,                       //Global counter 1

   //--------------------------------
   // S_AXI_DDRA bus-interface ports
   //--------------------------------
   input  wire [15:0]   s_axi_ddra_awid,
   input  wire [63:0]   s_axi_ddra_awaddr,
   input  wire [7:0]    s_axi_ddra_awlen,
   input  wire [2:0]    s_axi_ddra_awsize,
   input  wire          s_axi_ddra_awvalid,
   output wire          s_axi_ddra_awready,
   input  wire [511:0]  s_axi_ddra_wdata,
   input  wire [63:0]   s_axi_ddra_wstrb,
   input  wire          s_axi_ddra_wlast,
   input  wire          s_axi_ddra_wvalid,
   output wire          s_axi_ddra_wready,
   output wire [15:0]   s_axi_ddra_bid,
   output wire [1:0]    s_axi_ddra_bresp,
   output wire          s_axi_ddra_bvalid,
   input  wire          s_axi_ddra_bready,
   input  wire [15:0]   s_axi_ddra_arid,
   input  wire [63:0]   s_axi_ddra_araddr,
   input  wire [7:0]    s_axi_ddra_arlen,
   input  wire [2:0]    s_axi_ddra_arsize,
   input  wire          s_axi_ddra_arvalid,
   output wire          s_axi_ddra_arready,
   output wire [15:0]   s_axi_ddra_rid,
   output wire [511:0]  s_axi_ddra_rdata,
   output wire [1:0]    s_axi_ddra_rresp,
   output wire          s_axi_ddra_rlast,
   output wire          s_axi_ddra_rvalid,
   input  wire          s_axi_ddra_rready,
      
   output wire          ddra_is_ready,

   //--------------------------------
   // S_AXI_DDRB bus-interface ports
   //--------------------------------
   input  wire [15:0]   s_axi_ddrb_awid,
   input  wire [63:0]   s_axi_ddrb_awaddr,
   input  wire [7:0]    s_axi_ddrb_awlen,
   input  wire [2:0]    s_axi_ddrb_awsize,
   input  wire          s_axi_ddrb_awvalid,
   output wire          s_axi_ddrb_awready,
   input  wire [511:0]  s_axi_ddrb_wdata,
   input  wire [63:0]   s_axi_ddrb_wstrb,
   input  wire          s_axi_ddrb_wlast,
   input  wire          s_axi_ddrb_wvalid,
   output wire          s_axi_ddrb_wready,
   output wire [15:0]   s_axi_ddrb_bid,
   output wire [1:0]    s_axi_ddrb_bresp,
   output wire          s_axi_ddrb_bvalid,
   input  wire          s_axi_ddrb_bready,
   input  wire [15:0]   s_axi_ddrb_arid,
   input  wire [63:0]   s_axi_ddrb_araddr,
   input  wire [7:0]    s_axi_ddrb_arlen,
   input  wire [2:0]    s_axi_ddrb_arsize,
   input  wire          s_axi_ddrb_arvalid,
   output wire          s_axi_ddrb_arready,
   output wire [15:0]   s_axi_ddrb_rid,
   output wire [511:0]  s_axi_ddrb_rdata,
   output wire [1:0]    s_axi_ddrb_rresp,
   output wire          s_axi_ddrb_rlast,
   output wire          s_axi_ddrb_rvalid,
   input  wire          s_axi_ddrb_rready,
      
   output wire          ddrb_is_ready,

   //--------------------------------
   // S_AXI_DDRC bus-interface ports
   //--------------------------------
   input  wire [15:0]   s_axi_ddrc_awid,
   input  wire [63:0]   s_axi_ddrc_awaddr,
   input  wire [7:0]    s_axi_ddrc_awlen,
   input  wire [2:0]    s_axi_ddrc_awsize,
   input  wire          s_axi_ddrc_awvalid,
   output wire          s_axi_ddrc_awready,
   input  wire [511:0]  s_axi_ddrc_wdata,
   input  wire [63:0]   s_axi_ddrc_wstrb,
   input  wire          s_axi_ddrc_wlast,
   input  wire          s_axi_ddrc_wvalid,
   output wire          s_axi_ddrc_wready,
   output wire [15:0]   s_axi_ddrc_bid,
   output wire [1:0]    s_axi_ddrc_bresp,
   output wire          s_axi_ddrc_bvalid,
   input  wire          s_axi_ddrc_bready,
   input  wire [15:0]   s_axi_ddrc_arid,
   input  wire [63:0]   s_axi_ddrc_araddr,
   input  wire [7:0]    s_axi_ddrc_arlen,
   input  wire [2:0]    s_axi_ddrc_arsize,
   input  wire          s_axi_ddrc_arvalid,
   output wire          s_axi_ddrc_arready,
   output wire [15:0]   s_axi_ddrc_rid,
   output wire [511:0]  s_axi_ddrc_rdata,
   output wire [1:0]    s_axi_ddrc_rresp,
   output wire          s_axi_ddrc_rlast,
   output wire          s_axi_ddrc_rvalid,
   input  wire          s_axi_ddrc_rready,
      
   output wire          ddrc_is_ready,

   //--------------------------------
   // S_AXI_DDRD bus-interface ports
   //--------------------------------
   input  wire [15:0]   s_axi_ddrd_awid,
   input  wire [63:0]   s_axi_ddrd_awaddr,
   input  wire [7:0]    s_axi_ddrd_awlen,
   input  wire [2:0]    s_axi_ddrd_awsize,
   input  wire          s_axi_ddrd_awvalid,
   output wire          s_axi_ddrd_awready,
   input  wire [511:0]  s_axi_ddrd_wdata,
   input  wire [63:0]   s_axi_ddrd_wstrb,
   input  wire          s_axi_ddrd_wlast,
   input  wire          s_axi_ddrd_wvalid,
   output wire          s_axi_ddrd_wready,
   output wire [15:0]   s_axi_ddrd_bid,
   output wire [1:0]    s_axi_ddrd_bresp,
   output wire          s_axi_ddrd_bvalid,
   input  wire          s_axi_ddrd_bready,
   input  wire [15:0]   s_axi_ddrd_arid,
   input  wire [63:0]   s_axi_ddrd_araddr,
   input  wire [7:0]    s_axi_ddrd_arlen,
   input  wire [2:0]    s_axi_ddrd_arsize,
   input  wire          s_axi_ddrd_arvalid,
   output wire          s_axi_ddrd_arready,
   output wire [15:0]   s_axi_ddrd_rid,
   output wire [511:0]  s_axi_ddrd_rdata,
   output wire [1:0]    s_axi_ddrd_rresp,
   output wire          s_axi_ddrd_rlast,
   output wire          s_axi_ddrd_rvalid,
   input  wire          s_axi_ddrd_rready,
      
   output wire          ddrd_is_ready,

   //--------------------------------
   // M_AXI_SDA bus-interface ports
   //--------------------------------
   output wire [31:0]   m_axi_sda_awaddr,
   output wire          m_axi_sda_awvalid,
   input  wire          m_axi_sda_awready,
   output wire [31:0]   m_axi_sda_wdata,
   output wire [3:0]    m_axi_sda_wstrb,
   output wire          m_axi_sda_wvalid,
   input  wire          m_axi_sda_wready,
   input  wire [1:0]    m_axi_sda_bresp,
   input  wire          m_axi_sda_bvalid,
   output wire          m_axi_sda_bready,
   output wire [31:0]   m_axi_sda_araddr,
   output wire          m_axi_sda_arvalid,
   input  wire          m_axi_sda_arready,
   input  wire [31:0]   m_axi_sda_rdata,
   input  wire [1:0]    m_axi_sda_rresp,
   input  wire          m_axi_sda_rvalid,
   output wire          m_axi_sda_rready,

   //--------------------------------
   // M_AXI_OCL bus-interface ports
   //--------------------------------
   output wire [31:0]   m_axi_ocl_awaddr,
   output wire          m_axi_ocl_awvalid,
   input  wire          m_axi_ocl_awready,
   output wire [31:0]   m_axi_ocl_wdata,
   output wire [3:0]    m_axi_ocl_wstrb,
   output wire          m_axi_ocl_wvalid,
   input  wire          m_axi_ocl_wready,
   input  wire [1:0]    m_axi_ocl_bresp,
   input  wire          m_axi_ocl_bvalid,
   output wire          m_axi_ocl_bready,
   output wire [31:0]   m_axi_ocl_araddr,
   output wire          m_axi_ocl_arvalid,
   input  wire          m_axi_ocl_arready,
   input  wire [31:0]   m_axi_ocl_rdata,
   input  wire [1:0]    m_axi_ocl_rresp,
   input  wire          m_axi_ocl_rvalid,
   output wire          m_axi_ocl_rready,

   //--------------------------------
   // M_AXI_BAR1 bus-interface ports
   //--------------------------------
   output wire [31:0]   m_axi_bar1_awaddr,
   output wire          m_axi_bar1_awvalid,
   input  wire          m_axi_bar1_awready,
   output wire [31:0]   m_axi_bar1_wdata,
   output wire [3:0]    m_axi_bar1_wstrb,
   output wire          m_axi_bar1_wvalid,
   input  wire          m_axi_bar1_wready,
   input  wire [1:0]    m_axi_bar1_bresp,
   input  wire          m_axi_bar1_bvalid,
   output wire          m_axi_bar1_bready,
   output wire [31:0]   m_axi_bar1_araddr,
   output wire          m_axi_bar1_arvalid,
   input  wire          m_axi_bar1_arready,
   input  wire [31:0]   m_axi_bar1_rdata,
   input  wire [1:0]    m_axi_bar1_rresp,
   input  wire          m_axi_bar1_rvalid,
   output wire          m_axi_bar1_rready,

   //--------------------------------
   // M_AXI_PCIS bus-interface ports (SH transactions to CL)
   //--------------------------------
   output wire [5:0]    m_axi_pcis_awid,
   output wire [63:0]   m_axi_pcis_awaddr,
   output wire [7:0]    m_axi_pcis_awlen,
   output wire [2:0]    m_axi_pcis_awsize,
   output wire          m_axi_pcis_awvalid,
   input  wire          m_axi_pcis_awready,
   output wire [511:0]  m_axi_pcis_wdata,
   output wire [63:0]   m_axi_pcis_wstrb,
   output wire          m_axi_pcis_wlast,
   output wire          m_axi_pcis_wvalid,
   input  wire          m_axi_pcis_wready,
   input  wire [5:0]    m_axi_pcis_bid,
   input  wire [1:0]    m_axi_pcis_bresp,
   input  wire          m_axi_pcis_bvalid,
   output wire          m_axi_pcis_bready,
   output wire [5:0]    m_axi_pcis_arid,
   output wire [63:0]   m_axi_pcis_araddr,
   output wire [7:0]    m_axi_pcis_arlen,
   output wire [2:0]    m_axi_pcis_arsize,
   output wire          m_axi_pcis_arvalid,
   input  wire          m_axi_pcis_arready,
   input  wire [5:0]    m_axi_pcis_rid,
   input  wire [511:0]  m_axi_pcis_rdata,
   input  wire [1:0]    m_axi_pcis_rresp,
   input  wire          m_axi_pcis_rlast,
   input  wire          m_axi_pcis_rvalid,
   output wire          m_axi_pcis_rready,
   output wire [1:0]    m_axi_pcis_awburst,
   output wire [1:0]    m_axi_pcis_arburst,
      
   //--------------------------------
   // S_AXI_PCIM bus-interface ports (CL transactions to SH)
   //--------------------------------
   input  wire [15:0]   s_axi_pcim_awid,
   input  wire [63:0]   s_axi_pcim_awaddr,
   input  wire [7:0]    s_axi_pcim_awlen,
   input  wire [2:0]    s_axi_pcim_awsize,
   input  wire [18:0]   s_axi_pcim_awuser,
   input  wire          s_axi_pcim_awvalid,
   output wire          s_axi_pcim_awready,
   input  wire [511:0]  s_axi_pcim_wdata,
   input  wire [63:0]   s_axi_pcim_wstrb,
   input  wire          s_axi_pcim_wlast,
   input  wire          s_axi_pcim_wvalid,
   output wire          s_axi_pcim_wready,
   output wire [15:0]   s_axi_pcim_bid,
   output wire [1:0]    s_axi_pcim_bresp,
   output wire          s_axi_pcim_bvalid,
   input  wire          s_axi_pcim_bready,
   input  wire [15:0]   s_axi_pcim_arid,
   input  wire [63:0]   s_axi_pcim_araddr,
   input  wire [7:0]    s_axi_pcim_arlen,
   input  wire [2:0]    s_axi_pcim_arsize,
   input  wire [18:0]   s_axi_pcim_aruser,
   input  wire          s_axi_pcim_arvalid,
   output wire          s_axi_pcim_arready,
   output wire [15:0]   s_axi_pcim_rid,
   output wire [511:0]  s_axi_pcim_rdata,
   output wire [1:0]    s_axi_pcim_rresp,
   output wire          s_axi_pcim_rlast,
   output wire          s_axi_pcim_rvalid,
   input  wire          s_axi_pcim_rready,
   
   output wire [1:0]    cfg_max_payload_out,  //Max payload size - 00:128B, 01:256B, 10:512B
   output wire [2:0]    cfg_max_read_req_out  //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
  );
  
  generate

    assign clk_main_a0_out     = clk_main_a0          ; 
    assign clk_extra_a1_out    = C_NUM_A_CLOCKS>1 ? clk_extra_a1 : 1'b0         ; 
    assign clk_extra_a2_out    = C_NUM_A_CLOCKS>2 ? clk_extra_a2 : 1'b0         ; 
    assign clk_extra_a3_out    = C_NUM_A_CLOCKS>3 ? clk_extra_a3 : 1'b0         ; 
    assign clk_extra_b0_out    = C_NUM_B_CLOCKS>0 ? clk_extra_b0 : 1'b0         ; 
    assign clk_extra_b1_out    = C_NUM_B_CLOCKS>1 ? clk_extra_b1 : 1'b0         ; 
    assign clk_extra_c0_out    = C_NUM_C_CLOCKS>0 ? clk_extra_c0 : 1'b0         ; 
    assign clk_extra_c1_out    = C_NUM_C_CLOCKS>1 ? clk_extra_c1 : 1'b0         ; 
    assign rst_main_n_out      = rst_main_n           ; 
    assign kernel_rst_n_out    = kernel_rst_n         ; 
    assign flr_assert          = sh_cl_flr_assert     ; 
    assign status_vdip         = sh_cl_status_vdip    ; 
    assign irq_ack             = sh_cl_apppf_irq_ack  ; 
    assign glcount0            = sh_cl_glcount0       ; 
    assign glcount1            = sh_cl_glcount1       ; 
   
    assign cl_sh_flr_done       = flr_done            ;                 
    assign cl_sh_status_vled    = status_vled         ;                 
    assign cl_sh_apppf_irq_req  = irq_req             ;                 
   
    assign cl_sh_status0        = 0 ;
    assign cl_sh_status1        = 0 ;
    assign cl_sh_id0            = {C_DEVICE_ID, C_VENDOR_ID} ;
    assign cl_sh_id1            = {C_SUBSYSTEM_ID, C_SUBSYSTEM_VENDOR_ID} ;
    
    assign cl_sh_dma_wr_full    = 1'b0;
    assign cl_sh_dma_rd_full    = 1'b0;
   
    assign cl_sh_ddr_awid     = s_axi_ddrc_awid     ;
    assign cl_sh_ddr_awaddr   = s_axi_ddrc_awaddr   ;
    assign cl_sh_ddr_awlen    = s_axi_ddrc_awlen    ;
    assign cl_sh_ddr_awsize   = s_axi_ddrc_awsize   ;
    assign cl_sh_ddr_awburst  = 2'b01               ;
    assign cl_sh_ddr_awvalid  = s_axi_ddrc_awvalid  ;
    assign cl_sh_ddr_wdata    = s_axi_ddrc_wdata    ;
    assign cl_sh_ddr_wstrb    = s_axi_ddrc_wstrb    ;
    assign cl_sh_ddr_wlast    = s_axi_ddrc_wlast    ;
    assign cl_sh_ddr_wvalid   = s_axi_ddrc_wvalid   ;
    assign cl_sh_ddr_bready   = s_axi_ddrc_bready   ;
    assign cl_sh_ddr_arid     = s_axi_ddrc_arid     ;
    assign cl_sh_ddr_araddr   = s_axi_ddrc_araddr   ;
    assign cl_sh_ddr_arlen    = s_axi_ddrc_arlen    ;
    assign cl_sh_ddr_arsize   = s_axi_ddrc_arsize   ;
    assign cl_sh_ddr_arburst  = 2'b01               ;
    assign cl_sh_ddr_arvalid  = s_axi_ddrc_arvalid  ;
    assign cl_sh_ddr_rready   = s_axi_ddrc_rready   ;
    
    assign s_axi_ddrc_awready  = sh_cl_ddr_awready   ;
    assign s_axi_ddrc_wready   = sh_cl_ddr_wready    ;
    assign s_axi_ddrc_bid      = sh_cl_ddr_bid       ;
    assign s_axi_ddrc_bresp    = sh_cl_ddr_bresp     ;
    assign s_axi_ddrc_bvalid   = sh_cl_ddr_bvalid    ;
    assign s_axi_ddrc_arready  = sh_cl_ddr_arready   ;
    assign s_axi_ddrc_rid      = sh_cl_ddr_rid       ;
    assign s_axi_ddrc_rdata    = sh_cl_ddr_rdata     ;
    assign s_axi_ddrc_rresp    = sh_cl_ddr_rresp     ;
    assign s_axi_ddrc_rlast    = sh_cl_ddr_rlast     ;
    assign s_axi_ddrc_rvalid   = sh_cl_ddr_rvalid    ; 
    assign ddrc_is_ready       = sh_cl_ddr_is_ready  ;
    
    assign cl_sh_ddr_wid       = 0 ;
  
    assign cl_sda_awready  = m_axi_sda_awready   ;
    assign cl_sda_wready   = m_axi_sda_wready    ;
    assign cl_sda_bresp    = m_axi_sda_bresp     ;
    assign cl_sda_bvalid   = m_axi_sda_bvalid    ;
    assign cl_sda_arready  = m_axi_sda_arready   ;
    assign cl_sda_rdata    = m_axi_sda_rdata     ;
    assign cl_sda_rresp    = m_axi_sda_rresp     ;
    assign cl_sda_rvalid   = m_axi_sda_rvalid    ;
   
    assign m_axi_sda_awaddr    = sda_cl_awaddr   ;
    assign m_axi_sda_awvalid   = sda_cl_awvalid  ;
    assign m_axi_sda_wdata     = sda_cl_wdata    ;
    assign m_axi_sda_wstrb     = sda_cl_wstrb    ;
    assign m_axi_sda_wvalid    = sda_cl_wvalid   ;
    assign m_axi_sda_bready    = sda_cl_bready   ;
    assign m_axi_sda_araddr    = sda_cl_araddr   ;
    assign m_axi_sda_arvalid   = sda_cl_arvalid  ;
    assign m_axi_sda_rready    = sda_cl_rready   ;
    
    assign ocl_sh_awready  = m_axi_ocl_awready   ;
    assign ocl_sh_wready   = m_axi_ocl_wready    ;
    assign ocl_sh_bresp    = m_axi_ocl_bresp     ;
    assign ocl_sh_bvalid   = m_axi_ocl_bvalid    ;
    assign ocl_sh_arready  = m_axi_ocl_arready   ;
    assign ocl_sh_rdata    = m_axi_ocl_rdata     ;
    assign ocl_sh_rresp    = m_axi_ocl_rresp     ;
    assign ocl_sh_rvalid   = m_axi_ocl_rvalid    ;
   
    assign m_axi_ocl_awaddr    = sh_ocl_awaddr   ;
    assign m_axi_ocl_awvalid   = sh_ocl_awvalid  ;
    assign m_axi_ocl_wdata     = sh_ocl_wdata    ;
    assign m_axi_ocl_wstrb     = sh_ocl_wstrb    ;
    assign m_axi_ocl_wvalid    = sh_ocl_wvalid   ;
    assign m_axi_ocl_bready    = sh_ocl_bready   ;
    assign m_axi_ocl_araddr    = sh_ocl_araddr   ;
    assign m_axi_ocl_arvalid   = sh_ocl_arvalid  ;
    assign m_axi_ocl_rready    = sh_ocl_rready   ;
    
    assign bar1_sh_awready  = m_axi_bar1_awready   ;
    assign bar1_sh_wready   = m_axi_bar1_wready    ;
    assign bar1_sh_bresp    = m_axi_bar1_bresp     ;
    assign bar1_sh_bvalid   = m_axi_bar1_bvalid    ;
    assign bar1_sh_arready  = m_axi_bar1_arready   ;
    assign bar1_sh_rdata    = m_axi_bar1_rdata     ;
    assign bar1_sh_rresp    = m_axi_bar1_rresp     ;
    assign bar1_sh_rvalid   = m_axi_bar1_rvalid    ;
   
    assign m_axi_bar1_awaddr    = sh_bar1_awaddr   ;
    assign m_axi_bar1_awvalid   = sh_bar1_awvalid  ;
    assign m_axi_bar1_wdata     = sh_bar1_wdata    ;
    assign m_axi_bar1_wstrb     = sh_bar1_wstrb    ;
    assign m_axi_bar1_wvalid    = sh_bar1_wvalid   ;
    assign m_axi_bar1_bready    = sh_bar1_bready   ;
    assign m_axi_bar1_araddr    = sh_bar1_araddr   ;
    assign m_axi_bar1_arvalid   = sh_bar1_arvalid  ;
    assign m_axi_bar1_rready    = sh_bar1_rready   ;
    
    assign cl_sh_dma_pcis_awready  = m_axi_pcis_awready  ;
    assign cl_sh_dma_pcis_wready   = m_axi_pcis_wready   ;
    assign cl_sh_dma_pcis_bid      = m_axi_pcis_bid      ;
    assign cl_sh_dma_pcis_bresp    = m_axi_pcis_bresp    ;
    assign cl_sh_dma_pcis_bvalid   = m_axi_pcis_bvalid   ;
    assign cl_sh_dma_pcis_arready  = m_axi_pcis_arready  ;
    assign cl_sh_dma_pcis_rid      = m_axi_pcis_rid      ;
    assign cl_sh_dma_pcis_rdata    = m_axi_pcis_rdata    ;
    assign cl_sh_dma_pcis_rresp    = m_axi_pcis_rresp    ;
    assign cl_sh_dma_pcis_rlast    = m_axi_pcis_rlast    ;
    assign cl_sh_dma_pcis_rvalid   = m_axi_pcis_rvalid   ;
   
    assign m_axi_pcis_awid     = sh_cl_dma_pcis_awid     ;       
    assign m_axi_pcis_awaddr   = sh_cl_dma_pcis_awaddr   ;
    assign m_axi_pcis_awlen    = sh_cl_dma_pcis_awlen    ;
    assign m_axi_pcis_awsize   = sh_cl_dma_pcis_awsize   ;
    assign m_axi_pcis_awvalid  = sh_cl_dma_pcis_awvalid  ;
    assign m_axi_pcis_wdata    = sh_cl_dma_pcis_wdata    ;
    assign m_axi_pcis_wstrb    = sh_cl_dma_pcis_wstrb    ;
    assign m_axi_pcis_wlast    = sh_cl_dma_pcis_wlast    ;
    assign m_axi_pcis_wvalid   = sh_cl_dma_pcis_wvalid   ;
    assign m_axi_pcis_bready   = sh_cl_dma_pcis_bready   ;
    assign m_axi_pcis_arid     = sh_cl_dma_pcis_arid     ;
    assign m_axi_pcis_araddr   = sh_cl_dma_pcis_araddr   ;
    assign m_axi_pcis_arlen    = sh_cl_dma_pcis_arlen    ;
    assign m_axi_pcis_arsize   = sh_cl_dma_pcis_arsize   ;
    assign m_axi_pcis_arvalid  = sh_cl_dma_pcis_arvalid  ;
    assign m_axi_pcis_rready   = sh_cl_dma_pcis_rready   ;
    assign m_axi_pcis_awburst  = 2'b01   ;
    assign m_axi_pcis_arburst  = 2'b01   ;
      
    assign cl_sh_pcim_awid     = s_axi_pcim_awid     ;
    assign cl_sh_pcim_awaddr   = s_axi_pcim_awaddr   ;
    assign cl_sh_pcim_awlen    = s_axi_pcim_awlen    ;
    assign cl_sh_pcim_awsize   = s_axi_pcim_awsize   ;
    assign cl_sh_pcim_awuser   = s_axi_pcim_awuser   ;
    assign cl_sh_pcim_awvalid  = s_axi_pcim_awvalid  ;
    assign cl_sh_pcim_wdata    = s_axi_pcim_wdata    ;
    assign cl_sh_pcim_wstrb    = s_axi_pcim_wstrb    ;
    assign cl_sh_pcim_wlast    = s_axi_pcim_wlast    ;
    assign cl_sh_pcim_wvalid   = s_axi_pcim_wvalid   ;
    assign cl_sh_pcim_bready   = s_axi_pcim_bready   ;
    assign cl_sh_pcim_arid     = s_axi_pcim_arid     ;
    assign cl_sh_pcim_araddr   = s_axi_pcim_araddr   ;
    assign cl_sh_pcim_arlen    = s_axi_pcim_arlen    ;
    assign cl_sh_pcim_arsize   = s_axi_pcim_arsize   ;
    assign cl_sh_pcim_aruser   = s_axi_pcim_aruser   ;
    assign cl_sh_pcim_arvalid  = s_axi_pcim_arvalid  ;
    assign cl_sh_pcim_rready   = s_axi_pcim_rready   ;
   
    assign s_axi_pcim_awready  = sh_cl_pcim_awready  ;
    assign s_axi_pcim_wready   = sh_cl_pcim_wready   ;
    assign s_axi_pcim_bid      = sh_cl_pcim_bid      ;
    assign s_axi_pcim_bresp    = sh_cl_pcim_bresp    ;
    assign s_axi_pcim_bvalid   = sh_cl_pcim_bvalid   ;
    assign s_axi_pcim_arready  = sh_cl_pcim_arready  ;
    assign s_axi_pcim_rid      = sh_cl_pcim_rid      ;
    assign s_axi_pcim_rdata    = sh_cl_pcim_rdata    ;
    assign s_axi_pcim_rresp    = sh_cl_pcim_rresp    ;
    assign s_axi_pcim_rlast    = sh_cl_pcim_rlast    ;
    assign s_axi_pcim_rvalid   = sh_cl_pcim_rvalid   ;
    assign cfg_max_payload_out = cfg_max_payload     ;
    assign cfg_max_read_req_out = cfg_max_read_req    ;
    
  if ((C_MODE == 0) || (C_MODE == 1)) begin : gen_mem
    
    logic [15:0]      cl_sh_ddr_awid_2d[2:0];
    logic [63:0]      cl_sh_ddr_awaddr_2d[2:0];
    logic [7:0]       cl_sh_ddr_awlen_2d[2:0];
    logic [2:0]       cl_sh_ddr_awsize_2d[2:0];
    logic [1:0]       cl_sh_ddr_awburst_2d[2:0];
    logic             cl_sh_ddr_awvalid_2d[2:0];
    logic [2:0]       sh_cl_ddr_awready_2d;
    logic [15:0]      cl_sh_ddr_wid_2d[2:0];
    logic [511:0]     cl_sh_ddr_wdata_2d[2:0];
    logic [63:0]      cl_sh_ddr_wstrb_2d[2:0];
    logic [2:0]       cl_sh_ddr_wlast_2d;
    logic [2:0]       cl_sh_ddr_wvalid_2d;
    logic [2:0]       sh_cl_ddr_wready_2d;
    logic [15:0]      sh_cl_ddr_bid_2d[2:0];
    logic [1:0]       sh_cl_ddr_bresp_2d[2:0];
    logic [2:0]       sh_cl_ddr_bvalid_2d;
    logic [2:0]       cl_sh_ddr_bready_2d;
    logic [15:0]      cl_sh_ddr_arid_2d[2:0];
    logic [63:0]      cl_sh_ddr_araddr_2d[2:0];
    logic [7:0]       cl_sh_ddr_arlen_2d[2:0];
    logic [2:0]       cl_sh_ddr_arsize_2d[2:0];
    logic [1:0]       cl_sh_ddr_arburst_2d[2:0];
    logic [2:0]       cl_sh_ddr_arvalid_2d;
    logic [2:0]       sh_cl_ddr_arready_2d;
    logic [15:0]      sh_cl_ddr_rid_2d[2:0];
    logic [511:0]     sh_cl_ddr_rdata_2d[2:0];
    logic [1:0]       sh_cl_ddr_rresp_2d[2:0];
    logic [2:0]       sh_cl_ddr_rlast_2d;
    logic [2:0]       sh_cl_ddr_rvalid_2d;
    logic [2:0]       cl_sh_ddr_rready_2d;
    logic [2:0]       sh_cl_ddr_is_ready_2d;

    assign cl_sh_ddr_awid_2d[0]    = s_axi_ddra_awid         ;
    assign cl_sh_ddr_awaddr_2d[0]  = s_axi_ddra_awaddr       ;
    assign cl_sh_ddr_awlen_2d[0]   = s_axi_ddra_awlen        ;
    assign cl_sh_ddr_awsize_2d[0]  = s_axi_ddra_awsize       ;
    assign cl_sh_ddr_awburst_2d[0] = 2'b01                   ;
    assign cl_sh_ddr_awvalid_2d[0] = s_axi_ddra_awvalid      ;
    assign cl_sh_ddr_wid_2d[0]     = 0          ;
    assign cl_sh_ddr_wdata_2d[0]   = s_axi_ddra_wdata        ;
    assign cl_sh_ddr_wstrb_2d[0]   = s_axi_ddra_wstrb        ;
    assign cl_sh_ddr_wlast_2d[0]   = s_axi_ddra_wlast        ;
    assign cl_sh_ddr_wvalid_2d[0]  = s_axi_ddra_wvalid       ;
    assign cl_sh_ddr_bready_2d[0]  = s_axi_ddra_bready       ;
    assign cl_sh_ddr_arid_2d[0]    = s_axi_ddra_arid         ;
    assign cl_sh_ddr_araddr_2d[0]  = s_axi_ddra_araddr       ;
    assign cl_sh_ddr_arlen_2d[0]   = s_axi_ddra_arlen        ;
    assign cl_sh_ddr_arsize_2d[0]  = s_axi_ddra_arsize       ;
    assign cl_sh_ddr_arburst_2d[0] = 2'b01                   ;
    assign cl_sh_ddr_arvalid_2d[0] = s_axi_ddra_arvalid      ;
    assign cl_sh_ddr_rready_2d[0]  = s_axi_ddra_rready       ;
    
    assign s_axi_ddra_awready      = sh_cl_ddr_awready_2d[0] ;   
    assign s_axi_ddra_wready       = sh_cl_ddr_wready_2d[0]  ;   
    assign s_axi_ddra_bid          = sh_cl_ddr_bid_2d[0]     ;
    assign s_axi_ddra_bresp        = sh_cl_ddr_bresp_2d[0]   ;
    assign s_axi_ddra_bvalid       = sh_cl_ddr_bvalid_2d[0]  ;   
    assign s_axi_ddra_arready      = sh_cl_ddr_arready_2d[0] ;   
    assign s_axi_ddra_rid          = sh_cl_ddr_rid_2d[0]     ;
    assign s_axi_ddra_rdata        = sh_cl_ddr_rdata_2d[0]   ;
    assign s_axi_ddra_rresp        = sh_cl_ddr_rresp_2d[0]   ;
    assign s_axi_ddra_rlast        = sh_cl_ddr_rlast_2d[0]   ;   
    assign s_axi_ddra_rvalid       = sh_cl_ddr_rvalid_2d[0]  ;   
    assign ddra_is_ready           = sh_cl_ddr_is_ready_2d[0];   

    assign cl_sh_ddr_awid_2d[1]    = s_axi_ddrb_awid         ;
    assign cl_sh_ddr_awaddr_2d[1]  = s_axi_ddrb_awaddr       ;
    assign cl_sh_ddr_awlen_2d[1]   = s_axi_ddrb_awlen        ;
    assign cl_sh_ddr_awsize_2d[1]  = s_axi_ddrb_awsize       ;
    assign cl_sh_ddr_awburst_2d[1] = 2'b01                   ;
    assign cl_sh_ddr_awvalid_2d[1] = s_axi_ddrb_awvalid      ;
    assign cl_sh_ddr_wid_2d[1]     = 0          ;
    assign cl_sh_ddr_wdata_2d[1]   = s_axi_ddrb_wdata        ;
    assign cl_sh_ddr_wstrb_2d[1]   = s_axi_ddrb_wstrb        ;
    assign cl_sh_ddr_wlast_2d[1]   = s_axi_ddrb_wlast        ;
    assign cl_sh_ddr_wvalid_2d[1]  = s_axi_ddrb_wvalid       ;
    assign cl_sh_ddr_bready_2d[1]  = s_axi_ddrb_bready       ;
    assign cl_sh_ddr_arid_2d[1]    = s_axi_ddrb_arid         ;
    assign cl_sh_ddr_araddr_2d[1]  = s_axi_ddrb_araddr       ;
    assign cl_sh_ddr_arlen_2d[1]   = s_axi_ddrb_arlen        ;
    assign cl_sh_ddr_arsize_2d[1]  = s_axi_ddrb_arsize       ;
    assign cl_sh_ddr_arburst_2d[1] = 2'b01                   ;
    assign cl_sh_ddr_arvalid_2d[1] = s_axi_ddrb_arvalid      ;
    assign cl_sh_ddr_rready_2d[1]  = s_axi_ddrb_rready       ;
    
    assign s_axi_ddrb_awready      = sh_cl_ddr_awready_2d[1] ;   
    assign s_axi_ddrb_wready       = sh_cl_ddr_wready_2d[1]  ;   
    assign s_axi_ddrb_bid          = sh_cl_ddr_bid_2d[1]     ;
    assign s_axi_ddrb_bresp        = sh_cl_ddr_bresp_2d[1]   ;
    assign s_axi_ddrb_bvalid       = sh_cl_ddr_bvalid_2d[1]  ;   
    assign s_axi_ddrb_arready      = sh_cl_ddr_arready_2d[1] ;   
    assign s_axi_ddrb_rid          = sh_cl_ddr_rid_2d[1]     ;
    assign s_axi_ddrb_rdata        = sh_cl_ddr_rdata_2d[1]   ;
    assign s_axi_ddrb_rresp        = sh_cl_ddr_rresp_2d[1]   ;
    assign s_axi_ddrb_rlast        = sh_cl_ddr_rlast_2d[1]   ;   
    assign s_axi_ddrb_rvalid       = sh_cl_ddr_rvalid_2d[1]  ;   
    assign ddrb_is_ready           = sh_cl_ddr_is_ready_2d[1];   

    assign cl_sh_ddr_awid_2d[2]    = s_axi_ddrd_awid         ;
    assign cl_sh_ddr_awaddr_2d[2]  = s_axi_ddrd_awaddr       ;
    assign cl_sh_ddr_awlen_2d[2]   = s_axi_ddrd_awlen        ;
    assign cl_sh_ddr_awsize_2d[2]  = s_axi_ddrd_awsize       ;
    assign cl_sh_ddr_awburst_2d[2] = 2'b01                   ;
    assign cl_sh_ddr_awvalid_2d[2] = s_axi_ddrd_awvalid      ;
    assign cl_sh_ddr_wid_2d[2]     = 0          ;
    assign cl_sh_ddr_wdata_2d[2]   = s_axi_ddrd_wdata        ;
    assign cl_sh_ddr_wstrb_2d[2]   = s_axi_ddrd_wstrb        ;
    assign cl_sh_ddr_wlast_2d[2]   = s_axi_ddrd_wlast        ;
    assign cl_sh_ddr_wvalid_2d[2]  = s_axi_ddrd_wvalid       ;
    assign cl_sh_ddr_bready_2d[2]  = s_axi_ddrd_bready       ;
    assign cl_sh_ddr_arid_2d[2]    = s_axi_ddrd_arid         ;
    assign cl_sh_ddr_araddr_2d[2]  = s_axi_ddrd_araddr       ;
    assign cl_sh_ddr_arlen_2d[2]   = s_axi_ddrd_arlen        ;
    assign cl_sh_ddr_arsize_2d[2]  = s_axi_ddrd_arsize       ;
    assign cl_sh_ddr_arburst_2d[2] = 2'b01                   ;
    assign cl_sh_ddr_arvalid_2d[2] = s_axi_ddrd_arvalid      ;
    assign cl_sh_ddr_rready_2d[2]  = s_axi_ddrd_rready       ;
    
    assign s_axi_ddrd_awready      = sh_cl_ddr_awready_2d[2] ;   
    assign s_axi_ddrd_wready       = sh_cl_ddr_wready_2d[2]  ;   
    assign s_axi_ddrd_bid          = sh_cl_ddr_bid_2d[2]     ;
    assign s_axi_ddrd_bresp        = sh_cl_ddr_bresp_2d[2]   ;
    assign s_axi_ddrd_bvalid       = sh_cl_ddr_bvalid_2d[2]  ;   
    assign s_axi_ddrd_arready      = sh_cl_ddr_arready_2d[2] ;   
    assign s_axi_ddrd_rid          = sh_cl_ddr_rid_2d[2]     ;
    assign s_axi_ddrd_rdata        = sh_cl_ddr_rdata_2d[2]   ;
    assign s_axi_ddrd_rresp        = sh_cl_ddr_rresp_2d[2]   ;
    assign s_axi_ddrd_rlast        = sh_cl_ddr_rlast_2d[2]   ;   
    assign s_axi_ddrd_rvalid       = sh_cl_ddr_rvalid_2d[2]  ;   
    assign ddrd_is_ready           = sh_cl_ddr_is_ready_2d[2];   

    logic             ddr_aws_stat_ack0;
    logic [31:0]      ddr_aws_stat_rdata0;
    logic [7:0]       ddr_aws_stat_int0;
    logic             ddr_aws_stat_ack1;
    logic [31:0]      ddr_aws_stat_rdata1;
    logic [7:0]       ddr_aws_stat_int1;
    logic             ddr_aws_stat_ack2;
    logic [31:0]      ddr_aws_stat_rdata2;
    logic [7:0]       ddr_aws_stat_int2;
    
    logic [7:0]       pipe_ddr_stat_addr0;
    logic             pipe_ddr_stat_wr0;
    logic             pipe_ddr_stat_rd0; 
    logic [31:0]      pipe_ddr_stat_wdata0;
    logic             ddr_pipe_stat_ack0;
    logic [31:0]      ddr_pipe_stat_rdata0;
    logic [7:0]       ddr_pipe_stat_int0;

    logic [7:0]       pipe_ddr_stat_addr1;
    logic             pipe_ddr_stat_wr1;
    logic             pipe_ddr_stat_rd1; 
    logic [31:0]      pipe_ddr_stat_wdata1;
    logic             ddr_pipe_stat_ack1;
    logic [31:0]      ddr_pipe_stat_rdata1;
    logic [7:0]       ddr_pipe_stat_int1;

    logic [7:0]       pipe_ddr_stat_addr2;
    logic             pipe_ddr_stat_wr2;
    logic             pipe_ddr_stat_rd2; 
    logic [31:0]      pipe_ddr_stat_wdata2;
    logic             ddr_pipe_stat_ack2;
    logic [31:0]      ddr_pipe_stat_rdata2;
    logic [7:0]       ddr_pipe_stat_int2;

//-------------------------------------------------
// Tie-offs when DDRs are disabled
//-------------------------------------------------
    assign ddr_sh_stat_ack0   = (C_DDR_A_PRESENT!=0) ? ddr_aws_stat_ack0   : 1'b1;
    assign ddr_sh_stat_rdata0 = (C_DDR_A_PRESENT!=0) ? ddr_aws_stat_rdata0 : 0;
    assign ddr_sh_stat_int0   = (C_DDR_A_PRESENT!=0) ? ddr_aws_stat_int0   : 8'b0;
    assign ddr_sh_stat_ack1   = (C_DDR_B_PRESENT!=0) ? ddr_aws_stat_ack1   : 1'b1;
    assign ddr_sh_stat_rdata1 = (C_DDR_B_PRESENT!=0) ? ddr_aws_stat_rdata1 : 0;
    assign ddr_sh_stat_int1   = (C_DDR_B_PRESENT!=0) ? ddr_aws_stat_int1   : 8'b0;
    assign ddr_sh_stat_ack2   = (C_DDR_D_PRESENT!=0) ? ddr_aws_stat_ack2   : 1'b1;
    assign ddr_sh_stat_rdata2 = (C_DDR_D_PRESENT!=0) ? ddr_aws_stat_rdata2 : 0;
    assign ddr_sh_stat_int2   = (C_DDR_D_PRESENT!=0) ? ddr_aws_stat_int2   : 8'b0;

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------
  logic pre_sync_rst_n;
  logic sync_rst_n;
     
  always @(negedge rst_main_n or posedge clk_main_a0) begin
    if (!rst_main_n) begin
      pre_sync_rst_n <= 1'b0;
      sync_rst_n <= 1'b0;
    end else begin
      pre_sync_rst_n <= 1'b1;
      sync_rst_n <= pre_sync_rst_n;
    end
  end

  `ifdef FPGA_LESS_RST
    `undef FPGA_LESS_RST
  `endif  

  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wdata0 (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_wdata0),   .out_bus(pipe_ddr_stat_wdata0));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_addr0  (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_addr0),    .out_bus(pipe_ddr_stat_addr0));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wr0    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_wr0),      .out_bus(pipe_ddr_stat_wr0));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rd0    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_rd0),      .out_bus(pipe_ddr_stat_rd0));
  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rdata0 (.clk(clk_main_a0), .rst_n(1'b1),       .out_bus(ddr_aws_stat_rdata0), .in_bus(ddr_pipe_stat_rdata0));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_ack0   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_ack0),   .in_bus(ddr_pipe_stat_ack0));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_int0   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_int0),   .in_bus(ddr_pipe_stat_int0));

  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wdata1 (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_wdata1),   .out_bus(pipe_ddr_stat_wdata1));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_addr1  (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_addr1),    .out_bus(pipe_ddr_stat_addr1));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wr1    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_wr1),      .out_bus(pipe_ddr_stat_wr1));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rd1    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_rd1),      .out_bus(pipe_ddr_stat_rd1));
  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rdata1 (.clk(clk_main_a0), .rst_n(1'b1),       .out_bus(ddr_aws_stat_rdata1), .in_bus(ddr_pipe_stat_rdata1));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_ack1   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_ack1),   .in_bus(ddr_pipe_stat_ack1));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_int1   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_int1),   .in_bus(ddr_pipe_stat_int1));

  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wdata2 (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_wdata2),   .out_bus(pipe_ddr_stat_wdata2));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_addr2  (.clk(clk_main_a0), .rst_n(1'b1),       .in_bus(sh_ddr_stat_addr2),    .out_bus(pipe_ddr_stat_addr2));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_wr2    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_wr2),      .out_bus(pipe_ddr_stat_wr2));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rd2    (.clk(clk_main_a0), .rst_n(sync_rst_n), .in_bus(sh_ddr_stat_rd2),      .out_bus(pipe_ddr_stat_rd2));
  lib_pipe #(.WIDTH(32), .STAGES(C_NUM_STAGES_STATS)) pipe_stat_rdata2 (.clk(clk_main_a0), .rst_n(1'b1),       .out_bus(ddr_aws_stat_rdata2), .in_bus(ddr_pipe_stat_rdata2));
  lib_pipe #(.WIDTH(1),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_ack2   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_ack2),   .in_bus(ddr_pipe_stat_ack2));
  lib_pipe #(.WIDTH(8),  .STAGES(C_NUM_STAGES_STATS)) pipe_stat_int2   (.clk(clk_main_a0), .rst_n(sync_rst_n), .out_bus(ddr_aws_stat_int2),   .in_bus(ddr_pipe_stat_int2));

  sh_ddr #(
   .DDR_A_PRESENT(C_DDR_A_PRESENT),
   .DDR_B_PRESENT(C_DDR_B_PRESENT),
   .DDR_D_PRESENT(C_DDR_D_PRESENT)
   ) sh_ddr_0
   (
   .clk(clk_main_a0),
   .rst_n(sync_rst_n),

   .stat_clk(clk_main_a0),
   .stat_rst_n(sync_rst_n),

   .CLK_300M_DIMM0_DP(CLK_300M_DIMM0_DP),
   .CLK_300M_DIMM0_DN(CLK_300M_DIMM0_DN),
   .M_A_ACT_N(M_A_ACT_N),
   .M_A_MA(M_A_MA),
   .M_A_BA(M_A_BA),
   .M_A_BG(M_A_BG),
   .M_A_CKE(M_A_CKE),
   .M_A_ODT(M_A_ODT),
   .M_A_CS_N(M_A_CS_N),
   .M_A_CLK_DN(M_A_CLK_DN),
   .M_A_CLK_DP(M_A_CLK_DP),
   .M_A_PAR(M_A_PAR),
   .M_A_DQ(M_A_DQ),
   .M_A_ECC(M_A_ECC),
   .M_A_DQS_DP(M_A_DQS_DP),
   .M_A_DQS_DN(M_A_DQS_DN),
   .cl_RST_DIMM_A_N(cl_RST_DIMM_A_N),
   
   .CLK_300M_DIMM1_DP(CLK_300M_DIMM1_DP),
   .CLK_300M_DIMM1_DN(CLK_300M_DIMM1_DN),
   .M_B_ACT_N(M_B_ACT_N),
   .M_B_MA(M_B_MA),
   .M_B_BA(M_B_BA),
   .M_B_BG(M_B_BG),
   .M_B_CKE(M_B_CKE),
   .M_B_ODT(M_B_ODT),
   .M_B_CS_N(M_B_CS_N),
   .M_B_CLK_DN(M_B_CLK_DN),
   .M_B_CLK_DP(M_B_CLK_DP),
   .M_B_PAR(M_B_PAR),
   .M_B_DQ(M_B_DQ),
   .M_B_ECC(M_B_ECC),
   .M_B_DQS_DP(M_B_DQS_DP),
   .M_B_DQS_DN(M_B_DQS_DN),
   .cl_RST_DIMM_B_N(cl_RST_DIMM_B_N),

   .CLK_300M_DIMM3_DP(CLK_300M_DIMM3_DP),
   .CLK_300M_DIMM3_DN(CLK_300M_DIMM3_DN),
   .M_D_ACT_N(M_D_ACT_N),
   .M_D_MA(M_D_MA),
   .M_D_BA(M_D_BA),
   .M_D_BG(M_D_BG),
   .M_D_CKE(M_D_CKE),
   .M_D_ODT(M_D_ODT),
   .M_D_CS_N(M_D_CS_N),
   .M_D_CLK_DN(M_D_CLK_DN),
   .M_D_CLK_DP(M_D_CLK_DP),
   .M_D_PAR(M_D_PAR),
   .M_D_DQ(M_D_DQ),
   .M_D_ECC(M_D_ECC),
   .M_D_DQS_DP(M_D_DQS_DP),
   .M_D_DQS_DN(M_D_DQS_DN),
   .cl_RST_DIMM_D_N(cl_RST_DIMM_D_N),

   //------------------------------------------------------
   // AXI Slave Interfaces
   //------------------------------------------------------
   .cl_sh_ddr_awid(cl_sh_ddr_awid_2d),
   .cl_sh_ddr_awaddr(cl_sh_ddr_awaddr_2d),
   .cl_sh_ddr_awlen(cl_sh_ddr_awlen_2d),
   .cl_sh_ddr_awsize(cl_sh_ddr_awsize_2d),
   .cl_sh_ddr_awburst(cl_sh_ddr_awburst_2d),
   .cl_sh_ddr_awvalid(cl_sh_ddr_awvalid_2d),
   .sh_cl_ddr_awready(sh_cl_ddr_awready_2d),

   .cl_sh_ddr_wid(cl_sh_ddr_wid_2d),
   .cl_sh_ddr_wdata(cl_sh_ddr_wdata_2d),
   .cl_sh_ddr_wstrb(cl_sh_ddr_wstrb_2d),
   .cl_sh_ddr_wlast(cl_sh_ddr_wlast_2d),
   .cl_sh_ddr_wvalid(cl_sh_ddr_wvalid_2d),
   .sh_cl_ddr_wready(sh_cl_ddr_wready_2d),

   .sh_cl_ddr_bid(sh_cl_ddr_bid_2d),
   .sh_cl_ddr_bresp(sh_cl_ddr_bresp_2d),
   .sh_cl_ddr_bvalid(sh_cl_ddr_bvalid_2d),
   .cl_sh_ddr_bready(cl_sh_ddr_bready_2d),

   .cl_sh_ddr_arid(cl_sh_ddr_arid_2d),
   .cl_sh_ddr_araddr(cl_sh_ddr_araddr_2d),
   .cl_sh_ddr_arlen(cl_sh_ddr_arlen_2d),
   .cl_sh_ddr_arsize(cl_sh_ddr_arsize_2d),
   .cl_sh_ddr_arburst(cl_sh_ddr_arburst_2d),
   .cl_sh_ddr_arvalid(cl_sh_ddr_arvalid_2d),
   .sh_cl_ddr_arready(sh_cl_ddr_arready_2d),

   .sh_cl_ddr_rid(sh_cl_ddr_rid_2d),
   .sh_cl_ddr_rdata(sh_cl_ddr_rdata_2d),
   .sh_cl_ddr_rresp(sh_cl_ddr_rresp_2d),
   .sh_cl_ddr_rlast(sh_cl_ddr_rlast_2d),
   .sh_cl_ddr_rvalid(sh_cl_ddr_rvalid_2d),
   .cl_sh_ddr_rready(cl_sh_ddr_rready_2d),

   .sh_cl_ddr_is_ready(sh_cl_ddr_is_ready_2d),
   
   .sh_ddr_stat_addr0  (pipe_ddr_stat_addr0 ),
   .sh_ddr_stat_wr0    (pipe_ddr_stat_wr0   ),
   .sh_ddr_stat_rd0    (pipe_ddr_stat_rd0   ),
   .sh_ddr_stat_wdata0 (pipe_ddr_stat_wdata0),
   .ddr_sh_stat_ack0   (ddr_pipe_stat_ack0  ),
   .ddr_sh_stat_rdata0 (ddr_pipe_stat_rdata0),
   .ddr_sh_stat_int0   (ddr_pipe_stat_int0  ),

   .sh_ddr_stat_addr1  (pipe_ddr_stat_addr1 ),
   .sh_ddr_stat_wr1    (pipe_ddr_stat_wr1   ),
   .sh_ddr_stat_rd1    (pipe_ddr_stat_rd1   ),
   .sh_ddr_stat_wdata1 (pipe_ddr_stat_wdata1),
   .ddr_sh_stat_ack1   (ddr_pipe_stat_ack1  ),
   .ddr_sh_stat_rdata1 (ddr_pipe_stat_rdata1),
   .ddr_sh_stat_int1   (ddr_pipe_stat_int1  ),

   .sh_ddr_stat_addr2  (pipe_ddr_stat_addr2 ),
   .sh_ddr_stat_wr2    (pipe_ddr_stat_wr2   ),
   .sh_ddr_stat_rd2    (pipe_ddr_stat_rd2   ),
   .sh_ddr_stat_wdata2 (pipe_ddr_stat_wdata2),
   .ddr_sh_stat_ack2   (ddr_pipe_stat_ack2  ),
   .ddr_sh_stat_rdata2 (ddr_pipe_stat_rdata2),
   .ddr_sh_stat_int2   (ddr_pipe_stat_int2  )

   );
   
  end else begin : gen_non_mem
    
    assign s_axi_ddra_awready      = 0;   
    assign s_axi_ddra_wready       = 0;   
    assign s_axi_ddra_bid          = 0;
    assign s_axi_ddra_bresp        = 0;
    assign s_axi_ddra_bvalid       = 0;   
    assign s_axi_ddra_arready      = 0;   
    assign s_axi_ddra_rid          = 0;
    assign s_axi_ddra_rdata        = 0;
    assign s_axi_ddra_rresp        = 0;
    assign s_axi_ddra_rlast        = 1'b1;   
    assign s_axi_ddra_rvalid       = 0;   
    assign ddra_is_ready           = 0;   

    assign s_axi_ddrb_awready      = 0;   
    assign s_axi_ddrb_wready       = 0;   
    assign s_axi_ddrb_bid          = 0;
    assign s_axi_ddrb_bresp        = 0;
    assign s_axi_ddrb_bvalid       = 0;   
    assign s_axi_ddrb_arready      = 0;   
    assign s_axi_ddrb_rid          = 0;
    assign s_axi_ddrb_rdata        = 0;
    assign s_axi_ddrb_rresp        = 0;
    assign s_axi_ddrb_rlast        = 1'b1;   
    assign s_axi_ddrb_rvalid       = 0;   
    assign ddrb_is_ready           = 0;   

    assign s_axi_ddrd_awready      = 0;   
    assign s_axi_ddrd_wready       = 0;   
    assign s_axi_ddrd_bid          = 0;
    assign s_axi_ddrd_bresp        = 0;
    assign s_axi_ddrd_bvalid       = 0;   
    assign s_axi_ddrd_arready      = 0;   
    assign s_axi_ddrd_rid          = 0;
    assign s_axi_ddrd_rdata        = 0;
    assign s_axi_ddrd_rresp        = 0;
    assign s_axi_ddrd_rlast        = 1'b1;   
    assign s_axi_ddrd_rvalid       = 0;   
    assign ddrd_is_ready           = 0;   

    assign ddr_sh_stat_ack0        = 1'b1;
    assign ddr_sh_stat_rdata0      = 0;
    assign ddr_sh_stat_int0        = 8'b0;
    assign ddr_sh_stat_ack1        = 1'b1;
    assign ddr_sh_stat_rdata1      = 0;
    assign ddr_sh_stat_int1        = 8'b0;
    assign ddr_sh_stat_ack2        = 1'b1;
    assign ddr_sh_stat_rdata2      = 0;
    assign ddr_sh_stat_int2        = 8'b0;

    assign M_A_ACT_N               = 0;
    assign M_A_MA                  = 0;
    assign M_A_BA                  = 0;
    assign M_A_BG                  = 0;
    assign M_A_CKE                 = 0;
    assign M_A_ODT                 = 0;
    assign M_A_CS_N                = 0;
    assign M_A_CLK_DN              = 0;
    assign M_A_CLK_DP              = 0;
    assign M_A_PAR                 = 0;
    assign cl_RST_DIMM_A_N         = 0;
    
    assign M_B_ACT_N               = 0;
    assign M_B_MA                  = 0;
    assign M_B_BA                  = 0;
    assign M_B_BG                  = 0;
    assign M_B_CKE                 = 0;
    assign M_B_ODT                 = 0;
    assign M_B_CS_N                = 0;
    assign M_B_CLK_DN              = 0;
    assign M_B_CLK_DP              = 0;
    assign M_B_PAR                 = 0;
    assign cl_RST_DIMM_B_N         = 0;
    
    assign M_D_ACT_N               = 0;
    assign M_D_MA                  = 0;
    assign M_D_BA                  = 0;
    assign M_D_BG                  = 0;
    assign M_D_CKE                 = 0;
    assign M_D_ODT                 = 0;
    assign M_D_CS_N                = 0;
    assign M_D_CLK_DN              = 0;
    assign M_D_CLK_DP              = 0;
    assign M_D_PAR                 = 0;
    assign cl_RST_DIMM_D_N         = 0;
    
  end  // gen_mem
  endgenerate

endmodule
