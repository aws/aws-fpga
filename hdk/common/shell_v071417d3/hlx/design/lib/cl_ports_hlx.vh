//---------------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
// 
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//---------------------------------------------------------------------------------------

   //--------------------------------
   // Globals
   //--------------------------------
   input clk_main_a0,                           //Main clock.  This is the clock for all of the interfaces to the SH
   input clk_extra_a1,                          //Extra clock A1 (phase aligned to "A" clock group)
   input clk_extra_a2,                          //Extra clock A2 (phase aligned to "A" clock group)
   input clk_extra_a3,                          //Extra clock A3 (phase aligned to "A" clock group)
   
   input clk_extra_b0,                          //Extra clock B0 (phase aligned to "B" clock group)
   input clk_extra_b1,                          //Extra clock B1 (phase aligned to "B" clock group)
   
   input clk_extra_c0,                          //Extra clock C0 (phase aligned to "B" clock group)
   input clk_extra_c1,                          //Extra clock C1 (phase aligned to "B" clock group)
   
   input kernel_rst_n,                          //Kernel reset (for SDA platform)
     
   input rst_main_n,                            //Reset sync to main clock.

   input sh_cl_flr_assert,                      //Function level reset assertion.  Level signal that indicates PCIe function level reset is asserted 
   output logic cl_sh_flr_done,                 //Function level reset done indication.  Must be asserted by CL when done processing function level reset.
         
   output logic[31:0] cl_sh_status0,            //Functionality TBD
   output logic[31:0] cl_sh_status1,            //Functionality TBD
   output logic[31:0] cl_sh_id0,
   output logic[31:0] cl_sh_id1,

   input[31:0] sh_cl_ctl0,                      //Functionality TBD
   input[31:0] sh_cl_ctl1,                      //Functionality TBD

   input[15:0] sh_cl_status_vdip,               //Virtual DIP switches.  Controlled through FPGA management PF and tools.
   output logic[15:0] cl_sh_status_vled,        //Virtual LEDs, monitored through FPGA management PF and tools

   input[1:0] sh_cl_pwr_state,               	//Power state, 2'b00: Normal, 2'b11: Critical
   

   //-------------------------------------------------------------------------------------------
   // PCIe Master interface from CL
   //
   //    AXI-4 master interface per PCIe interface.  This is for PCIe transactions mastered
   //    from the SH targetting the host (DMA access to host).  Standard AXI-4 interface.
   //    NOTE: awuser pins have critical functionality and developer must read the detailed
   //    functional definitions of these pins
   //-------------------------------------------------------------------------------------------
   output logic[15:0] cl_sh_pcim_awid,
   output logic[63:0] cl_sh_pcim_awaddr,
   output logic[7:0] cl_sh_pcim_awlen,
   output logic[2:0] cl_sh_pcim_awsize,
   output logic[18:0] cl_sh_pcim_awuser,                             //10:0 Length in DW of the transaction
                                                                     //14:11 are the byte-enable for the first DW (bit value 1 mean byte is enable, i.e. not masked)
                                                                     //18:15 are the byte-enable for the last DW (bit value 1 mean byte is enable, i.e. not masked)

								
   output logic cl_sh_pcim_awvalid,
   input sh_cl_pcim_awready,
   
   output logic[511:0] cl_sh_pcim_wdata,
   output logic[63:0] cl_sh_pcim_wstrb,
   output logic cl_sh_pcim_wlast,
   output logic cl_sh_pcim_wvalid,
   input sh_cl_pcim_wready,
   
   input logic[15:0] sh_cl_pcim_bid,
   input logic[1:0] sh_cl_pcim_bresp,
   input logic sh_cl_pcim_bvalid,
   output logic cl_sh_pcim_bready,
  
   output logic[15:0] cl_sh_pcim_arid,		                           //Note max 32 outstanding txns are supported, width is larger to allow bits for AXI fabrics
   output logic[63:0] cl_sh_pcim_araddr,
   output logic[7:0] cl_sh_pcim_arlen,
   output logic[2:0] cl_sh_pcim_arsize,
   output logic[18:0] cl_sh_pcim_aruser,                             // 10:0 Length in DW of the transaction
                                                                     // 18:11 Must be set to 0xFF, could be ignored in next release

   output logic cl_sh_pcim_arvalid,
   input sh_cl_pcim_arready,
   
   input[15:0] sh_cl_pcim_rid,
   input[511:0] sh_cl_pcim_rdata,
   input[1:0] sh_cl_pcim_rresp,
   input sh_cl_pcim_rlast,
   input sh_cl_pcim_rvalid,
   output logic cl_sh_pcim_rready,

   input[1:0] cfg_max_payload,                                    //Max payload size - 00:128B, 01:256B, 10:512B
   input[2:0] cfg_max_read_req                                    //Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                                  // 100b-2048B, 101b:4096B
   
   //-----------------------------------------------------------------------------------------------
   // DDR-4 Interface 
   //
   //    x3 DDR is instantiated in CL.  This is the physical interface (fourth DDR is in SH)
   //-----------------------------------------------------------------------------------------------
`ifndef NO_CL_DDR
  ,
// ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
   input                CLK_300M_DIMM0_DP,
   input                CLK_300M_DIMM0_DN,
   output               M_A_ACT_N,
   output [16:0]        M_A_MA,
   output [1:0]         M_A_BA,
   output [1:0]         M_A_BG,
   output [0:0]         M_A_CKE,
   output [0:0]         M_A_ODT,
   output [0:0]         M_A_CS_N,
   output [0:0]         M_A_CLK_DN,
   output [0:0]         M_A_CLK_DP,
   output               M_A_PAR,
   inout  [63:0]        M_A_DQ,
   inout  [7:0]         M_A_ECC,
   inout  [17:0]        M_A_DQS_DP,
   inout  [17:0]        M_A_DQS_DN,
   output               cl_RST_DIMM_A_N,

// ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
   input                CLK_300M_DIMM1_DP,
   input                CLK_300M_DIMM1_DN,
   output               M_B_ACT_N,
   output [16:0]        M_B_MA,
   output [1:0]         M_B_BA,
   output [1:0]         M_B_BG,
   output [0:0]         M_B_CKE,
   output [0:0]         M_B_ODT,
   output [0:0]         M_B_CS_N,
   output [0:0]         M_B_CLK_DN,
   output [0:0]         M_B_CLK_DP,
   output               M_B_PAR,
   inout  [63:0]        M_B_DQ,
   inout  [7:0]         M_B_ECC,
   inout  [17:0]        M_B_DQS_DP,
   inout  [17:0]        M_B_DQS_DN,
   output               cl_RST_DIMM_B_N,


// ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
   input                CLK_300M_DIMM3_DP,
   input                CLK_300M_DIMM3_DN,
   output               M_D_ACT_N,
   output [16:0]        M_D_MA,
   output [1:0]         M_D_BA,
   output [1:0]         M_D_BG,
   output [0:0]         M_D_CKE,
   output [0:0]         M_D_ODT,
   output [0:0]         M_D_CS_N,
   output [0:0]         M_D_CLK_DN,
   output [0:0]         M_D_CLK_DP,
   output               M_D_PAR,
   inout  [63:0]        M_D_DQ,
   inout  [7:0]         M_D_ECC,
   inout  [17:0]        M_D_DQS_DP,
   inout  [17:0]        M_D_DQS_DN,
   output               cl_RST_DIMM_D_N

`endif

   //-----------------------------------------------------------------------------
   // DDR Stats interfaces for DDR controllers in the CL.  This must be hooked up
   // to the sh_ddr.sv for the DDR interfaces to function.
   //-----------------------------------------------------------------------------
   ,
   input [7:0] sh_ddr_stat_addr0,
   input sh_ddr_stat_wr0, 
   input sh_ddr_stat_rd0, 
   input [31:0] sh_ddr_stat_wdata0,
   output logic ddr_sh_stat_ack0,
   output logic[31:0] ddr_sh_stat_rdata0,
   output logic[7:0] ddr_sh_stat_int0,

   input [7:0] sh_ddr_stat_addr1,
   input sh_ddr_stat_wr1, 
   input sh_ddr_stat_rd1, 
   input [31:0] sh_ddr_stat_wdata1,
   output logic ddr_sh_stat_ack1,
   output logic[31:0] ddr_sh_stat_rdata1,
   output logic[7:0] ddr_sh_stat_int1,

   input [7:0] sh_ddr_stat_addr2,
   input sh_ddr_stat_wr2, 
   input sh_ddr_stat_rd2, 
   input [31:0] sh_ddr_stat_wdata2,
   output logic ddr_sh_stat_ack2,
   output logic[31:0] ddr_sh_stat_rdata2,
   output logic[7:0] ddr_sh_stat_int2,

   //-----------------------------------------------------------------------------------
   // AXI4 Interface for DDR_C 
   //    This is the DDR controller that is instantiated in the SH.  CL is the AXI-4
   //    master, and the DDR_C controller in the SH is the slave.
   //-----------------------------------------------------------------------------------
   output [15:0] cl_sh_ddr_awid,
   output [63:0] cl_sh_ddr_awaddr,
   output [7:0] cl_sh_ddr_awlen,
   output [2:0] cl_sh_ddr_awsize,
   output  cl_sh_ddr_awvalid,
   input sh_cl_ddr_awready,
      
   output [15:0] cl_sh_ddr_wid,
   output [511:0] cl_sh_ddr_wdata,
   output [63:0] cl_sh_ddr_wstrb,
   output  cl_sh_ddr_wlast,
   output  cl_sh_ddr_wvalid,
   input sh_cl_ddr_wready,
      
   input[15:0] sh_cl_ddr_bid,
   input[1:0] sh_cl_ddr_bresp,
   input sh_cl_ddr_bvalid,
   output  cl_sh_ddr_bready,
      
   output [15:0] cl_sh_ddr_arid,
   output [63:0] cl_sh_ddr_araddr,
   output [7:0] cl_sh_ddr_arlen,
   output [2:0] cl_sh_ddr_arsize,
   output  cl_sh_ddr_arvalid,
   input sh_cl_ddr_arready,
      
   input[15:0] sh_cl_ddr_rid,
   input[511:0] sh_cl_ddr_rdata,
   input[1:0] sh_cl_ddr_rresp,
   input sh_cl_ddr_rlast,
   input sh_cl_ddr_rvalid,
   output  cl_sh_ddr_rready,
      
   input sh_cl_ddr_is_ready

   `ifdef DDR_A_SH      //THIS IS NOT DEFINED
      //------------------------------------------------------------------------------------------
      // AXI4 Interface for DDRA (if in the SH)  This is an expermental mode for including
      //    DDR_A in the SH.  
      //------------------------------------------------------------------------------------------
      ,
      output [15:0] cl_sh_ddra_awid,
      output [63:0] cl_sh_ddra_awaddr,
      output [7:0] cl_sh_ddra_awlen,
      output  cl_sh_ddra_awvalid,
      input sh_cl_ddra_awready,
         
      output [15:0] cl_sh_ddra_wid,
      output [511:0] cl_sh_ddra_wdata,
      output [63:0] cl_sh_ddra_wstrb,
      output  cl_sh_ddra_wlast,
      output  cl_sh_ddra_wvalid,
      input sh_cl_ddra_wready,
         
      input[15:0] sh_cl_ddra_bid,
      input[1:0] sh_cl_ddra_bresp,
      input sh_cl_ddra_bvalid,
      output  cl_sh_ddra_bready,
         
      output [15:0] cl_sh_ddra_arid,
      output [63:0] cl_sh_ddra_araddr,
      output [7:0] cl_sh_ddra_arlen,
      output  cl_sh_ddra_arvalid,
      input sh_cl_ddra_arready,
         
      input[15:0] sh_cl_ddra_rid,
      input[511:0] sh_cl_ddra_rdata,
      input[1:0] sh_cl_ddra_rresp,
      input sh_cl_ddra_rlast,
      input sh_cl_ddra_rvalid,
      output  cl_sh_ddra_rready,
         
      input sh_cl_ddra_is_ready
   `endif
                                                                                                    
   //---------------------------------------------------------------------------------------
   // The user-defined interrupts.  These map to MSI-X vectors through mapping in the SH.
   //---------------------------------------------------------------------------------------
    ,
    output logic[15:0] cl_sh_apppf_irq_req,
    input [15:0] sh_cl_apppf_irq_ack

   //----------------------------------------------------
   // PCIS AXI-4 interface to master cycles to CL
   //----------------------------------------------------
   ,
   input[5:0] sh_cl_dma_pcis_awid,
   input[63:0] sh_cl_dma_pcis_awaddr,
   input[7:0] sh_cl_dma_pcis_awlen,
   input[2:0] sh_cl_dma_pcis_awsize,
   input sh_cl_dma_pcis_awvalid,
   output logic cl_sh_dma_pcis_awready,

   input[511:0] sh_cl_dma_pcis_wdata,
   input[63:0] sh_cl_dma_pcis_wstrb,
   input sh_cl_dma_pcis_wlast,
   input sh_cl_dma_pcis_wvalid,
   output logic cl_sh_dma_pcis_wready,

   output logic[5:0] cl_sh_dma_pcis_bid,
   output logic[1:0] cl_sh_dma_pcis_bresp,
   output logic cl_sh_dma_pcis_bvalid,
   input sh_cl_dma_pcis_bready,

   input[5:0] sh_cl_dma_pcis_arid,
   input[63:0] sh_cl_dma_pcis_araddr,
   input[7:0] sh_cl_dma_pcis_arlen,
   input[2:0] sh_cl_dma_pcis_arsize,
   input sh_cl_dma_pcis_arvalid,
   output logic cl_sh_dma_pcis_arready,

   output logic[5:0] cl_sh_dma_pcis_rid,
   output logic[511:0] cl_sh_dma_pcis_rdata,
   output logic[1:0] cl_sh_dma_pcis_rresp,
   output logic cl_sh_dma_pcis_rlast,
   output logic cl_sh_dma_pcis_rvalid,
   input sh_cl_dma_pcis_rready

   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through ManagementPF BAR4 for developer's use
   // If the CL is created through  Xilinx’s SDAccel, then this configuration bus
   // would be connected automatically to SDAccel generic logic (SmartConnect, APM etc)
   //------------------------------------------------------------------------------------------
    ,
   input sda_cl_awvalid,
   input[31:0] sda_cl_awaddr, 
   output logic cl_sda_awready,

   //Write data
   input sda_cl_wvalid,
   input[31:0] sda_cl_wdata,
   input[3:0] sda_cl_wstrb,
   output logic cl_sda_wready,

   //Write response
   output logic cl_sda_bvalid,
   output logic[1:0] cl_sda_bresp,
   input sda_cl_bready,

   //Read address
   input sda_cl_arvalid,
   input[31:0] sda_cl_araddr,
   output logic cl_sda_arready,

   //Read data/response
   output logic cl_sda_rvalid,
   output logic[31:0] cl_sda_rdata,
   output logic[1:0] cl_sda_rresp,

   input sda_cl_rready,

   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through AppPF BAR0
   // For example, this AXI-L interface can connect to OpenCL Kernels
   // This would connect automatically to the required logic 
   // if the CL is created through SDAccel flow   
   //------------------------------------------------------------------------------------------
   input sh_ocl_awvalid,
   input[31:0] sh_ocl_awaddr,
   output logic ocl_sh_awready,
                                                                                                                               
   //Write data                                                                                                                
   input sh_ocl_wvalid,
   input[31:0] sh_ocl_wdata,
   input[3:0] sh_ocl_wstrb,
   output logic ocl_sh_wready,
                                                                                                                               
   //Write response                                                                                                            
   output logic ocl_sh_bvalid,
   output logic[1:0] ocl_sh_bresp,
   input sh_ocl_bready,
                                                                                                                               
   //Read address                                                                                                              
   input sh_ocl_arvalid,
   input[31:0] sh_ocl_araddr,
   output logic ocl_sh_arready,
                                                                                                                               
   //Read data/response                                                                                                        
   output logic ocl_sh_rvalid,
   output logic[31:0] ocl_sh_rdata,
   output logic[1:0] ocl_sh_rresp,
                                                                                                                               
   input sh_ocl_rready,

   //------------------------------------------------------------------------------------------
   // AXI-L maps to any inbound PCIe access through AppPF BAR1
   // For example,
   //------------------------------------------------------------------------------------------
   input sh_bar1_awvalid,
   input[31:0] sh_bar1_awaddr,
   output logic bar1_sh_awready,
                                                                                                                               
   //Write data                                                                                                                
   input sh_bar1_wvalid,
   input[31:0] sh_bar1_wdata,
   input[3:0] sh_bar1_wstrb,
   output logic bar1_sh_wready,
                                                                                                                               
   //Write response                                                                                                            
   output logic bar1_sh_bvalid,
   output logic[1:0] bar1_sh_bresp,
   input sh_bar1_bready,
                                                                                                                               
   //Read address                                                                                                              
   input sh_bar1_arvalid,
   input[31:0] sh_bar1_araddr,
   output logic bar1_sh_arready,
                                                                                                                               
   //Read data/response                                                                                                        
   output logic bar1_sh_rvalid,
   output logic[31:0] bar1_sh_rdata,
   output logic[1:0] bar1_sh_rresp,
                                                                                                                               
   input sh_bar1_rready           


`ifdef HMC_PRESENT
   //-----------------------------------------------------------------
   // HMC Interface
   //-----------------------------------------------------------------
   ,
   input                       dev01_refclk_p ,
   input                       dev01_refclk_n ,
   input                       dev23_refclk_p ,
   input                       dev23_refclk_n ,
                               
                               /* HMC0 interface */ 
   output wire                 hmc0_dev_p_rst_n ,
   input wire                  hmc0_rxps ,
   output wire                 hmc0_txps ,
   output wire [7 : 0]         hmc0_txp ,
   output wire [7 : 0]         hmc0_txn ,
   input wire [7 : 0]          hmc0_rxp ,
   input wire [7 : 0]          hmc0_rxn ,
                               /* HMC1 interface */ 
   output wire                 hmc1_dev_p_rst_n ,
   input wire                  hmc1_rxps ,
   output wire                 hmc1_txps ,
   output wire [7 : 0]         hmc1_txp ,
   output wire [7 : 0]         hmc1_txn ,
   input wire [7 : 0]          hmc1_rxp ,
   input wire [7 : 0]          hmc1_rxn ,
                               /* HMC2 interface */ 
   output wire                 hmc2_dev_p_rst_n ,
   input wire                  hmc2_rxps ,
   output wire                 hmc2_txps ,
   output wire [7 : 0]         hmc2_txp ,
   output wire [7 : 0]         hmc2_txn ,
   input wire [7 : 0]          hmc2_rxp ,
   input wire [7 : 0]          hmc2_rxn ,
                               /* HMC3 interface */ 
   output wire                 hmc3_dev_p_rst_n ,
   input wire                  hmc3_rxps ,
   output wire                 hmc3_txps ,
   output wire [7 : 0]         hmc3_txp ,
   output wire [7 : 0]         hmc3_txn ,
   input wire [7 : 0]          hmc3_rxp ,
   input wire [7 : 0]          hmc3_rxn

   ,
   input                      hmc_iic_scl_i,
   output logic               hmc_iic_scl_o,
   output logic               hmc_iic_scl_t,
   input                      hmc_iic_sda_i,
   output logic               hmc_iic_sda_o,
   output logic               hmc_iic_sda_t,

   input[7:0]                 sh_hmc_stat_addr,
   input                      sh_hmc_stat_wr,
   input                      sh_hmc_stat_rd,
   input[31:0]                sh_hmc_stat_wdata,

   output logic               hmc_sh_stat_ack,
   output logic [31:0]        hmc_sh_stat_rdata,

   output logic[7:0]          hmc_sh_stat_int

`endif


   //-------------------------------------------------------------------------------------
   // Serial GTY interface
   //    AXI-Stream interface to send/receive packets to/from Serial interfaces.
   //    This interface TBD.
   //-------------------------------------------------------------------------------------
   //
   //------------------------------------------------------
   // Aurora Interface from CL (AXI-S)
   //------------------------------------------------------
`ifdef AURORA
    ,
   //-------------------------------
   // GTY
   //-------------------------------
   output [NUM_GTY-1:0]        cl_sh_aurora_channel_up,
   input [NUM_GTY-1:0]         gty_refclk_p,
   input [NUM_GTY-1:0]         gty_refclk_n,
   
   input [(NUM_GTY*4)-1:0]     gty_txp,
   input [(NUM_GTY*4)-1:0]     gty_txn,

   input [(NUM_GTY*4)-1:0]     gty_rxp,
   input [(NUM_GTY*4)-1:0]     gty_rxn

   ,
   input [7:0] sh_aurora_stat_addr,
   input sh_aurora_stat_wr, 
   input sh_aurora_stat_rd, 
   input [31:0] sh_aurora_stat_wdata, 
   output logic aurora_sh_stat_ack,
   output logic[31:0] aurora_sh_stat_rdata,
   output logic[7:0] aurora_sh_stat_int
`endif //  `ifdef AURORA

   //--------------------------------
   // Debug bridge
   //--------------------------------
`ifndef DISABLE_CHIPSCOPE_DEBUG
   ,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN drck" *) (* DEBUG="true" *)   
   input drck,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN shift" *) (* DEBUG="true" *)
   input shift,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN tdi" *) (* DEBUG="true" *)      
   input tdi,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN update" *) (* DEBUG="true" *)   
   input update,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN sel" *) (* DEBUG="true" *)      
   input sel,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN tdo" *) (* DEBUG="true" *)      
   output logic tdo,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN tms" *) (* DEBUG="true" *)   
   input tms,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN tck" *) (* DEBUG="true" *)
   input tck,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN runtest" *)
   input runtest,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN reset" *) (* DEBUG="true" *)  
   input reset,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN capture" *) (* DEBUG="true" *)    
   input capture,
(* X_INTERFACE_INFO = "xilinx.com:interface:bscan:1.0 S_BSCAN bscanid" *) (* DEBUG="true" *) 
   input bscanid_en
`endif

   ,
   input[63:0] sh_cl_glcount0,                  //Global counter 0
   input[63:0] sh_cl_glcount1                   //Global counter 1





