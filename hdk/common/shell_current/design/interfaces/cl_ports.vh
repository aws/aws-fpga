   // TODO - put header

// This file includes the entire list of interfaces between AWS shell (sh) and Custom Logic (cl)
// Most signals are "ACTIVE HIGH", i.e. value of 1'b1 means they are true/asserted and value of 1'b0 means they are false/deasserted
// signals with _n suffix are "ACTIVE LOW"

   //--------------------------------
   // Global Signals
   //--------------------------------
   input clk,                                //250MHz clock 
   input rst_n,                              //Reset sync to 250MHz clock

   input clk_xtra,                           // Free running 125MHz clock
   input rst_xtra_n,

   input sh_cl_flr_assert,                   // A signal set when the PCIe Application PF gets Function Level Reset (FLR) 
                                             // from host through PCIe
   output logic cl_sh_flr_done,
         
   output logic[31:0] cl_sh_status0,         // RESERVED FOR FUTURE USE
   output logic[31:0] cl_sh_status1,         // RESERVED FOR FUTURE USE
   output logic[31:0] cl_sh_id0,             // RESERVED FOR FUTURE USE
   output logic[31:0] cl_sh_id1,             // RESERVED FOR FUTURE USE

   input[31:0] sh_cl_ctl0,                   // RESERVED FOR FUTURE USE
   input[31:0] sh_cl_ctl1,                   // RESERVED FOR FUTURE USE

   input[1:0] sh_cl_pwr_state,               //Power state, 2'b00: Normal, 2'b11: Critical
                                             // Developer can ignore these signals

   //------------------------------------------------------------------------------------------
   // PCL Slave interface (AXI-4)
   //    AXI slave interface per PCIe interface.   This is for PCIe transactions
   //    mastered from the Host targetting the CL (MMIO access), or 
   //    PCIe transactions mastered from other FPGAs targeting this CL
   //------------------------------------------------------------------------------------------
   input[63:0] sh_cl_pcis_awaddr[NUM_PCIE-1:0],
   input[4:0] sh_cl_pcis_awid[NUM_PCIE-1:0],
   input[7:0] sh_cl_pcis_awlen[NUM_PCIE-1:0],
   input[NUM_PCIE-1:0] sh_cl_pcis_awvalid,
   output logic[NUM_PCIE-1:0] cl_sh_pcis_awready,
   
   input[511:0] sh_cl_pcis_wdata[NUM_PCIE-1:0],
   input[63:0] sh_cl_pcis_wstrb[NUM_PCIE-1:0],
   input[NUM_PCIE-1:0] sh_cl_pcis_wlast,
   input[NUM_PCIE-1:0] sh_cl_pcis_wvalid,
   output logic[NUM_PCIE-1:0] cl_sh_pcis_wready,
   
   output logic[1:0] cl_sh_pcis_bresp[NUM_PCIE-1:0],
   output logic[4:0] cl_sh_pcis_bid[NUM_PCIE-1:0],
   output logic[NUM_PCIE-1:0] cl_sh_pcis_bvalid,
   input[NUM_PCIE-1:0] sh_cl_pcis_bready,
   
   input[63:0] sh_cl_pcis_araddr[NUM_PCIE-1:0],
   input[4:0] sh_cl_pcis_arid[NUM_PCIE-1:0],
   input[7:0] sh_cl_pcis_arlen[NUM_PCIE-1:0],
   input[NUM_PCIE-1:0] sh_cl_pcis_arvalid,
   output logic[NUM_PCIE-1:0] cl_sh_pcis_arready,
   
   output logic[511:0] cl_sh_pcis_rdata[NUM_PCIE-1:0],
   output logic[1:0] cl_sh_pcis_rresp[NUM_PCIE-1:0],
   output logic[4:0] cl_sh_pcis_rid[NUM_PCIE-1:0],
   output logic[NUM_PCIE-1:0] cl_sh_pcis_rlast,
   output logic[NUM_PCIE-1:0] cl_sh_pcis_rvalid,
   input logic[NUM_PCIE-1:0] sh_cl_pcis_rready,

   //-------------------------------------------------------------------------------------------
   // PCIe Master interface from CL
   //
   //    AXI-4 master interface per PCIe interface.  This is for PCIe transactions mastered
   //    from the CL targetting the host or other FPGAs on the same PCIe Fabric.  
   //    Its a standard AXI-4 interface except that awuser signals is required to pass
   //    the length of the transaction in DW (32-bit) as well as the byte-enable bit-mask for the first 
   //    and last DW. Please refer to AWS Shell Interface specifications
   //-------------------------------------------------------------------------------------------
   output logic[4:0] cl_sh_pcim_awid[NUM_PCIE-1:0],
   output logic[63:0] cl_sh_pcim_awaddr[NUM_PCIE-1:0],
   output logic[7:0] cl_sh_pcim_awlen[NUM_PCIE-1:0],
   output logic[18:0] cl_sh_pcim_awuser[NUM_PCIE-1:0],               //Length in DW of the transaction
   output logic[NUM_PCIE-1:0] cl_sh_pcim_awvalid,
   input[NUM_PCIE-1:0] sh_cl_pcim_awready,
   
//Not used   output logic[4:0] cl_sh_pcim_wid[NUM_PCIE-1:0],
   output logic[511:0] cl_sh_pcim_wdata[NUM_PCIE-1:0],
   output logic[63:0] cl_sh_pcim_wstrb[NUM_PCIE-1:0],
   output logic[NUM_PCIE-1:0] cl_sh_pcim_wlast,
   output logic[NUM_PCIE-1:0] cl_sh_pcim_wvalid,
   input[NUM_PCIE-1:0] sh_cl_pcim_wready,
   
   input logic[4:0] sh_cl_pcim_bid[NUM_PCIE-1:0],
   input logic[1:0] sh_cl_pcim_bresp[NUM_PCIE-1:0],
   input logic[NUM_PCIE-1:0] sh_cl_pcim_bvalid,
   output logic[NUM_PCIE-1:0] cl_sh_pcim_bready,
  
   output logic[4:0] cl_sh_pcim_arid[NUM_PCIE-1:0],
   output logic[63:0] cl_sh_pcim_araddr[NUM_PCIE-1:0],
   output logic[7:0] cl_sh_pcim_arlen[NUM_PCIE-1:0],
   output logic[18:0] cl_sh_pcim_aruser[NUM_PCIE-1:0],               //Length in DW, refer to AWS Shell specification
   output logic[NUM_PCIE-1:0] cl_sh_pcim_arvalid,
   input[NUM_PCIE-1:0] sh_cl_pcim_arready,
   
   input[4:0] sh_cl_pcim_rid[NUM_PCIE-1:0],
   input[511:0] sh_cl_pcim_rdata[NUM_PCIE-1:0],
   input[1:0] sh_cl_pcim_rresp[NUM_PCIE-1:0],
   input[NUM_PCIE-1:0] sh_cl_pcim_rlast,
   input[NUM_PCIE-1:0] sh_cl_pcim_rvalid,
   output logic[NUM_PCIE-1:0] cl_sh_pcim_rready,

   input[1:0] cfg_max_payload[NUM_PCIE-1:0],                      //PCIe Max payload size - 00:128B, 01:256B (Default), 10:512B
   input[2:0] cfg_max_read_req[NUM_PCIE-1:0]                      //PCIe Max read requst size - 000b:128B, 001b:256B, 010b:512B, 011b:1024B
                                                                  // 100b-2048B, 101b:4096B
   
   //-----------------------------------------------------------------------------------------------
   // DDR-4 Interface 
   //
   //  There are 3 DDR controllers that get instantiated in CL (DDR Interface A, B and D).  
   //  The fourth DDR (Interface C) is in shell, due to resource optimization considerations
   //  These are the signals physical I/O interface definition and connects directly to the 
   //  DRAM Controllers (DDRC)
   //-----------------------------------------------------------------------------------------------
`ifndef NO_CL_DDR
  ,
// ------------------- DDR4 x72 RDIMM Interface A ----------------------------------
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
   output               RST_DIMM_A_N,
   output               M_A_PAR,
   inout  [63:0]        M_A_DQ,
   inout  [7:0]         M_A_ECC,
   inout  [17:0]        M_A_DQS_DP,
   inout  [17:0]        M_A_DQS_DN,

// ------------------- DDR4 x72 RDIMM Interface B ----------------------------------
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
   output               RST_DIMM_B_N,
   output               M_B_PAR,
   inout  [63:0]        M_B_DQ,
   inout  [7:0]         M_B_ECC,
   inout  [17:0]        M_B_DQS_DP,
   inout  [17:0]        M_B_DQS_DN,


// ------------------- DDR4 x72 RDIMM Interface D ----------------------------------
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
   output               RST_DIMM_D_N,
   output               M_D_PAR,
   inout  [63:0]        M_D_DQ,
   inout  [7:0]         M_D_ECC,
   inout  [17:0]        M_D_DQS_DP,
   inout  [17:0]        M_D_DQS_DN

`endif

   //-----------------------------------
   // AXI4 Interface for DDRC
   //-----------------------------------
   ,
   input [7:0] sh_ddr_stat_addr[2:0],
   input[2:0] sh_ddr_stat_wr, 
   input[2:0] sh_ddr_stat_rd, 
   input [31:0] sh_ddr_stat_wdata[2:0], 
   output logic[2:0] ddr_sh_stat_ack,
   output logic[31:0] ddr_sh_stat_rdata[2:0],
   output logic[7:0] ddr_sh_stat_int[2:0],

   output [5:0] cl_sh_ddr_awid,
   output [63:0] cl_sh_ddr_awaddr,
   output [7:0] cl_sh_ddr_awlen,
   output  cl_sh_ddr_awvalid,
   input sh_cl_ddr_awready,
      
   output [5:0] cl_sh_ddr_wid,
   output [511:0] cl_sh_ddr_wdata,
   output [63:0] cl_sh_ddr_wstrb,
   output  cl_sh_ddr_wlast,
   output  cl_sh_ddr_wvalid,
   input sh_cl_ddr_wready,
      
   input[5:0] sh_cl_ddr_bid,
   input[1:0] sh_cl_ddr_bresp,
   input sh_cl_ddr_bvalid,
   output  cl_sh_ddr_bready,
      
   output [5:0] cl_sh_ddr_arid,
   output [63:0] cl_sh_ddr_araddr,
   output [7:0] cl_sh_ddr_arlen,
   output  cl_sh_ddr_arvalid,
   input sh_cl_ddr_arready,
      
   input[5:0] sh_cl_ddr_rid,
   input[511:0] sh_cl_ddr_rdata,
   input[1:0] sh_cl_ddr_rresp,
   input sh_cl_ddr_rlast,
   input sh_cl_ddr_rvalid,
   output  cl_sh_ddr_rready,
      
   input sh_cl_ddr_is_ready
                                                                                                    
`ifndef NO_XDMA
    ,
    output logic[15:0] cl_sh_irq_req,
    input [15:0] sh_cl_irq_ack
`else
    
`ifndef VU190    

`ifdef MSIX_PRESENT
   ,
   //-----------------------------------------
   // CL MSIX
   //-----------------------------------------
    output logic         cl_sh_msix_int,
    output logic [7:0]   cl_sh_msix_vec,
    input                sh_cl_msix_int_sent,
    input                sh_cl_msix_int_ack
`endif //  `ifdef MSIX_PRESENT

`endif //  `ifndef VU190
         
`endif // !`ifndef NO_XDMA
    
   // Some FPGA designs may have high-speed Serial HMC memory
   // Please contact AWS if you are interested in using HMC

`ifdef HMC_PRESENT
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
`endif

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
`endif //  `ifdef AURORA

   ,
   input [7:0] sh_aurora_stat_addr,
   input sh_aurora_stat_wr, 
   input sh_aurora_stat_rd, 
   input [31:0] sh_aurora_stat_wdata, 
   output logic aurora_sh_stat_ack,
   output logic[31:0] aurora_sh_stat_rdata,
   output logic[7:0] aurora_sh_stat_int

   //--------------------------------
   // Debug bridge to support chipscope
   //--------------------------------
   `ifdef ENABLE_CHIPSCOPE_DEBUG
   ,
   input clk,
   input drck,
   input shift,
   input tdi,
   input update,
   input sel,
   output logic tdo,
   input tms,
   input tck,
   input runtest,
   input reset,
   input capture,
   output logic[31:0] bscanid
   `endif

   //--------------------------------------------
   // XDMA
   //--------------------------------------------
   `ifndef NO_XDMA

   ,
   //-----------------------------------------------
   // AXI-L interface to access XDMA configuration
   output logic [31:0] cl_sh_xdcfg_awaddr,
   output logic cl_sh_xdcfg_awvalid,
   input sh_cl_xdcfg_awready,
   output logic[31:0] cl_sh_xdcfg_wdata,
   output logic[3:0] cl_sh_xdcfg_wstrb,
   output logic cl_sh_xdcfg_wvalid,
   input sh_cl_xdcfg_wready,
   input sh_cl_xdcfg_bvalid,
   input[1:0] sh_cl_xdcfg_bresp,
   output logic cl_sh_xdcfg_bready,

   output logic[31:0] cl_sh_xdcfg_araddr,
   output logic cl_sh_xdcfg_arvalid,
   input sh_cl_xdcfg_arready,
   input[31:0] sh_cl_xdcfg_rdata,
   input[1:0] sh_cl_xdcfg_rresp,
   input sh_cl_xdcfg_rvalid,
   output logic cl_sh_xdcfg_rready,

   //----------------------------------------------------
   // XDMA AXI-4 interface to master cycles to CL
   input[4:0] sh_cl_xdma_awid,
   input[63:0] sh_cl_xdma_awaddr,
   input[7:0] sh_cl_xdma_awlen,
   input sh_cl_xdma_awvalid,
   output logic cl_sh_xdma_awready,

   input[511:0] sh_cl_xdma_wdata,
   input[63:0] sh_cl_xdma_wstrb,
   input sh_cl_xdma_wlast,
   input sh_cl_xdma_wvalid,
   output logic cl_sh_xdma_wready,

   output logic[4:0] cl_sh_xdma_bid,
   output logic[1:0] cl_sh_xdma_bresp,
   output logic cl_sh_xdma_bvalid,
   input sh_cl_xdma_bready,

   input[4:0] sh_cl_xdma_arid,
   input[63:0] sh_cl_xdma_araddr,
   input[7:0] sh_cl_xdma_arlen,
   input sh_cl_xdma_arvalid,
   output logic cl_sh_xdma_arready,

   output logic[4:0] cl_sh_xdma_rid,
   output logic[511:0] cl_sh_xdma_rdata,
   output logic[1:0] cl_sh_xdma_rresp,
   output logic cl_sh_xdma_rlast,
   output logic cl_sh_xdma_rvalid,
   input sh_cl_xdma_rready

   `endif // NO_XDMA


