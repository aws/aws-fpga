`timescale 1ps/1ps

`include "uvm_macros.svh"

// Test module
module testbench;

  parameter NUM_DDR = 1;
   
  import uvm_pkg::*;

  // Import the DDVAPI CDN_AXI SV interface and the generic Mem interface
  import DenaliSvCdn_axi::*;
  import DenaliSvMem::*; 

  // Import the VIP UVM base classes
  import cdnAxiUvm::*;  

  // Import the example environment reusable files
  import axi4UvmUser::*;

  // Includes the Test library
  `include "axi4UvmUserTests.sv"

  reg aclk;
  reg aresetn;

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   wire [5:0]          cl_hl_ddr_awid[NUM_DDR-1:0];
   wire [63:0]         cl_hl_ddr_awaddr[NUM_DDR-1:0];
   wire [7:0]          cl_hl_ddr_awlen[NUM_DDR-1:0];
   //wire[10:0] cl_hl_ddr_awuser[NUM_DDR-1:0];
   wire                cl_hl_ddr_awvalid[NUM_DDR-1:0];
   wire                logic[NUM_DDR-1:0] hl_cl_ddr_awready;

   wire [5:0]          cl_hl_ddr_wid[NUM_DDR-1:0];
   wire [511:0]        cl_hl_ddr_wdata[NUM_DDR-1:0];
   wire [63:0]         cl_hl_ddr_wstrb[NUM_DDR-1:0];
   wire [NUM_DDR-1:0]  cl_hl_ddr_wlast;
   wire [NUM_DDR-1:0]  cl_hl_ddr_wvalid;
   wire [NUM_DDR-1:0]  hl_cl_ddr_wready;
   

   wire [5:0]          hl_cl_ddr_bid[NUM_DDR-1:0];
   wire [1:0]          hl_cl_ddr_bresp[NUM_DDR-1:0];
   wire [NUM_DDR-1:0]  hl_cl_ddr_bvalid;
   wire [NUM_DDR-1:0]  cl_hl_ddr_bready;
   

   wire [5:0]          cl_hl_ddr_arid[NUM_DDR-1:0];
   wire [63:0]         cl_hl_ddr_araddr[NUM_DDR-1:0];
   wire [7:0]          cl_hl_ddr_arlen[NUM_DDR-1:0];
   
   wire [NUM_DDR-1:0]  cl_hl_ddr_arvalid;
   wire [NUM_DDR-1:0]  hl_cl_ddr_arready;
   
   wire [5:0]         hl_cl_ddr_rid[NUM_DDR-1:0];
   wire [511:0]       hl_cl_ddr_rdata[NUM_DDR-1:0];
   wire [1:0]         hl_cl_ddr_rresp[NUM_DDR-1:0];
   wire [NUM_DDR-1:0] hl_cl_ddr_rlast;
   wire [NUM_DDR-1:0] hl_cl_ddr_rvalid;
   wire [NUM_DDR-1:0] cl_hl_ddr_rready;
   wire [NUM_DDR-1:0] hl_cl_ddr_is_ready;

  cdnAxi4Interface#(.ID_WIDTH(6), .ADDR_WIDTH(64), .DATA_WIDTH(512)) userDutInterface (aclk,aresetn);  
 
   assign cl_hl_ddr_awid[0]        = userDutInterface.awid;
   assign cl_hl_ddr_awaddr[0]      = userDutInterface.awaddr;
   assign cl_hl_ddr_awlen[0]       = userDutInterface.awlen;
   assign cl_hl_ddr_awvalid[0]     = userDutInterface.awvalid;
   assign userDutInterface.awready = hl_cl_ddr_awready; 

   assign cl_hl_ddr_wdata[0]   = userDutInterface.wdata;
   assign cl_hl_ddr_wstrb[0]   = userDutInterface.wstrb;
   assign cl_hl_ddr_wlast      = userDutInterface.wlast;
   assign cl_hl_ddr_wvalid     = userDutInterface.wvalid;
   assign userDutInterface.wready        = hl_cl_ddr_wready;

   assign userDutInterface.bid           = hl_cl_ddr_bid[0];
   assign userDutInterface.bresp         = hl_cl_ddr_bresp[0];
   assign userDutInterface.bvalid        = hl_cl_ddr_bvalid;
   assign cl_hl_ddr_bready     = userDutInterface.bready;

   assign cl_hl_ddr_arid[0]    = userDutInterface.arid;
   assign cl_hl_ddr_araddr[0]  = userDutInterface.araddr;
   assign cl_hl_ddr_arlen[0]   = userDutInterface.arlen;
   assign cl_hl_ddr_arvalid[0] = userDutInterface.arvalid;
   assign userDutInterface.arready       = hl_cl_ddr_arready;

   assign userDutInterface.rid           = hl_cl_ddr_rid[0];
   assign userDutInterface.rdata         = hl_cl_ddr_rdata[0];
   assign userDutInterface.rresp         = hl_cl_ddr_rresp[0];
   assign userDutInterface.rlast         = hl_cl_ddr_rlast;
   assign userDutInterface.rvalid        = hl_cl_ddr_rvalid;
   
   assign cl_hl_ddr_rready     = userDutInterface.rready;

  //Toggling the clock
  always #50 aclk = ~aclk;

  //Controlling the reset
  initial
  begin
    aclk = 1'b1;
    aresetn = 1'b1;
    #100;
    aresetn = 1'b0;   
    #5000;
    aresetn = 1'b1;
  end
  
  //setting the virtual interface to the sve and starting uvm.
  initial
  begin    
    uvm_config_db#(virtual interface cdnAxi4Interface#(.ID_WIDTH(6), .ADDR_WIDTH(64), .DATA_WIDTH(512)))::set(null,"*", "vif", userDutInterface);
    run_test(); 
  end    

   initial begin
      if (!$test$plusargs("NO_WAVES")) begin
         $vcdpluson;
         $vcdplusmemon;
      end
   end

hl_ddr #( .NUM_DDR(1)) dut
   (

   //---------------------------
   // Main clock/reset
   //---------------------------
   .clk(aclk),
   .rst_n(aresetn),

   //--------------------------
   // DDR Physical Interface
   //--------------------------

// ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
    .CLK_300M_DIMM0_DP(),
    .CLK_300M_DIMM0_DN(),
    .M_A_ACT_N(),
    .M_A_MA(),
    .M_A_BA(),
    .M_A_BG(),
    .M_A_CKE(),
    .M_A_ODT(),
    .M_A_CS_N(),
    .M_A_CLK_DN(),
    .M_A_CLK_DP(),
    .RST_DIMM_A_N(),
    .M_A_PAR(),
    .M_A_DQ(),
    .M_A_ECC(),
    .M_A_DQS_DP(),
    .M_A_DQS_DN(),

// ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
    .CLK_300M_DIMM1_DP(),
    .CLK_300M_DIMM1_DN(),
    .M_B_ACT_N(),
    .M_B_MA(),
    .M_B_BA(),
    .M_B_BG(),
    .M_B_CKE(),
    .M_B_ODT(),
    .M_B_CS_N(),
    .M_B_CLK_DN(),
    .M_B_CLK_DP(),
    .RST_DIMM_B_N(),
    .M_B_PAR(),
    .M_B_DQ(),
    .M_B_ECC(),
    .M_B_DQS_DP(),
    .M_B_DQS_DN(),

// ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
    .CLK_300M_DIMM2_DP(),
    .CLK_300M_DIMM2_DN(),
    .M_C_ACT_N(),
    .M_C_MA(),
    .M_C_BA(),
    .M_C_BG(),
    .M_C_CKE(),
    .M_C_ODT(),
    .M_C_CS_N(),
    .M_C_CLK_DN(),
    .M_C_CLK_DP(),
    .RST_DIMM_C_N(),
    .M_C_PAR(),
    .M_C_DQ(),
    .M_C_ECC(),
    .M_C_DQS_DP(),
    .M_C_DQS_DN(),

// ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
    .CLK_300M_DIMM3_DP(),
    .CLK_300M_DIMM3_DN(),
    .M_D_ACT_N(),
    .M_D_MA(),
    .M_D_BA(),
    .M_D_BG(),
    .M_D_CKE(),
    .M_D_ODT(),
    .M_D_CS_N(),
    .M_D_CLK_DN(),
    .M_D_CLK_DP(),
    .RST_DIMM_D_N(),
    .M_D_PAR(),
    .M_D_DQ(),
    .M_D_ECC(),
    .M_D_DQS_DP(),
    .M_D_DQS_DN(),


   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_hl_ddr_awid(cl_hl_ddr_awid),
   .cl_hl_ddr_awaddr(cl_hl_ddr_awaddr),
   .cl_hl_ddr_awlen(cl_hl_ddr_awlen),
   .cl_hl_ddr_awvalid(cl_hl_ddr_awvalid),
   .hl_cl_ddr_awready(hl_cl_ddr_awready),

   .cl_hl_ddr_wdata(cl_hl_ddr_wdata),
   .cl_hl_ddr_wstrb(cl_hl_ddr_wstrb),
   .cl_hl_ddr_wlast(cl_hl_ddr_wlast),
   .cl_hl_ddr_wvalid(cl_hl_ddr_wvalid),
   .hl_cl_ddr_wready(hl_cl_ddr_wready),

   .hl_cl_ddr_bid(hl_cl_ddr_bid),
   .hl_cl_ddr_bresp(hl_cl_ddr_bresp),
   .hl_cl_ddr_bvalid(hl_cl_ddr_bvalid),
   .cl_hl_ddr_bready(cl_hl_ddr_bready),
  
   .cl_hl_ddr_arid(cl_hl_ddr_arid),
   .cl_hl_ddr_araddr(cl_hl_ddr_araddr),
   .cl_hl_ddr_arlen(cl_hl_ddr_arlen),

   .cl_hl_ddr_arvalid(cl_hl_ddr_arvalid),
   .hl_cl_ddr_arready(hl_cl_ddr_arready),

   .hl_cl_ddr_rid(hl_cl_ddr_rid),
   .hl_cl_ddr_rdata(hl_cl_ddr_rdata),
   .hl_cl_ddr_rresp(hl_cl_ddr_rresp),
   .hl_cl_ddr_rlast(hl_cl_ddr_rlast),
   .hl_cl_ddr_rvalid(hl_cl_ddr_rvalid),
   .cl_hl_ddr_rready(cl_hl_ddr_rready),

   .hl_cl_ddr_is_ready(),

   .hl_ddr_stat_addr(),       // input [31:0]
   .hl_ddr_stat_wr(1'b0),     // input
   .hl_ddr_stat_rd(1'b0),     // input
   .hl_ddr_stat_wdata(),      // input [31:0]
   .hl_ddr_stat_sel(2'b00),   // input [1:0]
                                                         
   .ddr_hl_stat_ack(),        // output
   .ddr_hl_stat_rdata()       // output [31:0]
   );

endmodule
