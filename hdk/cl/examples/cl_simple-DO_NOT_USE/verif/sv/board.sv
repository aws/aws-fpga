// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`include "board_common.vh"

`define SIMULATION

`ifdef XILINX_SIMULATOR
module short(in1, in1);
inout in1;
endmodule
`endif

`timescale 1ns/1ps

   task automatic sys_init(ref int err_cnt);
      tb.RP.tx_usrapp.sys_init(err_cnt);
   endtask // sys_init

module tb;


      `define PCI_PATH TOP.SH
      `define AURORA_PATH TOP.CL

   semaphore pcie_access;

localparam[2:0] PF0_DEV_CAP_MAX_PAYLOAD_SIZE = 3'h2;

  localparam EXT_PIPE_SIM = "TRUE";
   defparam tb.RP.EXT_PIPE_SIM = "TRUE";
   defparam tb.RP.pcie_4_0_rport.pcie_4_0_int_inst.EXT_PIPE_SIM = "TRUE";

   `ifndef NO_XDMA
      defparam `PCI_PATH.pci_inst[0].genblk1.XDMA.inst.pcie4_ip_i.inst.PL_SIM_FAST_LINK_TRAINING=2'h3;
   `else
      defparam `PCI_PATH.pci_inst[0].genblk1.PCIE_CORE_0.inst.PL_SIM_FAST_LINK_TRAINING=2'h3;
   `endif


 `ifndef NO_XDMA
   defparam `PCI_PATH.pci_inst[0].genblk1.XDMA.inst.pcie4_ip_i.inst.EXT_PIPE_SIM = "TRUE";
 `else
   defparam `PCI_PATH.pci_inst[0].genblk1.PCIE_CORE_0.inst.EXT_PIPE_SIM = "TRUE";
 `endif


localparam ADDR_WIDTH                    = 17;
  localparam DQ_WIDTH                      = 72;
  localparam DQS_WIDTH                     = 18;
  localparam DM_WIDTH                      = 9;
  localparam DRAM_WIDTH                    = 4;
  localparam tCK                           = 952 ; //DDR4 interface clock period in ps
  localparam real SYSCLK_PERIOD            = tCK;
  localparam NUM_PHYSICAL_PARTS = (DQ_WIDTH/DRAM_WIDTH) ;
  parameter RANK_WIDTH                       = 1;
  parameter CS_WIDTH                       = 1;
  parameter ODT_WIDTH                      = 1;
  parameter CA_MIRROR                      = "OFF";

  localparam MRS                           = 3'b000;
  localparam REF                           = 3'b001;
  localparam PRE                           = 3'b010;
  localparam ACT                           = 3'b011;
  localparam WR                            = 3'b100;
  localparam RD                            = 3'b101;
  localparam ZQC                           = 3'b110;
  localparam NOP                           = 3'b111;
  //Added to support RDIMM wrapper
  localparam ODT_WIDTH_RDIMM   = 1;
  localparam CKE_WIDTH_RDIMM   = 1;
  localparam CS_WIDTH_RDIMM   = 1;
  localparam RANK_WIDTH_RDIMM   = 1;
  localparam RDIMM_SLOTS   = 4;
  localparam BANK_WIDTH_RDIMM = 2;
  localparam BANK_GROUP_WIDTH_RDIMM     = 2;

    localparam DM_DBI                        = "NONE";
  localparam DM_WIDTH_RDIMM                  = 18;
 localparam MEM_PART_WIDTH       = "x4";
  localparam REG_CTRL             = "ON";



  parameter         BIT_FILE          = "demo_st2_bitfile.bin";

//HMC parameters
parameter HMC_VER         = 1 ;
parameter N_FLIT          = 3 ;
parameter FULL_WIDTH      = 0 ;
parameter GT_USE_GTH      = 1 ;
parameter GTH_SPEED       = 15 ;
parameter GT_REFCLK_FREQ  = 125 ;
parameter DEV_CUB_ID      = 3'b000;
parameter DEV_INIT_TOKEN  = 219;
parameter HMCC_INIT_TOKEN = 512;
parameter  GTCLK_PERIOD = 8.0;





  // System-level clock and reset
  reg                 sys_rst_n;

  logic               ep_sys_clk_p;
  logic               ep_sys_clk_n;
  logic               rp_sys_clk_p;
  logic               rp_sys_clk_n;
  logic               hmc_gtclk;

  //
  // PCI-Express Serial Interconnect
  //

   localparam PCIE_TX_SIGS_WIDTH = 70;
   localparam PCIE_RX_SIGS_WIDTH = 84;

  // Xilinx Pipe Interface
wire [16:0] common_commands_out;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx0_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx1_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx2_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx3_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx4_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx5_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx6_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx7_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx8_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx9_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx10_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx11_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx12_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx13_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx14_sigs_ep;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx15_sigs_ep;

  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx0_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx1_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx2_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx3_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx4_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx5_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx6_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx7_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx8_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx9_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx10_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx11_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx12_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx13_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx14_sigs_ep;
  wire  [PCIE_RX_SIGS_WIDTH-1:0]  xil_rx15_sigs_ep;



  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx0_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx1_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx2_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx3_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx4_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx5_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx6_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx7_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx8_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx9_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx10_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx11_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx12_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx13_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx14_sigs_rp;
  wire  [PCIE_TX_SIGS_WIDTH-1:0]  xil_tx15_sigs_rp;

   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_act_n;
   wire [16:0]                 c0_ddr4_adr[(RDIMM_SLOTS - 1):0];
   wire [1:0]                  c0_ddr4_ba[(RDIMM_SLOTS - 1):0];
   wire [1:0]                  c0_ddr4_bg[(RDIMM_SLOTS - 1):0];
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_cke;
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_odt;
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_cs_n;
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_ck_t_int;
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_ck_c_int;
   wire                        c0_ddr4_ck_t[(RDIMM_SLOTS - 1):0];
   wire                        c0_ddr4_ck_c[(RDIMM_SLOTS - 1):0];
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_reset_n;
   wire [(RDIMM_SLOTS - 1):0]  c0_ddr4_parity;
   wire [3:0]                  c0_ddr4_dm_dbi_n[(RDIMM_SLOTS - 1):0];
   wire [71:0]                 c0_ddr4_dq[(RDIMM_SLOTS - 1):0];
   wire [17:0]                 c0_ddr4_dqs_c[(RDIMM_SLOTS - 1):0];
   wire [17:0]                 c0_ddr4_dqs_t[(RDIMM_SLOTS - 1):0];
   wire                        c0_init_calib_complete[(RDIMM_SLOTS - 1):0];
   wire                        c0_data_compare_error[(RDIMM_SLOTS - 1):0];
   wire [(RDIMM_SLOTS-1):0]  ddr_ck_t;
   wire [(RDIMM_SLOTS-1):0]  ddr_ck_c;

logic[7:0] hmc_l2txp[3:0];
logic[7:0] hmc_l2txn[3:0];
logic[7:0] hmc_l2rxp[3:0];
logic[7:0] hmc_l2rxn[3:0];
logic[3:0] hmc_l2rxps;
logic[3:0] hmc_l2txps;
logic[3:0] hmc_refclk_sel;
logic[3:0] hmc_ferr_n;
logic[3:0] hmc_rst_n;

logic spi_clk;
logic spi_miso;
logic spi_mosi;
logic spi_sel_n;

//------------------------------------------------------------------------------//
// Create semaphore for PCIe access
//------------------------------------------------------------------------------//
initial
begin
   pcie_access = new(1);
end

//------------------------------------------------------------------------------//
// Gen clocks
//------------------------------------------------------------------------------//
initial
begin
   rp_sys_clk_p = 1;
   ep_sys_clk_p = 1;
end

always #5 rp_sys_clk_p = ~rp_sys_clk_p;
always #5 ep_sys_clk_p = ~ep_sys_clk_p;

assign rp_sys_clk_n = ~rp_sys_clk_p;
assign ep_sys_clk_n = ~ep_sys_clk_p;

initial begin
  hmc_gtclk = 0;
  forever #(GTCLK_PERIOD/2) hmc_gtclk = ~hmc_gtclk;
end


  //------------------------------------------------------------------------------//
  // Generate DDR clock
  //------------------------------------------------------------------------------//
   reg ddr_clk_p_gen;
   reg ddr_clk_n_gen;

   logic[3:0] ddr_clk_p;
   logic[3:0] ddr_clk_n;

//Bittware has a 100MHz DDR reference clock

initial
begin
   ddr_clk_p_gen = 1;
end

`ifdef BITTWARE
   always #5 ddr_clk_p_gen = ~ddr_clk_p_gen;
`else
   always #1.666 ddr_clk_p_gen = ~ddr_clk_p_gen;
`endif

assign ddr_clk_n_gen = ~ddr_clk_p_gen;

assign ddr_clk_p = {4{ddr_clk_p_gen}};
assign ddr_clk_n = {4{ddr_clk_n_gen}};

  //------------------------------------------------------------------------------//
  // Generate XTRA clock
  //------------------------------------------------------------------------------//
   reg xtra_clk_p_gen;
   reg xtra_clk_n_gen;

   logic xtra_clk_p;
   logic xtra_clk_n;

initial
begin
   xtra_clk_p_gen = 1;
end

   always #4 xtra_clk_p_gen = ~xtra_clk_p_gen;

assign xtra_clk_n_gen = ~xtra_clk_p_gen;

assign xtra_clk_p = xtra_clk_p_gen;
assign xtra_clk_n = xtra_clk_n_gen;


  //------------------------------------------------------------------------------//
  // Generate QSFP clock
  //------------------------------------------------------------------------------//
   reg qsfp_clk_p_gen;
   reg qsfp_clk_n_gen;

   logic[3:0] qsfp_clk_p;
   logic[3:0] qsfp_clk_n;

   logic [3:0] qsfp_rxp[3:0];
   logic [3:0] qsfp_rxn[3:0];
   logic [3:0] qsfp_txp[3:0];
   logic [3:0] qsfp_txn[3:0];

initial
begin
   qsfp_clk_p_gen = 1;
end

   always #3.086 qsfp_clk_p_gen = ~qsfp_clk_p_gen;

assign qsfp_clk_n_gen = ~qsfp_clk_p_gen;

assign qsfp_clk_p = {4{qsfp_clk_p_gen}};
assign qsfp_clk_n = {4{qsfp_clk_n_gen}};

   // Assigning loopbacks
   assign qsfp_rxp[3:0] = qsfp_txp[3:0];
   assign qsfp_rxn[3:0] = qsfp_txn[3:0];

//------------------------------------------------------------------------------//
// Generate reset
//------------------------------------------------------------------------------//
initial begin
//   sys_rst_n <= 1'b1;
//   repeat(10) @(posedge rp_sys_clk_p);
   $display("[%t] : Asserting system reset", $realtime);
   sys_rst_n <= 1'b0;
   repeat (500) @(posedge rp_sys_clk_p);
   $display("[%t] : Deasserting sytem reset", $realtime);
   sys_rst_n <= 1'b1;
end


//---------------------
// DUT
//---------------------

      top #(.NUM_DDR(4)) TOP(


     .P3E_TXC_P(),
     .P3E_TXC_N(),
     .P3E_RXC_P(),
     .P3E_RXC_N(),
     .CLK_100M_PCIE0_DP(ep_sys_clk_p),
     .CLK_100M_PCIE0_DN(ep_sys_clk_n),
     .RST_FPGA_LS_N(sys_rst_n),

     .CLK_125MHZ_P (xtra_clk_p),
     .CLK_125MHZ_N (xtra_clk_n)

`ifdef I2C_SPI
,
   //---------------------
   // SPI Slave Interface
   //---------------------
   .SPI_UCTRL_SCK(spi_clk),
   .SPI_UCTRL_MISO(spi_miso),
   .SPI_UCTRL_MOSI(spi_mosi),
   .SPI_UCTRL_CS_N(spi_sel_n),
   .FPGA_UCTRL_GPIO0()
`endif //  `ifdef I2C_SPI

`ifndef NO_CL_DDR
         ,
        //----------------------------------
        // DDR4 x72 RDIMM 2100 Interface A
        //----------------------------------
        .CLK_300M_DIMM0_DP (ddr_clk_p[0]),
        .CLK_300M_DIMM0_DN (ddr_clk_n[0]),
        .M_A_ACT_N         (c0_ddr4_act_n[0]),
        .M_A_MA            (c0_ddr4_adr[0]),
        .M_A_BA            (c0_ddr4_ba[0]),
        .M_A_BG            (c0_ddr4_bg[0]),
        .M_A_CKE           (c0_ddr4_cke[0]),
        .M_A_ODT           (c0_ddr4_odt[0]),
        .M_A_CS_N          (c0_ddr4_cs_n[0]),
        .M_A_CLK_DN        (ddr_ck_c[0]),
        .M_A_CLK_DP        (ddr_ck_t[0]),
           .RST_DIMM_A_N      (),
           .sh_RST_DIMM_A_N   (c0_ddr4_reset_n[0]),
        .M_A_PAR           (c0_ddr4_parity[0]),
        .M_A_DQ            (c0_ddr4_dq[0][63:0]), // DEBUG: Is this right?
        .M_A_ECC           (c0_ddr4_dq[0][71:64]), // DEBUG: Is this right?
        .M_A_DQS_DP        (c0_ddr4_dqs_t[0]),
        .M_A_DQS_DN        (c0_ddr4_dqs_c[0])
// DEBUG: No port for c0_ddr4_dm_dbi_n signal?

        //----------------------------------
        // DDR4 x72 RDIMM 2100 Interface B
        //----------------------------------
         ,
        .CLK_300M_DIMM1_DP (ddr_clk_p[1]),
        .CLK_300M_DIMM1_DN (ddr_clk_n[1]),
        .M_B_ACT_N         (c0_ddr4_act_n[1]),
        .M_B_MA            (c0_ddr4_adr[1]),
        .M_B_BA            (c0_ddr4_ba[1]),
        .M_B_BG            (c0_ddr4_bg[1]),
        .M_B_CKE           (c0_ddr4_cke[1]),
        .M_B_ODT           (c0_ddr4_odt[1]),
        .M_B_CS_N          (c0_ddr4_cs_n[1]),
        .M_B_CLK_DN        (ddr_ck_c[1]),
        .M_B_CLK_DP        (ddr_ck_t[1]),
           .RST_DIMM_B_N      (),
           .sh_RST_DIMM_B_N   (c0_ddr4_reset_n[1]),
        .M_B_PAR           (c0_ddr4_parity[1]),
        .M_B_DQ            (c0_ddr4_dq[1][63:0]), // DEBUG: Is this right?
        .M_B_ECC           (c0_ddr4_dq[1][71:64]), // DEBUG: Is this right?
        .M_B_DQS_DP        (c0_ddr4_dqs_t[1]),
        .M_B_DQS_DN        (c0_ddr4_dqs_c[1])
`endif //  `ifndef NO_CL_DDR

        //----------------------------------
        // DDR4 x72 RDIMM 2100 Interface C
        //----------------------------------
        ,
        .CLK_300M_DIMM2_DP (ddr_clk_p[2]),
        .CLK_300M_DIMM2_DN (ddr_clk_n[2]),
        .M_C_ACT_N         (c0_ddr4_act_n[2]),
        .M_C_MA            (c0_ddr4_adr[2]),
        .M_C_BA            (c0_ddr4_ba[2]),
        .M_C_BG            (c0_ddr4_bg[2]),
        .M_C_CKE           (c0_ddr4_cke[2]),
        .M_C_ODT           (c0_ddr4_odt[2]),
        .M_C_CS_N          (c0_ddr4_cs_n[2]),
        .M_C_CLK_DN        (ddr_ck_c[2]),
        .M_C_CLK_DP        (ddr_ck_t[2]),
        .RST_DIMM_C_N      (c0_ddr4_reset_n[2]),
        .M_C_PAR           (c0_ddr4_parity[2]),
        .M_C_DQ            (c0_ddr4_dq[2][63:0]), // DEBUG: Is this right?
        .M_C_ECC           (c0_ddr4_dq[2][71:64]), // DEBUG: Is this right?
        .M_C_DQS_DP        (c0_ddr4_dqs_t[2]),
        .M_C_DQS_DN        (c0_ddr4_dqs_c[2])

`ifndef NO_CL_DDR
        ,
        //----------------------------------
        // DDR4 x72 RDIMM 2100 Interface D
        //----------------------------------
        .CLK_300M_DIMM3_DP (ddr_clk_p[3]),
        .CLK_300M_DIMM3_DN (ddr_clk_n[3]),
        .M_D_ACT_N         (c0_ddr4_act_n[3]),
        .M_D_MA            (c0_ddr4_adr[3]),
        .M_D_BA            (c0_ddr4_ba[3]),
        .M_D_BG            (c0_ddr4_bg[3]),
        .M_D_CKE           (c0_ddr4_cke[3]),
        .M_D_ODT           (c0_ddr4_odt[3]),
        .M_D_CS_N          (c0_ddr4_cs_n[3]),
        .M_D_CLK_DN        (ddr_ck_c[3]),
        .M_D_CLK_DP        (ddr_ck_t[3]),
           .RST_DIMM_D_N      (),
           .sh_RST_DIMM_D_N   (c0_ddr4_reset_n[3]),
        .M_D_PAR           (c0_ddr4_parity[3]),
        .M_D_DQ            (c0_ddr4_dq[3][63:0]), // DEBUG: Is this right?
        .M_D_ECC           (c0_ddr4_dq[3][71:64]), // DEBUG: Is this right?
        .M_D_DQS_DP        (c0_ddr4_dqs_t[3]),
        .M_D_DQS_DN        (c0_ddr4_dqs_c[3])
`endif //  `ifndef NO_CL_DDR





`ifdef I2C_SPI
   ,
   //---------------------
   // I2C Interface
   //---------------------
   .I2C_FPGA_QSFP28_R_SCL (qspf_i2c_scl),
   .I2C_FPGA_QSFP28_R_SDA (qspf_i2c_sda),

    .I2C_FPGA_MEM_R_SCL (mem_i2c_scl),
    .I2C_FPGA_MEM_R_SDA (mem_i2c_sda)

`endif //  `ifdef I2C_SPI






   );


assign `PCI_PATH.pipe_rx_0_sigs[0] = xil_rx0_sigs_ep;
assign `PCI_PATH.pipe_rx_1_sigs[0] = xil_rx1_sigs_ep;
assign `PCI_PATH.pipe_rx_2_sigs[0] = xil_rx2_sigs_ep;
assign `PCI_PATH.pipe_rx_3_sigs[0] = xil_rx3_sigs_ep;
assign `PCI_PATH.pipe_rx_4_sigs[0] = xil_rx4_sigs_ep;
assign `PCI_PATH.pipe_rx_5_sigs[0] = xil_rx5_sigs_ep;
assign `PCI_PATH.pipe_rx_6_sigs[0] = xil_rx6_sigs_ep;
assign `PCI_PATH.pipe_rx_7_sigs[0] = xil_rx7_sigs_ep;
assign `PCI_PATH.pipe_rx_8_sigs[0] = xil_rx8_sigs_ep;
assign `PCI_PATH.pipe_rx_9_sigs[0] = xil_rx9_sigs_ep;
assign `PCI_PATH.pipe_rx_10_sigs[0] = xil_rx10_sigs_ep;
assign `PCI_PATH.pipe_rx_11_sigs[0] = xil_rx11_sigs_ep;
assign `PCI_PATH.pipe_rx_12_sigs[0] = xil_rx12_sigs_ep;
assign `PCI_PATH.pipe_rx_13_sigs[0] = xil_rx13_sigs_ep;
assign `PCI_PATH.pipe_rx_14_sigs[0] = xil_rx14_sigs_ep;
assign `PCI_PATH.pipe_rx_15_sigs[0] = xil_rx15_sigs_ep;

assign `PCI_PATH.common_commands_in[0] = 0;

assign xil_tx0_sigs_ep = `PCI_PATH.pipe_tx_0_sigs[0];
assign xil_tx1_sigs_ep = `PCI_PATH.pipe_tx_1_sigs[0];
assign xil_tx2_sigs_ep = `PCI_PATH.pipe_tx_2_sigs[0];
assign xil_tx3_sigs_ep = `PCI_PATH.pipe_tx_3_sigs[0];
assign xil_tx4_sigs_ep = `PCI_PATH.pipe_tx_4_sigs[0];
assign xil_tx5_sigs_ep = `PCI_PATH.pipe_tx_5_sigs[0];
assign xil_tx6_sigs_ep = `PCI_PATH.pipe_tx_6_sigs[0];
assign xil_tx7_sigs_ep = `PCI_PATH.pipe_tx_7_sigs[0];
assign xil_tx8_sigs_ep = `PCI_PATH.pipe_tx_8_sigs[0];
assign xil_tx9_sigs_ep = `PCI_PATH.pipe_tx_9_sigs[0];
assign xil_tx10_sigs_ep = `PCI_PATH.pipe_tx_10_sigs[0];
assign xil_tx11_sigs_ep = `PCI_PATH.pipe_tx_11_sigs[0];
assign xil_tx12_sigs_ep = `PCI_PATH.pipe_tx_12_sigs[0];
assign xil_tx13_sigs_ep = `PCI_PATH.pipe_tx_13_sigs[0];
assign xil_tx14_sigs_ep = `PCI_PATH.pipe_tx_14_sigs[0];
assign xil_tx15_sigs_ep = `PCI_PATH.pipe_tx_15_sigs[0];

assign common_commands_out = `PCI_PATH.common_commands_out[0];

//------------------------------------------------------------------------------//
// RP Model
//------------------------------------------------------------------------------//

  xilinx_pcie4_uscale_rp
  #(
     .BIT_FILE(BIT_FILE),
     .PF0_DEV_CAP_MAX_PAYLOAD_SIZE(PF0_DEV_CAP_MAX_PAYLOAD_SIZE)
     //ONLY FOR RP
  ) RP (
    // SYS Interface
    .sys_clk_n(rp_sys_clk_n),
    .sys_clk_p(rp_sys_clk_p),
    .sys_rst_n(sys_rst_n),

    .pci_exp_txp(),
    .pci_exp_txn(),
    .pci_exp_rxp(),
    .pci_exp_rxn(),

    // Xilinx Pipe Interface
    .common_commands_in ({25'b0,common_commands_out[0]} ), // pipe_clk from EP
    .pipe_rx_0_sigs     ({45'b0,xil_tx0_sigs_ep[38:0]}),
    .pipe_rx_1_sigs     ({45'b0,xil_tx1_sigs_ep[38:0]}),
    .pipe_rx_2_sigs     ({45'b0,xil_tx2_sigs_ep[38:0]}),
    .pipe_rx_3_sigs     ({45'b0,xil_tx3_sigs_ep[38:0]}),
    .pipe_rx_4_sigs     ({45'b0,xil_tx4_sigs_ep[38:0]}),
    .pipe_rx_5_sigs     ({45'b0,xil_tx5_sigs_ep[38:0]}),
    .pipe_rx_6_sigs     ({45'b0,xil_tx6_sigs_ep[38:0]}),
    .pipe_rx_7_sigs     ({45'b0,xil_tx7_sigs_ep[38:0]}),
    .pipe_rx_8_sigs     ({45'b0,xil_tx8_sigs_ep[38:0]}),
    .pipe_rx_9_sigs     ({45'b0,xil_tx9_sigs_ep[38:0]}),
    .pipe_rx_10_sigs     ({45'b0,xil_tx10_sigs_ep[38:0]}),
    .pipe_rx_11_sigs     ({45'b0,xil_tx11_sigs_ep[38:0]}),
    .pipe_rx_12_sigs     ({45'b0,xil_tx12_sigs_ep[38:0]}),
    .pipe_rx_13_sigs     ({45'b0,xil_tx13_sigs_ep[38:0]}),
    .pipe_rx_14_sigs     ({45'b0,xil_tx14_sigs_ep[38:0]}),
    .pipe_rx_15_sigs     ({45'b0,xil_tx15_sigs_ep[38:0]}),
    .common_commands_out(),  
    .pipe_tx_0_sigs     (xil_tx0_sigs_rp),
    .pipe_tx_1_sigs     (xil_tx1_sigs_rp),
    .pipe_tx_2_sigs     (xil_tx2_sigs_rp),
    .pipe_tx_3_sigs     (xil_tx3_sigs_rp),
    .pipe_tx_4_sigs     (xil_tx4_sigs_rp),
    .pipe_tx_5_sigs     (xil_tx5_sigs_rp),
    .pipe_tx_6_sigs     (xil_tx6_sigs_rp),
    .pipe_tx_7_sigs     (xil_tx7_sigs_rp)
    ,
    .pipe_tx_8_sigs     (xil_tx8_sigs_rp),
    .pipe_tx_9_sigs     (xil_tx9_sigs_rp),
    .pipe_tx_10_sigs     (xil_tx10_sigs_rp),
    .pipe_tx_11_sigs     (xil_tx11_sigs_rp),
    .pipe_tx_12_sigs     (xil_tx12_sigs_rp),
    .pipe_tx_13_sigs     (xil_tx13_sigs_rp),
    .pipe_tx_14_sigs     (xil_tx14_sigs_rp),
    .pipe_tx_15_sigs     (xil_tx15_sigs_rp)
  );

     assign xil_rx0_sigs_ep  = {45'b0,xil_tx0_sigs_rp[38:0]};
     assign xil_rx1_sigs_ep  = {45'b0,xil_tx1_sigs_rp[38:0]};
     assign xil_rx2_sigs_ep  = {45'b0,xil_tx2_sigs_rp[38:0]};
     assign xil_rx3_sigs_ep  = {45'b0,xil_tx3_sigs_rp[38:0]};
     assign xil_rx4_sigs_ep  = {45'b0,xil_tx4_sigs_rp[38:0]};
     assign xil_rx5_sigs_ep  = {45'b0,xil_tx5_sigs_rp[38:0]};
     assign xil_rx6_sigs_ep  = {45'b0,xil_tx6_sigs_rp[38:0]};
     assign xil_rx7_sigs_ep  = {45'b0,xil_tx7_sigs_rp[38:0]};
     assign xil_rx8_sigs_ep  = {45'b0,xil_tx8_sigs_rp[38:0]};
     assign xil_rx9_sigs_ep  = {45'b0,xil_tx9_sigs_rp[38:0]};
     assign xil_rx10_sigs_ep  = {45'b0,xil_tx10_sigs_rp[38:0]};
     assign xil_rx11_sigs_ep  = {45'b0,xil_tx11_sigs_rp[38:0]};
     assign xil_rx12_sigs_ep  = {45'b0,xil_tx12_sigs_rp[38:0]};
     assign xil_rx13_sigs_ep  = {45'b0,xil_tx13_sigs_rp[38:0]};
     assign xil_rx14_sigs_ep  = {45'b0,xil_tx14_sigs_rp[38:0]};
     assign xil_rx15_sigs_ep  = {45'b0,xil_tx15_sigs_rp[38:0]};

  //===========================================================================
  //                         Memory Model instantiation
  //===========================================================================

   genvar  rdimm_x;

   generate
      for(rdimm_x=0; rdimm_x<RDIMM_SLOTS; rdimm_x=rdimm_x+1)
        begin: instance_of_rdimm_slots
           ddr4_rdimm_wrapper #(
             .MC_DQ_WIDTH(DQ_WIDTH),
             .MC_DQS_BITS(DQS_WIDTH),
             .MC_DM_WIDTH(DM_WIDTH_RDIMM),
             .MC_CKE_NUM(CKE_WIDTH_RDIMM),
             .MC_ODT_WIDTH(ODT_WIDTH_RDIMM),
             .MC_ABITS(ADDR_WIDTH),
             .MC_BANK_WIDTH(BANK_WIDTH_RDIMM),
             .MC_BANK_GROUP(BANK_GROUP_WIDTH_RDIMM),
             .MC_CS_NUM(CS_WIDTH_RDIMM),
             .MC_RANKS_NUM(RANK_WIDTH_RDIMM),
             .NUM_PHYSICAL_PARTS(NUM_PHYSICAL_PARTS),
             .CALIB_EN("NO"),
             .tCK(tCK),
             .tPDM(),
             .MIN_TOTAL_R2R_DELAY(),
             .MAX_TOTAL_R2R_DELAY(),
             .TOTAL_FBT_DELAY(),
             .MEM_PART_WIDTH(MEM_PART_WIDTH),
             .MC_CA_MIRROR(CA_MIRROR),
            // .SDRAM("DDR4"),
   `ifdef SAMSUNG
             .DDR_SIM_MODEL("SAMSUNG"),

   `else
             .DDR_SIM_MODEL("MICRON"),
   `endif
             .DM_DBI(DM_DBI),
             .MC_REG_CTRL(REG_CTRL),
             .DIMM_MODEL ("RDIMM"),
             .RDIMM_SLOTS (RDIMM_SLOTS)

                               )
           u_ddr4_rdimm_wrapper  (
                                  .ddr4_act_n(c0_ddr4_act_n[rdimm_x]),
                                  .ddr4_addr(c0_ddr4_adr[rdimm_x]),
                                  .ddr4_ba(c0_ddr4_ba[rdimm_x]),
                                  .ddr4_bg(c0_ddr4_bg[rdimm_x]),
                                  .ddr4_par(c0_ddr4_parity[rdimm_x]),
                                  .ddr4_cke(c0_ddr4_cke[rdimm_x]),
                                  .ddr4_odt(c0_ddr4_odt[rdimm_x]),
                                  .ddr4_cs_n(c0_ddr4_cs_n[rdimm_x]),
                                  .ddr4_ck_t(ddr_ck_t[rdimm_x]),
                                  .ddr4_ck_c(ddr_ck_c[rdimm_x]),
                                  .ddr4_reset_n(c0_ddr4_reset_n[rdimm_x]),
//AK                                  .ddr4_dm_dbi_n(c0_ddr4_dm_dbi_n[rdimm_x]),
                                  .ddr4_dm_dbi_n(),
                                  .ddr4_dq(c0_ddr4_dq[rdimm_x]),
                                  .ddr4_dqs_t(c0_ddr4_dqs_t[rdimm_x]),
                                  .ddr4_dqs_c(c0_ddr4_dqs_c[rdimm_x]),
                                  .ddr4_alert_n(),
                                  .initDone(),
                                  .scl(),
                                  .sa0(),
                                  .sa1(),
                                  .sa2(),
                                  .sda(),
                                  .bfunc(),
                                  .vddspd());
        end

   endgenerate


//---------------------------
// SPI Master
//---------------------------
uc_spi_model #(.SPI_CLK_PERIOD(10)) UC_SPI_MODEL(
   .rst_n(sys_rst_n),

   .spi_clk(spi_clk),
   .spi_sel_n(spi_sel_n),
   .spi_mosi(spi_mosi),

   .spi_miso(spi_miso)
   );

// End SPI Master
//--------------------------------


`ifdef VCS
initial begin
   if (!$test$plusargs("NO_WAVES")) begin
      $vcdpluson;
      $vcdplusmemon;
   end
end
`endif


     //Simultate the global reset that occurs after configuration at the beginning
     //of the simulation. Note that both GTX swift models use the same global signals.
     assign glbl.GSR = ~sys_rst_n;
     assign glbl.GTS = 1'b0;



`ifdef AURORA_CLOCK_CHECK
// The user clock from Aurora should be up and running automatically.
// But this does not happen sometimes (dont know whats the reason).
// This is to check and save time if the situation happens again.
  int clk_cnt0 = 0;
  int clk_cnt1 = 0;
  int clk_cnt2 = 0;
  int clk_cnt3 = 0;

initial begin
    // Check if the user_clk from aurora core is up and running
 #50us;
  #30us;
  if (clk_cnt0 == 0) begin
     $display ("[%t] : *** ERROR *** Aurora Core 0 USER Clock did not start. Try rerunning the test", $realtime);
     $finish;
  end

  if (clk_cnt1 == 0) begin
     $display ("[%t] : *** ERROR *** Aurora Core 1 USER Clock did not start. Try rerunning the test", $realtime);
     $finish;
  end

  if (clk_cnt2 == 0) begin
     $display ("[%t] : *** ERROR *** Aurora Core 2 USER Clock did not start. Try rerunning the test", $realtime);
     $finish;
  end

  if (clk_cnt3 == 0) begin
     $display ("[%t] : *** ERROR *** Aurora Core 3 USER Clock did not start. Try rerunning the test", $realtime);
     $finish;
  end

end

always @(posedge `AURORA_PATH.AURORA_WRAPPER.aurora_user_clk_out[0])
  clk_cnt0 = 1;
always @(posedge `AURORA_PATH.AURORA_WRAPPER.aurora_user_clk_out[1])
  clk_cnt1 = 1;
always @(posedge `AURORA_PATH.AURORA_WRAPPER.aurora_user_clk_out[2])
  clk_cnt2 = 1;
always @(posedge `AURORA_PATH.AURORA_WRAPPER.aurora_user_clk_out[3])
  clk_cnt3 = 1;

`endif //  `ifdef AURORA_CLOCK_CHECK


endmodule
