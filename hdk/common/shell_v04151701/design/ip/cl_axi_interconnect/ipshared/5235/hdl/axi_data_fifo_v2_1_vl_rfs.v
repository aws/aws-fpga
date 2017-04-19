// -- (c) Copyright 2010 - 2011 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Generic single-channel AXI FIFO
// Synchronous FIFO is implemented using either LUTs (SRL) or BRAM.
// Transfers received on the AXI slave port are pushed onto the FIFO.
// FIFO output, when available, is presented on the AXI master port and
//   popped when the master port responds (M_READY).
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
// Structure:
//   axic_fifo
//     fifo_gen
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_axic_fifo #
  (
   parameter         C_FAMILY          = "virtex6",
   parameter integer C_FIFO_DEPTH_LOG  = 5,      // FIFO depth = 2**C_FIFO_DEPTH_LOG
                                                 // Range = [5:9] when TYPE="lut",
                                                 // Range = [5:12] when TYPE="bram",
   parameter integer C_FIFO_WIDTH      = 64,     // Width of payload [1:512]
   parameter         C_FIFO_TYPE       = "lut"   // "lut" = LUT (SRL) based,
                                                 // "bram" = BRAM based
   )
  (
   // Global inputs
   input  wire                        ACLK,    // Clock
   input  wire                        ARESET,  // Reset
   // Slave  Port
   input  wire [C_FIFO_WIDTH-1:0]     S_MESG,  // Payload (may be any set of channel signals)
   input  wire                        S_VALID, // FIFO push
   output wire                        S_READY, // FIFO not full
   // Master  Port
   output wire [C_FIFO_WIDTH-1:0]     M_MESG,  // Payload
   output wire                        M_VALID, // FIFO not empty
   input  wire                        M_READY  // FIFO pop
   );

   axi_data_fifo_v2_1_11_fifo_gen #(
     .C_FAMILY(C_FAMILY),
     .C_COMMON_CLOCK(1),
     .C_FIFO_DEPTH_LOG(C_FIFO_DEPTH_LOG),
     .C_FIFO_WIDTH(C_FIFO_WIDTH),
     .C_FIFO_TYPE(C_FIFO_TYPE))
   inst (
     .clk(ACLK),
     .rst(ARESET),
     .wr_clk(1'b0),
     .wr_en(S_VALID),
     .wr_ready(S_READY),
     .wr_data(S_MESG),
     .rd_clk(1'b0),
     .rd_en(M_READY),
     .rd_valid(M_VALID),
     .rd_data(M_MESG));

endmodule


// -- (c) Copyright 1995 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------

// The synthesis directives "translate_off/translate_on" specified below are
// supported by Xilinx, Mentor Graphics and Synplicity synthesis
// tools. Ensure they are correct for your synthesis tool(s).

// You must compile the fifo_generator wrapper file when simulating
// the core. When compiling the wrapper file, be sure to
// reference the XilinxCoreLib Verilog simulation library. For detailed
// instructions, please refer to the "CORE Generator Help".

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_fifo_gen #(
parameter C_FAMILY          = "virtex7",
parameter integer C_COMMON_CLOCK    = 1,
parameter integer C_SYNCHRONIZER_STAGE = 3,
parameter integer C_FIFO_DEPTH_LOG  = 5,
parameter integer C_FIFO_WIDTH      = 64,
parameter C_FIFO_TYPE       = "lut"
)(
  clk,
  rst,
  wr_clk,
  wr_en,
  wr_ready,
  wr_data,
  rd_clk,
  rd_en,
  rd_valid,
  rd_data);

input clk;
input wr_clk;
input rd_clk;
input rst;
input [C_FIFO_WIDTH-1 : 0] wr_data;
input wr_en;
input rd_en;
output [C_FIFO_WIDTH-1 : 0] rd_data;
output wr_ready;
output rd_valid;

wire  full;
wire  empty;
wire  rd_valid = ~empty;
wire  wr_ready = ~full;

localparam C_MEMORY_TYPE =  (C_FIFO_TYPE == "bram")? 1 : 2;

localparam C_IMPLEMENTATION_TYPE = (C_COMMON_CLOCK == 1)? 0 : 2;

  fifo_generator_v13_1_4 #(
    .C_COMMON_CLOCK(C_COMMON_CLOCK),
    .C_DIN_WIDTH(C_FIFO_WIDTH),
    .C_DOUT_WIDTH(C_FIFO_WIDTH),
    .C_FAMILY(C_FAMILY),
    .C_IMPLEMENTATION_TYPE(C_IMPLEMENTATION_TYPE),
    .C_MEMORY_TYPE(C_MEMORY_TYPE),
    .C_RD_DEPTH(1<<C_FIFO_DEPTH_LOG),
    .C_RD_PNTR_WIDTH(C_FIFO_DEPTH_LOG),
    .C_WR_DEPTH(1<<C_FIFO_DEPTH_LOG),
    .C_WR_PNTR_WIDTH(C_FIFO_DEPTH_LOG),
    .C_ADD_NGC_CONSTRAINT(0),
    .C_APPLICATION_TYPE_AXIS(0),
    .C_APPLICATION_TYPE_RACH(0),
    .C_APPLICATION_TYPE_RDCH(0),
    .C_APPLICATION_TYPE_WACH(0),
    .C_APPLICATION_TYPE_WDCH(0),
    .C_APPLICATION_TYPE_WRCH(0),
    .C_AXIS_TDATA_WIDTH(64),
    .C_AXIS_TDEST_WIDTH(4),
    .C_AXIS_TID_WIDTH(8),
    .C_AXIS_TKEEP_WIDTH(4),
    .C_AXIS_TSTRB_WIDTH(4),
    .C_AXIS_TUSER_WIDTH(4),
    .C_AXIS_TYPE(0),
    .C_AXI_ADDR_WIDTH(32),
    .C_AXI_ARUSER_WIDTH(1),
    .C_AXI_AWUSER_WIDTH(1),
    .C_AXI_BUSER_WIDTH(1),
    .C_AXI_DATA_WIDTH(64),
    .C_AXI_ID_WIDTH(4),
    .C_AXI_LEN_WIDTH(8),
    .C_AXI_LOCK_WIDTH(2),
    .C_AXI_RUSER_WIDTH(1),
    .C_AXI_TYPE(0),
    .C_AXI_WUSER_WIDTH(1),
    .C_COUNT_TYPE(0),
    .C_DATA_COUNT_WIDTH(6),
    .C_DEFAULT_VALUE("BlankString"),
    .C_DIN_WIDTH_AXIS(1),
    .C_DIN_WIDTH_RACH(32),
    .C_DIN_WIDTH_RDCH(64),
    .C_DIN_WIDTH_WACH(32),
    .C_DIN_WIDTH_WDCH(64),
    .C_DIN_WIDTH_WRCH(2),
    .C_DOUT_RST_VAL("0"),
    .C_ENABLE_RLOCS(0),
    .C_ENABLE_RST_SYNC(1),
    .C_ERROR_INJECTION_TYPE(0),
    .C_ERROR_INJECTION_TYPE_AXIS(0),
    .C_ERROR_INJECTION_TYPE_RACH(0),
    .C_ERROR_INJECTION_TYPE_RDCH(0),
    .C_ERROR_INJECTION_TYPE_WACH(0),
    .C_ERROR_INJECTION_TYPE_WDCH(0),
    .C_ERROR_INJECTION_TYPE_WRCH(0),
    .C_FULL_FLAGS_RST_VAL(0),
    .C_HAS_ALMOST_EMPTY(0),
    .C_HAS_ALMOST_FULL(0),
    .C_HAS_AXIS_TDATA(0),
    .C_HAS_AXIS_TDEST(0),
    .C_HAS_AXIS_TID(0),
    .C_HAS_AXIS_TKEEP(0),
    .C_HAS_AXIS_TLAST(0),
    .C_HAS_AXIS_TREADY(1),
    .C_HAS_AXIS_TSTRB(0),
    .C_HAS_AXIS_TUSER(0),
    .C_HAS_AXI_ARUSER(0),
    .C_HAS_AXI_AWUSER(0),
    .C_HAS_AXI_BUSER(0),
    .C_HAS_AXI_RD_CHANNEL(0),
    .C_HAS_AXI_RUSER(0),
    .C_HAS_AXI_WR_CHANNEL(0),
    .C_HAS_AXI_WUSER(0),
    .C_HAS_BACKUP(0),
    .C_HAS_DATA_COUNT(0),
    .C_HAS_DATA_COUNTS_AXIS(0),
    .C_HAS_DATA_COUNTS_RACH(0),
    .C_HAS_DATA_COUNTS_RDCH(0),
    .C_HAS_DATA_COUNTS_WACH(0),
    .C_HAS_DATA_COUNTS_WDCH(0),
    .C_HAS_DATA_COUNTS_WRCH(0),
    .C_HAS_INT_CLK(0),
    .C_HAS_MASTER_CE(0),
    .C_HAS_MEMINIT_FILE(0),
    .C_HAS_OVERFLOW(0),
    .C_HAS_PROG_FLAGS_AXIS(0),
    .C_HAS_PROG_FLAGS_RACH(0),
    .C_HAS_PROG_FLAGS_RDCH(0),
    .C_HAS_PROG_FLAGS_WACH(0),
    .C_HAS_PROG_FLAGS_WDCH(0),
    .C_HAS_PROG_FLAGS_WRCH(0),
    .C_HAS_RD_DATA_COUNT(0),
    .C_HAS_RD_RST(0),
    .C_HAS_RST(1),
    .C_HAS_SLAVE_CE(0),
    .C_HAS_SRST(0),
    .C_HAS_UNDERFLOW(0),
    .C_HAS_VALID(0),
    .C_HAS_WR_ACK(0),
    .C_HAS_WR_DATA_COUNT(0),
    .C_HAS_WR_RST(0),
    .C_IMPLEMENTATION_TYPE_AXIS(1),
    .C_IMPLEMENTATION_TYPE_RACH(1),
    .C_IMPLEMENTATION_TYPE_RDCH(1),
    .C_IMPLEMENTATION_TYPE_WACH(1),
    .C_IMPLEMENTATION_TYPE_WDCH(1),
    .C_IMPLEMENTATION_TYPE_WRCH(1),
    .C_INIT_WR_PNTR_VAL(0),
    .C_INTERFACE_TYPE(0),
    .C_MIF_FILE_NAME("BlankString"),
    .C_MSGON_VAL(1),
    .C_OPTIMIZATION_MODE(0),
    .C_OVERFLOW_LOW(0),
    .C_PRELOAD_LATENCY(0),
    .C_PRELOAD_REGS(1),
    .C_PRIM_FIFO_TYPE("512x36"),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL(4),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(1022),
    .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(1022),
    .C_PROG_EMPTY_THRESH_NEGATE_VAL(5),
    .C_PROG_EMPTY_TYPE(0),
    .C_PROG_EMPTY_TYPE_AXIS(0),
    .C_PROG_EMPTY_TYPE_RACH(0),
    .C_PROG_EMPTY_TYPE_RDCH(0),
    .C_PROG_EMPTY_TYPE_WACH(0),
    .C_PROG_EMPTY_TYPE_WDCH(0),
    .C_PROG_EMPTY_TYPE_WRCH(0),
    .C_PROG_FULL_THRESH_ASSERT_VAL(31),
    .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(1023),
    .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(1023),
    .C_PROG_FULL_THRESH_NEGATE_VAL(30),
    .C_PROG_FULL_TYPE(0),
    .C_PROG_FULL_TYPE_AXIS(0),
    .C_PROG_FULL_TYPE_RACH(0),
    .C_PROG_FULL_TYPE_RDCH(0),
    .C_PROG_FULL_TYPE_WACH(0),
    .C_PROG_FULL_TYPE_WDCH(0),
    .C_PROG_FULL_TYPE_WRCH(0),
    .C_RACH_TYPE(0),
    .C_RDCH_TYPE(0),
    .C_RD_DATA_COUNT_WIDTH(6),
    .C_RD_FREQ(1),
    .C_REG_SLICE_MODE_AXIS(0),
    .C_REG_SLICE_MODE_RACH(0),
    .C_REG_SLICE_MODE_RDCH(0),
    .C_REG_SLICE_MODE_WACH(0),
    .C_REG_SLICE_MODE_WDCH(0),
    .C_REG_SLICE_MODE_WRCH(0),
    .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
    .C_UNDERFLOW_LOW(0),
    .C_USE_COMMON_OVERFLOW(0),
    .C_USE_COMMON_UNDERFLOW(0),
    .C_USE_DEFAULT_SETTINGS(0),
    .C_USE_DOUT_RST(0),
    .C_USE_ECC(0),
    .C_USE_ECC_AXIS(0),
    .C_USE_ECC_RACH(0),
    .C_USE_ECC_RDCH(0),
    .C_USE_ECC_WACH(0),
    .C_USE_ECC_WDCH(0),
    .C_USE_ECC_WRCH(0),
    .C_USE_EMBEDDED_REG(0),
    .C_USE_FIFO16_FLAGS(0),
    .C_USE_FWFT_DATA_COUNT(1),
    .C_VALID_LOW(0),
    .C_WACH_TYPE(0),
    .C_WDCH_TYPE(0),
    .C_WRCH_TYPE(0),
    .C_WR_ACK_LOW(0),
    .C_WR_DATA_COUNT_WIDTH(6),
    .C_WR_DEPTH_AXIS(1024),
    .C_WR_DEPTH_RACH(16),
    .C_WR_DEPTH_RDCH(1024),
    .C_WR_DEPTH_WACH(16),
    .C_WR_DEPTH_WDCH(1024),
    .C_WR_DEPTH_WRCH(16),
    .C_WR_FREQ(1),
    .C_WR_PNTR_WIDTH_AXIS(10),
    .C_WR_PNTR_WIDTH_RACH(4),
    .C_WR_PNTR_WIDTH_RDCH(10),
    .C_WR_PNTR_WIDTH_WACH(4),
    .C_WR_PNTR_WIDTH_WDCH(10),
    .C_WR_PNTR_WIDTH_WRCH(4),
    .C_WR_RESPONSE_LATENCY(1)
    )
  fifo_gen_inst (
    .clk(clk),
    .din(wr_data),
    .dout(rd_data),
    .empty(empty),
    .full(full),
    .rd_clk(rd_clk),
    .rd_en(rd_en),
    .rst(rst),
    .wr_clk(wr_clk),
    .wr_en(wr_en),
    .almost_empty(),
    .almost_full(),
    .axi_ar_data_count(),
    .axi_ar_dbiterr(),
    .axi_ar_injectdbiterr(1'b0),
    .axi_ar_injectsbiterr(1'b0),
    .axi_ar_overflow(),
    .axi_ar_prog_empty(),
    .axi_ar_prog_empty_thresh(4'b0),
    .axi_ar_prog_full(),
    .axi_ar_prog_full_thresh(4'b0),
    .axi_ar_rd_data_count(),
    .axi_ar_sbiterr(),
    .axi_ar_underflow(),
    .axi_ar_wr_data_count(),
    .axi_aw_data_count(),
    .axi_aw_dbiterr(),
    .axi_aw_injectdbiterr(1'b0),
    .axi_aw_injectsbiterr(1'b0),
    .axi_aw_overflow(),
    .axi_aw_prog_empty(),
    .axi_aw_prog_empty_thresh(4'b0),
    .axi_aw_prog_full(),
    .axi_aw_prog_full_thresh(4'b0),
    .axi_aw_rd_data_count(),
    .axi_aw_sbiterr(),
    .axi_aw_underflow(),
    .axi_aw_wr_data_count(),
    .axi_b_data_count(),
    .axi_b_dbiterr(),
    .axi_b_injectdbiterr(1'b0),
    .axi_b_injectsbiterr(1'b0),
    .axi_b_overflow(),
    .axi_b_prog_empty(),
    .axi_b_prog_empty_thresh(4'b0),
    .axi_b_prog_full(),
    .axi_b_prog_full_thresh(4'b0),
    .axi_b_rd_data_count(),
    .axi_b_sbiterr(),
    .axi_b_underflow(),
    .axi_b_wr_data_count(),
    .axi_r_data_count(),
    .axi_r_dbiterr(),
    .axi_r_injectdbiterr(1'b0),
    .axi_r_injectsbiterr(1'b0),
    .axi_r_overflow(),
    .axi_r_prog_empty(),
    .axi_r_prog_empty_thresh(10'b0),
    .axi_r_prog_full(),
    .axi_r_prog_full_thresh(10'b0),
    .axi_r_rd_data_count(),
    .axi_r_sbiterr(),
    .axi_r_underflow(),
    .axi_r_wr_data_count(),
    .axi_w_data_count(),
    .axi_w_dbiterr(),
    .axi_w_injectdbiterr(1'b0),
    .axi_w_injectsbiterr(1'b0),
    .axi_w_overflow(),
    .axi_w_prog_empty(),
    .axi_w_prog_empty_thresh(10'b0),
    .axi_w_prog_full(),
    .axi_w_prog_full_thresh(10'b0),
    .axi_w_rd_data_count(),
    .axi_w_sbiterr(),
    .axi_w_underflow(),
    .axi_w_wr_data_count(),
    .axis_data_count(),
    .axis_dbiterr(),
    .axis_injectdbiterr(1'b0),
    .axis_injectsbiterr(1'b0),
    .axis_overflow(),
    .axis_prog_empty(),
    .axis_prog_empty_thresh(10'b0),
    .axis_prog_full(),
    .axis_prog_full_thresh(10'b0),
    .axis_rd_data_count(),
    .axis_sbiterr(),
    .axis_underflow(),
    .axis_wr_data_count(),
    .backup(1'b0),
    .backup_marker(1'b0),
    .data_count(),
    .dbiterr(),
    .injectdbiterr(1'b0),
    .injectsbiterr(1'b0),
    .int_clk(1'b0),
    .m_aclk(1'b0),
    .m_aclk_en(1'b0),
    .m_axi_araddr(),
    .m_axi_arburst(),
    .m_axi_arcache(),
    .m_axi_arid(),
    .m_axi_arlen(),
    .m_axi_arlock(),
    .m_axi_arprot(),
    .m_axi_arqos(),
    .m_axi_arready(1'b0),
    .m_axi_arregion(),
    .m_axi_arsize(),
    .m_axi_aruser(),
    .m_axi_arvalid(),
    .m_axi_awaddr(),
    .m_axi_awburst(),
    .m_axi_awcache(),
    .m_axi_awid(),
    .m_axi_awlen(),
    .m_axi_awlock(),
    .m_axi_awprot(),
    .m_axi_awqos(),
    .m_axi_awready(1'b0),
    .m_axi_awregion(),
    .m_axi_awsize(),
    .m_axi_awuser(),
    .m_axi_awvalid(),
    .m_axi_bid(4'b0),
    .m_axi_bready(),
    .m_axi_bresp(2'b0),
    .m_axi_buser(1'b0),
    .m_axi_bvalid(1'b0),
    .m_axi_rdata(64'b0),
    .m_axi_rid(4'b0),
    .m_axi_rlast(1'b0),
    .m_axi_rready(),
    .m_axi_rresp(2'b0),
    .m_axi_ruser(1'b0),
    .m_axi_rvalid(1'b0),
    .m_axi_wdata(),
    .m_axi_wid(),
    .m_axi_wlast(),
    .m_axi_wready(1'b0),
    .m_axi_wstrb(),
    .m_axi_wuser(),
    .m_axi_wvalid(),
    .m_axis_tdata(),
    .m_axis_tdest(),
    .m_axis_tid(),
    .m_axis_tkeep(),
    .m_axis_tlast(),
    .m_axis_tready(1'b0),
    .m_axis_tstrb(),
    .m_axis_tuser(),
    .m_axis_tvalid(),
    .overflow(),
    .prog_empty(),
    .prog_empty_thresh(5'b0),
    .prog_empty_thresh_assert(5'b0),
    .prog_empty_thresh_negate(5'b0),
    .prog_full(),
    .prog_full_thresh(5'b0),
    .prog_full_thresh_assert(5'b0),
    .prog_full_thresh_negate(5'b0),
    .rd_data_count(),
    .rd_rst(1'b0),
    .s_aclk(1'b0),
    .s_aclk_en(1'b0),
    .s_aresetn(1'b0),
    .s_axi_araddr(32'b0),
    .s_axi_arburst(2'b0),
    .s_axi_arcache(4'b0),
    .s_axi_arid(4'b0),
    .s_axi_arlen(8'b0),
    .s_axi_arlock(2'b0),
    .s_axi_arprot(3'b0),
    .s_axi_arqos(4'b0),
    .s_axi_arready(),
    .s_axi_arregion(4'b0),
    .s_axi_arsize(3'b0),
    .s_axi_aruser(1'b0),
    .s_axi_arvalid(1'b0),
    .s_axi_awaddr(32'b0),
    .s_axi_awburst(2'b0),
    .s_axi_awcache(4'b0),
    .s_axi_awid(4'b0),
    .s_axi_awlen(8'b0),
    .s_axi_awlock(2'b0),
    .s_axi_awprot(3'b0),
    .s_axi_awqos(4'b0),
    .s_axi_awready(),
    .s_axi_awregion(4'b0),
    .s_axi_awsize(3'b0),
    .s_axi_awuser(1'b0),
    .s_axi_awvalid(1'b0),
    .s_axi_bid(),
    .s_axi_bready(1'b0),
    .s_axi_bresp(),
    .s_axi_buser(),
    .s_axi_bvalid(),
    .s_axi_rdata(),
    .s_axi_rid(),
    .s_axi_rlast(),
    .s_axi_rready(1'b0),
    .s_axi_rresp(),
    .s_axi_ruser(),
    .s_axi_rvalid(),
    .s_axi_wdata(64'b0),
    .s_axi_wid(4'b0),
    .s_axi_wlast(1'b0),
    .s_axi_wready(),
    .s_axi_wstrb(8'b0),
    .s_axi_wuser(1'b0),
    .s_axi_wvalid(1'b0),
    .s_axis_tdata(64'b0),
    .s_axis_tdest(4'b0),
    .s_axis_tid(8'b0),
    .s_axis_tkeep(4'b0),
    .s_axis_tlast(1'b0),
    .s_axis_tready(),
    .s_axis_tstrb(4'b0),
    .s_axis_tuser(4'b0),
    .s_axis_tvalid(1'b0),
    .sbiterr(),
    .srst(1'b0),
    .underflow(),
    .valid(),
    .wr_ack(),
    .wr_data_count(),
    .wr_rst(1'b0),
    .wr_rst_busy(),
    .rd_rst_busy(),
    .sleep(1'b0)
  );

endmodule



// -- (c) Copyright 2008 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: N-deep SRL pipeline element with generic single-channel AXI interfaces.
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
// Structure:
//   axic_srl_fifo
//     ndeep_srl
//       nto1_mux
//--------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_axic_srl_fifo #
  (
   parameter         C_FAMILY   = "none", // FPGA Family
   parameter integer C_FIFO_WIDTH  = 1, // Width of S_MESG/M_MESG.
   parameter integer C_MAX_CTRL_FANOUT = 33, // Maximum number of mesg bits
                                             // the control logic can be used
                                             // on before the control logic
                                             // needs to be replicated.
   parameter integer C_FIFO_DEPTH_LOG =  2,  // Depth of FIFO is 2**C_FIFO_DEPTH_LOG.  
                                             // The minimum size fifo generated is 4-deep.
   parameter         C_USE_FULL =  1         // Prevent overwrite by throttling S_READY.                                              
   )
  (
   input  wire                        ACLK,    // Clock
   input  wire                        ARESET,  // Reset
   input  wire [C_FIFO_WIDTH-1:0]     S_MESG,  // Input data
   input  wire                        S_VALID, // Input data valid
   output wire                        S_READY, // Input data ready
   output wire [C_FIFO_WIDTH-1:0]     M_MESG,  // Output data
   output wire                        M_VALID, // Output data valid
   input  wire                        M_READY  // Output data ready
   );
  
  localparam P_FIFO_DEPTH_LOG = (C_FIFO_DEPTH_LOG>1) ? C_FIFO_DEPTH_LOG : 2;
  localparam P_EMPTY       = {P_FIFO_DEPTH_LOG{1'b1}};
  localparam P_ALMOSTEMPTY = {P_FIFO_DEPTH_LOG{1'b0}};
  localparam P_ALMOSTFULL_TEMP  = {P_EMPTY, 1'b0};
  localparam P_ALMOSTFULL  = P_ALMOSTFULL_TEMP[0+:P_FIFO_DEPTH_LOG];
  localparam P_NUM_REPS    = (((C_FIFO_WIDTH+1)%C_MAX_CTRL_FANOUT) == 0) ?
                             (C_FIFO_WIDTH+1)/C_MAX_CTRL_FANOUT :
                             ((C_FIFO_WIDTH+1)/C_MAX_CTRL_FANOUT)+1;

  (* syn_keep = "1" *) reg [P_NUM_REPS*P_FIFO_DEPTH_LOG-1:0]  fifoaddr;
  (* syn_keep = "1" *) wire [P_NUM_REPS*P_FIFO_DEPTH_LOG-1:0] fifoaddr_i;

  genvar i;
  genvar j;

  reg  M_VALID_i;
  reg  S_READY_i;
  wire push;     // FIFO push
  wire pop;      // FIFO pop
  reg  areset_d1; // Reset delay register
  wire [C_FIFO_WIDTH-1:0] m_axi_mesg_i; // Intermediate SRL data

  assign M_VALID = M_VALID_i;
  assign S_READY = C_USE_FULL ? S_READY_i : 1'b1;
  assign M_MESG = m_axi_mesg_i;
  assign push = S_VALID & (C_USE_FULL ? S_READY_i : 1'b1);
  assign pop  = M_VALID_i & M_READY;
  
  always @(posedge ACLK) begin
    areset_d1 <= ARESET;
  end
      
  generate
    //---------------------------------------------------------------------------
    // Create count of number of elements in FIFOs
    //---------------------------------------------------------------------------
    for (i=0;i<P_NUM_REPS;i=i+1) begin : gen_rep
      assign fifoaddr_i[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] = 
         push ? fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] + 1 :
                fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] - 1;
      always @(posedge ACLK) begin
        if (ARESET)
          fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] <= 
                {P_FIFO_DEPTH_LOG{1'b1}};
        else if (push ^ pop)
          fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] <= 
                fifoaddr_i[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i];
      end
    end

    //---------------------------------------------------------------------------
    // When FIFO is empty, reset master valid bit.  When not empty set valid bit.
    // When FIFO is full,  reset slave  ready bit.  When not full  set ready bit.
    //---------------------------------------------------------------------------
    
    always @(posedge ACLK) begin
      if (ARESET) begin
        M_VALID_i <= 1'b0;
      end else if ((fifoaddr[P_FIFO_DEPTH_LOG*P_NUM_REPS-1:P_FIFO_DEPTH_LOG*(P_NUM_REPS-1)] == 
                               P_ALMOSTEMPTY) && pop && ~push) begin
        M_VALID_i <= 1'b0;
      end else if (push) begin
        M_VALID_i <= 1'b1;
      end
    end
      
    always @(posedge ACLK) begin
      if (ARESET) begin
        S_READY_i <= 1'b0;
      end else if (areset_d1) begin
        S_READY_i <= 1'b1;
      end else if (C_USE_FULL && 
        ((fifoaddr[P_FIFO_DEPTH_LOG*P_NUM_REPS-1:P_FIFO_DEPTH_LOG*(P_NUM_REPS-1)] == 
         P_ALMOSTFULL) && push && ~pop)) begin
        S_READY_i <= 1'b0;
      end else if (C_USE_FULL && pop) begin
        S_READY_i <= 1'b1;
      end
    end

    //---------------------------------------------------------------------------
    // Instantiate SRLs
    //---------------------------------------------------------------------------
    for (i=0;i<(C_FIFO_WIDTH/C_MAX_CTRL_FANOUT)+((C_FIFO_WIDTH%C_MAX_CTRL_FANOUT)>0);i=i+1) begin : gen_srls
      for (j=0;((j<C_MAX_CTRL_FANOUT)&&(i*C_MAX_CTRL_FANOUT+j<C_FIFO_WIDTH));j=j+1) begin : gen_rep
        axi_data_fifo_v2_1_11_ndeep_srl #
          (
           .C_FAMILY  (C_FAMILY),
           .C_A_WIDTH (P_FIFO_DEPTH_LOG)
          )
          srl_nx1
          (
           .CLK (ACLK),
           .A   (fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:
                          P_FIFO_DEPTH_LOG*(i)]),
           .CE  (push),
           .D   (S_MESG[i*C_MAX_CTRL_FANOUT+j]),
           .Q   (m_axi_mesg_i[i*C_MAX_CTRL_FANOUT+j])
          );
      end
    end      
  endgenerate
  
endmodule

`default_nettype wire


// -- (c) Copyright 2010 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
// Description: N-deep SRL pipeline element with generic single-channel AXI interfaces.
//   Interface outputs are synchronized using ordinary flops for improved timing.
//--------------------------------------------------------------------------
// Structure:
//   axic_reg_srl_fifo
//     ndeep_srl
//       nto1_mux
//--------------------------------------------------------------------------


`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_axic_reg_srl_fifo #
  (
   parameter         C_FAMILY   = "none", // FPGA Family
   parameter integer C_FIFO_WIDTH  = 1, // Width of S_MESG/M_MESG.
   parameter integer C_MAX_CTRL_FANOUT = 33, // Maximum number of mesg bits
                                             // the control logic can be used
                                             // on before the control logic
                                             // needs to be replicated.
   parameter integer C_FIFO_DEPTH_LOG =  2,  // Depth of FIFO is 2**C_FIFO_DEPTH_LOG.  
                                             // The minimum size fifo generated is 4-deep.
   parameter         C_USE_FULL =  1         // Prevent overwrite by throttling S_READY.                                              
   )
  (
   input  wire                        ACLK,    // Clock
   input  wire                        ARESET,  // Reset
   input  wire [C_FIFO_WIDTH-1:0]     S_MESG,  // Input data
   input  wire                        S_VALID, // Input data valid
   output wire                        S_READY, // Input data ready
   output wire [C_FIFO_WIDTH-1:0]     M_MESG,  // Output data
   output wire                        M_VALID, // Output data valid
   input  wire                        M_READY  // Output data ready
   );
  
  localparam P_FIFO_DEPTH_LOG = (C_FIFO_DEPTH_LOG>1) ? C_FIFO_DEPTH_LOG : 2;
  localparam P_EMPTY       = {P_FIFO_DEPTH_LOG{1'b1}};
  localparam P_ALMOSTEMPTY = {P_FIFO_DEPTH_LOG{1'b0}};
  localparam P_ALMOSTFULL_TEMP  = {P_EMPTY, 1'b0};
  localparam P_ALMOSTFULL  = P_ALMOSTFULL_TEMP[0+:P_FIFO_DEPTH_LOG];
  localparam P_NUM_REPS    = (((C_FIFO_WIDTH+1)%C_MAX_CTRL_FANOUT) == 0) ?
                             (C_FIFO_WIDTH+1)/C_MAX_CTRL_FANOUT :
                             ((C_FIFO_WIDTH+1)/C_MAX_CTRL_FANOUT)+1;

  (* syn_keep = "1" *) reg [P_NUM_REPS*P_FIFO_DEPTH_LOG-1:0]  fifoaddr;
  (* syn_keep = "1" *) wire [P_NUM_REPS*P_FIFO_DEPTH_LOG-1:0] fifoaddr_i;

  genvar i;
  genvar j;

  
  reg  m_valid_i = 1'b0;
  reg  s_ready_i;
  wire push;     // FIFO push
  wire pop;      // FIFO pop
  reg  areset_d1; // Reset delay register
  reg  [C_FIFO_WIDTH-1:0] storage_data1;
  wire [C_FIFO_WIDTH-1:0] storage_data2; // Intermediate SRL data
  reg                    load_s1;
  wire                   load_s1_from_s2;

  reg [1:0] state;
  localparam [1:0] 
    ZERO = 2'b10,
    ONE  = 2'b11,
    TWO  = 2'b01;
      
  assign M_VALID = m_valid_i;
  assign S_READY = C_USE_FULL ? s_ready_i : 1'b1;
  assign push = (S_VALID & (C_USE_FULL ? s_ready_i : 1'b1) & (state == TWO)) | (~M_READY & S_VALID & (state == ONE));
  assign pop  = M_READY & (state == TWO);
  assign M_MESG = storage_data1;
  
  always @(posedge ACLK) begin
    areset_d1 <= ARESET;
  end
      
  // Load storage1 with either slave side data or from storage2
  always @(posedge ACLK) 
  begin
    if (load_s1)
      if (load_s1_from_s2)
        storage_data1 <= storage_data2;
      else
        storage_data1 <= S_MESG;        
  end

  // Loading s1
  always @ *
  begin
    if ( ((state == ZERO) && (S_VALID == 1)) || // Load when empty on slave transaction
         // Load when ONE if we both have read and write at the same time
         ((state == ONE) && (S_VALID == 1) && (M_READY == 1)) ||
         // Load when TWO and we have a transaction on Master side
         ((state == TWO) && (M_READY == 1)))
      load_s1 = 1'b1;
    else
      load_s1 = 1'b0;
  end // always @ *

  assign load_s1_from_s2 = (state == TWO);
                   
  // State Machine for handling output signals
  always @(posedge ACLK) 
  begin
    if (areset_d1) begin
      state <= ZERO;
      m_valid_i <= 1'b0;
    end else begin
      case (state)
        // No transaction stored locally
        ZERO: begin
          if (S_VALID) begin
            state <= ONE; // Got one so move to ONE
            m_valid_i <= 1'b1;
          end
        end

        // One transaction stored locally
        ONE: begin
          if (M_READY & ~S_VALID) begin
            state <= ZERO; // Read out one so move to ZERO
            m_valid_i <= 1'b0;
          end else if (~M_READY & S_VALID) begin
            state <= TWO;  // Got another one so move to TWO
            m_valid_i <= 1'b1;
          end
        end

        // TWO transaction stored locally
        TWO: begin
          if ((fifoaddr[P_FIFO_DEPTH_LOG*P_NUM_REPS-1:P_FIFO_DEPTH_LOG*(P_NUM_REPS-1)] == 
                 P_ALMOSTEMPTY) && pop && ~push) begin
            state <= ONE; // Read out one so move to ONE
            m_valid_i <= 1'b1;
          end
        end
      endcase // case (state)
    end
  end // always @ (posedge ACLK)
      
  generate
    //---------------------------------------------------------------------------
    // Create count of number of elements in FIFOs
    //---------------------------------------------------------------------------
    for (i=0;i<P_NUM_REPS;i=i+1) begin : gen_rep
      assign fifoaddr_i[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] = 
         push ? fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] + 1 :
                fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] - 1;
      always @(posedge ACLK) begin
        if (ARESET)
          fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] <= 
                {P_FIFO_DEPTH_LOG{1'b1}};
        else if (push ^ pop)
          fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i] <= 
                fifoaddr_i[P_FIFO_DEPTH_LOG*(i+1)-1:P_FIFO_DEPTH_LOG*i];
      end
    end

    always @(posedge ACLK) begin
      if (ARESET) begin
        s_ready_i <= 1'b0;
      end else if (areset_d1) begin
        s_ready_i <= 1'b1;
      end else if (C_USE_FULL && 
        ((fifoaddr[P_FIFO_DEPTH_LOG*P_NUM_REPS-1:P_FIFO_DEPTH_LOG*(P_NUM_REPS-1)] == 
         P_ALMOSTFULL) && push && ~pop)) begin
        s_ready_i <= 1'b0;
      end else if (C_USE_FULL && pop) begin
        s_ready_i <= 1'b1;
      end
    end

    //---------------------------------------------------------------------------
    // Instantiate SRLs
    //---------------------------------------------------------------------------
    for (i=0;i<(C_FIFO_WIDTH/C_MAX_CTRL_FANOUT)+((C_FIFO_WIDTH%C_MAX_CTRL_FANOUT)>0);i=i+1) begin : gen_srls
      for (j=0;((j<C_MAX_CTRL_FANOUT)&&(i*C_MAX_CTRL_FANOUT+j<C_FIFO_WIDTH));j=j+1) begin : gen_rep
        axi_data_fifo_v2_1_11_ndeep_srl #
          (
           .C_FAMILY  (C_FAMILY),
           .C_A_WIDTH (P_FIFO_DEPTH_LOG)
          )
          srl_nx1
          (
           .CLK (ACLK),
           .A   (fifoaddr[P_FIFO_DEPTH_LOG*(i+1)-1:
                          P_FIFO_DEPTH_LOG*(i)]),
           .CE  (push),
           .D   (S_MESG[i*C_MAX_CTRL_FANOUT+j]),
           .Q   (storage_data2[i*C_MAX_CTRL_FANOUT+j])
          );
      end
    end      
  endgenerate
  
endmodule

`default_nettype wire


// -- (c) Copyright 2008 - 2014 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Description: This is a generic n-deep SRL instantiation
// Verilog-standard:  Verilog 2001
// $Revision: 
// $Date: 
//
//-----------------------------------------------------------------------------
`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_ndeep_srl #
  (
   parameter         C_FAMILY  = "rtl", // FPGA Family
   parameter         C_A_WIDTH = 1          // Address Width (>= 1)
   )
  (
   input  wire                 CLK, // Clock
   input  wire [C_A_WIDTH-1:0] A,   // Address
   input  wire                 CE,  // Clock Enable
   input  wire                 D,   // Input Data
   output wire                 Q    // Output Data
   );

  localparam integer P_SRLASIZE = 5;
  localparam integer P_SRLDEPTH = 32;
  localparam integer P_NUMSRLS  = (C_A_WIDTH>P_SRLASIZE) ? (2**(C_A_WIDTH-P_SRLASIZE)) : 1;
  localparam integer P_SHIFT_DEPTH  = 2**C_A_WIDTH;
  
  wire [P_NUMSRLS:0]   d_i;
  wire [P_NUMSRLS-1:0] q_i;
  wire [(C_A_WIDTH>P_SRLASIZE) ? (C_A_WIDTH-1) : (P_SRLASIZE-1) : 0] a_i;
  
  genvar i;
  
  // Instantiate SRLs in carry chain format
  assign d_i[0] = D;
  assign a_i = A;
  
  generate
					
    if (C_FAMILY == "rtl") begin : gen_rtl_shifter
      if (C_A_WIDTH <= P_SRLASIZE) begin : gen_inferred_srl
        reg [P_SRLDEPTH-1:0] shift_reg = {P_SRLDEPTH{1'b0}};
        always @(posedge CLK)
          if (CE)
            shift_reg <= {shift_reg[P_SRLDEPTH-2:0], D};
        assign Q = shift_reg[a_i];
      end else begin : gen_logic_shifter  // Very wasteful
        reg [P_SHIFT_DEPTH-1:0] shift_reg = {P_SHIFT_DEPTH{1'b0}};
        always @(posedge CLK)
          if (CE)
            shift_reg <= {shift_reg[P_SHIFT_DEPTH-2:0], D};
        assign Q = shift_reg[a_i];
      end
    end else begin : gen_primitive_shifter
      for (i=0;i<P_NUMSRLS;i=i+1) begin : gen_srls
        SRLC32E
          srl_inst
            (
             .CLK (CLK),
             .A   (a_i[P_SRLASIZE-1:0]),
             .CE  (CE),
             .D   (d_i[i]),
             .Q   (q_i[i]),
             .Q31 (d_i[i+1])
             );
      end
      
      if (C_A_WIDTH>P_SRLASIZE) begin : gen_srl_mux
        generic_baseblocks_v2_1_0_nto1_mux #
        (
          .C_RATIO         (2**(C_A_WIDTH-P_SRLASIZE)),
          .C_SEL_WIDTH     (C_A_WIDTH-P_SRLASIZE),
          .C_DATAOUT_WIDTH (1),
          .C_ONEHOT        (0)
        )
        srl_q_mux_inst
        (
          .SEL_ONEHOT ({2**(C_A_WIDTH-P_SRLASIZE){1'b0}}),
          .SEL        (a_i[C_A_WIDTH-1:P_SRLASIZE]),
          .IN         (q_i),
          .OUT        (Q)
        );
      end else begin : gen_no_srl_mux
        assign Q = q_i[0];
      end
    end
  endgenerate

endmodule

`default_nettype wire


// -- (c) Copyright 2010 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// AXI data fifo module:    
//   5-channel memory-mapped AXI4 interfaces.
//   SRL or BRAM based FIFO on AXI W and/or R channels.
//   FIFO to accommodate various data flow rates through the AXI interconnect
//
// Verilog-standard:  Verilog 2001
//-----------------------------------------------------------------------------
//
// Structure:
//   axi_data_fifo
//     fifo_generator
//
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_data_fifo_v2_1_11_axi_data_fifo #
  (
   parameter         C_FAMILY                    = "virtex7",
   parameter integer C_AXI_PROTOCOL              = 0,
   parameter integer C_AXI_ID_WIDTH              = 4,
   parameter integer C_AXI_ADDR_WIDTH            = 32,
   parameter integer C_AXI_DATA_WIDTH            = 32,
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS = 0,
   parameter integer C_AXI_AWUSER_WIDTH          = 1,
   parameter integer C_AXI_ARUSER_WIDTH          = 1,
   parameter integer C_AXI_WUSER_WIDTH           = 1,
   parameter integer C_AXI_RUSER_WIDTH           = 1,
   parameter integer C_AXI_BUSER_WIDTH           = 1,
   parameter integer C_AXI_WRITE_FIFO_DEPTH      = 0,      // Range: (0, 32, 512)
   parameter         C_AXI_WRITE_FIFO_TYPE       = "lut",  // "lut" = LUT (SRL) based,
                                                           // "bram" = BRAM based
   parameter integer C_AXI_WRITE_FIFO_DELAY      = 0,      // 0 = No, 1 = Yes
                       // Indicates whether AWVALID and WVALID assertion is delayed until:
                       //   a. the corresponding WLAST is stored in the FIFO, or
                       //   b. no WLAST is stored and the FIFO is full.
                       // 0 means AW channel is pass-through and 
                       //   WVALID is asserted whenever FIFO is not empty.
   parameter integer C_AXI_READ_FIFO_DEPTH       = 0,      // Range: (0, 32, 512)
   parameter         C_AXI_READ_FIFO_TYPE        = "lut",  // "lut" = LUT (SRL) based,
                                                           // "bram" = BRAM based
   parameter integer C_AXI_READ_FIFO_DELAY       = 0)      // 0 = No, 1 = Yes
                       // Indicates whether ARVALID assertion is delayed until the 
                       //   the remaining vacancy of the FIFO is at least the burst length
                       //   as indicated by ARLEN.
                       // 0 means AR channel is pass-through.
   // System Signals
  (input wire aclk,
   input wire aresetn,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_awlen,
   input  wire [3-1:0]                  s_axi_awsize,
   input  wire [2-1:0]                  s_axi_awburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_awlock,
   input  wire [4-1:0]                  s_axi_awcache,
   input  wire [3-1:0]                  s_axi_awprot,
   input  wire [4-1:0]                  s_axi_awregion,
   input  wire [4-1:0]                  s_axi_awqos,
   input  wire [C_AXI_AWUSER_WIDTH-1:0] s_axi_awuser,
   input  wire                          s_axi_awvalid,
   output wire                          s_axi_awready,

   // Slave Interface Write Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     s_axi_wid,
   input  wire [C_AXI_DATA_WIDTH-1:0]   s_axi_wdata,
   input  wire [C_AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
   input  wire                          s_axi_wlast,
   input  wire [C_AXI_WUSER_WIDTH-1:0]  s_axi_wuser,
   input  wire                          s_axi_wvalid,
   output wire                          s_axi_wready,

   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]     s_axi_bid,
   output wire [2-1:0]                  s_axi_bresp,
   output wire [C_AXI_BUSER_WIDTH-1:0]  s_axi_buser,
   output wire                          s_axi_bvalid,
   input  wire                          s_axi_bready,

   // Slave Interface Read Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_arlen,
   input  wire [3-1:0]                  s_axi_arsize,
   input  wire [2-1:0]                  s_axi_arburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_arlock,
   input  wire [4-1:0]                  s_axi_arcache,
   input  wire [3-1:0]                  s_axi_arprot,
   input  wire [4-1:0]                  s_axi_arregion,
   input  wire [4-1:0]                  s_axi_arqos,
   input  wire [C_AXI_ARUSER_WIDTH-1:0] s_axi_aruser,
   input  wire                          s_axi_arvalid,
   output wire                          s_axi_arready,

   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]     s_axi_rid,
   output wire [C_AXI_DATA_WIDTH-1:0]   s_axi_rdata,
   output wire [2-1:0]                  s_axi_rresp,
   output wire                          s_axi_rlast,
   output wire [C_AXI_RUSER_WIDTH-1:0]  s_axi_ruser,
   output wire                          s_axi_rvalid,
   input  wire                          s_axi_rready,
   
   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_awid,
   output wire [C_AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_awlen,
   output wire [3-1:0]                  m_axi_awsize,
   output wire [2-1:0]                  m_axi_awburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_awlock,
   output wire [4-1:0]                  m_axi_awcache,
   output wire [3-1:0]                  m_axi_awprot,
   output wire [4-1:0]                  m_axi_awregion,
   output wire [4-1:0]                  m_axi_awqos,
   output wire [C_AXI_AWUSER_WIDTH-1:0] m_axi_awuser,
   output wire                          m_axi_awvalid,
   input  wire                          m_axi_awready,
   
   // Master Interface Write Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_wid,
   output wire [C_AXI_DATA_WIDTH-1:0]   m_axi_wdata,
   output wire [C_AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
   output wire                          m_axi_wlast,
   output wire [C_AXI_WUSER_WIDTH-1:0]  m_axi_wuser,
   output wire                          m_axi_wvalid,
   input  wire                          m_axi_wready,
   
   // Master Interface Write Response Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     m_axi_bid,
   input  wire [2-1:0]                  m_axi_bresp,
   input  wire [C_AXI_BUSER_WIDTH-1:0]  m_axi_buser,
   input  wire                          m_axi_bvalid,
   output wire                          m_axi_bready,
   
   // Master Interface Read Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_arid,
   output wire [C_AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_arlen,
   output wire [3-1:0]                  m_axi_arsize,
   output wire [2-1:0]                  m_axi_arburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_arlock,
   output wire [4-1:0]                  m_axi_arcache,
   output wire [3-1:0]                  m_axi_arprot,
   output wire [4-1:0]                  m_axi_arregion,
   output wire [4-1:0]                  m_axi_arqos,
   output wire [C_AXI_ARUSER_WIDTH-1:0] m_axi_aruser,
   output wire                          m_axi_arvalid,
   input  wire                          m_axi_arready,
   
   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     m_axi_rid,
   input  wire [C_AXI_DATA_WIDTH-1:0]   m_axi_rdata,
   input  wire [2-1:0]                  m_axi_rresp,
   input  wire                          m_axi_rlast,
   input  wire [C_AXI_RUSER_WIDTH-1:0]  m_axi_ruser,
   input  wire                          m_axi_rvalid,
   output wire                          m_axi_rready);
  
  localparam integer P_WIDTH_RACH = 4+4+3+4+2+3+((C_AXI_PROTOCOL==1)?6:9)+C_AXI_ADDR_WIDTH+C_AXI_ID_WIDTH+C_AXI_ARUSER_WIDTH;
  localparam integer P_WIDTH_WACH = 4+4+3+4+2+3+((C_AXI_PROTOCOL==1)?6:9)+C_AXI_ADDR_WIDTH+C_AXI_ID_WIDTH+C_AXI_AWUSER_WIDTH;
  localparam integer P_WIDTH_RDCH = 1 + 2 + C_AXI_DATA_WIDTH + C_AXI_ID_WIDTH + C_AXI_RUSER_WIDTH;
  localparam integer P_WIDTH_WDCH = 1+C_AXI_DATA_WIDTH+C_AXI_DATA_WIDTH/8+((C_AXI_PROTOCOL==1)?C_AXI_ID_WIDTH:0)+C_AXI_WUSER_WIDTH;
  localparam integer P_WIDTH_WRCH = 2 + C_AXI_ID_WIDTH + C_AXI_BUSER_WIDTH;
  
  localparam         P_PRIM_FIFO_TYPE = "512x72" ;
  localparam integer P_AXI4 = 0;
  localparam integer P_AXI3 = 1;
  localparam integer P_AXILITE = 2;
  localparam integer P_WRITE_FIFO_DEPTH_LOG = (C_AXI_WRITE_FIFO_DEPTH > 1) ? f_ceil_log2(C_AXI_WRITE_FIFO_DEPTH) : 1;
  localparam integer P_READ_FIFO_DEPTH_LOG = (C_AXI_READ_FIFO_DEPTH > 1) ? f_ceil_log2(C_AXI_READ_FIFO_DEPTH) : 1;
  
  // Ceiling of log2(x)
  function integer f_ceil_log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      f_ceil_log2 = acc;
    end
  endfunction

  generate
    if (((C_AXI_WRITE_FIFO_DEPTH == 0) && (C_AXI_READ_FIFO_DEPTH == 0)) || (C_AXI_PROTOCOL == P_AXILITE)) begin : gen_bypass
      assign m_axi_awid     = s_axi_awid;
      assign m_axi_awaddr   = s_axi_awaddr;
      assign m_axi_awlen    = s_axi_awlen;
      assign m_axi_awsize   = s_axi_awsize;
      assign m_axi_awburst  = s_axi_awburst;
      assign m_axi_awlock   = s_axi_awlock;
      assign m_axi_awcache  = s_axi_awcache;
      assign m_axi_awprot   = s_axi_awprot;
      assign m_axi_awregion = s_axi_awregion;
      assign m_axi_awqos    = s_axi_awqos;
      assign m_axi_awuser   = s_axi_awuser;
      assign m_axi_awvalid  = s_axi_awvalid;
      assign s_axi_awready  = m_axi_awready;
      
      assign m_axi_wid      = s_axi_wid;
      assign m_axi_wdata    = s_axi_wdata;
      assign m_axi_wstrb    = s_axi_wstrb;
      assign m_axi_wlast    = s_axi_wlast;
      assign m_axi_wuser    = s_axi_wuser;
      assign m_axi_wvalid   = s_axi_wvalid;
      assign s_axi_wready   = m_axi_wready;
    
      assign s_axi_bid      = m_axi_bid;
      assign s_axi_bresp    = m_axi_bresp;
      assign s_axi_buser    = m_axi_buser;
      assign s_axi_bvalid   = m_axi_bvalid;
      assign m_axi_bready   = s_axi_bready;
    
      assign m_axi_arid     = s_axi_arid;
      assign m_axi_araddr   = s_axi_araddr;
      assign m_axi_arlen    = s_axi_arlen;
      assign m_axi_arsize   = s_axi_arsize;
      assign m_axi_arburst  = s_axi_arburst;
      assign m_axi_arlock   = s_axi_arlock;
      assign m_axi_arcache  = s_axi_arcache;
      assign m_axi_arprot   = s_axi_arprot;
      assign m_axi_arregion = s_axi_arregion;
      assign m_axi_arqos    = s_axi_arqos;
      assign m_axi_aruser   = s_axi_aruser;
      assign m_axi_arvalid  = s_axi_arvalid;
      assign s_axi_arready  = m_axi_arready;
  
      assign s_axi_rid      = m_axi_rid;
      assign s_axi_rdata    = m_axi_rdata;
      assign s_axi_rresp    = m_axi_rresp;
      assign s_axi_rlast    = m_axi_rlast;
      assign s_axi_ruser    = m_axi_ruser;
      assign s_axi_rvalid   = m_axi_rvalid;
      assign m_axi_rready   = s_axi_rready;
      
    end else begin : gen_fifo
      
      wire [4-1:0]                  s_axi_awregion_i;
      wire [4-1:0]                  s_axi_arregion_i;
      wire [4-1:0]                  m_axi_awregion_i;
      wire [4-1:0]                  m_axi_arregion_i;
      wire [C_AXI_ID_WIDTH-1:0]     s_axi_wid_i;
      wire [C_AXI_ID_WIDTH-1:0]     m_axi_wid_i;
      
      assign s_axi_awregion_i = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : s_axi_awregion;
      assign s_axi_arregion_i = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : s_axi_arregion;
      assign m_axi_awregion = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : m_axi_awregion_i;
      assign m_axi_arregion = (C_AXI_PROTOCOL == P_AXI3) ? 4'b0 : m_axi_arregion_i;
      assign s_axi_wid_i = (C_AXI_PROTOCOL == P_AXI3) ? s_axi_wid : {C_AXI_ID_WIDTH{1'b0}};
      assign m_axi_wid = (C_AXI_PROTOCOL == P_AXI3) ? m_axi_wid_i : {C_AXI_ID_WIDTH{1'b0}};


      fifo_generator_v13_1_4 #(
          .C_INTERFACE_TYPE(2),
          .C_AXI_TYPE((C_AXI_PROTOCOL == P_AXI4) ? 1 : 3),
          .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
          .C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
          .C_HAS_AXI_ID(1),
          .C_AXI_LEN_WIDTH((C_AXI_PROTOCOL == P_AXI4) ? 8 : 4),
          .C_AXI_LOCK_WIDTH((C_AXI_PROTOCOL == P_AXI4) ? 1 : 2),
          .C_HAS_AXI_ARUSER(1),
          .C_HAS_AXI_AWUSER(1),
          .C_HAS_AXI_BUSER(1),
          .C_HAS_AXI_RUSER(1),
          .C_HAS_AXI_WUSER(1),
          .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
          .C_AXI_ARUSER_WIDTH(C_AXI_ARUSER_WIDTH),
          .C_AXI_AWUSER_WIDTH(C_AXI_AWUSER_WIDTH),
          .C_AXI_BUSER_WIDTH(C_AXI_BUSER_WIDTH),
          .C_AXI_RUSER_WIDTH(C_AXI_RUSER_WIDTH),
          .C_AXI_WUSER_WIDTH(C_AXI_WUSER_WIDTH),
          .C_DIN_WIDTH_RACH(P_WIDTH_RACH),
          .C_DIN_WIDTH_RDCH(P_WIDTH_RDCH),
          .C_DIN_WIDTH_WACH(P_WIDTH_WACH),
          .C_DIN_WIDTH_WDCH(P_WIDTH_WDCH),
          .C_DIN_WIDTH_WRCH(P_WIDTH_WDCH),
          .C_RACH_TYPE(((C_AXI_READ_FIFO_DEPTH != 0) && C_AXI_READ_FIFO_DELAY) ? 0 : 2),
          .C_WACH_TYPE(((C_AXI_WRITE_FIFO_DEPTH != 0) && C_AXI_WRITE_FIFO_DELAY) ? 0 : 2),
          .C_WDCH_TYPE((C_AXI_WRITE_FIFO_DEPTH != 0) ? 0 : 2),
          .C_RDCH_TYPE((C_AXI_READ_FIFO_DEPTH != 0) ? 0 : 2),
          .C_WRCH_TYPE(2),
          .C_COMMON_CLOCK(1),
          .C_ADD_NGC_CONSTRAINT(0),
          .C_APPLICATION_TYPE_AXIS(0),
          .C_APPLICATION_TYPE_RACH(C_AXI_READ_FIFO_DELAY ? 1 : 0),
          .C_APPLICATION_TYPE_RDCH(0),
          .C_APPLICATION_TYPE_WACH(C_AXI_WRITE_FIFO_DELAY ? 1 : 0),
          .C_APPLICATION_TYPE_WDCH(0),
          .C_APPLICATION_TYPE_WRCH(0),
          .C_AXIS_TDATA_WIDTH(64),
          .C_AXIS_TDEST_WIDTH(4),
          .C_AXIS_TID_WIDTH(8),
          .C_AXIS_TKEEP_WIDTH(4),
          .C_AXIS_TSTRB_WIDTH(4),
          .C_AXIS_TUSER_WIDTH(4),
          .C_AXIS_TYPE(0),
          .C_COUNT_TYPE(0),
          .C_DATA_COUNT_WIDTH(10),
          .C_DEFAULT_VALUE("BlankString"),
          .C_DIN_WIDTH(18),
          .C_DIN_WIDTH_AXIS(1),
          .C_DOUT_RST_VAL("0"),
          .C_DOUT_WIDTH(18),
          .C_ENABLE_RLOCS(0),
          .C_ENABLE_RST_SYNC(1),
          .C_ERROR_INJECTION_TYPE(0),
          .C_ERROR_INJECTION_TYPE_AXIS(0),
          .C_ERROR_INJECTION_TYPE_RACH(0),
          .C_ERROR_INJECTION_TYPE_RDCH(0),
          .C_ERROR_INJECTION_TYPE_WACH(0),
          .C_ERROR_INJECTION_TYPE_WDCH(0),
          .C_ERROR_INJECTION_TYPE_WRCH(0),
          .C_FAMILY(C_FAMILY),
          .C_FULL_FLAGS_RST_VAL(1),
          .C_HAS_ALMOST_EMPTY(0),
          .C_HAS_ALMOST_FULL(0),
          .C_HAS_AXI_RD_CHANNEL(1),
          .C_HAS_AXI_WR_CHANNEL(1),
          .C_HAS_AXIS_TDATA(0),
          .C_HAS_AXIS_TDEST(0),
          .C_HAS_AXIS_TID(0),
          .C_HAS_AXIS_TKEEP(0),
          .C_HAS_AXIS_TLAST(0),
          .C_HAS_AXIS_TREADY(1),
          .C_HAS_AXIS_TSTRB(0),
          .C_HAS_AXIS_TUSER(0),
          .C_HAS_BACKUP(0),
          .C_HAS_DATA_COUNT(0),
          .C_HAS_DATA_COUNTS_AXIS(0),
          .C_HAS_DATA_COUNTS_RACH(0),
          .C_HAS_DATA_COUNTS_RDCH(0),
          .C_HAS_DATA_COUNTS_WACH(0),
          .C_HAS_DATA_COUNTS_WDCH(0),
          .C_HAS_DATA_COUNTS_WRCH(0),
          .C_HAS_INT_CLK(0),
          .C_HAS_MASTER_CE(0),
          .C_HAS_MEMINIT_FILE(0),
          .C_HAS_OVERFLOW(0),
          .C_HAS_PROG_FLAGS_AXIS(0),
          .C_HAS_PROG_FLAGS_RACH(0),
          .C_HAS_PROG_FLAGS_RDCH(0),
          .C_HAS_PROG_FLAGS_WACH(0),
          .C_HAS_PROG_FLAGS_WDCH(0),
          .C_HAS_PROG_FLAGS_WRCH(0),
          .C_HAS_RD_DATA_COUNT(0),
          .C_HAS_RD_RST(0),
          .C_HAS_RST(1),
          .C_HAS_SLAVE_CE(0),
          .C_HAS_SRST(0),
          .C_HAS_UNDERFLOW(0),
          .C_HAS_VALID(0),
          .C_HAS_WR_ACK(0),
          .C_HAS_WR_DATA_COUNT(0),
          .C_HAS_WR_RST(0),
          .C_IMPLEMENTATION_TYPE(0),
          .C_IMPLEMENTATION_TYPE_AXIS(1),
          .C_IMPLEMENTATION_TYPE_RACH(2),
          .C_IMPLEMENTATION_TYPE_RDCH((C_AXI_READ_FIFO_TYPE == "bram") ? 1 : 2),
          .C_IMPLEMENTATION_TYPE_WACH(2),
          .C_IMPLEMENTATION_TYPE_WDCH((C_AXI_WRITE_FIFO_TYPE == "bram") ? 1 : 2),
          .C_IMPLEMENTATION_TYPE_WRCH(2),
          .C_INIT_WR_PNTR_VAL(0),
          .C_MEMORY_TYPE(1),
          .C_MIF_FILE_NAME("BlankString"),
          .C_MSGON_VAL(1),
          .C_OPTIMIZATION_MODE(0),
          .C_OVERFLOW_LOW(0),
          .C_PRELOAD_LATENCY(1),
          .C_PRELOAD_REGS(0),
          .C_PRIM_FIFO_TYPE(P_PRIM_FIFO_TYPE),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL(2),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1022),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(30),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(510),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(30),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(510),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(14),
          .C_PROG_EMPTY_THRESH_NEGATE_VAL(3),
          .C_PROG_EMPTY_TYPE(0),
          .C_PROG_EMPTY_TYPE_AXIS(5),
          .C_PROG_EMPTY_TYPE_RACH(5),
          .C_PROG_EMPTY_TYPE_RDCH(5),
          .C_PROG_EMPTY_TYPE_WACH(5),
          .C_PROG_EMPTY_TYPE_WDCH(5),
          .C_PROG_EMPTY_TYPE_WRCH(5),
          .C_PROG_FULL_THRESH_ASSERT_VAL(1022),
          .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
          .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(31),
          .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(511),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(31),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(511),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(15),
          .C_PROG_FULL_THRESH_NEGATE_VAL(1021),
          .C_PROG_FULL_TYPE(0),
          .C_PROG_FULL_TYPE_AXIS(5),
          .C_PROG_FULL_TYPE_RACH(5),
          .C_PROG_FULL_TYPE_RDCH(5),
          .C_PROG_FULL_TYPE_WACH(5),
          .C_PROG_FULL_TYPE_WDCH(5),
          .C_PROG_FULL_TYPE_WRCH(5),
          .C_RD_DATA_COUNT_WIDTH(10),
          .C_RD_DEPTH(1024),
          .C_RD_FREQ(1),
          .C_RD_PNTR_WIDTH(10),
          .C_REG_SLICE_MODE_AXIS(0),
          .C_REG_SLICE_MODE_RACH(0),
          .C_REG_SLICE_MODE_RDCH(0),
          .C_REG_SLICE_MODE_WACH(0),
          .C_REG_SLICE_MODE_WDCH(0),
          .C_REG_SLICE_MODE_WRCH(0),
          .C_UNDERFLOW_LOW(0),
          .C_USE_COMMON_OVERFLOW(0),
          .C_USE_COMMON_UNDERFLOW(0),
          .C_USE_DEFAULT_SETTINGS(0),
          .C_USE_DOUT_RST(1),
          .C_USE_ECC(0),
          .C_USE_ECC_AXIS(0),
          .C_USE_ECC_RACH(0),
          .C_USE_ECC_RDCH(0),
          .C_USE_ECC_WACH(0),
          .C_USE_ECC_WDCH(0),
          .C_USE_ECC_WRCH(0),
          .C_USE_EMBEDDED_REG(0),
          .C_USE_FIFO16_FLAGS(0),
          .C_USE_FWFT_DATA_COUNT(0),
          .C_VALID_LOW(0),
          .C_WR_ACK_LOW(0),
          .C_WR_DATA_COUNT_WIDTH(10),
          .C_WR_DEPTH(1024),
          .C_WR_DEPTH_AXIS(1024),
          .C_WR_DEPTH_RACH(32),
          .C_WR_DEPTH_RDCH(C_AXI_READ_FIFO_DEPTH),
          .C_WR_DEPTH_WACH(32),
          .C_WR_DEPTH_WDCH(C_AXI_WRITE_FIFO_DEPTH),
          .C_WR_DEPTH_WRCH(16),
          .C_WR_FREQ(1),
          .C_WR_PNTR_WIDTH(10),
          .C_WR_PNTR_WIDTH_AXIS(10),
          .C_WR_PNTR_WIDTH_RACH(5),
          .C_WR_PNTR_WIDTH_RDCH((C_AXI_READ_FIFO_DEPTH> 1) ? f_ceil_log2(C_AXI_READ_FIFO_DEPTH) : 1),
          .C_WR_PNTR_WIDTH_WACH(5),
          .C_WR_PNTR_WIDTH_WDCH((C_AXI_WRITE_FIFO_DEPTH > 1) ? f_ceil_log2(C_AXI_WRITE_FIFO_DEPTH) : 1),
          .C_WR_PNTR_WIDTH_WRCH(4),
          .C_WR_RESPONSE_LATENCY(1)
        )
        fifo_gen_inst (
          .s_aclk(aclk),
          .s_aresetn(aresetn),
          .s_axi_awid(s_axi_awid),
          .s_axi_awaddr(s_axi_awaddr),
          .s_axi_awlen(s_axi_awlen),
          .s_axi_awsize(s_axi_awsize),
          .s_axi_awburst(s_axi_awburst),
          .s_axi_awlock(s_axi_awlock),
          .s_axi_awcache(s_axi_awcache),
          .s_axi_awprot(s_axi_awprot),
          .s_axi_awqos(s_axi_awqos),
          .s_axi_awregion(s_axi_awregion_i),
          .s_axi_awuser(s_axi_awuser),
          .s_axi_awvalid(s_axi_awvalid),
          .s_axi_awready(s_axi_awready),
          .s_axi_wid(s_axi_wid_i),
          .s_axi_wdata(s_axi_wdata),
          .s_axi_wstrb(s_axi_wstrb),
          .s_axi_wlast(s_axi_wlast),
          .s_axi_wvalid(s_axi_wvalid),
          .s_axi_wready(s_axi_wready),
          .s_axi_bid(s_axi_bid),
          .s_axi_bresp(s_axi_bresp),
          .s_axi_bvalid(s_axi_bvalid),
          .s_axi_bready(s_axi_bready),
          .m_axi_awid(m_axi_awid),
          .m_axi_awaddr(m_axi_awaddr),
          .m_axi_awlen(m_axi_awlen),
          .m_axi_awsize(m_axi_awsize),
          .m_axi_awburst(m_axi_awburst),
          .m_axi_awlock(m_axi_awlock),
          .m_axi_awcache(m_axi_awcache),
          .m_axi_awprot(m_axi_awprot),
          .m_axi_awqos(m_axi_awqos),
          .m_axi_awregion(m_axi_awregion_i),
          .m_axi_awuser(m_axi_awuser),
          .m_axi_awvalid(m_axi_awvalid),
          .m_axi_awready(m_axi_awready),
          .m_axi_wid(m_axi_wid_i),
          .m_axi_wdata(m_axi_wdata),
          .m_axi_wstrb(m_axi_wstrb),
          .m_axi_wlast(m_axi_wlast),
          .m_axi_wvalid(m_axi_wvalid),
          .m_axi_wready(m_axi_wready),
          .m_axi_bid(m_axi_bid),
          .m_axi_bresp(m_axi_bresp),
          .m_axi_bvalid(m_axi_bvalid),
          .m_axi_bready(m_axi_bready),
          .s_axi_arid(s_axi_arid),
          .s_axi_araddr(s_axi_araddr),
          .s_axi_arlen(s_axi_arlen),
          .s_axi_arsize(s_axi_arsize),
          .s_axi_arburst(s_axi_arburst),
          .s_axi_arlock(s_axi_arlock),
          .s_axi_arcache(s_axi_arcache),
          .s_axi_arprot(s_axi_arprot),
          .s_axi_arqos(s_axi_arqos),
          .s_axi_arregion(s_axi_arregion_i),
          .s_axi_arvalid(s_axi_arvalid),
          .s_axi_arready(s_axi_arready),
          .s_axi_rid(s_axi_rid),
          .s_axi_rdata(s_axi_rdata),
          .s_axi_rresp(s_axi_rresp),
          .s_axi_rlast(s_axi_rlast),
          .s_axi_rvalid(s_axi_rvalid),
          .s_axi_rready(s_axi_rready),
          .m_axi_arid(m_axi_arid),
          .m_axi_araddr(m_axi_araddr),
          .m_axi_arlen(m_axi_arlen),
          .m_axi_arsize(m_axi_arsize),
          .m_axi_arburst(m_axi_arburst),
          .m_axi_arlock(m_axi_arlock),
          .m_axi_arcache(m_axi_arcache),
          .m_axi_arprot(m_axi_arprot),
          .m_axi_arqos(m_axi_arqos),
          .m_axi_arregion(m_axi_arregion_i),
          .m_axi_arvalid(m_axi_arvalid),
          .m_axi_arready(m_axi_arready),
          .m_axi_rid(m_axi_rid),
          .m_axi_rdata(m_axi_rdata),
          .m_axi_rresp(m_axi_rresp),
          .m_axi_rlast(m_axi_rlast),
          .m_axi_rvalid(m_axi_rvalid),
          .m_axi_rready(m_axi_rready),
          .m_aclk(aclk),
          .m_aclk_en(1'b1),
          .s_aclk_en(1'b1),
          .s_axi_wuser(s_axi_wuser),
          .s_axi_buser(s_axi_buser),
          .m_axi_wuser(m_axi_wuser),
          .m_axi_buser(m_axi_buser),
          .s_axi_aruser(s_axi_aruser),
          .s_axi_ruser(s_axi_ruser),
          .m_axi_aruser(m_axi_aruser),
          .m_axi_ruser(m_axi_ruser),
          .almost_empty(),
          .almost_full(),
          .axis_data_count(),
          .axis_dbiterr(),
          .axis_injectdbiterr(1'b0),
          .axis_injectsbiterr(1'b0),
          .axis_overflow(),
          .axis_prog_empty(),
          .axis_prog_empty_thresh(10'b0),
          .axis_prog_full(),
          .axis_prog_full_thresh(10'b0),
          .axis_rd_data_count(),
          .axis_sbiterr(),
          .axis_underflow(),
          .axis_wr_data_count(),
          .axi_ar_data_count(),
          .axi_ar_dbiterr(),
          .axi_ar_injectdbiterr(1'b0),
          .axi_ar_injectsbiterr(1'b0),
          .axi_ar_overflow(),
          .axi_ar_prog_empty(),
          .axi_ar_prog_empty_thresh(5'b0),
          .axi_ar_prog_full(),
          .axi_ar_prog_full_thresh(5'b0),
          .axi_ar_rd_data_count(),
          .axi_ar_sbiterr(),
          .axi_ar_underflow(),
          .axi_ar_wr_data_count(),
          .axi_aw_data_count(),
          .axi_aw_dbiterr(),
          .axi_aw_injectdbiterr(1'b0),
          .axi_aw_injectsbiterr(1'b0),
          .axi_aw_overflow(),
          .axi_aw_prog_empty(),
          .axi_aw_prog_empty_thresh(5'b0),
          .axi_aw_prog_full(),
          .axi_aw_prog_full_thresh(5'b0),
          .axi_aw_rd_data_count(),
          .axi_aw_sbiterr(),
          .axi_aw_underflow(),
          .axi_aw_wr_data_count(),
          .axi_b_data_count(),
          .axi_b_dbiterr(),
          .axi_b_injectdbiterr(1'b0),
          .axi_b_injectsbiterr(1'b0),
          .axi_b_overflow(),
          .axi_b_prog_empty(),
          .axi_b_prog_empty_thresh(4'b0),
          .axi_b_prog_full(),
          .axi_b_prog_full_thresh(4'b0),
          .axi_b_rd_data_count(),
          .axi_b_sbiterr(),
          .axi_b_underflow(),
          .axi_b_wr_data_count(),
          .axi_r_data_count(),
          .axi_r_dbiterr(),
          .axi_r_injectdbiterr(1'b0),
          .axi_r_injectsbiterr(1'b0),
          .axi_r_overflow(),
          .axi_r_prog_empty(),
          .axi_r_prog_empty_thresh({P_READ_FIFO_DEPTH_LOG{1'b0}}),
          .axi_r_prog_full(),
          .axi_r_prog_full_thresh({P_READ_FIFO_DEPTH_LOG{1'b0}}),
          .axi_r_rd_data_count(),
          .axi_r_sbiterr(),
          .axi_r_underflow(),
          .axi_r_wr_data_count(),
          .axi_w_data_count(),
          .axi_w_dbiterr(),
          .axi_w_injectdbiterr(1'b0),
          .axi_w_injectsbiterr(1'b0),
          .axi_w_overflow(),
          .axi_w_prog_empty(),
          .axi_w_prog_empty_thresh({P_WRITE_FIFO_DEPTH_LOG{1'b0}}),
          .axi_w_prog_full(),
          .axi_w_prog_full_thresh({P_WRITE_FIFO_DEPTH_LOG{1'b0}}),
          .axi_w_rd_data_count(),
          .axi_w_sbiterr(),
          .axi_w_underflow(),
          .axi_w_wr_data_count(),
          .backup(1'b0),
          .backup_marker(1'b0),
          .clk(1'b0),
          .data_count(),
          .dbiterr(),
          .din(18'b0),
          .dout(),
          .empty(),
          .full(),
          .injectdbiterr(1'b0),
          .injectsbiterr(1'b0),
          .int_clk(1'b0),
          .m_axis_tdata(),
          .m_axis_tdest(),
          .m_axis_tid(),
          .m_axis_tkeep(),
          .m_axis_tlast(),
          .m_axis_tready(1'b0),
          .m_axis_tstrb(),
          .m_axis_tuser(),
          .m_axis_tvalid(),
          .overflow(),
          .prog_empty(),
          .prog_empty_thresh(10'b0),
          .prog_empty_thresh_assert(10'b0),
          .prog_empty_thresh_negate(10'b0),
          .prog_full(),
          .prog_full_thresh(10'b0),
          .prog_full_thresh_assert(10'b0),
          .prog_full_thresh_negate(10'b0),
          .rd_clk(1'b0),
          .rd_data_count(),
          .rd_en(1'b0),
          .rd_rst(1'b0),
          .rst(1'b0),
          .sbiterr(),
          .srst(1'b0),
          .s_axis_tdata(64'b0),
          .s_axis_tdest(4'b0),
          .s_axis_tid(8'b0),
          .s_axis_tkeep(4'b0),
          .s_axis_tlast(1'b0),
          .s_axis_tready(),
          .s_axis_tstrb(4'b0),
          .s_axis_tuser(4'b0),
          .s_axis_tvalid(1'b0),
          .underflow(),
          .valid(),
          .wr_ack(),
          .wr_clk(1'b0),
          .wr_data_count(),
          .wr_en(1'b0),
          .wr_rst(1'b0),
          .wr_rst_busy(),
          .rd_rst_busy(),
          .sleep(1'b0)
        );
    end
  endgenerate
endmodule



