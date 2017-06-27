//*****************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
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
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_byte_wrapper.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR3 SDRAM & DDR4 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_xiphy_byte_wrapper top level module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_phy_v2_2_0_xiphy_byte_wrapper #(

  //COMMON
  parameter          ENABLE_PRE_EMPHASIS = "FALSE",                                                        // Pre-emphasis output
  parameter integer  DATA_WIDTH         = 8,                                                            // Parallel input data width 2,4,8 bits
  parameter real     REFCLK_FREQ        = 300.0,                                                        // Clock frequency in MHz
  parameter          TBYTE_CTL          = "TBYTE_IN",                                                   // TBYTE_IN, T, Oserdes defaults to TBYTE_IN       
  parameter          DELAY_TYPE         = "FIXED",                                                      // Delay mode of delay FIXED, VARIABLE, VAR_LOAD
  parameter          DELAY_FORMAT       = "TIME",                                                       // TIME (mc_fixed_dly_ratio = (2*9)*(1000000/REFCLK_FREQ/DELAY_VAL), 
  //                                                                                                       COUNT (mc_fixed_delay_ratio={9'b0, DELAY_VAL}
  parameter          UPDATE_MODE        = "ASYNC",                                                      // ASYNC (mc_le_manual=0,mc_le_async=1), SYNC(mc_le_manual=0,mc_le_sync=0), 
  //                                                                                                       MANUAL (mc_le_manual=1,mc_le_async=0)
  parameter          PLLCLK_SRC         = 1'b0,                                                         // One of two PLL_CLK 0: pll_clk0, 1 : pll_clk1
  parameter          RXTX_BITSLICE_EN   = 13'b1111111111111,                                            // Skip bit, skip nibble (13'b1111111_000000 or 13'b0000000_111111) and skip byte (13'b0000000_000000)
  //BITSLICE (per RXTX and TRISTATE BITSLICE)
  parameter          GCLK_SRC           = 45'b000_000_000_000_000_000_000_000_000_000_000_000_000_000_000, // Per-RxTx(Tristate)_bitslice idelay global clock
  parameter          DCI_SRC            = 13'b0000000000000,                                            // Per-bit IOB ODT source 0:fabric, 1:control  
  parameter          INIT               = 15'b111111111111111,                                          // Per-Tx(Tristate) bitslice osersdes initial value 1'b0, 1'b1 
  parameter          RX_DATA_TYPE       = 15'b000000_00_00000_00,                                       // Bit 0 or 6 Data Type 00:NONE, 01:DATA(DQ_EN), 10:CLOCK(DQS_EN), 11:DATA_AND_CLOCK
  //                                                                                                       Bit 1-5 or 7-12 Data Type 0:SERIAL, 1:DATA(DQ_EN)
  parameter integer  RX_DELAY_VAL[12:0] = '{0,0,0,0,0,0,0,0,0,0,0,0,0},                                 // Desired odelay value 0 to 1250 pico sec                   
  parameter integer  TX_DELAY_VAL[12:0] = '{0,0,0,0,0,0,0,0,0,0,0,0,0},                                 // Desired idelay value 0 to 1250 pico sec                 
  parameter integer  TRI_DELAY_VAL[1:0] = '{0,0},                                                       // Desired tristate odelay value 0 to 1250 pico sec                   
  parameter          TX_OUTPUT_PHASE_90 = 13'b0000000000000,                                            // Delay output phase by 90 degree per-bitslice 1:TRUE, 0:FALSE
  parameter          TRI_OUTPUT_PHASE_90 = 2'b00,                                                       // Delay output phase by 90 degree per-tristate bitslice 1:TRUE, 0:FALSE
  parameter          NATIVE_ODELAY_BYPASS = 13'b0000000000000,                                          // Bypass ODELAY in RXTX Bitslices 1:TRUE, 0:FALSE
  parameter          NATIVE_ODELAY_BYPASS_TRI = 2'b00,                                                  // Bypass ODELAY in Tristate Bitslices 1:TRUE, 0:FALSE
  parameter          FIFO_SYNC_MODE     = 13'b0000000000000,                                            // Per-bit asynchronous read/write clocks, 0:FALSE (async mode), 1: TRUE (sync mode) 
  //BITSLICE_CONTROL (Per Nibble
  parameter          EN_OTHER_PCLK      = 2'b00,                                                        // PCLK from other bitslice control nibble 0=FALSE (not used), 1=TRUE (used)
  parameter          EN_OTHER_NCLK      = 2'b00,                                                        // NCLK from other bitslice control nibble 0=FALSE (not used), 1=TRUE (used)  
  parameter          EN_DYN_ODLY_MODE   = 2'b00,                                                        // Dynamic LD, CE, INC Control of ODELAY 0=FALSE, 1=TRUE  
  parameter          SERIAL_MODE        = 2'b00,                                                        // SGMII mode per nibble 0:FALSE (memory), 1=TRUE (sgmii)   
  parameter          RX_CLK_PHASE_P     = 2'b00,                                                        // Shift read clock dqs_p wrt DQ per nibble 0:SHIFT_0 (no shift), 1:SHIFT_90 (90 shift)
  parameter          RX_CLK_PHASE_N     = 2'b00,                                                        // Shift read clock dqs_n wrt DQ per nibble 0:SHIFT_0 (no shift), 1:SHIFT_90 (90 shift)
  parameter          INV_RXCLK          = 2'b00,                                                        // Invert clock path from IOB to RX Bitslice per nibble  0:FALSE (no invert), 1:TRUE (invert) 
  parameter          TX_GATING          = 2'b00,                                                        // Wrclkgen clock gating per nibble 0: DISABLE (free running clock), 1: ENABLE (gated strobe) 
  parameter          RX_GATING          = 2'b11,                                                        // Read DQS gating per nibble 0: DISABLE (no dqs gating), 1: ENABLE (dqs gating on preamble)   
  parameter          SELF_CALIBRATE     = 2'b11,                                                        // BISC Self Calibration 0:DISABLE, 1: ENABLE    
  parameter integer  READ_IDLE_COUNT[1:0] = '{31, 31},                                                  // Gap count between read bursts for ODT disable 
  parameter          DIV_MODE           = 2'b00,                                                        // Controller mode div2/div4 0:DIV4, 1:DIV2
  parameter          REFCLK_SRC         = 2'b00,                                                        // Input clock for delay control 0:PLLCLK, 1:REFCLK
  parameter integer  ROUNDING_FACTOR[1:0] = '{16,16},                                                   // Rounding factor for Bisc 0 to 255
  parameter          CTRL_CLK           = 2'b11,                                                        // EXTERNAL(1): riu_clk or INTERNAL(0): local_div_clk
  parameter          EN_CLK_TO_EXT_NORTH = 2'b00,                                                       // Enable global clock forwarding to north for inter-byte clocking 0:DISABLE, 1:ENABLE 
  parameter          EN_CLK_TO_EXT_SOUTH = 2'b00,                                                       // Enable global clock forwarding to south for inter-byte clocking 0:DISABLE, 1:ENABLE   
  parameter          IDLY_VT_TRACK       = 2'b11,                                                       // Enable VT Tracking for IDELAYs in a nibble 0:FALSE, 1:TRUE   
  parameter          ODLY_VT_TRACK       = 2'b11,                                                       // Enable VT Tracking for ODELAYs in a nibble 0:FALSE, 1:TRUE   
  parameter          QDLY_VT_TRACK       = 2'b11,                                                       // Enable VT Tracking for Quarter DELAYs in a nibble 0:FALSE, 1:TRUE   
  parameter          RXGATE_EXTEND       = 2'b00,                                                       // Extend RX Gate for Extended Read Preamble 0:FALSE, 1:TRUE
  parameter          SIM_DEVICE          = "ULTRASCALE"
) (
 // clocks
  input  [12:0]      clb2phy_fifo_clk,                  // per-bit fifo clk
  input              clb2phy_ctrl_clk_upp,              // riu clock upp
  input              clb2phy_ctrl_clk_low,              // riu clock low
  input              clb2phy_ref_clk_upp,               // ref clk upp
  input              clb2phy_ref_clk_low,               // ref clk low
 // resets
  input              clb2phy_ctrl_rst_upp,              // control reset upp
  input              clb2phy_ctrl_rst_low,              // control reset low
  input  [1:0]       clb2phy_txbit_tri_rst,             // TX tri-state oserdes reset
  input  [12:0]      clb2phy_txbit_rst,                 // TX oserdes reset [12:6]= upper, [5:0]= lower
  input  [12:0]      clb2phy_rxbit_rst,                 // RX oserdes reset [12:7]= upper, [5:0]= lower

 // global clocks
  input              pll_clk0,                          // pll0 clkin
  input              pll_clk1,                          // pll1 clkin
  input  [5:0]       gclk_in,                           // global blocks

  input  [12:0]      iob2phy_d_in_byte,

 // TX write data
  input  [7:0]       clb2phy_wr_dq0,                    // TX write data
  input  [7:0]       clb2phy_wr_dq1,                    // TX write data
  input  [7:0]       clb2phy_wr_dq2,                    // TX write data
  input  [7:0]       clb2phy_wr_dq3,                    // TX write data
  input  [7:0]       clb2phy_wr_dq4,                    // TX write data
  input  [7:0]       clb2phy_wr_dq5,                    // TX write data
  input  [7:0]       clb2phy_wr_dq6,                    // TX write data
  input  [7:0]       clb2phy_wr_dq7,                    // TX write data
  input  [7:0]       clb2phy_wr_dq8,                    // TX write data
  input  [7:0]       clb2phy_wr_dq9,                    // TX write data
  input  [7:0]       clb2phy_wr_dq10,                   // TX write data
  input  [7:0]       clb2phy_wr_dq11,                   // TX write data
  input  [7:0]       clb2phy_wr_dq12,                   // TX write data

 // TX tristate data
  input  [3:0]       clb2phy_t_b_upp,                   // TX tristate upper active low
  input  [3:0]       clb2phy_t_b_low,                   // TX tristate lower active low

  input  [3:0]       clb2phy_rden_upp,                  // FOR DQS gating upper
  input  [3:0]       clb2phy_rden_low,                  // FOR DQS gating lower

 // ODT signals
  input  [6:0]       clb2phy_odt_upp,                   // ODT  inputs for upper.
  input  [6:0]       clb2phy_odt_low,                   // ODT  inputs for lower
  output [12:0]      phy2iob_odt_out_byte,              // ODT  output to IOB

 // RIU
  input  [5:0]       clb2riu_addr,
  input  [15:0]      clb2riu_wr_data,
  input              clb2riu_wr_en,
  output [15:0]      riu2clb_rd_data,
  output             riu2clb_valid,
  input              clb2riu_nibble_sel_upp,
  input              clb2riu_nibble_sel_low,

  input  [12:0]      clb2phy_fifo_rden,                // per-bit fifo readenable, previously nibble based  
  output [12:0]      phy2clb_fifo_empty,               // per-bit fifo empty, previously nibble based


  output [12:0]      phy2iob_t,
  output [12:0]      phy2iob_q_out_byte,
//  output [12:0]      phy2iob_q2_out_byte,            // Removed this port

 // FIFO write clock forwarded to fabric
  output [1:0]       phy2rclk_ss_divclk,                // FIFO write clock forwarded to fabric

 // IFIFO  output to fabric
  output [7:0]       phy2clb_rd_dq0,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq1,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq2,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq3,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq4,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq5,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq6,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq7,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq8,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq9,                    // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq10,                   // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq11,                   // FIFO  output to fabric
  output [7:0]       phy2clb_rd_dq12,                   // 13ths bit, no fifo
 
 // IDELAY standalone ports 
  input  [12:0]      clb2phy_idelay_rst,                // idelay reset  inputs
  input  [12:0]      clb2phy_idelay_ce,                 // idelay ce  inputs
  input  [12:0]      clb2phy_idelay_inc,                // idelay inc  inputs
  input  [12:0]      clb2phy_idelay_ld,                 // idelay ld  inputs
  input  [116:0]     clb2phy_idelay_cntvaluein,         // idelay cntvaluein  inputs
  output [116:0]     phy2clb_idelay_cntvalueout,        // idelay cntvalueout  outputs

  input  [12:0]      clb2phy_odelay_rst,                // odelay reset  inputs
  input  [12:0]      clb2phy_odelay_ce,                 // odelay ce  inputs
  input  [12:0]      clb2phy_odelay_inc,                // odelay inc  inputs
  input  [12:0]      clb2phy_odelay_ld,                 // odelay ld  inputs
  input  [116:0]     clb2phy_odelay_cntvaluein,         // odelay cntvaluein  inputs
  output [116:0]     phy2clb_odelay_cntvalueout,        // odelay cntvlaueout  output

  input  [12:0]      clb2phy_t_txbit,                   // Oserdes T  inputs

  input  [1:0]       clb2phy_tristate_odelay_rst,       // tristate odelay reset
  input  [1:0]       clb2phy_tristate_odelay_ce,        // tristate odelay ce
  input  [1:0]       clb2phy_tristate_odelay_inc,       // tristate odelay inc
  input  [1:0]       clb2phy_tristate_odelay_ld,        // tristate odelay ld
  input  [17:0]      clb2phy_tristate_odelay_cntvaluein,// tristate odelay cntvaluein
  output [17:0]      phy2clb_tristate_odelay_cntvalueout,// tristate odelay cntvalueout

  input  [3:0]       clb2phy_wrcs0_upp,                 // rank select 
  input  [3:0]       clb2phy_wrcs1_upp,                 // rank select
  input  [3:0]       clb2phy_wrcs0_low,                 // rank select
  input  [3:0]       clb2phy_wrcs1_low,                 // rank select
  input  [3:0]       clb2phy_rdcs0_upp,                 // rank select
  input  [3:0]       clb2phy_rdcs1_upp,                 // rank select
  input  [3:0]       clb2phy_rdcs0_low,                 // rank select
  input  [3:0]       clb2phy_rdcs1_low,                 // rank select

  output             phy2clb_fixdly_rdy_upp,
  output             phy2clb_fixdly_rdy_low,

// interbyte clocking signals
  input              clk_from_ext_low,                  // interbyte clocking
  input              clk_from_ext_upp,                  // interbyte clocking
  output             clk_to_ext_north_upp,              // interbyte clocking
  output             clk_to_ext_south_upp,              // interbyte clocking
  output             clk_to_ext_north_low,              // interbyte clocking
  output             clk_to_ext_south_low,              // interbyte clocking

// t_out from TX for test
//  output [14:0]      phy2clb_t_out,                     // t_out from 13 bitslices + 2 tri-state, 15 bits total  

`ifdef BISC_CHAIN_EN
// BISC chain IO
  input              bisc_start_in,
  input              bisc_stop_in,
  output reg         bisc_start_out,
  output reg         bisc_stop_out,
`endif

// delaycontrol ports
  input  [12:0]      clb2phy_idelay_en_vtc,             // idelay en vtc control
  input  [12:0]      clb2phy_odelay_en_vtc,             // odelay en vtc control
  input  [1:0]       clb2phy_odelay_tristate_en_vtc,    // tristate en vtc control

  input              clb2phy_dlyctl_en_vtc_upp,       
  input              clb2phy_dlyctl_en_vtc_low,
  output             phy2clb_phy_rdy_upp,
  output             phy2clb_phy_rdy_low 
);

//assign phy2iob_q2_out_byte = 13'b0;  // this port has to be deleted in wrappers above. Until then driving a zero. 

`ifdef BISC_CHAIN_EN
reg bisc_start_out_0;
reg bisc_stop_out_1;
//BISC start chain implementation within a byte
generate
if (|RXTX_BITSLICE_EN[5:0]) begin: bisc_start_0
  always @(*) begin
    release I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_in;
    force I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_in 
          = bisc_start_in;
    bisc_start_out_0
          = I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_out;
  end
end else begin
  always @(*) begin
    bisc_start_out_0 = bisc_start_in;
  end
end

if (|RXTX_BITSLICE_EN[12:6]) begin: bisc_start_1
  always @(*) begin
    release I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_in;
    force I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_in 
          = bisc_start_out_0;
    bisc_start_out
          = I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_start_out;
  end 
end else begin
  always @(*) begin
    bisc_start_out = bisc_start_out_0;
  end
end

//BISC stop chain implementation within a byte
if (|RXTX_BITSLICE_EN[12:6]) begin: bisc_stop_1
  always @(*) begin
    release I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_in;
    force I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_in
          = bisc_stop_in;
    bisc_stop_out_1 
          = I_CONTROL[1].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_out;
  end
end else begin
  always @(*) begin
    bisc_stop_out_1 = bisc_stop_in;
  end
end

if (|RXTX_BITSLICE_EN[5:0]) begin: bisc_stop_0
  always @(*) begin
    release I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_in;
    force I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_in
          = bisc_stop_out_1;
    bisc_stop_out
          = I_CONTROL[0].GEN_I_CONTROL.u_xiphy_control.xiphy_control.SHIP.BUT.bisc_stop_out;
  end  
end else begin
  always @(*) begin
    bisc_stop_out = bisc_stop_out_1;
  end
end

endgenerate
`endif

wire [3:0] clb2phy_rdcs0_nibble [1:0]; 
wire [3:0] clb2phy_rdcs1_nibble [1:0]; 
wire [3:0] clb2phy_wrcs0_nibble [1:0]; 
wire [3:0] clb2phy_wrcs1_nibble [1:0];
assign clb2phy_rdcs0_nibble[1] = clb2phy_rdcs0_upp; 
assign clb2phy_wrcs0_nibble[1] = clb2phy_wrcs0_upp;
assign clb2phy_rdcs0_nibble[0] = clb2phy_rdcs0_low; 
assign clb2phy_wrcs0_nibble[0] = clb2phy_wrcs0_low; 
assign clb2phy_rdcs1_nibble[1] = clb2phy_rdcs1_upp; 
assign clb2phy_wrcs1_nibble[1] = clb2phy_wrcs1_upp;
assign clb2phy_rdcs1_nibble[0] = clb2phy_rdcs1_low; 
assign clb2phy_wrcs1_nibble[0] = clb2phy_wrcs1_low; 


wire [1:0] pdqs_gt_out;
wire [1:0] ndqs_gt_out;
wire [1:0] pdqs_gt_in;
wire [1:0] ndqs_gt_in;
`ifndef SYN
assign pdqs_gt_in[1] = (|RXTX_BITSLICE_EN[5:0]) ? pdqs_gt_out[0] : 1'b0;
assign ndqs_gt_in[1] = (|RXTX_BITSLICE_EN[5:0]) ? ndqs_gt_out[0] : 1'b0;
assign pdqs_gt_in[0] = (|RXTX_BITSLICE_EN[12:6]) ? pdqs_gt_out[1] : 1'b0;
assign ndqs_gt_in[0] = (|RXTX_BITSLICE_EN[12:6]) ? ndqs_gt_out[1] : 1'b0;
`else
assign pdqs_gt_in[1] = (|RXTX_BITSLICE_EN[5:0]) ? pdqs_gt_out[0] : 1'bz;
assign ndqs_gt_in[1] = (|RXTX_BITSLICE_EN[5:0]) ? ndqs_gt_out[0] : 1'bz;
assign pdqs_gt_in[0] = (|RXTX_BITSLICE_EN[12:6]) ? pdqs_gt_out[1] : 1'bz;
assign ndqs_gt_in[0] = (|RXTX_BITSLICE_EN[12:6]) ? ndqs_gt_out[1] : 1'bz;
`endif

//Resolved multiple driver issue
/* assign pdqs_gt_out[1] = pdqs_gt_in[0];
assign ndqs_gt_out[1] = ndqs_gt_in[0];
assign pdqs_gt_out[0] = pdqs_gt_in[1];
assign ndqs_gt_out[0] = ndqs_gt_in[1]; */

wire [1:0] clk_from_ext;
assign clk_from_ext[1] = clk_from_ext_upp;
assign clk_from_ext[0] = clk_from_ext_low;

wire [1:0] clk_to_ext_south;
assign clk_to_ext_south_upp = clk_to_ext_south[1];
assign clk_to_ext_south_low = clk_to_ext_south[0];

wire [1:0] clk_to_ext_north;
assign clk_to_ext_north_upp = clk_to_ext_north[1];
assign clk_to_ext_north_low = clk_to_ext_north[0];

wire [15:0] riu2clb_rd_data_array [1:0];
wire [15:0] riu2clb_rd_data_upp;
wire [15:0] riu2clb_rd_data_low;
assign riu2clb_rd_data_upp = riu2clb_rd_data_array[1];
assign riu2clb_rd_data_low = riu2clb_rd_data_array[0];

wire [1:0] riu2clb_valid_array;
wire riu2clb_valid_upp;
wire riu2clb_valid_low;
assign riu2clb_valid_upp = riu2clb_valid_array[1];
assign riu2clb_valid_low = riu2clb_valid_array[0];

wire [1:0] pll_clk;
assign pll_clk[1] = PLLCLK_SRC == 1'b0 ? pll_clk0 : pll_clk1;   // Inverter of the Inverting MUX pushed into BLH Model
assign pll_clk[0] = PLLCLK_SRC == 1'b0 ? pll_clk0 : pll_clk1;

// ****************************************************************
// gclk 6:1 mux for txrx clkdiv (tx_clk, rx_clk) 
// ****************************************************************
wire [12:0]  gclk_mux_txrx_clkdiv;       //[12:0] for bitslices
genvar j ;
wire [2:0] sel[12:0]; 
generate
for (j=0; j <=12; j=j+1)
   if (RXTX_BITSLICE_EN[j]) begin: MUX_6TO1_TXRX_CLKDIV
   assign sel[j] = GCLK_SRC[((j+1)*3 -1): j*3]; 
   assign gclk_mux_txrx_clkdiv[j] = sel[j] == 3'b000 ? gclk_in[0] : sel[j] == 3'b001 ? gclk_in[1] : sel[j] == 3'b010 ? gclk_in[2] : sel[j] == 3'b011 ? gclk_in[3]: sel[j] == 3'b100 ? gclk_in[4]: sel[j] == 3'b101 ? gclk_in[5] : 1'bx;      
   end
endgenerate

wire [1:0]  gclk_mux_tx_clkdiv_tri;       //for tri bitslices
genvar t ;
wire [2:0] sel_tri[1:0]; 
generate
for (t=0; t <=1; t=t+1)
   if (|RXTX_BITSLICE_EN[((t+1)*6-1+t):t*6]) begin: MUX_6TO1_TXRX_CLKDIV_TRI
   assign sel_tri[t] = GCLK_SRC[((13+t+1)*3 -1): (13+t)*3]; 
   assign gclk_mux_tx_clkdiv_tri[t] = sel_tri[t] == 3'b000 ? gclk_in[0] : sel_tri[t] == 3'b001 ? gclk_in[1] : sel_tri[t] == 3'b010 ? gclk_in[2] : sel_tri[t] == 3'b011 ? gclk_in[3]: sel_tri[t] == 3'b100 ? gclk_in[4]: sel_tri[t] == 3'b101 ? gclk_in[5] : 1'bx;      
   end
endgenerate

//wire [1:0]  gclk_mux_tx_clkdiv_tri;
//assign gclk_mux_tx_clkdiv_tri = {gclk_mux_txrx_clkdiv[14], gclk_mux_txrx_clkdiv[13]};

wire [6:0] ctl2iob_odt[1:0];
wire [6:0] ctl2iob_odt_upp;
wire [6:0] ctl2iob_odt_low;
assign ctl2iob_odt_upp = ctl2iob_odt[1];
assign ctl2iob_odt_low = ctl2iob_odt[0];

wire [6:0] phy2iob_odt_out_upp;
wire [5:0] phy2iob_odt_out_low;

// ****************************************************************
// DCI mux for upper control. Select between ctl2iob_odt_upp[6:0] 
// (from control) and clb2phy_odt_upp[6:0] (from fabric)
// ****************************************************************
genvar k;
generate
for (k=0; k <=6; k=k+1)
   if (RXTX_BITSLICE_EN[6+k]) begin: MUX_DCI_UPPER
     assign phy2iob_odt_out_upp[k] = DCI_SRC[6+k] ? ctl2iob_odt_upp[k] : clb2phy_odt_upp[k]; 
   end else begin
     assign phy2iob_odt_out_upp[k] = 0; 
   end
endgenerate

// ****************************************************************
// DCI mux for lower control. Select between ctl2iob_odt_low[6:0] 
// (from control) and clb2phy_odt_low[6:0] (from fabric)
// ****************************************************************
genvar p;
generate
for (p=0; p <=5; p=p+1)
   if (RXTX_BITSLICE_EN[p]) begin: MUX_DCI_LOWER
     assign phy2iob_odt_out_low[p] = DCI_SRC[p] ? ctl2iob_odt_low[p] : clb2phy_odt_low[p]; 
   end else begin
     assign phy2iob_odt_out_low[p] = 0; 
   end
endgenerate

assign phy2iob_odt_out_byte = {phy2iob_odt_out_upp, phy2iob_odt_out_low};

wire [1:0] clb2riu_nibble_sel;
assign clb2riu_nibble_sel[1] = clb2riu_nibble_sel_upp;
assign clb2riu_nibble_sel[0] = clb2riu_nibble_sel_low;

wire [1:0] clb2phy_ref_clk;
assign clb2phy_ref_clk[1] = clb2phy_ref_clk_upp;
assign clb2phy_ref_clk[0] = clb2phy_ref_clk_low;

wire [1:0] clb2phy_ctrl_clk;
assign clb2phy_ctrl_clk[1] = clb2phy_ctrl_clk_upp;
assign clb2phy_ctrl_clk[0] = clb2phy_ctrl_clk_low;

wire [1:0] clb2phy_ctrl_rst;
assign clb2phy_ctrl_rst[1] = clb2phy_ctrl_rst_upp;
assign clb2phy_ctrl_rst[0] = clb2phy_ctrl_rst_low;

wire [1:0] phy2clb_phy_rdy;
assign phy2clb_phy_rdy_upp = phy2clb_phy_rdy[1];
assign phy2clb_phy_rdy_low = phy2clb_phy_rdy[0];

wire [1:0] phy2clb_fixdly_rdy;
assign phy2clb_fixdly_rdy_upp = phy2clb_fixdly_rdy[1];
assign phy2clb_fixdly_rdy_low = phy2clb_fixdly_rdy[0];

wire [1:0] clb2phy_dlyctl_en_vtc;
assign clb2phy_dlyctl_en_vtc[1] = clb2phy_dlyctl_en_vtc_upp;
assign clb2phy_dlyctl_en_vtc[0] = clb2phy_dlyctl_en_vtc_low;

wire [3:0] clb2phy_t_b [1:0];            
assign clb2phy_t_b[1] = clb2phy_t_b_upp;
assign clb2phy_t_b[0] = clb2phy_t_b_low;

wire [3:0] clb2phy_rden [1:0];            
assign clb2phy_rden[0] = clb2phy_rden_low;
assign clb2phy_rden[1] = clb2phy_rden_upp;

wire [7:0] en_div_dly_oe [1:0];

wire [12:0] rx_ififo_wrclk;
assign phy2rclk_ss_divclk = {rx_ififo_wrclk[12], rx_ififo_wrclk[0]};

wire [7:0] rx_q_array_upper [6:0];   // 7 bitslices  for upper
wire [7:0] rx_q_array_lower [5:0];   // 6 bitslices  for lower

assign phy2clb_rd_dq0  = rx_q_array_lower[0];
assign phy2clb_rd_dq1  = rx_q_array_lower[1];
assign phy2clb_rd_dq2  = rx_q_array_lower[2];
assign phy2clb_rd_dq3  = rx_q_array_lower[3];
assign phy2clb_rd_dq4  = rx_q_array_lower[4];
assign phy2clb_rd_dq5  = rx_q_array_lower[5];

assign phy2clb_rd_dq6  = rx_q_array_upper[0];
assign phy2clb_rd_dq7  = rx_q_array_upper[1];
assign phy2clb_rd_dq8  = rx_q_array_upper[2];
assign phy2clb_rd_dq9  = rx_q_array_upper[3];
assign phy2clb_rd_dq10 = rx_q_array_upper[4];
assign phy2clb_rd_dq11 = rx_q_array_upper[5];
assign phy2clb_rd_dq12 = rx_q_array_upper[6];  // 13th bitslice identical to the rest 

//Not required as rx_p(n)dq[0-6]_in moved to rx_bit_ctrl_in ribbon cable  
//wire [7:0] rx_data_array [6:0][1:0];  // 2 d array

//assign rx_data_array[0][0] = rx_q_array_lower[0];
//assign rx_data_array[1][0] = rx_q_array_lower[1];
//assign rx_data_array[2][0] = rx_q_array_lower[2];
//assign rx_data_array[3][0] = rx_q_array_lower[3];
//assign rx_data_array[4][0] = rx_q_array_lower[4];
//assign rx_data_array[5][0] = rx_q_array_lower[5];
//assign rx_data_array[6][0] = 1'b0;
//assign rx_data_array[0][1] = rx_q_array_upper[0];
//assign rx_data_array[1][1] = rx_q_array_upper[1];
//assign rx_data_array[2][1] = rx_q_array_upper[2];
//assign rx_data_array[3][1] = rx_q_array_upper[3];
//assign rx_data_array[4][1] = rx_q_array_upper[4];
//assign rx_data_array[5][1] = rx_q_array_upper[5];
//assign rx_data_array[6][1] = rx_q_array_upper[6];

//assign phy2clb_rd_dq12 = rx_q_array_upper[6];  // 13th bitslice

wire [7:0] clb2phy_wr_dq_array [12:0];
assign clb2phy_wr_dq_array[0]  = clb2phy_wr_dq0;
assign clb2phy_wr_dq_array[1]  = clb2phy_wr_dq1;
assign clb2phy_wr_dq_array[2]  = clb2phy_wr_dq2;
assign clb2phy_wr_dq_array[3]  = clb2phy_wr_dq3;
assign clb2phy_wr_dq_array[4]  = clb2phy_wr_dq4;
assign clb2phy_wr_dq_array[5]  = clb2phy_wr_dq5;
assign clb2phy_wr_dq_array[6]  = clb2phy_wr_dq6;
assign clb2phy_wr_dq_array[7]  = clb2phy_wr_dq7;
assign clb2phy_wr_dq_array[8]  = clb2phy_wr_dq8;
assign clb2phy_wr_dq_array[9]  = clb2phy_wr_dq9;
assign clb2phy_wr_dq_array[10] = clb2phy_wr_dq10;
assign clb2phy_wr_dq_array[11] = clb2phy_wr_dq11;
assign clb2phy_wr_dq_array[12] = clb2phy_wr_dq12;

//wire [1:0] tristate_t_out;      // tri-state t_out to block out
//assign phy2clb_t_out = {tristate_t_out[1], tristate_t_out[0], phy2iob_t};  // 15 bits of t_out to block out

wire [1:0] tristate_q;

//Ribbon cable wire bus to all bitslices in nibble
//{pdqs_out, ndqs_out, ctrl_clk}
//wire [2:0] rx_nib_ctrl_out [1:0];
    
//Ribbon cable wire buses to per bitslice0-6
//{bs_reset, refclk_en[0-6], bs_dq_en[0-6], bs_dqs_en[0-6], ififo_bypass[0-6], idelay_ce_out[0-6], idelay_inc_out[0-6], idelay_ld_out[0-6], idelay00-06_out[8:0], rx_dcc[3:0]}
wire [39:0] rx_bit_ctrl_out0 [1:0];
wire [39:0] rx_bit_ctrl_out1 [1:0];
wire [39:0] rx_bit_ctrl_out2 [1:0];
wire [39:0] rx_bit_ctrl_out3 [1:0];
wire [39:0] rx_bit_ctrl_out4 [1:0];
wire [39:0] rx_bit_ctrl_out5 [1:0];
wire [39:0] rx_bit_ctrl_out6 [1:0];

wire [39:0] rx_bit_ctrl_to_bs_array [12:0];
assign rx_bit_ctrl_to_bs_array[0]  = rx_bit_ctrl_out0[0];
assign rx_bit_ctrl_to_bs_array[1]  = rx_bit_ctrl_out1[0];
assign rx_bit_ctrl_to_bs_array[2]  = rx_bit_ctrl_out2[0];
assign rx_bit_ctrl_to_bs_array[3]  = rx_bit_ctrl_out3[0];
assign rx_bit_ctrl_to_bs_array[4]  = rx_bit_ctrl_out4[0];
assign rx_bit_ctrl_to_bs_array[5]  = rx_bit_ctrl_out5[0];
assign rx_bit_ctrl_to_bs_array[6]  = rx_bit_ctrl_out0[1];
assign rx_bit_ctrl_to_bs_array[7]  = rx_bit_ctrl_out1[1];
assign rx_bit_ctrl_to_bs_array[8]  = rx_bit_ctrl_out2[1];
assign rx_bit_ctrl_to_bs_array[9]  = rx_bit_ctrl_out3[1];
assign rx_bit_ctrl_to_bs_array[10] = rx_bit_ctrl_out4[1];
assign rx_bit_ctrl_to_bs_array[11] = rx_bit_ctrl_out5[1];
assign rx_bit_ctrl_to_bs_array[12] = rx_bit_ctrl_out6[1];
    
//Ribbon cable wire buses from per bitslice0-6
//{rx_q[7], rx_q[3], fixdlyratio_idelay00-06[17:0], fixed_idelay00-06, bs2ctl_refclk_en_mask[0-6], bs2ctl_riu_bs_dq_en[0-6], bs2ctl_riu_bs_dqs_en[0-6], vtc_ready_idelay00-06, dqs_in, idelay00-06_in[8:0]}
wire [39:0] rx_bit_ctrl_in0 [1:0];
wire [39:0] rx_bit_ctrl_in1 [1:0];
wire [39:0] rx_bit_ctrl_in2 [1:0];
wire [39:0] rx_bit_ctrl_in3 [1:0];
wire [39:0] rx_bit_ctrl_in4 [1:0];
wire [39:0] rx_bit_ctrl_in5 [1:0];
wire [39:0] rx_bit_ctrl_in6 [1:0];

wire [39:0] rx_bit_bs_to_ctrl_array [12:0];
assign rx_bit_ctrl_in0[0] = rx_bit_bs_to_ctrl_array[0];
assign rx_bit_ctrl_in1[0] = rx_bit_bs_to_ctrl_array[1];
assign rx_bit_ctrl_in2[0] = rx_bit_bs_to_ctrl_array[2];
assign rx_bit_ctrl_in3[0] = rx_bit_bs_to_ctrl_array[3];
assign rx_bit_ctrl_in4[0] = rx_bit_bs_to_ctrl_array[4];
assign rx_bit_ctrl_in5[0] = rx_bit_bs_to_ctrl_array[5];
assign rx_bit_ctrl_in6[0] = 40'b0;
assign rx_bit_ctrl_in0[1] = rx_bit_bs_to_ctrl_array[6];
assign rx_bit_ctrl_in1[1] = rx_bit_bs_to_ctrl_array[7];
assign rx_bit_ctrl_in2[1] = rx_bit_bs_to_ctrl_array[8];
assign rx_bit_ctrl_in3[1] = rx_bit_bs_to_ctrl_array[9];
assign rx_bit_ctrl_in4[1] = rx_bit_bs_to_ctrl_array[10];
assign rx_bit_ctrl_in5[1] = rx_bit_bs_to_ctrl_array[11];
assign rx_bit_ctrl_in6[1] = rx_bit_bs_to_ctrl_array[12];

//Ribbon cable wire bus to TX bitslices in nibble
//{ddr_strb_out [1:0], div2_strb_out [1:0], div_clk_out [1:0], ctrl_clk}

//Ribbon cable output bus to 2nd & 13th TX bitslice
//{ddr_clk_out, div2_clk_out, div_clk_out, ctrl_clk}
//wire [3:0] tx_nib_ctrl_out [1:0];
//wire [3:0] tx_nib_ctrl_out6 [1:0];

//wire [3:0] tx_nib_ctrl_clk_out_array [12:0];

//assign tx_nib_ctrl_clk_out_array[0] = tx_nib_ctrl_out[0];   
//assign tx_nib_ctrl_clk_out_array[1] = tx_nib_ctrl_out6[0];   
//assign tx_nib_ctrl_clk_out_array[2] = tx_nib_ctrl_out[0];   
//assign tx_nib_ctrl_clk_out_array[3] = tx_nib_ctrl_out[0];   
//assign tx_nib_ctrl_clk_out_array[4] = tx_nib_ctrl_out[0];   
//assign tx_nib_ctrl_clk_out_array[5] = tx_nib_ctrl_out[0];   
//assign tx_nib_ctrl_clk_out_array[6] = tx_nib_ctrl_out[1];   
//assign tx_nib_ctrl_clk_out_array[7] = tx_nib_ctrl_out6[1];   
//assign tx_nib_ctrl_clk_out_array[8] = tx_nib_ctrl_out[1];   
//assign tx_nib_ctrl_clk_out_array[9] = tx_nib_ctrl_out[1];   
//assign tx_nib_ctrl_clk_out_array[10] = tx_nib_ctrl_out[1];   
//assign tx_nib_ctrl_clk_out_array[11] = tx_nib_ctrl_out[1];   
//assign tx_nib_ctrl_clk_out_array[12] = tx_nib_ctrl_out6[1];   



//Ribbon cable wire buses to per TX bitslice0-6
//{wl_train, tx_data_phase [0-6], bs_reset[0-6], ph02_div2_360, ph13_div2_360, ph0_div_720, ph1_div_720, ph2_div_720, ph3_div_720, \
//toggle_div2_sel, dynamic_mode_en , odelay_ce_out[0-6], odelay_inc_out[0-6], odelay_ld_out[0-6], odelay00-06_out[8:0]}
wire [39:0] tx_bit_ctrl_out0 [1:0];
wire [39:0] tx_bit_ctrl_out1 [1:0];
wire [39:0] tx_bit_ctrl_out2 [1:0];
wire [39:0] tx_bit_ctrl_out3 [1:0];
wire [39:0] tx_bit_ctrl_out4 [1:0];
wire [39:0] tx_bit_ctrl_out5 [1:0];
wire [39:0] tx_bit_ctrl_out6 [1:0];

wire [39:0] tx_bit_ctrl_to_bs_array [12:0];
assign tx_bit_ctrl_to_bs_array[0]  = tx_bit_ctrl_out0[0];
assign tx_bit_ctrl_to_bs_array[1]  = tx_bit_ctrl_out1[0];            
assign tx_bit_ctrl_to_bs_array[2]  = tx_bit_ctrl_out2[0];
assign tx_bit_ctrl_to_bs_array[3]  = tx_bit_ctrl_out3[0];
assign tx_bit_ctrl_to_bs_array[4]  = tx_bit_ctrl_out4[0];
assign tx_bit_ctrl_to_bs_array[5]  = tx_bit_ctrl_out5[0];
assign tx_bit_ctrl_to_bs_array[6]  = tx_bit_ctrl_out0[1];
assign tx_bit_ctrl_to_bs_array[7]  = tx_bit_ctrl_out1[1];
assign tx_bit_ctrl_to_bs_array[8]  = tx_bit_ctrl_out2[1];
assign tx_bit_ctrl_to_bs_array[9]  = tx_bit_ctrl_out3[1];
assign tx_bit_ctrl_to_bs_array[10] = tx_bit_ctrl_out4[1];
assign tx_bit_ctrl_to_bs_array[11] = tx_bit_ctrl_out5[1];
assign tx_bit_ctrl_to_bs_array[12] = tx_bit_ctrl_out6[1];

//Ribbon cable output bus from control to tristate bitslice
//{force_oe_b, en_div_dly_oe[7:0], tx_data_phase7, bs_reset_tri, ph02_div2_360, ph13_div2_360, ph0_div_720, ph1_div_720, ph2_div_720, ph3_div_720, \
//toggle_div2_sel, dynamic_mode_en, tristate_odelay_ce_out, tristate_odelay_inc_out, tristate_odelay_ld_out, tristate_odelay_out[8:0]}
wire [39:0] tx_bit_ctrl_out_tri [1:0];
wire [39:0] tx_bit_ctrl_to_tri_array [1:0];
assign tx_bit_ctrl_to_tri_array[0] = tx_bit_ctrl_out_tri[0];
assign tx_bit_ctrl_to_tri_array[1] = tx_bit_ctrl_out_tri[1];

//Ribbon cable wire buses to per TX bitslice0-6
//{bs2ctl_riu_tx_data_phase, fixdlyratio_odelay00-06[17:0], fixed_odelay00-06, vtc_ready_odelay00-06, odelay00-06_in[8:0]}
wire [39:0] tx_bit_ctrl_in0 [1:0];
wire [39:0] tx_bit_ctrl_in1 [1:0];
wire [39:0] tx_bit_ctrl_in2 [1:0];
wire [39:0] tx_bit_ctrl_in3 [1:0];
wire [39:0] tx_bit_ctrl_in4 [1:0];
wire [39:0] tx_bit_ctrl_in5 [1:0];
wire [39:0] tx_bit_ctrl_in6 [1:0];

wire [39:0] tx_bit_bs_to_ctrl_array [12:0];
assign tx_bit_ctrl_in0[0] = tx_bit_bs_to_ctrl_array[0];
assign tx_bit_ctrl_in1[0] = tx_bit_bs_to_ctrl_array[1];
assign tx_bit_ctrl_in2[0] = tx_bit_bs_to_ctrl_array[2];
assign tx_bit_ctrl_in3[0] = tx_bit_bs_to_ctrl_array[3];
assign tx_bit_ctrl_in4[0] = tx_bit_bs_to_ctrl_array[4];
assign tx_bit_ctrl_in5[0] = tx_bit_bs_to_ctrl_array[5];
assign tx_bit_ctrl_in6[0] = 40'b0;
assign tx_bit_ctrl_in0[1] = tx_bit_bs_to_ctrl_array[6];
assign tx_bit_ctrl_in1[1] = tx_bit_bs_to_ctrl_array[7];
assign tx_bit_ctrl_in2[1] = tx_bit_bs_to_ctrl_array[8];
assign tx_bit_ctrl_in3[1] = tx_bit_bs_to_ctrl_array[9];
assign tx_bit_ctrl_in4[1] = tx_bit_bs_to_ctrl_array[10];
assign tx_bit_ctrl_in5[1] = tx_bit_bs_to_ctrl_array[11];
assign tx_bit_ctrl_in6[1] = tx_bit_bs_to_ctrl_array[12];

//Ribbon cable input bus to tristate bitslice
//{bs2ctl_riu_tx_data_phase[7], tristate_vtc_ready, tristate_odelay_in[8:0]}
wire [39:0]  tx_bit_ctrl_in_tri [1:0];
wire [39:0]  tx_bit_tri_to_ctrl_array [1:0];
assign tx_bit_ctrl_in_tri[0] = tx_bit_tri_to_ctrl_array[0];
assign tx_bit_ctrl_in_tri[1] = tx_bit_tri_to_ctrl_array[1];

localparam [25:0] RDATA_TYPE = {1'b0, RX_DATA_TYPE[14], 1'b0, RX_DATA_TYPE[13], 1'b0, RX_DATA_TYPE[12], 1'b0, RX_DATA_TYPE[11], 1'b0, RX_DATA_TYPE[10], 1'b0, RX_DATA_TYPE[9], RX_DATA_TYPE[8:7], 1'b0, RX_DATA_TYPE[6], 1'b0, RX_DATA_TYPE[5], 1'b0, RX_DATA_TYPE[4], 1'b0, RX_DATA_TYPE[3], 1'b0, RX_DATA_TYPE[2], RX_DATA_TYPE[1:0]}; 

//*****************************************
//OR Gate For RIU Data and Control Outputs
//*****************************************

 ddr4_phy_v2_2_0_xiphy_riuor_wrapper #(
   .SIM_DEVICE  (SIM_DEVICE)
 ) u_xiphy_riuor (
`ifndef SYN
      .riu_rd_data_low    (|RXTX_BITSLICE_EN[5:0]  ? riu2clb_rd_data_low : 16'b0), 
      .riu_rd_data_upp    (|RXTX_BITSLICE_EN[12:6] ? riu2clb_rd_data_upp : 16'b0),     
      .riu_valid_low      (|RXTX_BITSLICE_EN[5:0]  ? riu2clb_valid_low   : 1'b1),
      .riu_valid_upp      (|RXTX_BITSLICE_EN[12:6] ? riu2clb_valid_upp   : 1'b1),
`else
      .riu_rd_data_low    (|RXTX_BITSLICE_EN[5:0]  ? riu2clb_rd_data_low : 16'bz), 
      .riu_rd_data_upp    (|RXTX_BITSLICE_EN[12:6] ? riu2clb_rd_data_upp : 16'bz),     
      .riu_valid_low      (|RXTX_BITSLICE_EN[5:0]  ? riu2clb_valid_low   : 1'bz),
      .riu_valid_upp      (|RXTX_BITSLICE_EN[12:6] ? riu2clb_valid_upp   : 1'bz),
`endif
      .riu_rd_data        (riu2clb_rd_data),
      .riu_valid          (riu2clb_valid)
 );

//**************************************************************************************
// Bitslice  lower  6 bitslices
//**************************************************************************************

genvar i_low;

generate for (i_low=0; i_low<=5; i_low=i_low+1)
   begin: I_BITSLICE_LOWER

   if (RXTX_BITSLICE_EN[i_low]) begin: GEN_RXTX_BITSLICE_EN

   ddr4_phy_v2_2_0_xiphy_bitslice_wrapper #(
      .FIFO_SYNC_MODE       ((FIFO_SYNC_MODE[i_low] == 1'b1) ? "TRUE" : "FALSE"),
      .ENABLE_PRE_EMPHASIS  (ENABLE_PRE_EMPHASIS),
      .RX_DATA_WIDTH	    (DATA_WIDTH),
      .RX_DELAY_FORMAT	    (DELAY_FORMAT),
      .RX_DATA_TYPE         ((RDATA_TYPE[((i_low+1)*2-1):i_low*2] == 2'b00) ? "SERIAL" : (RDATA_TYPE[((i_low+1)*2-1):i_low*2] == 2'b01) ? "DATA" : (RDATA_TYPE[((i_low+1)*2-1):i_low*2] == 2'b10) ? "CLOCK" : (RDATA_TYPE[((i_low+1)*2-1):i_low*2] == 2'b11) ? "DATA_AND_CLOCK": "SERIAL"),
      .RX_DELAY_TYPE        (DELAY_TYPE),
      .RX_DELAY_VAL         (RX_DELAY_VAL[i_low]),
      .RX_REFCLK_FREQ       (REFCLK_FREQ),
      .RX_UPDATE_MODE       (UPDATE_MODE),
      .TX_DATA_WIDTH	    (DATA_WIDTH),
      .TX_DELAY_FORMAT	    (DELAY_FORMAT),
      .TX_DELAY_TYPE        (DELAY_TYPE),
      .TX_REFCLK_FREQ       (REFCLK_FREQ),
      .TX_UPDATE_MODE       (UPDATE_MODE),
      .TX_DELAY_VAL         (TX_DELAY_VAL[i_low]),
      .INIT                 (INIT[i_low]),
      .TBYTE_CTL            (TBYTE_CTL),
      .TX_OUTPUT_PHASE_90   ((TX_OUTPUT_PHASE_90[i_low] == 1'b1) ? "TRUE" : "FALSE"),
      .NATIVE_ODELAY_BYPASS ((NATIVE_ODELAY_BYPASS[i_low] == 1'b1) ? "TRUE" : "FALSE"),
      .SIM_DEVICE           (SIM_DEVICE)
   )
   u_xiphy_bitslice_lower
   (
      .phy2clb_fifo_wrclk (rx_ififo_wrclk[i_low]),
      .phy2clb_fifo_empty (phy2clb_fifo_empty[i_low]),
      .clb2phy_fifo_rden  (clb2phy_fifo_rden[i_low]),
      .clb2phy_fifo_clk   (clb2phy_fifo_clk[i_low]),
      .rx_ce              (clb2phy_idelay_ce[i_low]), 
      .rx_clk             (gclk_mux_txrx_clkdiv[i_low]), 
      .rx_inc             (clb2phy_idelay_inc[i_low]), 
      .rx_ld              (clb2phy_idelay_ld[i_low]), 
      .rx_cntvaluein      (clb2phy_idelay_cntvaluein[((i_low+1)*9 -1) : i_low*9]), 
      .rx_cntvalueout     (phy2clb_idelay_cntvalueout[((i_low+1)*9 -1): i_low*9]), 
      .rx_d               (iob2phy_d_in_byte[i_low]),            //serial data in
      //.rx_dqs_out         (dqs_out_slice[i_low]),                //Only dqs_out_slice[1,7] is connected to bitslice_control dqs_in 
      .rx_q               (rx_q_array_lower[i_low]),             //parallel data out
      .rx_rst_dly         (clb2phy_idelay_rst[i_low]), 
      .rx_rst             (clb2phy_rxbit_rst[i_low]), 
      .rx_en_vtc          (clb2phy_idelay_en_vtc[i_low]), 
      //.rx_nib_ctrl_in     (rx_nib_ctrl_out[0]),
      .rx_bit_ctrl_in     (rx_bit_ctrl_to_bs_array[i_low]),
      .rx_bit_ctrl_out    (rx_bit_bs_to_ctrl_array[i_low]),
      .tx_ce              (clb2phy_odelay_ce[i_low]), 
      .tx_clk             (gclk_mux_txrx_clkdiv[i_low]), 
      .tx_inc             (clb2phy_odelay_inc[i_low]), 
      .tx_ld              (clb2phy_odelay_ld[i_low]), 
      .tx_cntvaluein      (clb2phy_odelay_cntvaluein[((i_low+1)*9 -1) : i_low*9]), 
      .tx_cntvalueout     (phy2clb_odelay_cntvalueout[((i_low+1)*9 -1): i_low*9]), 
      .tx_d               (clb2phy_wr_dq_array[i_low]),         //parallel data in   
      .tx_q               (phy2iob_q_out_byte[i_low]),          //serial data out
      .tx_rst_dly         (clb2phy_odelay_rst[i_low]), 
      .tx_rst             (clb2phy_txbit_rst[i_low]), 
      .tx_t               (clb2phy_t_txbit[i_low]),             //per-bit tri-state control in
      .tx_t_out           (phy2iob_t[i_low]),                   //tri-state control out
      .tx_tbyte_in        (tristate_q[0]), 
      .tx_en_vtc          (clb2phy_odelay_en_vtc[i_low]), 
      //.tx_nib_ctrl_in     (tx_nib_ctrl_clk_out_array[i_low]),
      .tx_bit_ctrl_in     (tx_bit_ctrl_to_bs_array[i_low]),
      .tx_bit_ctrl_out    (tx_bit_bs_to_ctrl_array[i_low])
   );
   end else begin 
     assign rx_q_array_lower[i_low] = 8'b0;
     assign rx_ififo_wrclk[i_low] = 1'b0;
     assign phy2clb_fifo_empty[i_low] = 1'b0;
     assign tx_bit_bs_to_ctrl_array[i_low] = 40'b0;
     assign rx_bit_bs_to_ctrl_array[i_low] = 40'b0;
   end
   end  
endgenerate

//**************************************************************************************
// Bitslice  upper  7 bitslices
//**************************************************************************************

genvar i_upp;

generate for (i_upp=0; i_upp<=6; i_upp=i_upp+1)
   begin: I_BITSLICE_UPPER

   if (RXTX_BITSLICE_EN[6+i_upp]) begin : GEN_RXTX_BITSLICE_EN

   ddr4_phy_v2_2_0_xiphy_bitslice_wrapper #(
      .FIFO_SYNC_MODE     ((FIFO_SYNC_MODE[6+i_upp] == 1'b1) ? "TRUE" : "FALSE"),
      .ENABLE_PRE_EMPHASIS (ENABLE_PRE_EMPHASIS),
      .RX_DATA_WIDTH	  (DATA_WIDTH),
      .RX_DELAY_FORMAT	  (DELAY_FORMAT),
      .RX_DATA_TYPE       ((RDATA_TYPE[((6+i_upp+1)*2-1):(6+i_upp)*2]== 2'b00) ? "SERIAL" : (RDATA_TYPE[((6+i_upp+1)*2-1):(6+i_upp)*2]== 2'b01) ? "DATA" : (RDATA_TYPE[((6+i_upp+1)*2-1):(6+i_upp)*2]== 2'b10) ? "CLOCK" : (RDATA_TYPE[((6+i_upp+1)*2-1):(6+i_upp)*2]== 2'b11) ? "DATA_AND_CLOCK": "SERIAL"),
      .RX_DELAY_TYPE      (DELAY_TYPE),
      .RX_DELAY_VAL       (RX_DELAY_VAL[6+i_upp]),
      .RX_REFCLK_FREQ     (REFCLK_FREQ),
      .RX_UPDATE_MODE     (UPDATE_MODE),
      .TX_DATA_WIDTH	  (DATA_WIDTH),
      .TX_DELAY_FORMAT	  (DELAY_FORMAT),
      .TX_DELAY_TYPE      (DELAY_TYPE),
      .TX_REFCLK_FREQ     (REFCLK_FREQ),
      .TX_UPDATE_MODE     (UPDATE_MODE),
      .TX_DELAY_VAL       (TX_DELAY_VAL[6+i_upp]),
      .INIT               (INIT[6+i_upp]),
      .TBYTE_CTL          (TBYTE_CTL),
      .TX_OUTPUT_PHASE_90 ((TX_OUTPUT_PHASE_90[6+i_upp] == 1'b1) ? "TRUE" : "FALSE"),
      .NATIVE_ODELAY_BYPASS ((NATIVE_ODELAY_BYPASS[6+i_upp] == 1'b1) ? "TRUE" : "FALSE"),
      .SIM_DEVICE           (SIM_DEVICE)
   )
   u_xiphy_bitslice_upper
   (
      .phy2clb_fifo_wrclk (rx_ififo_wrclk[6+i_upp]),
      .phy2clb_fifo_empty (phy2clb_fifo_empty[6+i_upp]),
      .clb2phy_fifo_rden  (clb2phy_fifo_rden[6+i_upp]),
      .clb2phy_fifo_clk   (clb2phy_fifo_clk[6+i_upp]),
      .rx_ce              (clb2phy_idelay_ce[6+i_upp]),
      .rx_clk             (gclk_mux_txrx_clkdiv[6+i_upp]),
      .rx_inc             (clb2phy_idelay_inc[6+i_upp]),
      .rx_ld              (clb2phy_idelay_ld[6+i_upp]),
      .rx_cntvaluein      (clb2phy_idelay_cntvaluein[((6+i_upp+1)*9 -1) : (6+i_upp)*9]),
      .rx_cntvalueout     (phy2clb_idelay_cntvalueout[((6+i_upp+1)*9 -1): (6+i_upp)*9]),
      .rx_d               (iob2phy_d_in_byte[6+i_upp]),         //serial data in
     // .rx_dqs_out         (dqs_out_slice[6+i_upp]),             //DQS output
      .rx_q               (rx_q_array_upper[i_upp]),            //parallel data out
      .rx_rst_dly         (clb2phy_idelay_rst[6+i_upp]),
      .rx_rst             (clb2phy_rxbit_rst[6+i_upp]),
      .rx_en_vtc          (clb2phy_idelay_en_vtc[6+i_upp]),
     // .rx_nib_ctrl_in     (rx_nib_ctrl_out[1]),
      .rx_bit_ctrl_in     (rx_bit_ctrl_to_bs_array[6+i_upp]),
      .rx_bit_ctrl_out    (rx_bit_bs_to_ctrl_array[6+i_upp]),
      .tx_ce              (clb2phy_odelay_ce[6+i_upp]),
      .tx_clk             (gclk_mux_txrx_clkdiv[6+i_upp]),
      .tx_inc             (clb2phy_odelay_inc[6+i_upp]),
      .tx_ld              (clb2phy_odelay_ld[6+i_upp]),
      .tx_cntvaluein      (clb2phy_odelay_cntvaluein[((6+i_upp+1)*9 -1) : (6+i_upp)*9]),
      .tx_cntvalueout     (phy2clb_odelay_cntvalueout[((6+i_upp+1)*9 -1) : (6+i_upp)*9]),
      .tx_d               (clb2phy_wr_dq_array[6+i_upp]),       //parallel data in   
      .tx_q               (phy2iob_q_out_byte[6+i_upp]),        //serial data out
      .tx_rst_dly         (clb2phy_odelay_rst[6+i_upp]),
      .tx_rst             (clb2phy_txbit_rst[6+i_upp]),
      .tx_t               (clb2phy_t_txbit[6+i_upp]),           //per-bit tri-state control in
      .tx_t_out           (phy2iob_t[6+i_upp]),                 //tri-state control out
      .tx_tbyte_in        (tristate_q[1]),
      .tx_en_vtc          (clb2phy_odelay_en_vtc[6+i_upp]),
     // .tx_nib_ctrl_in     (tx_nib_ctrl_clk_out_array[6+i_upp]),     //to accomodate 13th bitslice clock connections
      .tx_bit_ctrl_in     (tx_bit_ctrl_to_bs_array[6+i_upp]),
      .tx_bit_ctrl_out    (tx_bit_bs_to_ctrl_array[6+i_upp])
   );
   end else begin
     assign rx_q_array_upper[i_upp] = 8'b0;
     assign rx_ififo_wrclk[6+i_upp] = 1'b0;
     assign phy2clb_fifo_empty[6+i_upp] = 1'b0;
     assign tx_bit_bs_to_ctrl_array[6+i_upp] = 40'b0;
     assign rx_bit_bs_to_ctrl_array[6+i_upp] = 40'b0;
   end
   end 
endgenerate


//**************************************************************************************
// Nibble tri-state control Upper and Lower
//**************************************************************************************
genvar i_tri;

generate for (i_tri=0; i_tri<=1; i_tri=i_tri+1) begin: I_TRISTATE

 if (|RXTX_BITSLICE_EN[((i_tri+1)*6-1+i_tri):i_tri*6]) begin: GEN_TRISTATE

   ddr4_phy_v2_2_0_xiphy_tristate_wrapper #(
       .DATA_WIDTH            (DATA_WIDTH),
       .INIT                  (INIT[13+i_tri]),
       .DELAY_TYPE            (DELAY_TYPE),
       .DELAY_FORMAT          (DELAY_FORMAT),
       .UPDATE_MODE           (UPDATE_MODE),
       .DELAY_VAL             (TRI_DELAY_VAL[i_tri]),
       .REFCLK_FREQ           (REFCLK_FREQ),
       .OUTPUT_PHASE_90       ((TRI_OUTPUT_PHASE_90[i_tri] == 1'b1) ? "TRUE": "FALSE"),
       .NATIVE_ODELAY_BYPASS  ((NATIVE_ODELAY_BYPASS_TRI[i_tri] == 1'b1) ? "TRUE": "FALSE"),
       .SIM_DEVICE            (SIM_DEVICE)
   )
   u_xiphy_tristate
   (
       .ce                    (clb2phy_tristate_odelay_ce[i_tri]),
       .clk                   (gclk_mux_tx_clkdiv_tri[i_tri]),
       .inc                   (clb2phy_tristate_odelay_inc[i_tri]),
       .ld                    (clb2phy_tristate_odelay_ld[i_tri]),
       .cntvaluein            (clb2phy_tristate_odelay_cntvaluein[((i_tri+1)*9 -1) : i_tri*9]),
       .cntvalueout           (phy2clb_tristate_odelay_cntvalueout[((i_tri+1)*9 -1): i_tri*9]),
       .q                     (tristate_q[i_tri]),  //serial tri-state control data out (per-nibble)
       .regrst                (clb2phy_tristate_odelay_rst[i_tri]),
       .rst                   (clb2phy_txbit_tri_rst[i_tri]),
       .en_vtc                (clb2phy_odelay_tristate_en_vtc[i_tri]),
      // .nib_ctrl_in           (tx_nib_ctrl_out[i_tri]),    
       .bit_ctrl_in           (tx_bit_ctrl_to_tri_array[i_tri]),
       .bit_ctrl_out          (tx_bit_tri_to_ctrl_array[i_tri])
   );
   end 
 end 
endgenerate

//******************************************************************
// Nibble bitslice control (Upper and Lower)
//******************************************************************
/*
wire [1:0] bisc_start_in_internal;
wire [1:0] bisc_stop_in_internal;
wire [1:0] bisc_start_out_internal;
wire [1:0] bisc_stop_out_internal;

assign bisc_stop_in_internal[1] = bisc_stop_in;
assign bisc_stop_in_internal[0] = (|RXTX_BITSLICE_EN[12:6]) ? bisc_stop_out_internal[1] : bisc_stop_in;
assign bisc_stop_out = (|RXTX_BITSLICE_EN[5:0]) ?  bisc_stop_out_internal[0] : bisc_stop_out_internal[1];

assign bisc_start_in_internal[0] = bisc_start_in;
assign bisc_start_in_internal[1] = (|RXTX_BITSLICE_EN[5:0]) ? bisc_start_out_internal[0] : bisc_start_in;
assign bisc_start_out = (|RXTX_BITSLICE_EN[12:6]) ? bisc_start_out_internal[1] : bisc_start_out_internal[0];
*/

wire        clb2riu_wr_en_lut;

  (* DONT_TOUCH = "true" *) LUT1 #
    (
     .INIT (2'h2)
    )
    u_lut1_clb2riu_wr_en
    (
     .I0  (clb2riu_wr_en),
     .O   (clb2riu_wr_en_lut)
     );

genvar i_ctrl;

generate for (i_ctrl=0; i_ctrl<=1; i_ctrl=i_ctrl+1) begin: I_CONTROL

 if (|RXTX_BITSLICE_EN[((i_ctrl+1)*6-1+i_ctrl):i_ctrl*6]) begin: GEN_I_CONTROL
   ddr4_phy_v2_2_0_xiphy_control_wrapper #(
       .EN_OTHER_PCLK	       ((EN_OTHER_PCLK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .EN_OTHER_NCLK	       ((EN_OTHER_NCLK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .EN_DYN_ODLY_MODE       ((EN_DYN_ODLY_MODE[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .SERIAL_MODE  	       ((SERIAL_MODE[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .RX_CLK_PHASE_P         ((RX_CLK_PHASE_P[i_ctrl] == 1'b1) ? "SHIFT_90" : "SHIFT_0"),
       .RX_CLK_PHASE_N         ((RX_CLK_PHASE_N[i_ctrl] == 1'b1) ? "SHIFT_90" : "SHIFT_0"),
       .INV_RXCLK              ((INV_RXCLK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .TX_GATING              ((TX_GATING[i_ctrl] == 1'b1) ? "ENABLE" : "DISABLE"),
       .RX_GATING              ((RX_GATING[i_ctrl] == 1'b1) ? "ENABLE" : "DISABLE"),
       .SELF_CALIBRATE         ((SELF_CALIBRATE[i_ctrl] == 1'b1) ? "ENABLE" : "DISABLE"),
       .READ_IDLE_COUNT        (READ_IDLE_COUNT[i_ctrl]),
       .DIV_MODE               ((DIV_MODE[i_ctrl] == 1'b1) ? "DIV2" : "DIV4"),
       .REFCLK_SRC             ((REFCLK_SRC[i_ctrl] == 1'b1) ? "REFCLK" : "PLLCLK"),
       .ROUNDING_FACTOR        (ROUNDING_FACTOR[i_ctrl]),
       .CTRL_CLK               ((CTRL_CLK[i_ctrl] == 1'b1) ? "EXTERNAL" : "INTERNAL"),
       .EN_CLK_TO_EXT_NORTH    ((EN_CLK_TO_EXT_NORTH[i_ctrl] == 1'b1) ? "ENABLE" : "DISABLE"),
       .EN_CLK_TO_EXT_SOUTH    ((EN_CLK_TO_EXT_SOUTH[i_ctrl] == 1'b1) ? "ENABLE" : "DISABLE"),
       .IDLY_VT_TRACK          ((IDLY_VT_TRACK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .ODLY_VT_TRACK          ((ODLY_VT_TRACK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .QDLY_VT_TRACK          ((QDLY_VT_TRACK[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .RXGATE_EXTEND          ((RXGATE_EXTEND[i_ctrl] == 1'b1) ? "TRUE" : "FALSE"),
       .SIM_DEVICE             (SIM_DEVICE)
   )
   u_xiphy_control
   (
       //BITSLICE_CONTROL
       .refclk                 (clb2phy_ref_clk[i_ctrl]),
       .clb2phy_ctrl_rst       (clb2phy_ctrl_rst[i_ctrl]),
       .en_vtc                 (clb2phy_dlyctl_en_vtc[i_ctrl]),
       .phy2clb_fixdly_rdy     (phy2clb_fixdly_rdy[i_ctrl]),
       .phy2clb_phy_rdy        (phy2clb_phy_rdy[i_ctrl]),
       .riu_clk                (clb2phy_ctrl_clk[i_ctrl]),
       .clb2riu_addr           (clb2riu_addr),
       .clb2riu_wr_data        (clb2riu_wr_data),
       .riu2clb_rd_data        (riu2clb_rd_data_array[i_ctrl]), 
       .riu2clb_valid          (riu2clb_valid_array[i_ctrl]),
       .clb2riu_wr_en          (clb2riu_wr_en_lut),
       .clb2riu_nibble_sel     (clb2riu_nibble_sel[i_ctrl]),
       .clb2phy_rdcs0          (clb2phy_rdcs0_nibble[i_ctrl]),   
       .clb2phy_rdcs1          (clb2phy_rdcs1_nibble[i_ctrl]), 
       .clb2phy_wrcs0          (clb2phy_wrcs0_nibble[i_ctrl]), 
       .clb2phy_wrcs1          (clb2phy_wrcs1_nibble[i_ctrl]),
       .clb2phy_t_b            (clb2phy_t_b[i_ctrl]),
       .clb2phy_rden           (clb2phy_rden[i_ctrl]),
       .dyn_dci_out            (ctl2iob_odt[i_ctrl]),
       .clk_to_ext_south       (clk_to_ext_south[i_ctrl]),  
       .clk_to_ext_north       (clk_to_ext_north[i_ctrl]),
       .pll_clk                (pll_clk[i_ctrl]),
       .clk_from_ext	       (clk_from_ext[i_ctrl]),
       .pdqs_gt_in	       (pdqs_gt_in[i_ctrl]),
       .ndqs_gt_in	       (ndqs_gt_in[i_ctrl]),
       .pdqs_gt_out	       (pdqs_gt_out[i_ctrl]),
       .ndqs_gt_out	       (ndqs_gt_out[i_ctrl]),
       .rx_bit_ctrl_out0       (rx_bit_ctrl_out0[i_ctrl]),
       .rx_bit_ctrl_out1       (rx_bit_ctrl_out1[i_ctrl]),
       .rx_bit_ctrl_out2       (rx_bit_ctrl_out2[i_ctrl]),
       .rx_bit_ctrl_out3       (rx_bit_ctrl_out3[i_ctrl]),
       .rx_bit_ctrl_out4       (rx_bit_ctrl_out4[i_ctrl]),
       .rx_bit_ctrl_out5       (rx_bit_ctrl_out5[i_ctrl]),
       .rx_bit_ctrl_out6       (rx_bit_ctrl_out6[i_ctrl]),
       .tx_bit_ctrl_out0       (tx_bit_ctrl_out0[i_ctrl]),
       .tx_bit_ctrl_out1       (tx_bit_ctrl_out1[i_ctrl]),
       .tx_bit_ctrl_out2       (tx_bit_ctrl_out2[i_ctrl]),
       .tx_bit_ctrl_out3       (tx_bit_ctrl_out3[i_ctrl]),
       .tx_bit_ctrl_out4       (tx_bit_ctrl_out4[i_ctrl]),
       .tx_bit_ctrl_out5       (tx_bit_ctrl_out5[i_ctrl]),
       .tx_bit_ctrl_out6       (tx_bit_ctrl_out6[i_ctrl]),
       .tx_bit_ctrl_out_tri    (tx_bit_ctrl_out_tri[i_ctrl]),
       .tx_bit_ctrl_in_tri     (tx_bit_ctrl_in_tri[i_ctrl]),
       //BIT_CTRL_IN[39:0] ribbon cables to CONTROL
     `ifndef SYN
       .rx_bit_ctrl_in0        (RXTX_BITSLICE_EN[6*i_ctrl]   ? rx_bit_ctrl_in0[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in1        (RXTX_BITSLICE_EN[6*i_ctrl+1] ? rx_bit_ctrl_in1[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in2        (RXTX_BITSLICE_EN[6*i_ctrl+2] ? rx_bit_ctrl_in2[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in3        (RXTX_BITSLICE_EN[6*i_ctrl+3] ? rx_bit_ctrl_in3[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in4        (RXTX_BITSLICE_EN[6*i_ctrl+4] ? rx_bit_ctrl_in4[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in5        (RXTX_BITSLICE_EN[6*i_ctrl+5] ? rx_bit_ctrl_in5[i_ctrl] : 40'b0),
       .rx_bit_ctrl_in6        (RXTX_BITSLICE_EN[6*i_ctrl+6] ? rx_bit_ctrl_in6[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in0        (RXTX_BITSLICE_EN[6*i_ctrl]   ? tx_bit_ctrl_in0[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in1        (RXTX_BITSLICE_EN[6*i_ctrl+1] ? tx_bit_ctrl_in1[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in2        (RXTX_BITSLICE_EN[6*i_ctrl+2] ? tx_bit_ctrl_in2[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in3        (RXTX_BITSLICE_EN[6*i_ctrl+3] ? tx_bit_ctrl_in3[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in4        (RXTX_BITSLICE_EN[6*i_ctrl+4] ? tx_bit_ctrl_in4[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in5        (RXTX_BITSLICE_EN[6*i_ctrl+5] ? tx_bit_ctrl_in5[i_ctrl] : 40'b0),
       .tx_bit_ctrl_in6        (RXTX_BITSLICE_EN[6*i_ctrl+6] ? tx_bit_ctrl_in6[i_ctrl] : 40'b0)
     `else
       .rx_bit_ctrl_in0        (RXTX_BITSLICE_EN[6*i_ctrl]   ? rx_bit_ctrl_in0[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in1        (RXTX_BITSLICE_EN[6*i_ctrl+1] ? rx_bit_ctrl_in1[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in2        (RXTX_BITSLICE_EN[6*i_ctrl+2] ? rx_bit_ctrl_in2[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in3        (RXTX_BITSLICE_EN[6*i_ctrl+3] ? rx_bit_ctrl_in3[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in4        (RXTX_BITSLICE_EN[6*i_ctrl+4] ? rx_bit_ctrl_in4[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in5        (RXTX_BITSLICE_EN[6*i_ctrl+5] ? rx_bit_ctrl_in5[i_ctrl] : 40'bz),
       .rx_bit_ctrl_in6        (RXTX_BITSLICE_EN[6*i_ctrl+6] ? rx_bit_ctrl_in6[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in0        (RXTX_BITSLICE_EN[6*i_ctrl]   ? tx_bit_ctrl_in0[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in1        (RXTX_BITSLICE_EN[6*i_ctrl+1] ? tx_bit_ctrl_in1[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in2        (RXTX_BITSLICE_EN[6*i_ctrl+2] ? tx_bit_ctrl_in2[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in3        (RXTX_BITSLICE_EN[6*i_ctrl+3] ? tx_bit_ctrl_in3[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in4        (RXTX_BITSLICE_EN[6*i_ctrl+4] ? tx_bit_ctrl_in4[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in5        (RXTX_BITSLICE_EN[6*i_ctrl+5] ? tx_bit_ctrl_in5[i_ctrl] : 40'bz),
       .tx_bit_ctrl_in6        (RXTX_BITSLICE_EN[6*i_ctrl+6] ? tx_bit_ctrl_in6[i_ctrl] : 40'bz)
     `endif
   );
   
   end
 end
endgenerate

//pragma translate off
`ifdef ASSERT_ON
genvar idx_txbit;
generate for (idx_txbit=0; idx_txbit<13; idx_txbit=idx_txbit+1)
initial
begin
  @(negedge clb2phy_txbit_rst[idx_txbit]);
  #10;
  assert (^clb2phy_wr_dq_array[idx_txbit] !== 1'bx) 
  else $error("clb2phy_wr_dq_array[%d] = X at time %0t",idx_txbit,$time);
  assert (clb2phy_t_txbit[idx_txbit] !== 1'bx) 
  else $error("clb2phy_t_txbit[%d] = X at time %0t",idx_txbit,$time);
end
endgenerate

genvar idx_rxbit;
generate for (idx_rxbit=0; idx_rxbit<13; idx_rxbit=idx_rxbit+1)
initial
begin
    @(negedge clb2phy_rxbit_rst[idx_rxbit]);
    #10;
    assert (clb2phy_fifo_rden[idx_rxbit] !== 1'bx) 
    else $error("clb2phy_fifo_rden[%d] = X at time %0t",idx_rxbit,$time);
end
endgenerate

wire [8:0] clb2phy_idelay_cntvaluein_array[12:0];
assign clb2phy_idelay_cntvaluein_array[0]  = clb2phy_idelay_cntvaluein[8:0];
assign clb2phy_idelay_cntvaluein_array[1]  = clb2phy_idelay_cntvaluein[17:9];
assign clb2phy_idelay_cntvaluein_array[2]  = clb2phy_idelay_cntvaluein[26:18];
assign clb2phy_idelay_cntvaluein_array[3]  = clb2phy_idelay_cntvaluein[35:27];
assign clb2phy_idelay_cntvaluein_array[4]  = clb2phy_idelay_cntvaluein[44:36];
assign clb2phy_idelay_cntvaluein_array[5]  = clb2phy_idelay_cntvaluein[53:45];
assign clb2phy_idelay_cntvaluein_array[6]  = clb2phy_idelay_cntvaluein[62:54];
assign clb2phy_idelay_cntvaluein_array[7]  = clb2phy_idelay_cntvaluein[71:63];
assign clb2phy_idelay_cntvaluein_array[8]  = clb2phy_idelay_cntvaluein[80:72];
assign clb2phy_idelay_cntvaluein_array[9]  = clb2phy_idelay_cntvaluein[89:81];
assign clb2phy_idelay_cntvaluein_array[10] = clb2phy_idelay_cntvaluein[98:90];
assign clb2phy_idelay_cntvaluein_array[11] = clb2phy_idelay_cntvaluein[107:99];
assign clb2phy_idelay_cntvaluein_array[12] = clb2phy_idelay_cntvaluein[116:108];

genvar idx_idly;
generate for (idx_idly=0; idx_idly<13; idx_idly=idx_idly+1)
initial
begin
  @(negedge clb2phy_idelay_rst[idx_idly]);
  #10;
  assert (clb2phy_idelay_ce[idx_idly] !== 1'bx) 
  else $error("clb2phy_idelay_ce[%d] = X at time %0t",idx_idly,$time);
  assert (clb2phy_idelay_inc[idx_idly] !== 1'bx) 
  else $error("clb2phy_idelay_inc[%d] = X at time %0t",idx_idly,$time);
  assert (clb2phy_idelay_ld[idx_idly] !== 1'bx) 
  else $error("clb2phy_idelay_ld[%d] = X at time %0t",idx_idly,$time);
  assert (^clb2phy_idelay_cntvaluein_array[idx_idly] !== 1'bx) 
  else $error("clb2phy_idelay_cntvaluein%d = X at time %0t",idx_idly,$time);
end
endgenerate

wire [8:0] clb2phy_odelay_cntvaluein_array[12:0];
assign clb2phy_odelay_cntvaluein_array[0]  = clb2phy_odelay_cntvaluein[8:0];
assign clb2phy_odelay_cntvaluein_array[1]  = clb2phy_odelay_cntvaluein[17:9];
assign clb2phy_odelay_cntvaluein_array[2]  = clb2phy_odelay_cntvaluein[26:18];
assign clb2phy_odelay_cntvaluein_array[3]  = clb2phy_odelay_cntvaluein[35:27];
assign clb2phy_odelay_cntvaluein_array[4]  = clb2phy_odelay_cntvaluein[44:36];
assign clb2phy_odelay_cntvaluein_array[5]  = clb2phy_odelay_cntvaluein[53:45];
assign clb2phy_odelay_cntvaluein_array[6]  = clb2phy_odelay_cntvaluein[62:54];
assign clb2phy_odelay_cntvaluein_array[7]  = clb2phy_odelay_cntvaluein[71:63];
assign clb2phy_odelay_cntvaluein_array[8]  = clb2phy_odelay_cntvaluein[80:72];
assign clb2phy_odelay_cntvaluein_array[9]  = clb2phy_odelay_cntvaluein[89:81];
assign clb2phy_odelay_cntvaluein_array[10] = clb2phy_odelay_cntvaluein[98:90];
assign clb2phy_odelay_cntvaluein_array[11] = clb2phy_odelay_cntvaluein[107:99];
assign clb2phy_odelay_cntvaluein_array[12] = clb2phy_odelay_cntvaluein[116:108];

genvar idx_odly;
generate for (idx_odly=0; idx_odly<13; idx_odly=idx_odly+1)
initial
begin
  @(negedge clb2phy_odelay_rst[idx_odly]);
  #10;
  assert (clb2phy_odelay_ce[idx_odly] !== 1'bx) 
  else $error("clb2phy_odelay_ce[%d] = X at time %0t",idx_odly,$time);
  assert (clb2phy_odelay_inc[idx_odly] !== 1'bx) 
  else $error("clb2phy_odelay_inc[%d] = X at time %0t",idx_odly,$time);
  assert (clb2phy_odelay_ld[idx_odly] !== 1'bx) 
  else $error("clb2phy_odelay_ld[%d] = X at time %0t",idx_odly,$time);
  assert (^clb2phy_odelay_cntvaluein_array[idx_odly] !== 1'bx) 
  else $error("clb2phy_odelay_cntvaluein%d = X at time %0t",idx_odly,$time);
end
endgenerate

wire [8:0] clb2phy_tristate_odelay_cntvaluein_array[1:0];
assign clb2phy_tristate_odelay_cntvaluein_array[0]  = clb2phy_tristate_odelay_cntvaluein[8:0];
assign clb2phy_tristate_odelay_cntvaluein_array[1]  = clb2phy_tristate_odelay_cntvaluein[17:9];

genvar idx_tri;
generate for (idx_tri=0; idx_tri<2; idx_tri=idx_tri+1)
initial
begin
  @(negedge clb2phy_tristate_odelay_rst[idx_tri]);
  #10;
  assert (clb2phy_tristate_odelay_ce[idx_tri] !== 1'bx) 
  else $error("clb2phy_tristate_odelay_ce[%d] = X at time %0t",idx_tri,$time);
  assert (clb2phy_tristate_odelay_inc[idx_tri] !== 1'bx) 
  else $error("clb2phy_tristate_odelay_inc[%d] = X at time %0t",idx_tri,$time);
  assert (clb2phy_tristate_odelay_ld[idx_tri] !== 1'bx) 
  else $error("clb2phy_tristate_odelay_ld[%d] = X at time %0t",idx_tri,$time);
  assert (^clb2phy_tristate_odelay_cntvaluein_array[idx_tri] !== 1'bx) 
  else $error("clb2phy_tristate_odelay_cntvaluein%d = X at time %0t",idx_tri,$time);
end
endgenerate

initial
begin
  @(negedge clb2phy_ctrl_rst_low);
  #10;
  assert (clb2phy_ctrl_clk_low !== 1'bx) 
  else $error("clb2phy_ctrl_clk_low = X at time %0t", $time);
  assert (^clb2phy_t_b_low !== 1'bx) 
  else $error("clb2phy_t_b_low = X at time %0t", $time);
  assert (^clb2phy_rden_low !== 1'bx) 
  else $error("clb2phy_rden_low = X at time %0t", $time);
  assert (^clb2riu_addr !== 1'bx)
  else $error("clb2ruy_addr = X at time %0t", $time);
  assert (^clb2riu_wr_data !== 1'bx)
  else $error("clb2riu_wr_data = X at time %0t", $time);
  assert (clb2riu_wr_en !== 1'bx)
  else $error("clb2riu_wr_en = X at time %0t", $time);
  assert (clb2riu_nibble_sel_low !== 1'bx)
  else $error("clb2riu_nibble_sel_low = X at time %0t", $time);
  assert (^clb2phy_wrcs0_low !== 1'bx)
  else $error("clb2phy_wrcs0_low = X at time %0t", $time);
  assert (^clb2phy_wrcs1_low !== 1'bx)
  else $error("clb2phy_wrcs1_low = X at time %0t", $time);
  assert (^clb2phy_rdcs0_low !== 1'bx)
  else $error("clb2phy_rdcs0_low = X at time %0t", $time);
  assert (^clb2phy_rdcs1_low !== 1'bx)
  else $error("clb2phy_rdcs1_low = X at time %0t", $time);
  assert (clb2phy_dlyctl_en_vtc_low !== 1'bx)
  else $error("clb2phy_dlyctl_en_vtc_low = X at time %0t", $time);
end

initial
begin
  @(negedge clb2phy_ctrl_rst_upp);
  #10;
  assert (clb2phy_ctrl_clk_upp !== 1'bx) 
  else $error("clb2phy_ctrl_clk_upp = X at time %0t", $time);
  assert (^clb2phy_t_b_upp !== 1'bx) 
  else $error("clb2phy_t_b_upp = X at time %0t", $time);
  assert (^clb2phy_rden_upp !== 1'bx) 
  else $error("clb2phy_rden_upp = X at time %0t", $time);
  assert (^clb2riu_addr !== 1'bx)
  else $error("clb2ruy_addr = X at time %0t", $time);
  assert (^clb2riu_wr_data !== 1'bx)
  else $error("clb2riu_wr_data = X at time %0t", $time);
  assert (clb2riu_wr_en !== 1'bx)
  else $error("clb2riu_wr_en = X at time %0t", $time);
  assert (clb2riu_nibble_sel_upp !== 1'bx)
  else $error("clb2riu_nibble_sel_upp = X at time %0t", $time);
  assert (^clb2phy_wrcs0_upp !== 1'bx)
  else $error("clb2phy_wrcs0_upp = X at time %0t", $time);
  assert (^clb2phy_wrcs1_upp !== 1'bx)
  else $error("clb2phy_wrcs1_upp = X at time %0t", $time);
  assert (^clb2phy_rdcs0_upp !== 1'bx)
  else $error("clb2phy_rdcs0_upp = X at time %0t", $time);
  assert (^clb2phy_rdcs1_upp !== 1'bx)
  else $error("clb2phy_rdcs1_upp = X at time %0t", $time);
  assert (clb2phy_dlyctl_en_vtc_upp !== 1'bx)
  else $error("clb2phy_dlyctl_en_vtc_upp = X at time %0t", $time);
end

initial
begin
  #100;
  assert (clb2phy_ctrl_rst_upp !== 1'bx) 
  else $error("clb2phy_ctrl_rst_upp = X at time %0t", $time);
  assert (clb2phy_ctrl_rst_low !== 1'bx) 
  else $error("clb2phy_ctrl_rst_low = X at time %0t", $time);
  assert (^clb2phy_txbit_tri_rst !== 1'bx) 
  else $error("clb2phy_txbit_tri_rst = X at time %0t", $time);
  assert (^clb2phy_txbit_rst !== 1'bx) 
  else $error("clb2phy_txbit_rst = X at time %0t", $time);
  assert (^clb2phy_rxbit_rst !== 1'bx) 
  else $error("clb2phy_rxbit_rst = X at time %0t", $time);
  assert (^clb2phy_fifo_clk !== 1'bx) 
  else $error("clb2phy_fifo_clk = X at time %0t", $time);
  assert (clb2phy_ref_clk_upp !== 1'bx) 
  else $error("clb2phy_ref_clk_upp = X at time %0t", $time);
  assert (clb2phy_ref_clk_low !== 1'bx) 
  else $error("clb2phy_ref_clk_low = X at time %0t", $time);
  assert (pll_clk0 !== 1'bx) 
  else $error("pll_clk0 = X at time %0t", $time);
  assert (pll_clk1 !== 1'bx) 
  else $error("pll_clk1 = X at time %0t", $time);
  assert (^gclk_in !== 1'bx) 
  else $error("gclk_in = X at time %0t", $time);
  assert (clk_from_ext_upp !== 1'bx) 
  else $error("clk_from_ext_upp = X at time %0t", $time);
  assert (clk_from_ext_low !== 1'bx) 
  else $error("clk_from_ext_low = X at time %0t", $time);
  assert (^clb2phy_odt_upp !== 1'bx) 
  else $error("clb2phy_odt_upp = X at time %0t", $time);
  assert (^clb2phy_odt_low !== 1'bx) 
  else $error("clb2phy_odt_low = X at time %0t", $time);
  assert (^clb2phy_idelay_en_vtc !== 1'bx) 
  else $error("clb2phy_idelay_en_vtc = X at time %0t", $time);
  assert (^clb2phy_odelay_en_vtc !== 1'bx) 
  else $error("clb2phy_odelay_en_vtc = X at time %0t", $time);
  assert (^clb2phy_odelay_tristate_en_vtc !== 1'bx) 
  else $error("clb2phy_odelay_tristate_en_vtc = X at time %0t", $time);
end

always @*
begin
  assert (^iob2phy_d_in_byte !== 1'bx)
  else $info("iob2phy_d_in_byte = X at time %0t", $time);
end
`endif
//pragma translate on


endmodule

