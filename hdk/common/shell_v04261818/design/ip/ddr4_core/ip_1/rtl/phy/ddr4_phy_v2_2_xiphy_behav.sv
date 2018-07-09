/******************************************************************************
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
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_behav.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : 8 Series
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                    ddr4_phy_v2_2_0_xiphy_behav module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps/1ps

module ddr4_phy_v2_2_0_xiphy_behav #(
    parameter           tCK                           = 1250 
   ,parameter integer BYTES                           = 7
   ,parameter integer DBYTES                          = 4
   ,parameter         TBYTE_CTL                       = "TBYTE_IN"
   ,parameter         DELAY_TYPE                      = "FIXED"
   ,parameter         DELAY_FORMAT                    = "TIME"
   ,parameter         UPDATE_MODE                     = "ASYNC"
   ,parameter         PLLCLK_SRC                      = 1'b0
   ,parameter  [13*BYTES-1:0] FIFO_SYNC_MODE          = '0
   ,parameter   [1:0] DIV_MODE                        = 2'b00
   ,parameter   [1:0] REFCLK_SRC                      = 2'b00
   ,parameter   [1:0] CTRL_CLK                        = 2'b11
   ,parameter  [45*BYTES-1:0] GCLK_SRC                = '0
   ,parameter  [15*BYTES-1:0] INIT                    = '0
   ,parameter  [15*BYTES-1:0] RX_DATA_TYPE            = '0
   ,parameter  [13*BYTES-1:0] TX_OUTPUT_PHASE_90      = '0
   ,parameter  [13*BYTES-1:0] RXTX_BITSLICE_EN        = '0   
   ,parameter   [2*BYTES-1:0] TRI_OUTPUT_PHASE_90     = '0
   ,parameter  [13*BYTES-1:0] NATIVE_ODELAY_BYPASS    = '0
   ,parameter   [2*BYTES-1:0] EN_OTHER_PCLK           = '0
   ,parameter   [2*BYTES-1:0] EN_OTHER_NCLK           = '0
   ,parameter   [2*BYTES-1:0] SERIAL_MODE             = '0
   ,parameter   [2*BYTES-1:0] RX_CLK_PHASE_P          = '0
   ,parameter   [2*BYTES-1:0] RX_CLK_PHASE_N          = '0
   ,parameter   [2*BYTES-1:0] INV_RXCLK               = '0
   ,parameter   [2*BYTES-1:0] TX_GATING               = '0
   ,parameter   [2*BYTES-1:0] RX_GATING               = '1
   ,parameter   [2*BYTES-1:0] EN_CLK_TO_EXT_NORTH     = '0
   ,parameter   [2*BYTES-1:0] EN_CLK_TO_EXT_SOUTH     = '0
   ,parameter integer RX_DELAY_VAL             [12:0] = '{default: 0}
   ,parameter integer TX_DELAY_VAL             [12:0] = '{default: 0}
   ,parameter integer TRI_DELAY_VAL             [1:0] = '{default: 0}
   ,parameter integer READ_IDLE_COUNT           [1:0] = '{31, 31}
   ,parameter integer ROUNDING_FACTOR           [1:0] = '{16, 16}
   ,parameter integer DATA_WIDTH                      = 8
   ,parameter real    REFCLK_FREQ                     = 300.0
   ,parameter  [13*BYTES-1:0] DCI_SRC                 = '0
   ,parameter   [2*BYTES-1:0] EN_DYN_ODLY_MODE        = '0
   ,parameter   [2*BYTES-1:0] SELF_CALIBRATE          = '0
   ,parameter   [2*BYTES-1:0] IDLY_VT_TRACK           = '1
   ,parameter   [2*BYTES-1:0] ODLY_VT_TRACK           = '1
   ,parameter   [2*BYTES-1:0] QDLY_VT_TRACK           = '1
   ,parameter   [2*BYTES-1:0] RXGATE_EXTEND           = '0
   ,parameter                  DRAM_TYPE              = "DDR4"
   ,parameter   [BYTES-1:0]    PING_PONG_CH1_BYTES_MAP = '0
   ,parameter   [39*BYTES-1:0] IOBTYPE                = '0  
)(
    input [BYTES-1:0]  pll_clk0
   ,input [BYTES-1:0]  pll_clk1
   ,input [5:0]            gclk_in
   ,output  [BYTES*16-1:0] riu2clb_rd_data  
   ,output   [BYTES*1-1:0] riu2clb_valid    
   ,output  [BYTES*13-1:0] phy2clb_fifo_empty 
   ,output   [BYTES*2-1:0] phy2rclk_ss_divclk 
   ,output   [BYTES*8-1:0] phy2clb_rd_dq0
   ,output   [BYTES*8-1:0] phy2clb_rd_dq1
   ,output   [BYTES*8-1:0] phy2clb_rd_dq2
   ,output   [BYTES*8-1:0] phy2clb_rd_dq3
   ,output   [BYTES*8-1:0] phy2clb_rd_dq4
   ,output   [BYTES*8-1:0] phy2clb_rd_dq5
   ,output   [BYTES*8-1:0] phy2clb_rd_dq6
   ,output   [BYTES*8-1:0] phy2clb_rd_dq7
   ,output   [BYTES*8-1:0] phy2clb_rd_dq8
   ,output   [BYTES*8-1:0] phy2clb_rd_dq9
   ,output   [BYTES*8-1:0] phy2clb_rd_dq10
   ,output   [BYTES*8-1:0] phy2clb_rd_dq11
   ,output   [BYTES*8-1:0] phy2clb_rd_dq12
   ,output [BYTES*117-1:0] phy2clb_idelay_cntvalueout 
   ,output [BYTES*117-1:0] phy2clb_odelay_cntvalueout 
   ,output  [BYTES*18-1:0] phy2clb_tristate_odelay_cntvalueout 
   ,output  reg [BYTES*1-1:0] phy2clb_fixdly_rdy_upp
   ,output  reg [BYTES*1-1:0] phy2clb_fixdly_rdy_low
   ,output   [BYTES*1-1:0] clk_to_ext_north_upp 
   ,output   [BYTES*1-1:0] clk_to_ext_south_upp
   ,output   [BYTES*1-1:0] clk_to_ext_north_low
   ,output   [BYTES*1-1:0] clk_to_ext_south_low
   ,output  reg [BYTES*1-1:0] phy2clb_phy_rdy_upp
   ,output  reg [BYTES*1-1:0] phy2clb_phy_rdy_low
   ,output  [BYTES*13-1:0] phy2iob_q_out_byte
   ,output  [BYTES*13-1:0] phy2iob_odt_out_byte 
   ,output  [BYTES*13-1:0] phy2iob_t 
   ,input  [BYTES*13-1:0] clb2phy_fifo_clk
   ,input   [BYTES*1-1:0] clb2phy_ctrl_clk_upp
   ,input   [BYTES*1-1:0] clb2phy_ctrl_clk_low
   ,input   [BYTES*1-1:0] clb2phy_ref_clk_upp
   ,input   [BYTES*1-1:0] clb2phy_ref_clk_low
   ,input   [BYTES*1-1:0] clb2phy_ctrl_rst_upp
   ,input   [BYTES*1-1:0] clb2phy_ctrl_rst_low
   ,input   [BYTES*2-1:0] clb2phy_txbit_tri_rst
   ,input  [BYTES*13-1:0] clb2phy_txbit_rst
   ,input  [BYTES*13-1:0] clb2phy_rxbit_rst
   ,input   [BYTES*8-1:0] clb2phy_wr_dq0
   ,input   [BYTES*8-1:0] clb2phy_wr_dq1
   ,input   [BYTES*8-1:0] clb2phy_wr_dq2
   ,input   [BYTES*8-1:0] clb2phy_wr_dq3
   ,input   [BYTES*8-1:0] clb2phy_wr_dq4
   ,input   [BYTES*8-1:0] clb2phy_wr_dq5
   ,input   [BYTES*8-1:0] clb2phy_wr_dq6
   ,input   [BYTES*8-1:0] clb2phy_wr_dq7
   ,input   [BYTES*8-1:0] clb2phy_wr_dq8
   ,input   [BYTES*8-1:0] clb2phy_wr_dq9
   ,input   [BYTES*8-1:0] clb2phy_wr_dq10
   ,input   [BYTES*8-1:0] clb2phy_wr_dq11
   ,input   [BYTES*8-1:0] clb2phy_wr_dq12
   ,input   [BYTES*4-1:0] clb2phy_t_b_upp
   ,input   [BYTES*4-1:0] clb2phy_t_b_low
   ,input   [BYTES*4-1:0] clb2phy_rden_upp
   ,input   [BYTES*4-1:0] clb2phy_rden_low
   ,input   [BYTES*6-1:0] clb2riu_addr 
   ,input  [BYTES*16-1:0] clb2riu_wr_data 
   ,input   [BYTES*1-1:0] clb2riu_wr_en 
   ,input   [BYTES*1-1:0] clb2riu_nibble_sel_upp 
   ,input   [BYTES*1-1:0] clb2riu_nibble_sel_low 
   ,input  [BYTES*13-1:0] clb2phy_fifo_rden
   ,input  [BYTES*13-1:0] clb2phy_idelay_rst  
   ,input  [BYTES*13-1:0] clb2phy_idelay_ce 
   ,input  [BYTES*13-1:0] clb2phy_idelay_inc 
   ,input  [BYTES*13-1:0] clb2phy_idelay_ld 
   ,input [BYTES*117-1:0] clb2phy_idelay_cntvaluein 
   ,input  [BYTES*13-1:0] clb2phy_odelay_rst 
   ,input  [BYTES*13-1:0] clb2phy_odelay_ce 
   ,input  [BYTES*13-1:0] clb2phy_odelay_inc 
   ,input  [BYTES*13-1:0] clb2phy_odelay_ld 
   ,input [BYTES*117-1:0] clb2phy_odelay_cntvaluein 
   ,input  [BYTES*13-1:0] clb2phy_t_txbit
   ,input  [BYTES*13-1:0] clb2phy_tristate_odelay_rst 
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_ce 
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_inc 
   ,input   [BYTES*2-1:0] clb2phy_tristate_odelay_ld 
   ,input  [BYTES*18-1:0] clb2phy_tristate_odelay_cntvaluein 
   ,input   [BYTES*4-1:0] clb2phy_wrcs0_upp
   ,input   [BYTES*4-1:0] clb2phy_wrcs1_upp
   ,input   [BYTES*4-1:0] clb2phy_wrcs0_low
   ,input   [BYTES*4-1:0] clb2phy_wrcs1_low
   ,input   [BYTES*4-1:0] clb2phy_rdcs0_upp
   ,input   [BYTES*4-1:0] clb2phy_rdcs1_upp
   ,input   [BYTES*4-1:0] clb2phy_rdcs0_low
   ,input   [BYTES*4-1:0] clb2phy_rdcs1_low
   ,input   [BYTES*1-1:0] clk_from_ext_low
   ,input   [BYTES*1-1:0] clk_from_ext_upp
   ,input  [BYTES*13-1:0] clb2phy_idelay_en_vtc   
   ,input  [BYTES*13-1:0] clb2phy_odelay_en_vtc 
   ,input   [BYTES*2-1:0] clb2phy_odelay_tristate_en_vtc 
   ,input   [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_upp 
   ,input   [BYTES*1-1:0] clb2phy_dlyctl_en_vtc_low 
   ,input  [BYTES*13-1:0] iob2phy_d_in_byte
   ,input   [BYTES*7-1:0] clb2phy_odt_upp
   ,input   [BYTES*7-1:0] clb2phy_odt_low
);

//Calculation of dqs index based on IOBTYPE Parameter, dqs is a bidirectional differential I/O.  
function integer dqs_index (bit [BYTES*39-1:0] iobtype) ;
  dqs_index = 0 ;
  for(int i = 0 ; i < (BYTES*39)/3 ; i++)begin
    if(((((iobtype) >> i*3) & 3'h7) == 7) && (PING_PONG_CH1_BYTES_MAP[i/13] == 0))begin
      dqs_index = i ;
      return dqs_index ;
    end 
  end
endfunction

function integer dqs_index_ch1 (bit [BYTES*39-1:0] iobtype) ;
  dqs_index_ch1 = 0 ;
  for(int i = 0 ; i < (BYTES*39)/3 ; i++)begin
    if(((((iobtype) >> i*3) & 3'h7) == 7) && (PING_PONG_CH1_BYTES_MAP[i/13] == 1))begin
      dqs_index_ch1 = i ;
     // $display("DQS_INDEX_ch1==== %d",dqs_index_ch1);
      return dqs_index_ch1 ;
    end 
  end
endfunction

assign phy2iob_odt_out_byte = {BYTES{1'b0}};

genvar i;
genvar i_low;
genvar i_upp;
bit dqs_in ;
bit dqs_in_ch1 ;
//assign dqs_in from iob2phy_d_in_byte 
assign dqs_in = iob2phy_d_in_byte[dqs_index(IOBTYPE)] ;
assign dqs_in_ch1 = iob2phy_d_in_byte[dqs_index_ch1(IOBTYPE)] ;

// Preserve the hierarchy as observed with regular xiphy.
generate
  for (i = 0; i < BYTES; i = i + 1) begin : byte_num
  wire [7:0] clb2phy_wr_dq_array [i*13+12:i*13];
  wire [7:0] phy2clb_rd_dq_array [i*13+12:i*13];
	assign clb2phy_wr_dq_array[i*13]  = clb2phy_wr_dq0[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+1]  = clb2phy_wr_dq1[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+2]  = clb2phy_wr_dq2[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+3]  = clb2phy_wr_dq3[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+4]  = clb2phy_wr_dq4[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+5]  = clb2phy_wr_dq5[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+6]  = clb2phy_wr_dq6[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+7]  = clb2phy_wr_dq7[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+8]  = clb2phy_wr_dq8[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+9]  = clb2phy_wr_dq9[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+10] = clb2phy_wr_dq10[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+11] = clb2phy_wr_dq11[i*8+:8];
	assign clb2phy_wr_dq_array[i*13+12] = clb2phy_wr_dq12[i*8+:8];
	assign phy2clb_rd_dq0[i*8+:8] = phy2clb_rd_dq_array[i*13];
	assign phy2clb_rd_dq1[i*8+:8] = phy2clb_rd_dq_array[i*13+1];
	assign phy2clb_rd_dq2[i*8+:8] = phy2clb_rd_dq_array[i*13+2];
	assign phy2clb_rd_dq3[i*8+:8] = phy2clb_rd_dq_array[i*13+3];
	assign phy2clb_rd_dq4[i*8+:8] = phy2clb_rd_dq_array[i*13+4];
	assign phy2clb_rd_dq5[i*8+:8] = phy2clb_rd_dq_array[i*13+5];
	assign phy2clb_rd_dq6[i*8+:8] = phy2clb_rd_dq_array[i*13+6];
	assign phy2clb_rd_dq7[i*8+:8] = phy2clb_rd_dq_array[i*13+7];
	assign phy2clb_rd_dq8[i*8+:8] = phy2clb_rd_dq_array[i*13+8];
	assign phy2clb_rd_dq9[i*8+:8] = phy2clb_rd_dq_array[i*13+9];
	assign phy2clb_rd_dq10[i*8+:8] = phy2clb_rd_dq_array[i*13+10];
	assign phy2clb_rd_dq11[i*8+:8] = phy2clb_rd_dq_array[i*13+11];
	assign phy2clb_rd_dq12[i*8+:8] = phy2clb_rd_dq_array[i*13+12];
     if(|RXTX_BITSLICE_EN[i*13+:13]) begin : xiphy_byte_wrapper
       for (i_low=0; i_low<=5; i_low=i_low+1)
         begin: I_BITSLICE_LOWER
         if (RXTX_BITSLICE_EN[i*13+i_low]) begin: GEN_RXTX_BITSLICE_EN
           ddr4_phy_v2_2_0_bitslice_behav #(
	             .TX_OUTPUT_PHASE_90  (TX_OUTPUT_PHASE_90[i*13+i_low])
         	    ,.DATA_WIDTH          (DATA_WIDTH)
         	    ,.DIV_MODE            (DIV_MODE)
		          ,.tCK		              (tCK)
		          ,.DRAM_TYPE	          (DRAM_TYPE)
			  ,.INIT		(INIT[i*15+i_low])
			  ,.PING_PONG_CH1_BYTES_MAP (PING_PONG_CH1_BYTES_MAP[i])
           ) bitslice_behav_inst_lower (
               .in		(clb2phy_wr_dq_array[i*13+i_low])
              ,.iob_in	(iob2phy_d_in_byte[i*13+i_low])
              ,.out_data      (phy2clb_rd_dq_array[i*13+i_low])
              ,.fifo_empty	(phy2clb_fifo_empty[i*13+i_low])
              ,.in_clk       (clb2phy_fifo_clk[i*13+i_low])
              ,.rst          (clb2phy_ctrl_rst_low[i])
              ,.o_clk        (pll_clk0[i])
             	,.dqs_in       (dqs_in)
             	,.dqs_in_ch1   (dqs_in_ch1)
              ,.t_state      (clb2phy_t_b_low[i*4+:4])
              ,.mcal_clb2phy_rden (clb2phy_rden_low[i*4+:4])
              ,.mcal_clb2phy_fifo_rden (clb2phy_fifo_rden[i*13+i_low])
              ,.o            (phy2iob_q_out_byte[i*13+i_low])
              ,.tri_out      (phy2iob_t[i*13+i_low])
           );
	       end
 	     end
       for (i_upp=0; i_upp<=6; i_upp=i_upp+1)
         begin: I_BITSLICE_UPPER
         if (RXTX_BITSLICE_EN[i*13+6+i_upp]) begin: GEN_RXTX_BITSLICE_EN
           ddr4_phy_v2_2_0_bitslice_behav #(
	               .TX_OUTPUT_PHASE_90  (TX_OUTPUT_PHASE_90[i*13+6+i_upp])
         	      ,.DATA_WIDTH          (DATA_WIDTH)
         	      ,.DIV_MODE            (DIV_MODE)
		            ,.tCK		              (tCK)
		            ,.DRAM_TYPE	          (DRAM_TYPE) 
			    ,.INIT		(INIT[i*15+6+i_upp])
			    ,.PING_PONG_CH1_BYTES_MAP (PING_PONG_CH1_BYTES_MAP[i])
	         ) bitslice_behav_inst_upper (
	      		 .in		(clb2phy_wr_dq_array[i*13+6+i_upp])
	      		,.iob_in	(iob2phy_d_in_byte[i*13+6+i_upp])
	      		,.out_data      (phy2clb_rd_dq_array[i*13+6+i_upp])
	      		,.fifo_empty	(phy2clb_fifo_empty[i*13+6+i_upp])
	      		,.in_clk       (clb2phy_fifo_clk[i*13+6+i_upp])
	      		,.rst          (clb2phy_ctrl_rst_upp[i])
	      		,.o_clk        (pll_clk0[i])
	        	,.dqs_in       (dqs_in)
            ,.dqs_in_ch1   (dqs_in_ch1)
	      		,.t_state      (clb2phy_t_b_upp[i*4+:4])
	      		,.mcal_clb2phy_rden (clb2phy_rden_upp[i*4+:4])
	      		,.mcal_clb2phy_fifo_rden (clb2phy_fifo_rden[i*13+6+i_upp])
	      		,.o            (phy2iob_q_out_byte[i*13+6+i_upp])
	      		,.tri_out      (phy2iob_t[i*13+6+i_upp])
	         );
	       end
	     end
     end
  end
endgenerate

reg [2:0] cnt = '0;

// Assert fixdly_rdy and phy_rdy after 5 ctrl_clk cycles.
always@(posedge clb2phy_ctrl_clk_upp[0]) begin
  if(clb2phy_ctrl_rst_upp)begin
    phy2clb_fixdly_rdy_upp <= 'b0 ;
    phy2clb_fixdly_rdy_low <= 'b0 ;
    phy2clb_phy_rdy_upp	   <= 'b0 ;
    phy2clb_phy_rdy_low	   <= 'b0 ;
  end else begin
    if(cnt < 'd5) begin
	    cnt <= cnt  + 1 ;
    end else begin
      phy2clb_fixdly_rdy_upp 	<= '1;
      phy2clb_fixdly_rdy_low 	<= '1;
      phy2clb_phy_rdy_upp	<= '1;
      phy2clb_phy_rdy_low	<= '1;
    end 
  end 
end 
endmodule

//bitslice behavioral model
module ddr4_phy_v2_2_0_bitslice_behav #(
         parameter TX_OUTPUT_PHASE_90      = 1'b0
        ,parameter integer DATA_WIDTH                      = 8
        ,parameter   [1:0] DIV_MODE                        = 2'b00
	,parameter IN_DLY      = 0
	,parameter O_DLY = 1
	,parameter TCQ = 10 
	,parameter tCK = 1250 
	,parameter         DRAM_TYPE = "DDR4"
	,parameter INIT = 0
	,parameter PING_PONG_CH1_BYTES_MAP = 1'b0
	)(
	 input [7:0] in // from fabric/memory controller
	,input iob_in // from iob
	,output  reg   [7:0] out_data // To MC
	,output     fifo_empty
	,input 	     in_clk
	,input	     rst
	,input	     o_clk
	,input	     dqs_in 
	,input	     dqs_in_ch1 
	,input [3:0]  t_state
	,input [3:0] mcal_clb2phy_rden 
	,input 	     mcal_clb2phy_fifo_rden
	,output	     o 
	,output	reg  tri_out 
	);

reg [2:0] cnt ;//for div_clk generation and to count w.r.to o_clk
wire [7:0] out_data_tmp ;//ouput from fifo to MC
reg [7:0] out_data_tmp_r1 ;//delayed ouput data from fifo 
reg [7:0] out_data_tmp_r2 ; 
reg [7:0] out_data_tmp_r3 ; 
reg o_out ;//serialised input data from MC after delayed based on O_DLY parameter
reg o_in ;//delayed version of input data from iob
reg [7:0] in_r ;//one cycle delayed input data from MC 
reg [7:0] in_r1 ; 
reg [7:0] in_r2 ;
reg [7:0] in_r3 ;
reg [7:0] in_final ;//Final input data from MC based on O_DLY parameter
reg [3:0] t_state_r ;//one cycle delayed t_state from MC
reg [3:0] t_state_r1 ; 
reg [3:0] t_state_r2 ;
reg [3:0] t_state_r3 ;
reg [3:0] t_state_r4 ;
reg [3:0] t_state_final ;//Final t_state from MC based on O_DLY parameter
reg[3:0] mcal_clb2phy_rden_r ;//one cycle delayed mcal_clb2phy_rden 
reg[3:0] mcal_clb2phy_rden_r1 ;
reg[3:0] mcal_clb2phy_rden_r2 ;
reg[3:0] mcal_clb2phy_rden_r3 ;
wire o_clk_d ;//delayed version of o_clk
reg o_clk_rd ;//delayed version of o_clk_d
reg [1:0] dqs_in_ch1_valid  = 0 ;//read dqs based on rd_en  
reg [1:0] dqs_in_valid  = 0 ;//read dqs based on rd_en  
reg [1:0] dqs_in_valid_r ;//registered dqs_in_valid
reg [1:0] dqs_in_ch1_valid_r ;//registered dqs_in_valid
reg [2:0] dq_in_cnt = 0 ;//read dq count
wire data_in_valid ;//read data valid based read dqs_in_valid 
reg [2:0] rd_en ;//rd_en based on oclk_rd and cnt value 
reg div_clk = 1'b0;//divde 
reg o_out_90 ;//90 degree version of o_out
reg[7:0] out ;//deserialised data from IOB 
reg[7:0] wr_data ;//Fifo write data
reg div_clk_wr = 1 ;//Fifo write clock

initial begin
	o_out = INIT;
	o_out_90 = INIT;
end

//CLK DIV
always @(cnt[2] or rst) begin
 if (rst == 1'b1)
   div_clk <= 1'b0;
 else if (o_clk === 1'b1)
  div_clk <= ~div_clk;
 else
  div_clk <= div_clk;
end

//Increment counter for every posedge o_clk
always@(posedge o_clk or posedge rst )begin
  if(rst)begin
    cnt <= #TCQ 3'b111 ;
  end else begin
    cnt <= #TCQ cnt + 1 ;
  end 
end 

//#1 delay to avoid race condition between cnt and o_clk.
assign #1 o_clk_d = o_clk ; 

always@(*)begin
  o_clk_rd <= #((tCK/8)+(tCK/4)) o_clk ; //delayed version to capture read data
end 

//MEMORY CONTROLLER TO IOB WRITE LOGIC 
//Sampling of input data and t_state(from fabric/memory controller) w.r.t div_clk
always@(posedge div_clk)begin
  in_r <= #TCQ in ;
  in_r1 <= #TCQ in_r ;
  in_r2 <= #TCQ in_r1 ;
  in_r3 <= #TCQ in_r2 ;
  t_state_r <= #TCQ t_state ;
  t_state_r1 <= #TCQ t_state_r ;
  t_state_r2 <= #TCQ t_state_r1 ;
  t_state_r3 <= #TCQ t_state_r2 ;
  t_state_r4 <= #TCQ t_state_r3 ;
end

// Delaying input data and t_state from fabric/memory controller based on O_DLY parameter.
always@(posedge div_clk or posedge rst)begin
  if(rst) begin
      in_final <= 0;
      in_r <= 0; 
      in_r1 <= 0;
      in_r2 <= 0; 
      in_r3 <= 0;
  end
  else
  begin		  
  case(O_DLY)
    'd0 : begin  in_final <= in  ; t_state_final <= t_state_r;  end 
    'd1 : begin  in_final <= in_r ; t_state_final <= t_state_r1 ;  end
    'd2 : begin  in_final <= in_r1 ; t_state_final <= t_state_r2 ;  end
    'd3 : begin  in_final <= in_r2 ; t_state_final <= t_state_r3 ;  end
    'd4 : begin  in_final <= in_r3 ; t_state_final <= t_state_r4 ;  end
  endcase
  end
end 

//Serializing input data after it is delayed.
always@(posedge o_clk_d or posedge rst)begin
    if(rst) begin
	o_out <= 0;
    end
    else
    begin		    
    case(cnt)
      'd0 : o_out <=  in_final[0];
      'd1 : o_out <=  in_final[1];
      'd2 : o_out <=  in_final[2];
      'd3 : o_out <=  in_final[3];
      'd4 : o_out <=  in_final[4];
      'd5 : o_out <=  in_final[5];
      'd6 : o_out <=  in_final[6];
      'd7 : o_out <=  in_final[7];
    endcase
    end
end

//90 degree version of o_out is required if TX_OUTPUT_PHASE_90 is 1 
always@(*)begin
 o_out_90 <= #(tCK/4) o_out ;
end 

//Serializing T input after it is delayed.#tCK/4 is for dq/dqs alignment
always@(posedge o_clk_d)begin
//  if(|t_state_final) begin //Fix for tWPST Violation for Ranks=4
    case(cnt)
      'd0 : tri_out <= #(tCK/4) (t_state_final[0]) ? 1'b0 : 1'b1 ;
      'd1 : tri_out <= #(tCK/4) (t_state_final[0]) ? 1'b0 : 1'b1 ;
      'd2 : tri_out <= #(tCK/4) (t_state_final[1]) ? 1'b0 : 1'b1 ;
      'd3 : tri_out <= #(tCK/4) (t_state_final[1]) ? 1'b0 : 1'b1 ;
      'd4 : tri_out <= #(tCK/4) (t_state_final[2]) ? 1'b0 : 1'b1 ;
      'd5 : tri_out <= #(tCK/4) (t_state_final[2]) ? 1'b0 : 1'b1 ;
      'd6 : tri_out <= #(tCK/4) (t_state_final[3]) ? 1'b0 : 1'b1 ;
      'd7 : tri_out <= #(tCK/4) (t_state_final[3]) ? 1'b0 : 1'b1 ;
    endcase
  //end else begin
  //  tri_out <= 1'b1 ;
  //end
end

assign o = (TX_OUTPUT_PHASE_90 == 1'b1) ? o_out_90 : o_out;

//IOB TO MEMORY CONTROLLER READ LOGIC
//Sampling of mcal_clb2phy_rden(from fabric/memory controller) w.r.t div_clk
always@(posedge div_clk or posedge rst)begin
  if(rst) begin
     mcal_clb2phy_rden_r  <= #TCQ 'b0 ;
     mcal_clb2phy_rden_r1 <= #TCQ 'b0;
     mcal_clb2phy_rden_r2 <= #TCQ 'b0;
     mcal_clb2phy_rden_r3 <= #TCQ 'b0;
  end else begin
  mcal_clb2phy_rden_r <= #TCQ mcal_clb2phy_rden ;
  mcal_clb2phy_rden_r1 <= #TCQ mcal_clb2phy_rden_r ;
  mcal_clb2phy_rden_r2 <= #TCQ mcal_clb2phy_rden_r1;
  mcal_clb2phy_rden_r3 <= #TCQ mcal_clb2phy_rden_r2;
  end
end 

//Serializing mcal_clb2phy_rden after it is delayed.
always@(posedge o_clk_rd or posedge rst) begin
  if(rst)
     rd_en <= #TCQ 'b0;
  else begin 
 case(cnt)
   'd0 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[0];
   'd1 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[0];
   'd2 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[1];
   'd3 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[1];
   'd4 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[2];
   'd5 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[2];
   'd6 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[3];
   'd7 : rd_en[0] <= #TCQ mcal_clb2phy_rden_r2[3];
 endcase
 rd_en[1] <= #TCQ rd_en[0] ; 
 rd_en[2] <= #TCQ rd_en[1] ; 
  end
end

//valid read dqs generation based on rd_en
always@(posedge o_clk_rd or posedge rst)begin
  if(rst)begin
    dqs_in_valid <= #TCQ 'b0;
    dqs_in_ch1_valid <= #TCQ 'b0;
  end else if(|(rd_en))begin
    dqs_in_valid[0] <= dqs_in ;
    dqs_in_valid[1] <= dqs_in_valid[0] ;
    dqs_in_ch1_valid[0] <= dqs_in_ch1 ;
    dqs_in_ch1_valid[1] <= dqs_in_ch1_valid[0] ;
  end
end 

//Registered version of valid read dqs
always@(posedge o_clk_rd or posedge rst)begin
  if(rst) begin
    dqs_in_valid_r <= #TCQ 'b0;
    dqs_in_ch1_valid_r <= #TCQ 'b0;
  end else begin
    dqs_in_valid_r <= #1 dqs_in_valid ;
    dqs_in_ch1_valid_r <= #1 dqs_in_ch1_valid ;
  end 
end 

//data_in_valid is asserted when dqs_in_valid or dqs_in_valid_r toggles
always@(*)begin
 o_in <= #(tCK/2) iob_in ;
end 
// assign data_in_valid = (^dqs_in_valid_r) | (^dqs_in_valid) |(^dqs_in_ch1_valid_r) |(^dqs_in_ch1_valid);
assign data_in_valid = (PING_PONG_CH1_BYTES_MAP == 1'b0)? ((^dqs_in_valid_r) | (^dqs_in_valid)): ((^dqs_in_ch1_valid_r) |(^dqs_in_ch1_valid));

//increment dq_in_cnt based on data_in_valid and o_clk_rd
always@(posedge o_clk_rd or negedge data_in_valid)begin
  if(~data_in_valid)begin
    dq_in_cnt <= 0 ;
  end else begin
      dq_in_cnt <= dq_in_cnt + 1 ;
  end 
end 

//fifo write clock generation based on dq_in_cnt[2]
always@(*)begin
  div_clk_wr <= #50 ~dq_in_cnt[2] ;
end 

//Deserializing input data coming from IOB.
always@(posedge o_clk_rd or posedge rst ) begin
  if(rst)begin
    out <= 'b0 ;
  end else begin
    if(data_in_valid)begin
        case(dq_in_cnt)
          'd0 : out[0] <= data_in_valid ? o_in : out[0];
          'd1 : out[1] <= data_in_valid ? o_in : out[1];
          'd2 : out[2] <= data_in_valid ? o_in : out[2];
          'd3 : out[3] <= data_in_valid ? o_in : out[3];
          'd4 : out[4] <= data_in_valid ? o_in : out[4];
          'd5 : out[5] <= data_in_valid ? o_in : out[5];
          'd6 : out[6] <= data_in_valid ? o_in : out[6];
          'd7 : out[7] <= data_in_valid ? o_in : out[7];
        endcase
    end
  end
end 

always@(*)begin
  wr_data = out ;
end

//Delaying fifo output data going to fabric/memory controller
always@(posedge in_clk)begin
  out_data_tmp_r1 <= #TCQ out_data_tmp ;
  out_data_tmp_r2 <= #TCQ out_data_tmp_r1 ;
  out_data_tmp_r3 <= #TCQ out_data_tmp_r2 ;
end

//Delaying fifo output data going to fabric/memory controller based on IN_DLY parameter.
always@(*)begin
if(rst)begin
    out_data <= 'b0 ;
  end else begin
  case(IN_DLY)
    'd0 : begin  out_data <= out_data_tmp   ; end
    'd1 : begin  out_data <= out_data_tmp_r1 ;  end
    'd2 : begin  out_data <= out_data_tmp_r2 ;  end
    'd3 : begin  out_data <= out_data_tmp_r3 ;  end
    default : begin out_data <= out_data_tmp ;  end
  endcase
end 
end 

//Fifo to handle asyncronous clocks and enables.
  ddr4_phy_v2_2_0_fifo_sv #(
	 .DEPTH (16) 
	)u_fifo_sv (
	  .rd_clk	 (in_clk)
	 ,.wr_clk        (div_clk_wr) 
	 ,.wr_data       (wr_data)
	 ,.rd_en         (mcal_clb2phy_fifo_rden)
	 ,.wr_en         (data_in_valid)
	 ,.rst           (rst)
	 ,.empty         (fifo_empty)
	 ,.rd_data       (out_data_tmp)
	);


endmodule

module ddr4_phy_v2_2_0_fifo_sv #(
	 parameter DEPTH = 8 
	)(
	  input rd_clk
	 ,input wr_clk
	 ,input [7:0] wr_data
	 ,input rd_en 
	 ,input	wr_en
	 ,input rst
	 ,output reg empty
	 ,output reg [7:0] rd_data
	);
reg full;
bit[7:0] fifo_array [$] ;
reg empty_tmp , empty_tmp_r ,empty_tmp_r1  ;
reg [7:0] rd_data_int ;

//writing to the fifo
always@(posedge wr_clk or posedge rst)begin
  if(rst)begin
   fifo_array = {};
  end else begin
    if(wr_en & !full)begin
      fifo_array.push_back(wr_data) ;
    end 
  end 
end 

//Reading from fifo
always@(posedge rd_clk or posedge rst)begin
  if(rst)begin
    rd_data <= 'b0 ;
  end else begin
    if(rd_en & !empty_tmp)begin
      rd_data_int <= fifo_array.pop_front();
    end 
    if(fifo_array.size() > 0 )begin
      rd_data <= fifo_array[0] ;
    end
  end 
end

//Assert full flag when FIFO is full
always@(posedge wr_clk)begin
 if(rst)begin
   full <= 1'b0 ;
 end else begin
   if(fifo_array.size() == DEPTH) begin
     full <= 1'b1 ;
   end else begin
     full <= 1'b0 ;
   end 
 end
end 

//Assert empty flag if FIFO is empty
always@(posedge rd_clk or posedge rst)begin
 if(rst)begin
   empty_tmp <= 1'b1 ;
 end else begin
  if(fifo_array.size() > 0) begin
    empty_tmp <= 1'b0 ;
  end else begin
    empty_tmp <= 1'b1 ;
  end 
 end 
end

always@(posedge rd_clk)begin
  empty_tmp_r  <= empty_tmp    ;
  empty_tmp_r1 <= empty_tmp_r  ;
  empty        <= empty_tmp_r ;
end 

endmodule

