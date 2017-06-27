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
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_tristate_wrapper.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR3 SDRAM & DDR4 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_xiphy_tristate_wrapper module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps / 1ps

module ddr4_phy_v2_2_0_xiphy_tristate_wrapper #(

   parameter integer   DATA_WIDTH	= 8,           //8, 4, 1-bit interface 
   parameter           INIT             = 1'b0,        //Initial Oserdes value
   parameter           DELAY_TYPE       = "FIXED",     //FIXED, VAR_LOAD, VARIABLE type of ODELAY     
   parameter           DELAY_FORMAT     = "TIME",      //TIME (mc_fixed_dly_ratio = (2*9)*(1000000/REFCLK_FREQ/DELAY_VAL), COUNT (mc_fixed_delay_ratio={9'b0, DELAY_VAL})
   parameter           UPDATE_MODE      = "ASYNC",     //ASYNC (mc_le_manual=0,mc_le_async=1), SYNC(mc_le_manual=0,mc_le_sync=0), MANUAL (mc_le_manual=1,mc_le_async=0)
   parameter           DELAY_VAL        = 0,           //0 to 1250 ps
   parameter real      REFCLK_FREQ	= 300.0,       //300-2667 MHz
   parameter           OUTPUT_PHASE_90  = "FALSE",      //Delay DQ phase by 90 wrt write DQS
   parameter           NATIVE_ODELAY_BYPASS  = "FALSE",     //Delay DQ phase by 90 wrt write DQS
   parameter           SIM_DEVICE            = "ULTRASCALE"
) (
  input          ce,                 // odelay ce
  input          clk,                // odelay clk
  input          inc,                // odelay inc
  input          ld,                 // odelay ld
  input  [8:0]   cntvaluein,         // odelay 
  output [8:0]   cntvalueout,        // odelay cntvalueout
  output         q,                  // TX q output
  input          regrst,             // odelay reset
  input          rst,                // oserdes reset
  input          en_vtc,             // odelay en_vtc
  //Ribbon cable input bus from bitslice control 
//  input  [3:0]   nib_ctrl_in,        // {ddr_clk, div2_clk, div4_clk, ctrl_clk}  

  //Ribbon cable per-bit input bus from bitslice control 
  input  [39:0]  bit_ctrl_in,
  // {div4_clk, div2_clk, ddr_clk, force_oe_b, d[7:0], ctl2bs_tx_ddr_phase_sel, tx_bs_reset, tx_mux_360_p_sel, tx_mux_360_n_sel, tx_mux_720_p0_sel, tx_mux_720_p1_sel, tx_mux_720_p2_sel, tx_mux_720_p3_sel, 
  //toggle_div2_sel, ctl2bs_dynamic_mode_en, ctrl_ce, ctrl_inc, ctrl_ld, ctrl_dly[8:0], ctrl_clk}  

  //Ribbon cable per-bit output bus to bitslice control 
  //{bs2ctl_tx_ddr_phase_sel, vtc_ready, cntvalueout[8:0]}         
//  input  [10:0]  bit_ctrl_out 
  output  [39:0]  bit_ctrl_out

);

`ifdef ULTRASCALE_PHY_BLH
B_TX_BITSLICE_TRI #(
`else
TX_BITSLICE_TRI #(
`endif
   .DATA_WIDTH              (DATA_WIDTH),       //8, 2, 1
   .DELAY_FORMAT            (DELAY_FORMAT),     //TIME, COUNT
   .UPDATE_MODE             (UPDATE_MODE),      //SYNC, ASYNC, MANUAL 
   .INIT	                (INIT),             //Initial Oserdes value             
   .DELAY_TYPE   	        (DELAY_TYPE),       //FIXED, VAR_LOAD, VARIABLE
   .DELAY_VALUE	            (DELAY_VAL),        //0 to 1250 ps
   .REFCLK_FREQUENCY	    (REFCLK_FREQ),      //300-2667
   .OUTPUT_PHASE_90	        (OUTPUT_PHASE_90),   //delay output phase by 90
`ifndef ULTRASCALE_PHY_BLH
   .SIM_DEVICE              (SIM_DEVICE),
`endif
   .NATIVE_ODELAY_BYPASS    (NATIVE_ODELAY_BYPASS)
) 
xiphy_bitslice_write
(
   .CE                      (ce),
   .CLK                     (clk),
   .INC                     (inc),
   .LOAD                    (ld),
   .CNTVALUEIN              (cntvaluein),
   .CNTVALUEOUT             (cntvalueout),
   .TRI_OUT                 (q),
   .RST_DLY                 (regrst),
   .RST                     (rst),
   .EN_VTC                  (en_vtc),
 //  .NIB_CTRL_IN             (nib_ctrl_in),
   .BIT_CTRL_IN             (bit_ctrl_in),
   .BIT_CTRL_OUT            (bit_ctrl_out)
);

endmodule

