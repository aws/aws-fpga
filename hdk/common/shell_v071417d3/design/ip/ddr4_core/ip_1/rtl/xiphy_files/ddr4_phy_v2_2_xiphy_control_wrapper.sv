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
//  /   /         Filename           : ddr4_phy_v2_2_0_xiphy_control_wrapper.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR3 SDRAM & DDR4 SDRAM
// Purpose          :
//                   ddr4_phy_v2_2_0_xiphy_control_wrapper module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps / 1ps

module ddr4_phy_v2_2_0_xiphy_control_wrapper #(
    parameter          EN_OTHER_PCLK    =  "FALSE",    //PCLK from other bitslice not used
    parameter          EN_OTHER_NCLK    =  "FALSE",    //NCLK from other bitslice not used 
    parameter          EN_DYN_ODLY_MODE =  "FALSE",    //Dynamic LD, CE, INC Control of ODELAY false 
    parameter          SERIAL_MODE  	=  "FALSE",    //SGMII mode disabled for DDR3
    parameter          RX_CLK_PHASE_P   =  "SHIFT_0",  //No shift on read clock relative to DQ
    parameter          RX_CLK_PHASE_N   =  "SHIFT_0",  //No shift on read clock relative to DQ
    parameter          INV_RXCLK        =  "FALSE",    //Don't invert clock path from RX Bitslice
    parameter          TX_GATING        =  "DISABLE",  //Write clock gating disabled
    parameter          RX_GATING        =  "ENABLE",   //Read DQS gating enabled 
    parameter          SELF_CALIBRATE   =  "ENABLE",   //BISC Self Calibration enabled
    parameter integer  READ_IDLE_COUNT  =  31,         //Gap count between read bursts
    parameter          DIV_MODE	        =  "DIV4",     //Controller mode div2/div4 
    parameter          REFCLK_SRC       =  "PLLCLK",   //input clock for delay control 
    parameter integer  ROUNDING_FACTOR  =  16,         //0 to 255
    parameter          CTRL_CLK	        =  "EXTERNAL", //DIV_CLK, RIU_CLK
    parameter          EN_CLK_TO_EXT_NORTH = "DISABLE",//Global inter-byte clocking disabled for DDR3 
    parameter          EN_CLK_TO_EXT_SOUTH = "DISABLE", //Global inter-byte clocking disabled for DDR3  
    parameter          IDLY_VT_TRACK    = "TRUE",      // VT Tracking for IDELAYs  
    parameter          ODLY_VT_TRACK    = "TRUE",      // VT Tracking for ODELAYs  
    parameter          QDLY_VT_TRACK    = "TRUE",      // VT Tracking for Quarter DELAYs  
    parameter          RXGATE_EXTEND    = "FALSE",     // Extend RX_GATE for extended  Preamble
    parameter          SIM_DEVICE       = "ULTRASCALE"
) (
    //BITSLICE_CONTROL
//    input         bisc_start_in,          
//    input         bisc_stop_in,          
//    output        bisc_start_out,          
//    output        bisc_stop_out,          
    input         pll_clk,              //PLL CLK
    input         refclk,               //Global clock to ddr_clk path in TxClkGen
    input         clb2phy_ctrl_rst,   //From Fabric. Active low asynchronous user reset
    input         en_vtc,               //From Fabric. Enable VTC tracking
    output        phy2clb_fixdly_rdy,   //To Fabric. Indicates fixed delay calibration complete and fabric can start eye training
    output        phy2clb_phy_rdy,      //To Fabric. PHY calibration is complete
    input         riu_clk,              //From Fabric. RIU system clock 
    input [5:0 ]  clb2riu_addr,         //From Fabric. Address of the register
    input [15:0]  clb2riu_wr_data,      //From Fabric. Write data to the register
    output [15:0] riu2clb_rd_data,      //To Fabric. Read data to the controller
    output        riu2clb_valid,        //To Fabric. Read valid to the controller
    input         clb2riu_wr_en,        //From Fabric. Active high register write enable
    input         clb2riu_nibble_sel,   //From Fabric. Nibble select to enable RIU register read/write
    input [3:0]   clb2phy_rdcs0,        //From Fabric. Selects one of four ranks for read rank switching
    input [3:0]   clb2phy_rdcs1,        //From Fabric. Selects one of four ranks for read rank switching
    input [3:0]   clb2phy_wrcs0,        //From Fabric. Selects one of four ranks for write rank switching
    input [3:0]   clb2phy_wrcs1,        //From Fabric. Selects one of four ranks for write rank switching
    input [3:0]   clb2phy_t_b,          //From Fabric. Tristate output enable and Write ClkGen
    input [3:0]   clb2phy_rden,         //From Fabric. Read burst enable
    output [6:0]  dyn_dci_out,          //To BitSlice. Local ODT per Bitslice
    input         clk_from_ext,         //Interbyte clock coming from north or south byte
    output        clk_to_ext_south,     //Interbyte clock going to south 
    output        clk_to_ext_north,     //Interbyte clock going to north 
    input         pdqs_gt_in,           //From Other control block. PDQS strobe
    input         ndqs_gt_in,           //From Other control block. NDQS strobe 
    output        pdqs_gt_out,          //To Other control block. PDQS strobe
    output        ndqs_gt_out,          //To Other control block. NDQS strobe
/*    input         rx_pdq0_in,           //From data sample of Rxp BitSlice0 
//    input         rx_ndq0_in,           //From data sample of Rxn Bitslice0
//    input         rx_pdq1_in,           //From data sample of Rxp BitSlice1 
//    input         rx_ndq1_in,           //From data sample of Rxn Bitslice1
//    input         rx_pdq2_in,           //From data sample of Rxp BitSlice2 
//    input         rx_ndq2_in,           //From data sample of Rxn Bitslice2
//    input         rx_pdq3_in,           //From data sample of Rxp BitSlice3 
//    input         rx_ndq3_in,           //From data sample of Rxn Bitslice3
//    input         rx_pdq4_in,           //From data sample of Rxp BitSlice4 
//    input         rx_ndq4_in,           //From data sample of Rxn Bitslice4
//    input         rx_pdq5_in,           //From data sample of Rxp BitSlice5 
//    input         rx_ndq5_in,           //From data sample of Rxn Bitslice5
//    input         rx_pdq6_in,           //From data sample of Rxp BitSlice6 
//    input         rx_ndq6_in,           //From data sample of Rxn Bitslice6
*/
//    output        ififo_wrclk,          //DIVCLK to Bitslices and FIFO wrclk

    //Ribbon cable output bus to all bitslices in nibble
    //{pdqs_out, ndqs_out, ctrl_clk}
    //output [2:0]  rx_nib_ctrl_out,
    
    //Ribbon cable output buses to per bitslice0-6
    //{pdqs_out[0-6], ndqs_out[0-6], idelay_ctrl_clk[0-6], bs_reset[0-6], refclk_en[0-6], bs_dq_en[0-6], bs_dqs_en[0-6], ififo_bypass[0-6], idelay_ce_out[0-6], idelay_inc_out[0-6], idelay_ld_out[0-6], idelay00-06_out[8:0], rx_dcc00-06[3:0]}
    output [39:0] rx_bit_ctrl_out0,
    output [39:0] rx_bit_ctrl_out1,
    output [39:0] rx_bit_ctrl_out2,
    output [39:0] rx_bit_ctrl_out3,
    output [39:0] rx_bit_ctrl_out4,
    output [39:0] rx_bit_ctrl_out5,
    output [39:0] rx_bit_ctrl_out6,
    
    //Ribbon cable input buses from per bitslice0-6
    //{rx_pdq[0-6]_in, rx_ndq[0-6]_in, fixdlyratio_idelay00-06[17:0], fixed_idelay00-06, bs2ctl_refclk_en_mask[0-6], bs2ctl_riu_bs_dq_en[0-6], bs2ctl_riu_bs_dqs_en[0-6], vtc_ready_idelay00-06, dqs_in[0-6], idelay00-06_in[8:0]}
    input  [39:0] rx_bit_ctrl_in0,
    input  [39:0] rx_bit_ctrl_in1,
    input  [39:0] rx_bit_ctrl_in2,
    input  [39:0] rx_bit_ctrl_in3,
    input  [39:0] rx_bit_ctrl_in4,
    input  [39:0] rx_bit_ctrl_in5,
    input  [39:0] rx_bit_ctrl_in6,

    //Ribbon cable output bus to TX bitslices in nibble
    //{ddr_strb_out, div2_strb_out, div_clk_out, ctrl_clk}
    //output [3:0]  tx_nib_ctrl_out,

    //Ribbon cable output bus to 13th TX bitslice
    //{ddr_clk_out, div2_clk_out, div_clk_out, ctrl_clk}
    //output [3:0]  tx_nib_ctrl_out6,

    //Ribbon cable output buses to per TX bitslice0-6
    //{div_clk_out[0-6], div2_clk_out[0-6], ddr_clk_out[0-6], wl_train, tx_data_phase[0-6], bs_reset[0-6], ph02_div2_360, ph13_div2_360, ph0_div_720, ph1_div_720, ph2_div_720, ph3_div_720, \
    //toggle_div2_sel, dynamic_mode_en, odelay_ce_out[0-6], odelay_inc_out[0-6], odelay_ld_out[0-6], odelay00-06_out[8:0], odelay_ctrl_clk[0-6]}
    output [39:0] tx_bit_ctrl_out0,
    output [39:0] tx_bit_ctrl_out1,
    output [39:0] tx_bit_ctrl_out2,
    output [39:0] tx_bit_ctrl_out3,
    output [39:0] tx_bit_ctrl_out4,
    output [39:0] tx_bit_ctrl_out5,
    output [39:0] tx_bit_ctrl_out6,

    //Ribbon cable output bus to tristate bitslice
    //{div_clk_out[7], div2_clk_out[7], ddr_clk_out[7], force_oe_b, en_div_dly_oe[7:0], tx_data_phase7, bs_reset_tri, ph02_div2_360, ph13_div2_360, ph0_div_720, ph1_div_720, ph2_div_720, ph3_div_720, \
    //toggle_div2_sel, dynamic_mode_en, tristate_odelay_ce_out, tristate_odelay_inc_out, tristate_odelay_ld_out, tristate_odelay_out[8:0], odelay_ctrl_clk[7]}
    output [39:0] tx_bit_ctrl_out_tri, 

    //Ribbon cable input buses to per TX bitslice0-6
    //{bs2ctl_riu_tx_data_phase[0-6], fixdlyratio_odelay00-06[17:0], fixed_odelay00-06, vtc_ready_odelay00-06, odelay00-06_in[8:0]}
    input  [39:0] tx_bit_ctrl_in0,
    input  [39:0] tx_bit_ctrl_in1,
    input  [39:0] tx_bit_ctrl_in2,
    input  [39:0] tx_bit_ctrl_in3,
    input  [39:0] tx_bit_ctrl_in4,
    input  [39:0] tx_bit_ctrl_in5,
    input  [39:0] tx_bit_ctrl_in6,

    //Ribbon cable input bus to tristate bitslice
    //{bs2ctl_riu_tx_data_phase[7], tristate_vtc_ready, tristate_odelay_in[8:0]}
    input  [39:0]  tx_bit_ctrl_in_tri
);

wire ififo_bypass;
wire ififo_reset;

`ifdef ULTRASCALE_PHY_BLH
B_BITSLICE_CONTROL #(
`else
BITSLICE_CONTROL #(
`endif
   .EN_OTHER_PCLK	        (EN_OTHER_PCLK),       //PCLK from other bitslice not used
   .EN_OTHER_NCLK	        (EN_OTHER_NCLK),       //NCLK from other bitslice not used 
   .SERIAL_MODE  	        (SERIAL_MODE),         //SGMII mode disabled for DDR3
   .RX_CLK_PHASE_P  	        (RX_CLK_PHASE_P),      //SHIFT_0 or SHIFT_90 on dqs_p
   .RX_CLK_PHASE_N  	        (RX_CLK_PHASE_N),      //SHIFT_0 or SHIFT_90 on dqs_n 
   .INV_RXCLK                   (INV_RXCLK),           //Don't invert clock path from RX Bitslice
   .TX_GATING                   (TX_GATING),           //ENABLE, DISABLE Write clock gating disabled
   .RX_GATING                   (RX_GATING),           //ENABLE, DISABLE Read DQS gating enabled 
   .READ_IDLE_COUNT             (READ_IDLE_COUNT),     //0 to 63      (Gap count between read bursts)
   .DIV_MODE	                (DIV_MODE),            //DIV2, DIV4 Controller mode
   .REFCLK_SRC	                (REFCLK_SRC),          //PLLCLK, REFCLK to clkgen
   .ROUNDING_FACTOR             (ROUNDING_FACTOR),     //0 to 255
   .CTRL_CLK	                (CTRL_CLK),            //DIV_CLK, RIU_CLK
   .SELF_CALIBRATE              (SELF_CALIBRATE),      //BISC Self Calibration (ENABLE, DISABLE)
   .EN_CLK_TO_EXT_NORTH         (EN_CLK_TO_EXT_NORTH), //Global inter-byte clocking disabled for DDR3 
   .EN_CLK_TO_EXT_SOUTH         (EN_CLK_TO_EXT_SOUTH), //Global inter-byte clocking disabled for DDR3  
   .EN_DYN_ODLY_MODE            (EN_DYN_ODLY_MODE),     //Dynamic LD, CE, INC Control of ODELAY (TRUE,FALSE)   
   .IDLY_VT_TRACK               (IDLY_VT_TRACK),       // Enables VT Tracking for IDELAYs
   .ODLY_VT_TRACK               (ODLY_VT_TRACK),       // Enables VT Tracking for ODELAYs
   .QDLY_VT_TRACK               (QDLY_VT_TRACK),       // Enables VT Tracking for Quarter DELAYs
`ifndef ULTRASCALE_PHY_BLH
   .SIM_DEVICE                  (SIM_DEVICE),
`endif
   .RXGATE_EXTEND               (RXGATE_EXTEND)         // Extend Read Preamble
) 
xiphy_control
(
   .PLL_CLK	                (pll_clk),
   .REFCLK                      (refclk),
   .RST                         (clb2phy_ctrl_rst),
   .EN_VTC                      (en_vtc),  
   .DLY_RDY     	        (phy2clb_fixdly_rdy),
   .VTC_RDY     	        (phy2clb_phy_rdy),
   .RIU_CLK	                (riu_clk),
   .RIU_ADDR	                (clb2riu_addr),
   .RIU_WR_DATA	                (clb2riu_wr_data),
   .RIU_RD_DATA   	        (riu2clb_rd_data),
   .RIU_VALID	                (riu2clb_valid),
   .RIU_WR_EN	                (clb2riu_wr_en),
   .RIU_NIBBLE_SEL              (clb2riu_nibble_sel),
   .PHY_RDCS0	                (clb2phy_rdcs0),
   .PHY_RDCS1	                (clb2phy_rdcs1),
   .PHY_WRCS0	                (clb2phy_wrcs0),
   .PHY_WRCS1	                (clb2phy_wrcs1),
   .TBYTE_IN	                (clb2phy_t_b),
   .PHY_RDEN	                (clb2phy_rden),
   .DYN_DCI	                (dyn_dci_out),
   .CLK_FROM_EXT                (clk_from_ext),
   .CLK_TO_EXT_NORTH            (clk_to_ext_north),
   .CLK_TO_EXT_SOUTH            (clk_to_ext_south),
   .PCLK_NIBBLE_IN              (pdqs_gt_in),
   .NCLK_NIBBLE_IN              (ndqs_gt_in),
   .PCLK_NIBBLE_OUT             (pdqs_gt_out),
   .NCLK_NIBBLE_OUT	        (ndqs_gt_out),
/*
//   .SAMPLE_FIFO_BITSLICE0_BIT7  (rx_pdq0_in), 
//   .SAMPLE_FIFO_BITSLICE0_BIT3  (rx_ndq0_in),  
//   .SAMPLE_FIFO_BITSLICE1_BIT7  (rx_pdq1_in),  
//   .SAMPLE_FIFO_BITSLICE1_BIT3  (rx_ndq1_in),  
//   .SAMPLE_FIFO_BITSLICE2_BIT7  (rx_pdq2_in),  
//   .SAMPLE_FIFO_BITSLICE2_BIT3  (rx_ndq2_in),  
//   .SAMPLE_FIFO_BITSLICE3_BIT7  (rx_pdq3_in),  
//   .SAMPLE_FIFO_BITSLICE3_BIT3  (rx_ndq3_in), 
//   .SAMPLE_FIFO_BITSLICE4_BIT7  (rx_pdq4_in),  
//   .SAMPLE_FIFO_BITSLICE4_BIT3  (rx_ndq4_in),  
//   .SAMPLE_FIFO_BITSLICE5_BIT7  (rx_pdq5_in), 
//   .SAMPLE_FIFO_BITSLICE5_BIT3  (rx_ndq5_in),
//   .SAMPLE_FIFO_BITSLICE6_BIT7  (rx_pdq6_in),      
//   .SAMPLE_FIFO_BITSLICE6_BIT3  (rx_ndq6_in),
*/
   //.RX_NIB_CTRL_OUT	        (rx_nib_ctrl_out),  
   .RX_BIT_CTRL_OUT0	        (rx_bit_ctrl_out0), 
   .RX_BIT_CTRL_OUT1	        (rx_bit_ctrl_out1), 
   .RX_BIT_CTRL_OUT2	        (rx_bit_ctrl_out2), 
   .RX_BIT_CTRL_OUT3	        (rx_bit_ctrl_out3), 
   .RX_BIT_CTRL_OUT4	        (rx_bit_ctrl_out4), 
   .RX_BIT_CTRL_OUT5	        (rx_bit_ctrl_out5), 
   .RX_BIT_CTRL_OUT6	        (rx_bit_ctrl_out6),
   .RX_BIT_CTRL_IN0	        (rx_bit_ctrl_in0), 
   .RX_BIT_CTRL_IN1	        (rx_bit_ctrl_in1),
   .RX_BIT_CTRL_IN2	        (rx_bit_ctrl_in2),
   .RX_BIT_CTRL_IN3	        (rx_bit_ctrl_in3),
   .RX_BIT_CTRL_IN4	        (rx_bit_ctrl_in4),
   .RX_BIT_CTRL_IN5	        (rx_bit_ctrl_in5),
   .RX_BIT_CTRL_IN6	        (rx_bit_ctrl_in6),
   //.TX_NIB_CTRL_OUT	        (tx_nib_ctrl_out),  
   //.TX_NIB_CTRL_OUT6	        (tx_nib_ctrl_out6),   
   .TX_BIT_CTRL_OUT0	        (tx_bit_ctrl_out0),
   .TX_BIT_CTRL_OUT1	        (tx_bit_ctrl_out1),
   .TX_BIT_CTRL_OUT2	        (tx_bit_ctrl_out2),
   .TX_BIT_CTRL_OUT3	        (tx_bit_ctrl_out3),
   .TX_BIT_CTRL_OUT4	        (tx_bit_ctrl_out4),
   .TX_BIT_CTRL_OUT5	        (tx_bit_ctrl_out5),
   .TX_BIT_CTRL_OUT6	        (tx_bit_ctrl_out6),
   .TX_BIT_CTRL_OUT_TRI	        (tx_bit_ctrl_out_tri),
   .TX_BIT_CTRL_IN0	        (tx_bit_ctrl_in0), 
   .TX_BIT_CTRL_IN1	        (tx_bit_ctrl_in1),
   .TX_BIT_CTRL_IN2	        (tx_bit_ctrl_in2),
   .TX_BIT_CTRL_IN3	        (tx_bit_ctrl_in3),
   .TX_BIT_CTRL_IN4	        (tx_bit_ctrl_in4),
   .TX_BIT_CTRL_IN5	        (tx_bit_ctrl_in5),
   .TX_BIT_CTRL_IN6	        (tx_bit_ctrl_in6),
   .TX_BIT_CTRL_IN_TRI          (tx_bit_ctrl_in_tri)
);

endmodule

