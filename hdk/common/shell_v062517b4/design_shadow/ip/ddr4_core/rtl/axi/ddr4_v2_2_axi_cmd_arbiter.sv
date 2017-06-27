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
//  /   /         Filename           : ddr4_v2_2_0_axi_cmd_arbiter.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale 
//Design Name: AXI Slave
//Purpose:
// Description: 
// This arbiter arbitrates commands from the read and write address channels
// of AXI to the single CMD channel of the MC interface.  The inputs are the
// read and write commands that have already been translated to the MC
// format.
//
//Reference:
//Revision History:
//*****************************************************************************
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_cmd_arbiter #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // Width of cmd_byte_addr
                    // Range: 30
  parameter integer C_MC_ADDR_WIDTH =   30,
                    
                    // write command starve limit in read priority reg mode
                    // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN = 1,
  parameter integer C_AXI_WR_STARVE_LIMIT = 256,
                   // log2 of C_AXI_WR_STARVE_LIMIT ceil (log2(C_AXI_WR_STARVE_LIMIT))
  parameter integer C_AXI_STARVE_CNT_WIDTH = 8,
  parameter         C_RD_WR_ARB_ALGORITHM = "RD_PRI_REG"
                    // Indicates the Arbitration
                    // Allowed values - "TDM", "ROUND_ROBIN",
                    // "RD_PRI_REG", "RD_PRI_REG_STARVE_LIMIT"
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI Slave Interface
  // Slave Interface System Signals           
  input  wire                                 clk              , 
  input  wire                                 reset            , 

  input  wire                                 awvalid     ,
  input  wire [3:0]                           awqos       ,
  input  wire                                 wr_cmd_en        , 
  input  wire                                 wr_cmd_en_last   ,
  input  wire [2:0]                           wr_cmd_instr     , 
  input  wire [C_MC_ADDR_WIDTH-1:0]           wr_cmd_byte_addr , 
  output wire                                 wr_cmd_full      , 

  input  wire                                 arvalid     ,
  input  wire [3:0]                           arqos       ,
  input  wire                                 rd_cmd_en        , 
  input  wire                                 rd_cmd_en_last   ,
  input  wire [2:0]                           rd_cmd_instr     , 
  input  wire [C_MC_ADDR_WIDTH-1:0]           rd_cmd_byte_addr ,  
  output wire                                 rd_cmd_full      , 

  output wire                                 mc_app_en        , 
  output wire [2:0]                           mc_app_cmd       , 
  output wire                                 mc_app_size      , 
  output wire [C_MC_ADDR_WIDTH-1:0]           mc_app_addr      ,
  output wire                                 mc_app_hi_pri    , 
  output wire                                 mc_app_autoprecharge, 
  input  wire                                 mc_app_rdy

);



////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////

wire rnw;
////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
assign mc_app_en     = rnw ? rd_cmd_en        : wr_cmd_en;
assign mc_app_cmd    = rnw ? rd_cmd_instr     : wr_cmd_instr;
assign mc_app_addr   = rnw ? rd_cmd_byte_addr : wr_cmd_byte_addr;
assign mc_app_size   = 1'b0; 
assign wr_cmd_full   = rnw ? 1'b1 : ~mc_app_rdy;
assign rd_cmd_full   = ~rnw ? 1'b1 : ~mc_app_rdy;
assign mc_app_hi_pri = 1'b0;
assign mc_app_autoprecharge = 1'b0;
   
                        

generate
  // TDM Arbitration scheme
  if (C_RD_WR_ARB_ALGORITHM == "TDM") begin : TDM
    reg rnw_i;
    always @(posedge clk) begin
      if (reset) begin
        rnw_i <= 1'b0;
      end else begin
        rnw_i <= ~rnw_i;
      end
    end
    assign rnw = rnw_i;
  end
  else if (C_RD_WR_ARB_ALGORITHM == "ROUND_ROBIN") begin : ROUND_ROBIN
    reg rnw_i;
    always @(posedge clk) begin
      if (reset) begin
        rnw_i <= 1'b0;
      end else begin
        rnw_i <= ~rnw;
      end
    end
    assign rnw = (rnw_i & rd_cmd_en) | (~rnw_i & rd_cmd_en & ~wr_cmd_en);
  end
  else if (C_RD_WR_ARB_ALGORITHM == "RD_PRI_REG") begin : RD_PRI_REG
    reg rnw_i;
    reg rd_cmd_hold;
    reg wr_cmd_hold;
    reg [4:0] rd_wait_limit;
    reg [4:0] wr_wait_limit;
    reg [9:0] rd_starve_cnt;
    reg [9:0] wr_starve_cnt;

    always @(posedge clk) begin
      if (~rnw | ~rd_cmd_hold) begin
        rd_wait_limit <= 5'b0;
        rd_starve_cnt <= (C_MC_BURST_LEN * 2);
      end else if (mc_app_rdy) begin
        if (~arvalid | rd_cmd_en)
          rd_wait_limit <= 5'b0;
        else
          rd_wait_limit <= rd_wait_limit + C_MC_BURST_LEN;

        if (rd_cmd_en & ~rd_starve_cnt[8])
          rd_starve_cnt <= rd_starve_cnt + C_MC_BURST_LEN;
      end
    end

    always @(posedge clk) begin
      if (rnw | ~wr_cmd_hold) begin
        wr_wait_limit <= 5'b0;
        wr_starve_cnt <= (C_MC_BURST_LEN * 2);
      end else if (mc_app_rdy) begin
        if (~awvalid | wr_cmd_en)
          wr_wait_limit <= 5'b0;
        else
          wr_wait_limit <= wr_wait_limit + C_MC_BURST_LEN;

        if (wr_cmd_en & ~wr_starve_cnt[8])
          wr_starve_cnt <= wr_starve_cnt + C_MC_BURST_LEN;
      end
    end
    always @(posedge clk) begin
      if (reset) begin
        rd_cmd_hold <= 1'b0;
        wr_cmd_hold <= 1'b0;
      end else begin
        rd_cmd_hold <= (rnw | rd_cmd_hold) & ~(rd_cmd_en_last & ((awvalid & (|awqos)) | rd_starve_cnt[8])) & ~rd_wait_limit[4];
        wr_cmd_hold <= (~rnw | wr_cmd_hold) & ~(wr_cmd_en_last & ((arvalid & (|arqos)) | wr_starve_cnt[8])) & ~wr_wait_limit[4];
      end
    end

    always @(posedge clk) begin
      if (reset)
        rnw_i <= 1'b1;
      else
        rnw_i <= rnw;
    end
    assign rnw = (rnw_i & ~(rd_cmd_hold & arvalid) & awvalid) ? 1'b0 :  // RD -> WR
                 (~rnw_i & ~(wr_cmd_hold & awvalid) & arvalid) ? 1'b1 : // WR -> RD
                 rnw_i;
  end // block: RD_PRI_REG
  else if (C_RD_WR_ARB_ALGORITHM == "RD_PRI_REG_STARVE_LIMIT") begin : RD_PRI_REG_STARVE
    reg rnw_i;
    reg rd_cmd_en_d1;
    reg wr_cmd_en_d1;
    reg [C_AXI_STARVE_CNT_WIDTH-1:0] wr_starve_cnt;
    reg wr_enable;
    reg [8:0] rd_starve_cnt;

  // write starve count logic.
  // wr_enable to give priority to write commands will be set
  // when the write commands have been starved till the starve
  // limit. The wr_enable will be de-asserted when the pending write
  // command is processed or if the rd has been starved for 256 clock
  // cycles. 
   always @(posedge clk) begin
     if(reset | ( ~(wr_cmd_en | wr_cmd_en_d1))
        | rd_starve_cnt[8])begin
       wr_starve_cnt <= 'b0;
       wr_enable <=  'b0;
     end else if(wr_cmd_en & (mc_app_rdy)) begin 
       if(wr_starve_cnt < (C_AXI_WR_STARVE_LIMIT-1))
         wr_starve_cnt <= wr_starve_cnt + rnw_i;
       else
         wr_enable <= 1'b1;
     end // if (wr_cmd_en & (mc_app_rdy)
    end // always @ (posedge clk)

   // The rd command should not be starved for ever in this mode.
   // The maximum the read will starve is 256 clocks. 
   always @(posedge clk) begin
     if(reset | rnw_i)begin
       rd_starve_cnt <= 'b0;
     end else if(rd_cmd_en & (mc_app_rdy)) begin 
       rd_starve_cnt <= rd_starve_cnt + 1;
     end // if (wr_cmd_en & (mc_app_rdy)
    end // always @ (posedge clk)    

    always @(posedge clk) begin
      if (reset) begin
        rd_cmd_en_d1 <= 1'b0;
        wr_cmd_en_d1 <= 1'b0;
      end else begin
      if (mc_app_rdy) begin
        rd_cmd_en_d1 <= rd_cmd_en & rnw;
        wr_cmd_en_d1 <= wr_cmd_en & ~rnw;
      end
     end
    end
    always @(posedge clk) begin
      if (reset) begin
        rnw_i <= 1'b1;
      end else begin
        // Only set RNW to 0 if there is a write pending and read is idle
       // rnw_i <= ~((wr_cmd_en | wr_cmd_en_d1) & (~rd_cmd_en) & (~rd_cmd_en_d1));
        rnw_i <= ~(((wr_cmd_en | wr_cmd_en_d1) & (~rd_cmd_en) & (~rd_cmd_en_d1)) | wr_enable);
      end
    end
    assign rnw = rnw_i;
  end
  else if (C_RD_WR_ARB_ALGORITHM == "RD_PRI") begin : RD_PRI
    assign rnw = ~(wr_cmd_en & ~rd_cmd_en);
  end
  else if (C_RD_WR_ARB_ALGORITHM == "WR_PR_REG") begin : WR_PR_REG
    reg rnw_i;
    always @(posedge clk) begin
      if (reset) begin
        rnw_i <= 1'b0;
      end else begin
        // Only set RNW to 1 if there is a read pending and write is idle
        // rnw_i <= (~wr_cmd_en & rd_cmd_en);
        rnw_i <=  (~awvalid & arvalid);
      end
    end
    assign rnw = rnw_i;
  end
  else begin : WR_PR // if (C_RD_WR_ARB_ALGORITHM == "WR_PR") begin
    // assign rnw =  (~wr_cmd_en & rd_cmd_en);
    assign rnw =  (~awvalid & arvalid);
  end
endgenerate

endmodule
`default_nettype wire

