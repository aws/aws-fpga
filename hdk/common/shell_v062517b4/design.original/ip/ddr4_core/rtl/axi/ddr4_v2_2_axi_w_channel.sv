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
//  /   /         Filename           : ddr4_v2_2_0_axi_w_channel.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Apr 17 2014
//  \___\/\___\
//
//Device: UltraScale
//Design Name: AXI Slave
//Purpose:
// Description:
// write data channel module is used to buffer the write data from AXI, mask extra transactions 
// that are not needed in BL8 mode and send them to the MC write data FIFO. 
// The use of register slice could result in write data arriving to this modules well before the 
// the commands are processed by the address modules. The data from AXI will be buffered 
// in the write data FIFO before being sent to the MC.
// The address channel modules will send signals to mask appropriate data to before being sent 
// to the MC. 
//Reference:
//Revision History:
//*****************************************************************************

`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_w_channel #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
                    // Width of AXI xDATA and MCB xx_data
                    // Range: 32, 64, 128.
  parameter integer C_DATA_WIDTH              = 32,
                        // MC burst length. = 1 for BL4 or BC4, = 2 for BL8
  parameter integer C_MC_BURST_LEN              = 1,
                    // axi addr width 
  parameter integer C_AXI_ADDR_WIDTH            = 32,
                    // ECC
  parameter         C_ECC               = "OFF"
)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  input  wire                                 clk         , 
  input  wire                                 reset   , 

  input  wire [C_DATA_WIDTH-1:0]              wdata,
  input  wire [C_DATA_WIDTH/8-1:0]            wstrb,
  input  wire                                 wvalid,
  output reg                                  wready,

  input  wire                                 awvalid,
  input  wire                                 w_cmd_rdy,
  input  wire                                 w_ignore_begin,
  input  wire                                 w_ignore_end,
  
  output wire                                 cmd_wr_bytes,
 
  output wire                                 mc_app_wdf_wren,
  output wire  [C_DATA_WIDTH/8-1:0]           mc_app_wdf_mask,
  output wire [C_DATA_WIDTH-1:0]              mc_app_wdf_data,
  output wire                                 mc_app_wdf_last,
  input  wire                                 mc_app_wdf_rdy,

  output wire                                 w_data_rdy
);

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
//states
localparam SM_FIRST_DATA   = 1'b0;
localparam SM_SECOND_DATA  = 1'b1;

////////////////////////////////////////////////////////////////////////////////
// Wire and register declarations
////////////////////////////////////////////////////////////////////////////////
reg  [C_DATA_WIDTH/8-1:0] wdf_mask;
reg  [C_DATA_WIDTH-1:0]   wdf_data;
reg                       valid;

wire                      wdf_last;
wire                      assert_wren;
wire                      disable_data;
wire [C_DATA_WIDTH/8-1:0] next_wdf_mask;
wire [C_DATA_WIDTH-1:0]   next_wdf_data;
wire                      fsm_ready;
wire                      wvalid_int;

wire [C_DATA_WIDTH-1:0]   next_mc_app_wdf_data;
wire                      next_mc_app_wdf_wren;
wire [C_DATA_WIDTH/8-1:0] next_mc_app_wdf_mask;
wire                      next_mc_app_wdf_last;

reg                       mc_app_wdf_wren_reg;
reg  [C_DATA_WIDTH/8-1:0] mc_app_wdf_mask_reg;
reg [C_DATA_WIDTH-1:0]    mc_app_wdf_data_reg;
reg                       mc_app_wdf_last_reg;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
assign wvalid_int = wready ? wvalid : valid;

always @(posedge clk) begin
  if(reset) begin
    valid <= 1'b0;
    wready <= 1'b0;
  end else begin
    valid <= wvalid_int;
    wready <= ~wvalid_int | fsm_ready;
  end
end

assign fsm_ready         = (assert_wren & ~disable_data);

assign mc_app_wdf_wren = next_mc_app_wdf_wren;
assign mc_app_wdf_last = next_mc_app_wdf_last;
assign mc_app_wdf_mask = next_mc_app_wdf_mask;
assign mc_app_wdf_data = next_mc_app_wdf_data;

assign next_mc_app_wdf_wren = mc_app_wdf_rdy ? assert_wren : mc_app_wdf_wren_reg;
assign next_mc_app_wdf_last = mc_app_wdf_rdy ? wdf_last : mc_app_wdf_last_reg;
assign next_mc_app_wdf_mask = mc_app_wdf_rdy ? ((disable_data)? {C_DATA_WIDTH/8{1'b1}} : next_wdf_mask) : mc_app_wdf_mask_reg;
assign next_mc_app_wdf_data = mc_app_wdf_rdy ? next_wdf_data : mc_app_wdf_data_reg;

always @(posedge clk) begin
  if(reset) begin
    mc_app_wdf_wren_reg <= 1'b0;
    mc_app_wdf_last_reg <= 1'b0;
    mc_app_wdf_mask_reg <= {C_DATA_WIDTH/8{1'b0}};
  end else begin
    mc_app_wdf_wren_reg <= next_mc_app_wdf_wren;
    mc_app_wdf_last_reg <= next_mc_app_wdf_last;
    mc_app_wdf_mask_reg <= next_mc_app_wdf_mask;
  end
end

always @(posedge clk) begin
  mc_app_wdf_data_reg <= next_mc_app_wdf_data;
end

assign next_wdf_mask = wready ? ~wstrb : wdf_mask;
assign next_wdf_data = wready ? wdata : wdf_data;

always @(posedge clk) begin
  wdf_mask <= next_wdf_mask;
  wdf_data <= next_wdf_data;
end

generate
  if(C_MC_BURST_LEN == 1) begin : gen_bc1
    // w_data_rdy to axi_mc_cmd_fsm when one Bl8 or Bl4 worth of write data 
    // is pumped into to MC WDF.  
    assign w_data_rdy = wvalid_int & mc_app_wdf_rdy;

    // write enable signal to WDF
    assign assert_wren = w_cmd_rdy;
    assign wdf_last = w_cmd_rdy;
    assign disable_data = 1'b0;

  end else begin : gen_bc2
    // Declaration of signals used only in BC2 mode
    reg                       state;
    reg                       next_state;
    reg                       w_ignore_end_r;

    always @(posedge clk) begin
      if (reset)
        state <= SM_FIRST_DATA;
      else
        state <= next_state;
    end

    // Next state transitions.
    // Simple state machine to push data into the MC write data FIFO(WDF). 
    // For BL4 only one data will be written into the WDF.  For BL8 two 
    // beats of data will be written into the WDF. 
    always @(*)
    begin
      next_state = state;
      case (state)
        SM_FIRST_DATA:
          if(awvalid & wvalid_int & mc_app_wdf_rdy)
            next_state = SM_SECOND_DATA; 
          else 
            next_state = state;

        SM_SECOND_DATA:
          if(w_cmd_rdy)
            next_state = SM_FIRST_DATA;
          else
            next_state = state;

        default:
          next_state = SM_FIRST_DATA;
      endcase // case(state)
    end // always @ (*)

    // w_data_rdy to axi_mc_cmd_fsm when one Bl8 or Bl4 worth of write data 
    // is pumped into to MC WDF.  
    assign w_data_rdy = ((state == SM_SECOND_DATA) & (wvalid_int | w_ignore_end_r) & mc_app_wdf_rdy);

    // write enable signal to WDF
    assign assert_wren = ((state == SM_FIRST_DATA) & (next_state == SM_SECOND_DATA)) |
                         ((state == SM_SECOND_DATA) & (next_state == SM_FIRST_DATA));

    assign wdf_last = w_cmd_rdy;

    always @(posedge clk) begin
      w_ignore_end_r <= w_ignore_end;
    end

    // Disable data by asserting all the MASK signals based on the
    // ignore signals from the address modules 
    assign disable_data = (((state == SM_FIRST_DATA) & w_ignore_begin) |
                         ((state == SM_SECOND_DATA) & w_ignore_end_r));

  end // if (C_MC_BURST_LEN == 1)
endgenerate 

generate
  if(C_ECC == "ON") begin : gen_ecc
    if(C_MC_BURST_LEN == 1) begin : gen_ecc1
      assign cmd_wr_bytes = |next_mc_app_wdf_mask;

    end else begin : gen_ecc2

      wire  mask_or;
      reg  pre_mask_or;
      
      assign cmd_wr_bytes = (pre_mask_or | mask_or);

      assign mask_or = |next_mc_app_wdf_mask; 
      
      always @(posedge clk)
        if (next_mc_app_wdf_wren & mc_app_wdf_rdy)
          pre_mask_or <= mask_or;

    end // if (C_MC_BURST_LEN == 1)
  end // if (C_ECC == "ON")
endgenerate 

endmodule
`default_nettype wire

