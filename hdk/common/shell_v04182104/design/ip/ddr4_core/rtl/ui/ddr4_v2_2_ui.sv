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
// /___/  \  /    Vendor                : Xilinx
// \   \   \/     Version               : 1.1
//  \   \         Application           : MIG
//  /   /         Filename              : ddr4_v2_2_10_ui.sv
// /___/   /\     Date Last Modified    : $Date$
// \   \  /  \    Date Created          : Thu Apr 18 2013
//  \___\/\___\
//
//Device            : UltraScale
//Design Name       : DDR3 SDRAM & DDR4 SDRAM
//Purpose           :
//Reference         :
//Revision History  :
//*****************************************************************************

// Top level of simple user interface.


`timescale 1 ps / 1 ps

module ddr4_v2_2_10_ui #
  (
   parameter MEM                  = "DDR4",
   parameter TCQ                  = 100,
   parameter ADDR_WIDTH           = 33,
   parameter APP_DATA_WIDTH       = 256,
   parameter APP_MASK_WIDTH       = 32,
   parameter BANK_WIDTH           = 2,
   parameter BANK_GROUP_WIDTH     = 2,
   parameter COL_WIDTH            = 10,
   parameter DATA_BUF_ADDR_WIDTH  = 5,
   parameter EARLY_WR_DATA        = "OFF",
   parameter ECC                  = "OFF",
   parameter ECC_TEST             = "OFF",
   parameter ORDERING             = "NORM",
   parameter nCK_PER_CLK          = 2, 
   parameter RANKS                = 4,
   parameter REG_CTRL             = "OFF", // "ON" for registered DIMM
   parameter RANK_WIDTH           = 1,
   parameter ROW_WIDTH            = 18,
   parameter AUTO_AP_COL_A3       = "OFF",
   parameter S_HEIGHT             = 1,
   parameter LR_WIDTH             = 1,
   parameter MEM_ADDR_ORDER       = "TG_TEST"
  )
  (/*AUTOARG*/
  // Outputs
  wr_data_mask, wr_data, use_addr, size, row, raw_not_ecc, rank, lr,
  hi_priority, autoprecharge, data_buf_addr, col, cmd, bank, group, app_wdf_rdy, app_rdy,
  app_rd_data_valid, app_rd_data_end, app_rd_data,
  app_ecc_multiple_err, correct_en, sr_req, ref_req, app_ref_ack,
  zq_req, app_zq_ack, ui_busy,
  // Inputs
  wr_data_offset, wr_data_en, wr_data_addr, rst, rd_data_offset,
  rd_data_end, rd_data_en, rd_data_addr, rd_data, ecc_multiple, clk,
  app_wdf_wren, app_wdf_mask, app_wdf_end, app_wdf_data, app_sz,
  app_raw_not_ecc, app_hi_pri, app_autoprecharge, app_en, app_cmd, app_addr, accept_ns,
  accept, app_correct_en, app_sr_req, app_ref_req, ref_ack,
  app_zq_req, zq_ack, mc_block_req
  );

  input accept;
 // localparam ADDR_WIDTH = RANK_WIDTH + BANK_GROUP_WIDTH + BANK_WIDTH + ROW_WIDTH + COL_WIDTH;
  

  input app_correct_en;
  output wire correct_en;
  assign correct_en = app_correct_en;
  
  input app_sr_req;
  output wire sr_req;
  assign sr_req = app_sr_req;
  
  input app_ref_req;
  output wire ref_req;
  assign ref_req = app_ref_req;
  
  input ref_ack;
  output wire app_ref_ack;
  assign app_ref_ack = ref_ack;
  
  input app_zq_req;
  output wire zq_req;
  assign zq_req = app_zq_req;
  
  input zq_ack;
  output wire app_zq_ack;
  assign app_zq_ack = zq_ack;

  input                 mc_block_req;
  input                 accept_ns;              // To ui_cmd0 of ui_cmd.sv
  input [ADDR_WIDTH-1:0] app_addr;              // To ui_cmd0 of ui_cmd.sv
  input [2:0]           app_cmd;                // To ui_cmd0 of ui_cmd.sv
  input                 app_en;                 // To ui_cmd0 of ui_cmd.sv
  input                 app_hi_pri;             // To ui_cmd0 of ui_cmd.sv
  input                 app_autoprecharge;      // To ui_cmd0 of ui_cmd.sv
  input [2*nCK_PER_CLK-1:0]           app_raw_not_ecc;        // To ui_wr_data0 of ui_wr_data.sv
  input                 app_sz;                 // To ui_cmd0 of ui_cmd.sv
  input [APP_DATA_WIDTH-1:0] app_wdf_data;      // To ui_wr_data0 of ui_wr_data.sv
  input                 app_wdf_end;            // To ui_wr_data0 of ui_wr_data.sv
  input [APP_MASK_WIDTH-1:0] app_wdf_mask;      // To ui_wr_data0 of ui_wr_data.sv
  input                 app_wdf_wren;           // To ui_wr_data0 of ui_wr_data.sv
  input                 clk;                    // To ui_cmd0 of ui_cmd.sv, ...
  input [2*nCK_PER_CLK-1:0]           ecc_multiple;           // spyglass disable W498   waiver expires 14.4      To ui_rd_data0 of ui_rd_data.sv
  input [APP_DATA_WIDTH-1:0] rd_data;           // To ui_rd_data0 of ui_rd_data.sv
  input [DATA_BUF_ADDR_WIDTH-1:0] rd_data_addr; // To ui_rd_data0 of ui_rd_data.sv
  input                 rd_data_en;             // To ui_rd_data0 of ui_rd_data.sv
  input                 rd_data_end;            // To ui_rd_data0 of ui_rd_data.sv
  input                 rd_data_offset;         // To ui_rd_data0 of ui_rd_data.sv
  input                 rst;                    // To ui_cmd0 of ui_cmd.sv, ...
  input [DATA_BUF_ADDR_WIDTH-1:0] wr_data_addr; // spyglass disable W498            To ui_wr_data0 of ui_wr_data.sv
  input                 wr_data_en;             // To ui_wr_data0 of ui_wr_data.sv
  input                 wr_data_offset;         // To ui_wr_data0 of ui_wr_data.sv

  output [2*nCK_PER_CLK-1:0]          app_ecc_multiple_err;   // From ui_rd_data0 of ui_rd_data.sv
  output [APP_DATA_WIDTH-1:0] app_rd_data;      // From ui_rd_data0 of ui_rd_data.sv
  output                app_rd_data_end;        // From ui_rd_data0 of ui_rd_data.sv
  output                app_rd_data_valid;      // From ui_rd_data0 of ui_rd_data.sv
  output                app_rdy;                // From ui_cmd0 of ui_cmd.sv
  output                app_wdf_rdy;            // From ui_wr_data0 of ui_wr_data.sv
  output [BANK_WIDTH-1:0] bank;                 // From ui_cmd0 of ui_cmd.sv
  output [BANK_GROUP_WIDTH-1:0] group;          // From ui_cmd0 of ui_cmd.sv
  output [2:0]          cmd;                    // From ui_cmd0 of ui_cmd.sv
  output [COL_WIDTH-1:0] col;                   // From ui_cmd0 of ui_cmd.sv
  output [DATA_BUF_ADDR_WIDTH-1:0]data_buf_addr;// From ui_cmd0 of ui_cmd.sv
  output                hi_priority;            // From ui_cmd0 of ui_cmd.sv
  output                autoprecharge;          // From ui_cmd0 of ui_cmd.sv
  output [RANK_WIDTH-1:0] rank;                 // From ui_cmd0 of ui_cmd.sv
  output [2*nCK_PER_CLK-1:0]          raw_not_ecc;            // From ui_wr_data0 of ui_wr_data.sv
  output [ROW_WIDTH-1:0] row;                   // From ui_cmd0 of ui_cmd.sv
  output                size;                   // From ui_cmd0 of ui_cmd.sv
  output                use_addr;               // From ui_cmd0 of ui_cmd.sv
  output [APP_DATA_WIDTH-1:0] wr_data;          // From ui_wr_data0 of ui_wr_data.sv
  output [APP_MASK_WIDTH-1:0] wr_data_mask;     // From ui_wr_data0 of ui_wr_data.sv
  output  wire 		ui_busy;
  output [LR_WIDTH-1:0] lr;
  // End of automatics

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire [3:0] ram_init_addr;                     // From ui_rd_data0 of ui_rd_data.sv
  wire [3:0]            ram_init_done_r;        // From ui_rd_data0 of ui_rd_data.sv
  wire                  rd_accepted;            // From ui_cmd0 of ui_cmd.sv
  wire                  rd_buf_full;            // From ui_rd_data0 of ui_rd_data.sv
  wire [DATA_BUF_ADDR_WIDTH-1:0]rd_data_buf_addr_r;// From ui_rd_data0 of ui_rd_data.sv
  wire                  wr_accepted;            // From ui_cmd0 of ui_cmd.sv
  wire [DATA_BUF_ADDR_WIDTH-1:0] wr_data_buf_addr;// From ui_wr_data0 of ui_wr_data.sv
  wire                  wr_req_16;              // From ui_wr_data0 of ui_wr_data.sv
  // End of automatics

  (* keep = "TRUE" *) reg rst_r1;

  always @(posedge clk)
    rst_r1 <= rst;

  // In the UI, the read and write buffers are allowed to be asymmetric to
  // to maximize read performance, but the MC's native interface requires
  // symmetry, so we zero-fill the write pointer
  generate
    if(DATA_BUF_ADDR_WIDTH > 4) begin
      assign wr_data_buf_addr[DATA_BUF_ADDR_WIDTH-1:4] = 0;
    end
  endgenerate

  ddr4_v2_2_10_ui_cmd #
    (/*AUTOINSTPARAM*/
     // Parameters
     .MEM                               (MEM),
     .TCQ                               (TCQ),
     .ADDR_WIDTH                        (ADDR_WIDTH),
     .BANK_WIDTH                        (BANK_WIDTH),
     .BANK_GROUP_WIDTH                  (BANK_GROUP_WIDTH),
     .COL_WIDTH                         (COL_WIDTH),
     .DATA_BUF_ADDR_WIDTH               (DATA_BUF_ADDR_WIDTH),
     .RANK_WIDTH                        (RANK_WIDTH),
     .ROW_WIDTH                         (ROW_WIDTH),
     .S_HEIGHT                          (S_HEIGHT),
     .LR_WIDTH                          (LR_WIDTH),
     .RANKS                             (RANKS),
     .AUTO_AP_COL_A3                    (AUTO_AP_COL_A3),
     .MEM_ADDR_ORDER                    (MEM_ADDR_ORDER))
    u_ddr_ui_cmd
      (/*AUTOINST*/
       // Outputs
       .app_rdy                         (app_rdy),
       .use_addr                        (use_addr),
       .rank                            (rank[RANK_WIDTH-1:0]),
       .lr                              (lr[LR_WIDTH-1:0]),
       .bank                            (bank[BANK_WIDTH-1:0]),
       .group                           (group[BANK_GROUP_WIDTH-1:0]),
       .row                             (row[ROW_WIDTH-1:0]),
       .col                             (col[COL_WIDTH-1:0]),
       .size                            (size),
       .cmd                             (cmd[2:0]),
       .hi_priority                     (hi_priority),
       .autoprecharge                   (autoprecharge),
       .rd_accepted                     (rd_accepted),
       .wr_accepted                     (wr_accepted),
       .data_buf_addr                   (data_buf_addr),
       // Inputs
       .rst                             (rst_r1),
       .clk                             (clk),
       .accept_ns                       (accept_ns),
       .rd_buf_full                     (rd_buf_full),
       .wr_req_16                       (wr_req_16),
       .app_addr                        (app_addr[ADDR_WIDTH-1:0]),
       .app_cmd                         (app_cmd[2:0]),
       .app_sz                          (app_sz),
       .app_hi_pri                      (app_hi_pri),
       .app_autoprecharge               (app_autoprecharge),
       .app_en                          (app_en),
       .wr_data_buf_addr                (wr_data_buf_addr),
       .rd_data_buf_addr_r              (rd_data_buf_addr_r),
       .ui_busy                         (ui_busy),
       .mc_block_req                    (mc_block_req)
       );

  ddr4_v2_2_10_ui_wr_data #
    (/*AUTOINSTPARAM*/
     // Parameters
     .TCQ                               (TCQ),
     .APP_DATA_WIDTH                    (APP_DATA_WIDTH),
     .APP_MASK_WIDTH                    (APP_MASK_WIDTH),
     .nCK_PER_CLK                       (nCK_PER_CLK),
     .EARLY_WR_DATA                     (EARLY_WR_DATA),
     .ECC                               (ECC),
     .ECC_TEST                          (ECC_TEST))
    u_ddr_ui_wr_data
      (/*AUTOINST*/
       // Outputs
       .app_wdf_rdy                     (app_wdf_rdy),
       .wr_req_16                       (wr_req_16),
       .wr_data_buf_addr                (wr_data_buf_addr[3:0]),
       .wr_data                         (wr_data[APP_DATA_WIDTH-1:0]),
       .wr_data_mask                    (wr_data_mask[APP_MASK_WIDTH-1:0]),
       .raw_not_ecc                     (raw_not_ecc[2*nCK_PER_CLK-1:0]),
       // Inputs
       .rst                             (rst_r1),
       .clk                             (clk),
       .app_wdf_data                    (app_wdf_data[APP_DATA_WIDTH-1:0]),
       .app_wdf_mask                    (app_wdf_mask[APP_MASK_WIDTH-1:0]),
       .app_raw_not_ecc                 (app_raw_not_ecc[2*nCK_PER_CLK-1:0]),
       .app_wdf_wren                    (app_wdf_wren),
       .app_wdf_end                     (app_wdf_end),
       .wr_data_offset                  (wr_data_offset),
       .wr_data_addr                    (wr_data_addr[3:0]),
       .wr_data_en                      (wr_data_en),
       .wr_accepted                     (wr_accepted),
       .ram_init_done_r                 (ram_init_done_r),
       .ram_init_addr                   (ram_init_addr));

  ddr4_v2_2_10_ui_rd_data #
    (/*AUTOINSTPARAM*/
     // Parameters
     .TCQ                               (TCQ),
     .APP_DATA_WIDTH                    (APP_DATA_WIDTH),
     .DATA_BUF_ADDR_WIDTH               (DATA_BUF_ADDR_WIDTH),
     .nCK_PER_CLK                       (nCK_PER_CLK),
     .ECC                               (ECC),
     .ORDERING                          (ORDERING))
    u_ddr_ui_rd_data
      (/*AUTOINST*/
       // Outputs
       .ram_init_done_r                 (ram_init_done_r),
       .ram_init_addr                   (ram_init_addr),
       .app_rd_data_valid               (app_rd_data_valid),
       .app_rd_data_end                 (app_rd_data_end),
       .app_rd_data                     (app_rd_data[APP_DATA_WIDTH-1:0]),
       .app_ecc_multiple_err            (app_ecc_multiple_err[2*nCK_PER_CLK-1:0]),
       .rd_buf_full                     (rd_buf_full),
       .rd_data_buf_addr_r              (rd_data_buf_addr_r),
       // Inputs
       .rst                             (rst_r1),
       .clk                             (clk),
       .rd_data_en                      (rd_data_en),
       .rd_data_addr                    (rd_data_addr),
       .rd_data_offset                  (rd_data_offset),
       .rd_data_end                     (rd_data_end),
       .rd_data                         (rd_data[APP_DATA_WIDTH-1:0]),
       .ecc_multiple                    (ecc_multiple),
       .rd_accepted                     (rd_accepted));


endmodule // ddr4_v2_2_10_ui

// Local Variables:
// verilog-library-directories:("." "../mc")
// End:

