//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : pcie4_uscale_plus_0_bram_16k.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_bram_16k #(

  parameter           TCQ = 100
, parameter           TO_RAM_WRITE_PIPELINE="FALSE"
, parameter           TO_RAM_READ_PIPELINE="FALSE"
, parameter           FROM_RAM_READ_PIPELINE="FALSE"

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire   [8:0] waddr0_i,
  input  wire   [0:0] wen0_i,
  input  wire [143:0] wdata0_i,
  input  wire   [8:0] waddr1_i,
  input  wire   [0:0] wen1_i,
  input  wire [143:0] wdata1_i,

  input  wire   [8:0] raddr0_i,
  input  wire   [0:0] ren0_i,
  output wire [143:0] rdata0_o,
  input  wire   [8:0] raddr1_i,
  input  wire   [0:0] ren1_i,
  output wire [143:0] rdata1_o,

  output wire   [5:0] err_cor_o,
  output wire   [5:0] err_uncor_o

  );

  reg           [8:0] waddr0;
  reg           [0:0] wen0;
  reg         [143:0] wdata0;
  reg           [8:0] waddr1;
  reg           [0:0] wen1;
  reg         [143:0] wdata1;
  reg           [8:0] raddr0;
  reg           [0:0] ren0;
  reg           [8:0] raddr1;
  reg           [0:0] ren1;
  wire        [143:0] rdata0;
  wire        [143:0] rdata1;
  wire          [5:0] err_cor;
  wire          [5:0] err_uncor;
  reg         [143:0] reg_rdata0;
  reg         [143:0] reg_rdata1;
  reg           [5:0] reg_err_cor;
  reg           [5:0] reg_err_uncor;

  //
  // Optional input pipe stages
  //
  generate

    if (TO_RAM_WRITE_PIPELINE == "TRUE") begin : TOWRPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_i) begin

          waddr0 <= #(TCQ) 9'b0;
          wen0 <= #(TCQ) 1'b0;
          wdata0 <= #(TCQ) 144'b0;
          waddr1 <= #(TCQ) 9'b0;
          wen1 <= #(TCQ) 1'b0;
          wdata1 <= #(TCQ) 144'b0;

        end else begin

          waddr0 <= #(TCQ) waddr0_i;
          wen0 <= #(TCQ) wen0_i;
          wdata0 <= #(TCQ) wdata0_i;
          waddr1 <= #(TCQ) waddr1_i;
          wen1 <= #(TCQ) wen1_i;
          wdata1 <= #(TCQ) wdata1_i;

        end

      end

    end else begin : NOTOWRPIPELINE

      always @(*) begin

        waddr0 = waddr0_i;
        wen0 = wen0_i;
        wdata0 = wdata0_i;
        waddr1 = waddr1_i;
        wen1 = wen1_i;
        wdata1 = wdata1_i;

      end

    end

    if (TO_RAM_READ_PIPELINE == "TRUE") begin : TORDPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_i) begin

          raddr0 <= #(TCQ) 9'b0;
          ren0 <= #(TCQ) 1'b0;
          raddr1 <= #(TCQ) 9'b0;
          ren1 <= #(TCQ) 1'b0;

        end else begin

          raddr0 <= #(TCQ) raddr0_i;
          ren0 <= #(TCQ) ren0_i;
          raddr1 <= #(TCQ) raddr1_i;
          ren1 <= #(TCQ) ren1_i;

        end

      end

    end else begin : NOTORDPIPELINE

      always @(*) begin

        raddr0 = raddr0_i;
        ren0 = ren0_i;
        raddr1 = raddr1_i;
        ren1 = ren1_i;

      end

    end
  
  endgenerate

  //
  // Optional output pipe stages
  //
  generate

    if (FROM_RAM_READ_PIPELINE == "TRUE") begin : FRMRDPIPELINE


      always @(posedge clk_i) begin
     
        if (reset_i) begin

          reg_rdata0 <= #(TCQ) 144'b0;
          reg_rdata1 <= #(TCQ) 144'b0;
          reg_err_cor <= #(TCQ) 6'b0;
          reg_err_uncor <= #(TCQ) 6'b0;

         end else begin

          reg_rdata0 <= #(TCQ) rdata0;
          reg_rdata1 <= #(TCQ) rdata1;
          reg_err_cor <= #(TCQ) err_cor;
          reg_err_uncor <= #(TCQ) err_uncor;

        end

      end

    end else begin : NOFRMRDPIPELINE

      always @(*) begin

          reg_rdata0 = rdata0;
          reg_rdata1 = rdata1;
          reg_err_cor = err_cor;
          reg_err_uncor = err_uncor;

      end

    end
  
  endgenerate

  assign rdata0_o = reg_rdata0;
  assign rdata1_o = reg_rdata1;
  assign err_cor_o = reg_err_cor;
  assign err_uncor_o = reg_err_uncor;

  pcie4_uscale_plus_0_bram_16k_int #(
      .TCQ(TCQ)
    )
    bram_16k_int (

      .clk_i (clk_i),
      .reset_i (reset_i),

      .waddr0_i(waddr0[8:0]),
      .wdata0_i(wdata0[143:0]),
      .wen0_i(wen0),
      .waddr1_i(waddr1[8:0]),
      .wdata1_i(wdata1[143:0]),
      .wen1_i(wen1),
      .raddr0_i(raddr0[8:0]),
      .rdata0_o(rdata0[143:0]),
      .ren0_i(ren0),
      .raddr1_i(raddr1[8:0]),
      .rdata1_o(rdata1[143:0]),
      .ren1_i(ren1),
      .err_cor_o(err_cor[5:0]),
      .err_uncor_o(err_uncor[5:0])

  );


endmodule
