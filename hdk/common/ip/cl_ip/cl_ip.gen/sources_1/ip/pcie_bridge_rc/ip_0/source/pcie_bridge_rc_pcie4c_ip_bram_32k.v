//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_rc_pcie4c_ip_bram_32k.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_bram_32k #(

  parameter           TCQ = 100
, parameter           TO_RAM_WRITE_PIPELINE="FALSE"
, parameter           TO_RAM_READ_PIPELINE="FALSE"
, parameter           FROM_RAM_READ_PIPELINE="FALSE"
, parameter           ECC_PIPELINE="FALSE"

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire   [8:0] waddr0_i,
  input  wire   [1:0] wen0_i,
  input  wire [143:0] wdata0_i,
  input  wire   [8:0] waddr1_i,
  input  wire   [1:0] wen1_i,
  input  wire [143:0] wdata1_i,

  input  wire   [8:0] raddr0_i,
  input  wire   [1:0] ren0_i,
  output wire [143:0] rdata0_o,
  input  wire   [8:0] raddr1_i,
  input  wire   [1:0] ren1_i,
  output wire [143:0] rdata1_o,

  output wire   [11:0] err_cor_o,
  output wire   [11:0] err_uncor_o

  );

  wire [143:0] rdata0_0;
  wire [143:0] rdata0_1;
  wire [143:0] rdata1_0;
  wire [143:0] rdata1_1;

  wire  [11:0] err_cor;
  wire  [11:0] err_uncor;

  reg  [143:0] reg_rdata0;
  reg  [143:0] reg_rdata1;
  reg   [11:0] reg_err_cor;
  reg   [11:0] reg_err_uncor;

  reg    [0:0] reg_raddr0_10_p0;
  reg    [0:0] reg_raddr1_10_p0;
  reg    [0:0] reg_raddr0_10_p1;
  reg    [0:0] reg_raddr1_10_p1;
  wire   [0:0] raddr0_10_p0;
  wire   [0:0] raddr1_10_p0;

  reg    [8:0] raddr0;
  reg    [1:0] ren0;
  reg    [8:0] raddr1;
  reg    [1:0] ren1;

  reg    [8:0] waddr0;
  reg    [1:0] wen0;
  reg  [143:0] wdata0;
  reg    [8:0] waddr1;
  reg    [1:0] wen1;
  reg  [143:0] wdata1;

  wire                reset_pipe;

  assign reset_pipe  = 1'b0;
  
  //
  // Optional input pipe stages
  //
  generate

    if (TO_RAM_WRITE_PIPELINE == "TRUE") begin : TOWRPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_pipe) begin

          waddr0 <= #(TCQ) 9'b0;
          wen0 <= #(TCQ) 2'b0;
          wdata0 <= #(TCQ) 144'b0;
          waddr1 <= #(TCQ) 9'b0;
          wen1 <= #(TCQ) 2'b0;
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
     
        if (reset_pipe) begin

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
  // output pipe stage
  //

  generate

    if (FROM_RAM_READ_PIPELINE == "TRUE") begin : FRMRDPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_pipe) begin

          reg_rdata0 <= #(TCQ) 144'b0;
          reg_rdata1 <= #(TCQ) 144'b0;
    
        end else begin
    
          reg_rdata0 <= #(TCQ) raddr0_10_p0 ? rdata1_0 : rdata0_0;
          reg_rdata1 <= #(TCQ) raddr1_10_p0 ? rdata1_1 : rdata0_1;
    
        end
    
      end

      always @(posedge clk_i) begin
     
        if (reset_i) begin

          reg_err_cor <= #(TCQ) 12'b0;
          reg_err_uncor <= #(TCQ) 12'b0;
    
        end else begin
    
          reg_err_cor <= #(TCQ) err_cor;
          reg_err_uncor <= #(TCQ) err_uncor;
    
        end
    
      end

   end else begin : NOFRMRDPIPELINE

      always @(*) begin

        reg_rdata0 = raddr0_10_p0 ? rdata1_0 : rdata0_0;
        reg_rdata1 = raddr1_10_p0 ? rdata1_1 : rdata0_1;
        reg_err_cor = err_cor;
        reg_err_uncor = err_uncor;

      end

   end

  endgenerate

  always @(posedge clk_i) begin
     
    if (reset_pipe) begin

      reg_raddr0_10_p0 <= #(TCQ) 1'b0;
      reg_raddr1_10_p0 <= #(TCQ) 1'b0;
      reg_raddr0_10_p1 <= #(TCQ) 1'b0;
      reg_raddr1_10_p1 <= #(TCQ) 1'b0;
    
    end else begin
    
      reg_raddr0_10_p0 <= #(TCQ) ren0[1];
      reg_raddr1_10_p0 <= #(TCQ) ren1[1];
      reg_raddr0_10_p1 <= #(TCQ) reg_raddr0_10_p0;
      reg_raddr1_10_p1 <= #(TCQ) reg_raddr1_10_p0;
    
    end
    
  end

  assign rdata0_o = reg_rdata0;
  assign rdata1_o = reg_rdata1;
  assign err_cor_o = reg_err_cor;
  assign err_uncor_o = reg_err_uncor;
  assign raddr0_10_p0 = reg_raddr0_10_p1;
  assign raddr1_10_p0 = reg_raddr1_10_p1;

  // Upper 512 Words
  pcie_bridge_rc_pcie4c_ip_bram_16k_int #( 
   .EN_ECC_PIPE(ECC_PIPELINE),
	.TCQ(TCQ)) 
  bram_16k_0_int (
    .clk_i (clk_i),
    .reset_i (reset_i),

    .waddr0_i(waddr0[8:0]),
    .wdata0_i(wdata0[143:0]),
    .wen0_i(wen0[0]),
    .waddr1_i(waddr1[8:0]),
    .wdata1_i(wdata1[143:0]),
    .wen1_i(wen1[0]),
    .raddr0_i(raddr0[8:0]),
    .rdata0_o(rdata0_0[143:0]),
    .ren0_i(ren0[0]),
    .raddr1_i(raddr1[8:0]),
    .rdata1_o(rdata0_1[143:0]),
    .ren1_i(ren1[0]),
    .err_cor_o(err_cor[5:0]),
    .err_uncor_o(err_uncor[5:0])

  );
  
  // Lower 512 Words
  pcie_bridge_rc_pcie4c_ip_bram_16k_int #( 
   .EN_ECC_PIPE(ECC_PIPELINE),
	.TCQ(TCQ)) 
  bram_16k_1_int (
    .clk_i (clk_i),
    .reset_i (reset_i),

    .waddr0_i(waddr0[8:0]),
    .wdata0_i(wdata0[143:0]),
    .wen0_i(wen0[1]),
    .waddr1_i(waddr1[8:0]),
    .wdata1_i(wdata1[143:0]),
    .wen1_i(wen1[1]),
    .raddr0_i(raddr0[8:0]),
    .rdata0_o(rdata1_0[143:0]),
    .ren0_i(ren0[1]),
    .raddr1_i(raddr1[8:0]),
    .rdata1_o(rdata1_1[143:0]),
    .ren1_i(ren1[1]),
    .err_cor_o(err_cor[11:6]),
    .err_uncor_o(err_uncor[11:6])

  );

endmodule
