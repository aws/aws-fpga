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
// File       : pcie4_uscale_plus_0_bram_rep.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_bram_rep #(
  parameter           TCQ = 100
, parameter           TO_RAM_PIPELINE="FALSE"
, parameter           FROM_RAM_PIPELINE="FALSE"

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire   [8:0] addr_i,
  input  wire   [0:0] wen_i,
  input  wire [255:0] wdata_i,

  output wire [255:0] rdata_o,
  input  wire   [0:0] ren_i,

  output wire   [3:0] err_cor_o,
  output wire   [3:0] err_uncor_o

  );

  reg           [8:0] addr;
  reg           [0:0] wen;
  reg           [0:0] ren;
  reg         [255:0] wdata;

  wire        [255:0] rdata;
  wire          [3:0] err_cor;
  wire          [3:0] err_uncor;

  reg         [255:0] reg_rdata;
  reg           [3:0] reg_err_cor;
  reg           [3:0] reg_err_uncor;

  //
  // Optional input pipe stages
  //
  
  generate

    if (TO_RAM_PIPELINE == "TRUE") begin : TORAMPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_i) begin

          addr <= #(TCQ) 9'b0;
          wen <= #(TCQ) 1'b0;
          wdata <= #(TCQ) 256'b0;
          ren <= #(TCQ) 1'b0;

        end else begin

          addr <= #(TCQ) addr_i;
          wen <= #(TCQ) wen_i;
          wdata <= #(TCQ) wdata_i;
          ren <= #(TCQ) ren_i;

        end

      end

    end else begin : NOTORAMPIPELINE

      always @(*) begin

        addr = addr_i;
        wen = wen_i;
        wdata = wdata_i;
        ren = ren_i;

      end

    end

  endgenerate

  //
  // Optional output pipe stages
  //
  
  generate

    if (FROM_RAM_PIPELINE == "TRUE") begin : FRMRAMPIPELINE


      always @(posedge clk_i) begin
     
        if (reset_i) begin

          reg_rdata <= #(TCQ) 256'b0;
          reg_err_cor <= #(TCQ) 4'b0;
          reg_err_uncor <= #(TCQ) 4'b0;

        end else begin

          reg_rdata <= #(TCQ) rdata;
          reg_err_cor <= #(TCQ) err_cor;
          reg_err_uncor <= #(TCQ) err_uncor;

        end

      end

    end else begin : NOFRMRAMPIPELINE

      always @(*) begin

        reg_rdata = rdata;
        reg_err_cor = err_cor;
        reg_err_uncor = err_uncor;

      end

    end
  
  endgenerate

  assign rdata_o = reg_rdata;

  assign err_cor_o = reg_err_cor;
  assign err_uncor_o = reg_err_uncor;

  pcie4_uscale_plus_0_bram_rep_int #(
      .TCQ(TCQ)
    )
    bram_rep_int_0 (

      .clk_i (clk_i),
      .reset_i (reset_i),

      .addr_i(addr[8:0]),
      .wdata_i(wdata[255:0]),
      .wen_i(wen),
      .ren_i(ren),
      .rdata_o(rdata[255:0]),
      .err_cor_o(err_cor[3:0]),
      .err_uncor_o(err_uncor[3:0])

  );


endmodule
