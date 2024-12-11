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
// File       : pcie_bridge_rc_pcie4c_ip_bram_msix.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_bram_msix #(

  parameter           TCQ = 100
, parameter           TO_RAM_PIPELINE="FALSE"
, parameter           FROM_RAM_PIPELINE="FALSE"
, parameter           MSIX_CAP_TABLE_SIZE=11'h0
, parameter           MSIX_TABLE_RAM_ENABLE="FALSE"

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire  [12:0] addr_i,
  input  wire  [31:0] wdata_i,
  input  wire   [3:0] wdip_i,
  input  wire   [3:0] wen_i,
  output wire  [31:0] rdata_o,
  output wire   [3:0] rdop_o

  );

  // WIP : Use Total number of functions (PFs + VFs) to calculate the NUM_BRAM_4K
  localparam integer NUM_BRAM_4K = (MSIX_TABLE_RAM_ENABLE == "TRUE") ? 8 : 0 ;
 

  reg          [12:0] addr;
  reg          [12:0] addr_p0;
  reg          [12:0] addr_p1;
  reg          [31:0] wdata;
  reg           [3:0] wdip;
  reg           [3:0] wen;
  reg          [31:0] reg_rdata;
  reg           [3:0] reg_rdop;
  wire         [31:0] rdata;
  wire          [3:0] rdop;
  genvar              i;
  wire    [(8*4)-1:0] bram_4k_wen;
  wire   [(8*32)-1:0] rdata_t;
  wire    [(8*4)-1:0] rdop_t;

  //
  // Optional input pipe stages
  //
  generate

    if (TO_RAM_PIPELINE == "TRUE") begin : TORAMPIPELINE

      always @(posedge clk_i) begin
     
        if (reset_i) begin

          addr <= #(TCQ) 13'b0;
          wdata <= #(TCQ) 32'b0;
          wdip <= #(TCQ) 4'b0;
          wen <= #(TCQ) 4'b0;

        end else begin

          addr <= #(TCQ) addr_i;
          wdata <= #(TCQ) wdata_i;
          wdip <= #(TCQ) wdip_i;
          wen <= #(TCQ) wen_i;

        end

      end

    end else begin : NOTORAMPIPELINE

      always @(*) begin

          addr = addr_i;
          wdata = wdata_i;
          wdip = wdip_i;
          wen = wen_i;

      end


    end

  endgenerate

  // 
  // Address pipeline
  //
  always @(posedge clk_i) begin
     
    if (reset_i) begin

      addr_p0 <= #(TCQ) 13'b0;
      addr_p1 <= #(TCQ) 13'b0;

    end else begin

      addr_p0 <= #(TCQ) addr;
      addr_p1 <= #(TCQ) addr_p0;

    end

  end

  //
  // Optional output pipe stages
  //
  generate

    if (FROM_RAM_PIPELINE == "TRUE") begin : FRMRAMPIPELINE


      always @(posedge clk_i) begin
     
        if (reset_i) begin

          reg_rdata <= #(TCQ) 32'b0;
          reg_rdop <= #(TCQ) 4'b0;

        end else begin

          case (addr_p1[12:10]) 
            3'b000 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(0))+31:(32*(0))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(0))+3:(4*(0))+0];
            end
            3'b001 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(1))+31:(32*(1))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(1))+3:(4*(1))+0];
            end
            3'b010 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(2))+31:(32*(2))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(2))+3:(4*(2))+0];
            end
            3'b011 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(3))+31:(32*(3))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(3))+3:(4*(3))+0];
            end
            3'b100 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(4))+31:(32*(4))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(4))+3:(4*(4))+0];
            end
            3'b101 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(5))+31:(32*(5))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(5))+3:(4*(5))+0];
            end
            3'b110 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(6))+31:(32*(6))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(6))+3:(4*(6))+0];
            end
            3'b111 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(7))+31:(32*(7))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(7))+3:(4*(7))+0];
            end
          endcase

        end

      end

    end else begin : NOFRMRAMPIPELINE

      always @(*) begin

          case (addr_p1[12:10]) 
            3'b000 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(0))+31:(32*(0))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(0))+3:(4*(0))+0];
            end
            3'b001 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(1))+31:(32*(1))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(1))+3:(4*(1))+0];
            end
            3'b010 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(2))+31:(32*(2))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(2))+3:(4*(2))+0];
            end
            3'b011 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(3))+31:(32*(3))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(3))+3:(4*(3))+0];
            end
            3'b100 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(4))+31:(32*(4))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(4))+3:(4*(4))+0];
            end
            3'b101 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(5))+31:(32*(5))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(5))+3:(4*(5))+0];
            end
            3'b110 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(6))+31:(32*(6))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(6))+3:(4*(6))+0];
            end
            3'b111 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(7))+31:(32*(7))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(7))+3:(4*(7))+0];
            end
          endcase

      end

    end
  
  endgenerate

  assign rdata_o = (MSIX_TABLE_RAM_ENABLE == "TRUE") ?  reg_rdata : 32'h0;
  assign rdop_o = (MSIX_TABLE_RAM_ENABLE == "TRUE") ? reg_rdop : 4'h0;

  generate 
  
    for (i=0; i<NUM_BRAM_4K; i=i+1) begin : BRAM4K

      pcie_bridge_rc_pcie4c_ip_bram_4k_int #(
          .TCQ(TCQ)
        )
        bram_4k_int (
    
          .clk_i (clk_i),
          .reset_i (reset_i),
    
          .addr_i(addr[9:0]),
          .wdata_i(wdata),
          .wdip_i(wdip),
          .wen_i(bram_4k_wen[(4*(i))+3:(4*(i))+0]),
          .rdata_o(rdata_t[(32*i)+31:(32*i)+0]),
          .rdop_o(rdop_t[(4*i)+3:(4*i)+0]),
          .baddr_i(10'b0),
          .brdata_o()

      );
      assign bram_4k_wen[(4*(i))+3:(4*(i))+0] = wen & {4{(i == addr[12:10])}};  
      
    end

  endgenerate

endmodule
