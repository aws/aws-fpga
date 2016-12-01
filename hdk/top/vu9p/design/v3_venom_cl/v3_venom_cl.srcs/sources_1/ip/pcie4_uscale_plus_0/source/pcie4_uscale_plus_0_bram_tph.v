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
// File       : pcie4_uscale_plus_0_bram_tph.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_bram_tph #(
  parameter           TCQ = 100
, parameter           TO_RAM_PIPELINE="FALSE"
, parameter           FROM_RAM_PIPELINE="FALSE"
, parameter [1:0]     TL_PF_ENABLE_REG=2'h0
, parameter [3:0]     SRIOV_CAP_ENABLE=4'h0
, parameter [15:0]    PF0_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF1_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF2_SRIOV_CAP_TOTAL_VF=16'h0
, parameter [15:0]    PF3_SRIOV_CAP_TOTAL_VF=16'h0
, parameter           PF0_TPHR_CAP_ENABLE="FALSE"

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire   [7:0] user_tph_stt_func_num_i,     // 0-255
  input  wire   [5:0] user_tph_stt_index_i,        // 0-63
  input  wire         user_tph_stt_rd_en_i,
  output wire   [7:0] user_tph_stt_rd_data_o,

  input  wire  [11:0] addr_i,
  input  wire  [31:0] wdata_i,
  input  wire   [3:0] wdip_i,
  input  wire   [3:0] wen_i,
  output wire  [31:0] rdata_o,
  output wire   [3:0] rdop_o

  );
  localparam integer NUM_VFUNCTIONS = (SRIOV_CAP_ENABLE == 4'h0) ? 0 : 
                              (SRIOV_CAP_ENABLE == 4'h1) ? PF0_SRIOV_CAP_TOTAL_VF : 
                              (SRIOV_CAP_ENABLE == 4'h3) ? (PF0_SRIOV_CAP_TOTAL_VF + PF1_SRIOV_CAP_TOTAL_VF) : 
                              (SRIOV_CAP_ENABLE == 4'h7) ? (PF0_SRIOV_CAP_TOTAL_VF + PF1_SRIOV_CAP_TOTAL_VF + PF2_SRIOV_CAP_TOTAL_VF) : 
                              (PF0_SRIOV_CAP_TOTAL_VF + PF1_SRIOV_CAP_TOTAL_VF + PF2_SRIOV_CAP_TOTAL_VF + PF3_SRIOV_CAP_TOTAL_VF);

  localparam integer NUM_FUNCTIONS = (TL_PF_ENABLE_REG == 2'h0) ? (NUM_VFUNCTIONS + 1) :
                             (TL_PF_ENABLE_REG == 2'h1) ? (NUM_VFUNCTIONS + 2) :
                             (TL_PF_ENABLE_REG == 2'h2) ? (NUM_VFUNCTIONS + 3) : (NUM_VFUNCTIONS + 4);

  localparam integer NUM_BRAM_4K = (PF0_TPHR_CAP_ENABLE == "TRUE") ?  
                                   ((NUM_FUNCTIONS  <= 64) ? 1 : 
                                   ((NUM_FUNCTIONS  > 64) && (NUM_FUNCTIONS  <= 128)) ? 2 : 
                                   ((NUM_FUNCTIONS  > 128) && (NUM_FUNCTIONS  <= 192)) ? 3 : 4) : 4;
 

  reg          [11:0] addr;
  reg          [11:0] addr_p0;
  reg          [11:0] addr_p1;
  reg          [31:0] wdata;
  reg           [3:0] wdip;
  reg           [3:0] wen;
  reg          [31:0] reg_rdata;
  reg           [3:0] reg_rdop;
  wire         [31:0] rdata;
  wire          [3:0] rdop;
  genvar              i;
  wire         [13:0] baddr; 
  reg          [13:0] baddr_p0; 
  reg          [13:0] baddr_p1; 
  reg          [31:0] brdata_w;
  wire   [(4*32)-1:0] rdata_t;
  wire    [(4*4)-1:0] rdop_t;
  wire   [(4*32)-1:0] brdata;
  wire    [(4*4)-1:0] bram_4k_wen;

  generate

    if (PF0_TPHR_CAP_ENABLE == "TRUE") begin : TPHR_CAP_PRESENT

      //
      // Optional input pipe stages
      //

      if (TO_RAM_PIPELINE == "TRUE") begin : TORAMPIPELINE

        always @(posedge clk_i) begin
     
          if (reset_i) begin

            addr <= #(TCQ) 12'b0;
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


    // 
    // Address pipeline
    //

    always @(posedge clk_i) begin
     
      if (reset_i) begin

        addr_p0 <= #(TCQ) 12'b0;
        addr_p1 <= #(TCQ) 12'b0;
        baddr_p0 <= #(TCQ) 2'b0;
        baddr_p1 <= #(TCQ) 2'b0;
    
      end else begin
    
        addr_p0 <= #(TCQ) addr;
        addr_p1 <= #(TCQ) addr_p0;
        baddr_p0 <= #(TCQ) baddr;
        baddr_p1 <= #(TCQ) baddr_p0;
    
      end
    
    end

    //
    // Optional output pipe stages
    //

    if (FROM_RAM_PIPELINE == "TRUE") begin : FRMRAMPIPELINE
    
    
      always @(posedge clk_i) begin
         
        if (reset_i) begin
    
          reg_rdata <= #(TCQ) 32'b0;
          reg_rdop <= #(TCQ) 4'b0;
    
         end else begin
    
           case (addr_p1[11:10]) 
             2'b00 : begin
               reg_rdata <= #(TCQ) rdata_t[(32*(0))+31:(32*(0))+0];
               reg_rdop <= #(TCQ) rdop_t[(4*(0))+3:(4*(0))+0];
             end
             2'b01 : begin
               reg_rdata <= #(TCQ) rdata_t[(32*(1))+31:(32*(1))+0];
               reg_rdop <= #(TCQ) rdop_t[(4*(1))+3:(4*(1))+0];
             end
             2'b10 : begin
               reg_rdata <= #(TCQ) rdata_t[(32*(2))+31:(32*(2))+0];
               reg_rdop <= #(TCQ) rdop_t[(4*(2))+3:(4*(2))+0];
             end
             2'b11 : begin
               reg_rdata <= #(TCQ) rdata_t[(32*(3))+31:(32*(3))+0];
               reg_rdop <= #(TCQ) rdop_t[(4*(3))+3:(4*(3))+0];
             end
           endcase
    
          end

        end // always

      end else begin : NOFRMRAMPIPELINE
    
        always @(*) begin

          case (addr_p1[11:10]) 
            2'b00 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(0))+31:(32*(0))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(0))+3:(4*(0))+0];
            end
            2'b01 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(1))+31:(32*(1))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(1))+3:(4*(1))+0];
            end
            2'b10 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(2))+31:(32*(2))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(2))+3:(4*(2))+0];
            end
            2'b11 : begin
              reg_rdata <= #(TCQ) rdata_t[(32*(3))+31:(32*(3))+0];
              reg_rdop <= #(TCQ) rdop_t[(4*(3))+3:(4*(3))+0];
            end
          endcase
    
        end // always

      end // (FROM_RAM_PIPELINE == "TRUE") begin : FRMRAMPIPELINE
  
      assign rdata_o = reg_rdata;
      assign rdop_o = reg_rdop;
      assign baddr = {user_tph_stt_func_num_i[7:0], user_tph_stt_index_i[5:0]};

      always @ (*) begin
    
        if (baddr_p1[13:12] == 2'b00)
          brdata_w = brdata[(32*(0))+31:(32*(0))+0];
        else if (baddr_p1[13:12] == 2'b01)
          brdata_w = brdata[(32*(1))+31:(32*(1))+0];
        else if (baddr_p1[13:12] == 2'b10)
          brdata_w = brdata[(32*(2))+31:(32*(2))+0];
        else
          brdata_w = brdata[(32*(3))+31:(32*(3))+0];
    
      end
    
      assign user_tph_stt_rd_data_o = (baddr_p1[1:0] == 2'b00) ? brdata_w[7:0] : 
                                      (baddr_p1[1:0] == 2'b01) ? brdata_w[15:8] :  
                                      (baddr_p1[1:0] == 2'b10) ? brdata_w[23:16] : brdata_w[31:24];
    
      //
      // BRAM instances
      //

      for (i=0; i<4; i=i+1) begin : BRAM4K

      pcie4_uscale_plus_0_bram_4k_int #(

          .TCQ(TCQ)

        )
        bram_4k_int (
        
          .clk_i (clk_i),
          .reset_i (reset_i),
          .addr_i(addr[9:0]),
          .wdata_i(wdata),
          .wdip_i(wdip),
          .wen_i(bram_4k_wen[(4*i)+3:(4*i)+0]),
          .rdata_o(rdata_t[(32*i)+31:(32*i)+0]),
          .rdop_o(rdop_t[(4*i)+3:(4*i)+0]),
          .baddr_i(baddr[11:2]),
          .brdata_o(brdata[(32*i)+31:(32*i)+0])

        );
        assign bram_4k_wen[(4*i)+3:(4*i)+0] = (i == addr[11:10]) ? wen : 4'h0;
      
      end

    end else begin : TPHR_CAP_NOT_PRESENT 

      assign rdata_o = 32'h0;
      assign rdop_o = 4'h0;
      assign user_tph_stt_rd_data_o = 8'h0;

    end // (PF0_TPHR_CAP_ENABLE == "TRUE") begin : TPHR_CAP_PRESENT

  endgenerate

endmodule
