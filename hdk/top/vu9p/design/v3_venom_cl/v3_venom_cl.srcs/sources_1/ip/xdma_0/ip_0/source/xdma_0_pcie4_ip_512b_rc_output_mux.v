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
// File       : xdma_0_pcie4_ip_512b_rc_output_mux.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_512b_rc_output_mux #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter IN_DATA_WIDTH = 512+183+16+1,    
   parameter OUT_DATA_WIDTH = 512,
   parameter TUSER_WIDTH = 183,
   parameter TKEEP_WIDTH = 16
   )
  (
    input  wire           clk_i // 250 MHz clock for client-facing interfaces
   ,input  wire           reset_n_i // Reset in the user clock domain
   ,input  wire           link_down_reset_i // Link went down

   ,input  wire           attr_straddle_en_i // Enable straddle

   ,input wire[IN_DATA_WIDTH-1:0] in_data_i
   ,input wire in_data_valid_i
   ,output wire upstream_ready_o

   ,output reg [OUT_DATA_WIDTH-1:0]  out_data_o
   ,output reg           out_data_valid_o
   ,output reg [TUSER_WIDTH-1:0] out_tuser_o
   ,output wire          out_tlast_o
   ,output wire [TKEEP_WIDTH-1:0] out_tkeep_o
   ,input  wire           downstream_ready_i

   // Completion delivered indications to AXI hard block
   ,output reg [3:0]     pcie_compl_delivered_o
   ,output reg [7:0]     pcie_compl_delivered_tag0_o
   ,output reg [7:0]     pcie_compl_delivered_tag1_o
   ,output reg [7:0]     pcie_compl_delivered_tag2_o
   ,output reg [7:0]     pcie_compl_delivered_tag3_o
   );


   localparam MAX_CREDIT = 32;

   reg [1:0] output_fifo_occupancy;
   reg          output_fifo_write_ptr;
   reg          output_fifo_read_ptr;
   wire      output_fifo_full;
   wire      output_fifo_empty;

   reg [OUT_DATA_WIDTH-1:0] m_axis_rc_tdata_first_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_rc_tkeep_first_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_rc_tuser_first_reg;
   reg                 m_axis_rc_tlast_first_reg;
   
   reg [OUT_DATA_WIDTH-1:0] m_axis_rc_tdata_second_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_rc_tkeep_second_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_rc_tuser_second_reg;
   reg                 m_axis_rc_tlast_second_reg;
   
   wire             output_reg_mux_sel;
   reg                 out_tlast_reg;
   reg [TKEEP_WIDTH-1:0]    out_tkeep_reg;

  wire                 sop0_dw0;
  wire                 sop0_dw4;
  wire                 sop0_dw8;
  wire                 sop0_dw12;
  wire                 sop1_dw4;
  wire                 sop1_dw8;
  wire                 sop1_dw12;
  wire                 sop2_dw8;
  wire                 sop2_dw12;
  wire                 sop3_dw12;

   //---------------------------------------------------------------------------------------------
   // Output FIFO
   // The main FIFO feeds into two read registers in the user clock domain, which are configured
   // as a 2-entry FIFO.
   // These are termed m_axis_rc_*_reg_first and m_axis_rc_*_reg_second.
   // These can be thought of as logical extensions of the main FIFO.
   //---------------------------------------------------------------------------------------------

   // Send signal to read from main FIFO into the output FIFO when the latter is not full.
   assign    upstream_ready_o = ~output_fifo_full;

   // Maintain write and read pointers
   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_write_ptr <= #(TCQ) 1'b0;
     else if (link_down_reset_i)
       output_fifo_write_ptr <= #(TCQ) 1'b0;
     else
       if (in_data_valid_i & ~output_fifo_full)
     output_fifo_write_ptr <= #(TCQ) ~output_fifo_write_ptr;

   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_read_ptr <= #(TCQ) 1'b0;
     else if (link_down_reset_i)
       output_fifo_read_ptr <= #(TCQ) 1'b0;
     else
       if ((downstream_ready_i | ~out_data_valid_o) &
       ~output_fifo_empty)
     output_fifo_read_ptr <= #(TCQ) ~output_fifo_read_ptr;

    // Maintain FIFO occupancy
   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_occupancy <= #(TCQ) 2'd0;
     else if (link_down_reset_i)
       output_fifo_occupancy <= #(TCQ) 2'd0;
     else
       if ((in_data_valid_i & ~output_fifo_full) &
       ~((downstream_ready_i | ~out_data_valid_o) &
         ~output_fifo_empty))
     output_fifo_occupancy <= #(TCQ) output_fifo_occupancy + 2'd1;
       else
     if (~(in_data_valid_i & ~output_fifo_full) &
         ((downstream_ready_i | ~out_data_valid_o) &
          ~output_fifo_empty))
       output_fifo_occupancy <= #(TCQ) output_fifo_occupancy - 2'd1;
   

   assign output_fifo_full = output_fifo_occupancy[1];
   assign output_fifo_empty = (output_fifo_occupancy == 2'b00);

   // Write data into the Output FIFO.                                                                                    
   always @(posedge clk_i)
     if (~reset_n_i)
       begin
          m_axis_rc_tdata_first_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_rc_tdata_second_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_rc_tkeep_first_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_rc_tkeep_second_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_rc_tuser_first_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_rc_tuser_second_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_rc_tlast_first_reg <= #(TCQ) 1'b0;
          m_axis_rc_tlast_second_reg <= #(TCQ) 1'b0;
       end
     else
        if (in_data_valid_i & ~output_fifo_full)
      begin
         case(output_fifo_write_ptr)
           1'b0:
         begin
            m_axis_rc_tdata_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_rc_tkeep_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_rc_tuser_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_rc_tlast_first_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
         end
           default:
         begin
            m_axis_rc_tdata_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_rc_tkeep_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_rc_tuser_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_rc_tlast_second_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
         end
         endcase // case(output_fifo_write_ptr)
      end // if (in_data_valid_i & ~output_fifo_full)
   
   // Output registers

   assign output_reg_mux_sel = output_fifo_read_ptr;

   always @(posedge clk_i)
     if (~reset_n_i)
       begin
      out_data_o <= #(TCQ) {OUT_DATA_WIDTH-1{1'b0}};
      out_tuser_o <= #(TCQ) {TUSER_WIDTH-1{1'b0}};
      out_tkeep_reg <= #(TCQ) {TKEEP_WIDTH-1{1'b0}};
      out_tlast_reg <= #(TCQ) 1'b0;
       end
     else
       if (~out_data_valid_o | downstream_ready_i)
     begin
        case(output_reg_mux_sel)
          1'b0:
        begin
           out_data_o <= #(TCQ) m_axis_rc_tdata_first_reg;
           out_tkeep_reg <= #(TCQ) m_axis_rc_tkeep_first_reg;
           out_tuser_o <= #(TCQ) m_axis_rc_tuser_first_reg;
           out_tlast_reg <= #(TCQ) m_axis_rc_tlast_first_reg;
        end
          default:
        begin
           out_data_o <= #(TCQ) m_axis_rc_tdata_second_reg;
           out_tkeep_reg <= #(TCQ) m_axis_rc_tkeep_second_reg;
           out_tuser_o <= #(TCQ) m_axis_rc_tuser_second_reg;
           out_tlast_reg <= #(TCQ) m_axis_rc_tlast_second_reg;
        end
        endcase // case(output_reg_mux_sel)
     end // if (~out_data_o | downstream_ready_i)

   always @(posedge clk_i)
     if (~reset_n_i)
       out_data_valid_o <= #(TCQ) 1'b0;
     else
       if (~out_data_valid_o | downstream_ready_i)
     out_data_valid_o <= #(TCQ) ~output_fifo_empty;

  assign out_tkeep_o =  attr_straddle_en_i? {TKEEP_WIDTH{1'b1}}: out_tkeep_reg;
  assign out_tlast_o =  attr_straddle_en_i? 1'b0: out_tlast_reg;

  //-----------------------------------------------------------------------------------------
  // Generate Completion delivered indications to AXI hard block
  //-----------------------------------------------------------------------------------------

  reg                  compl_data_valid;
  reg [3:0]          compl_delivered;
  reg              pkt_in_progress;
  reg [3:0]          compl_sop;
  reg [3:0]          compl_eop;
  reg [1:0]          compl_sop0_ptr;
  reg [1:0]          compl_sop1_ptr;
  reg [1:0]          compl_sop2_ptr;
  reg [7:0]          compl_tag0;
  reg [7:0]          compl_tag1;
  reg [7:0]          compl_tag2;
  reg [7:0]          compl_tag3;

  reg              saved_compl_delivered;
  reg [7:0]          saved_compl_tag;

  always @(posedge clk_i)
    if (~reset_n_i)
      compl_data_valid <= #(TCQ) 1'b0;
    else if (link_down_reset_i)
      compl_data_valid <= #(TCQ) 1'b0;
    else
      compl_data_valid <= #(TCQ) out_data_valid_o & downstream_ready_i;
  
  always @(posedge clk_i)
    if (~reset_n_i)
      begin
    compl_sop <= #(TCQ) 4'd0;
    compl_eop <= #(TCQ) 4'd0;
    compl_sop0_ptr <= #(TCQ) 2'd0;
    compl_sop1_ptr <= #(TCQ) 2'd0;
    compl_sop2_ptr <= #(TCQ) 2'd0;
    compl_delivered <= #(TCQ) 4'd0;
    compl_tag0 <= #(TCQ) 8'd0;
    compl_tag1 <= #(TCQ) 8'd0;
    compl_tag2 <= #(TCQ) 8'd0;
    compl_tag3 <= #(TCQ) 8'd0;
      end // if (~reset_n_i)
    else
      begin
    if (attr_straddle_en_i)
      begin
        compl_sop <= #(TCQ) out_tuser_o[67:64];
        compl_sop0_ptr <= #(TCQ) out_tuser_o[69:68];
        compl_sop1_ptr <= #(TCQ) out_tuser_o[71:70];
        compl_sop2_ptr <= #(TCQ) out_tuser_o[73:72];
        compl_eop <= #(TCQ) out_tuser_o[79:76];
        compl_delivered[0] <= #(TCQ) out_data_o[30] && (out_data_o[15:12] != 4'b0110);  // Exclude invalid tag error
        compl_delivered[1] <= #(TCQ) out_data_o[128+30] && (out_data_o[128+15:128+12] != 4'b0110);
        compl_delivered[2] <= #(TCQ) out_data_o[128*2+30] && (out_data_o[128*2+15:128*2+12] != 4'b0110);
        compl_delivered[3] <= #(TCQ) out_data_o[128*3+30] && (out_data_o[128*3+15:128*3+12] != 4'b0110);    
        compl_tag0 <= #(TCQ) out_data_o[71:64];
        compl_tag1 <= #(TCQ) out_data_o[128+71:128+64];
        compl_tag2 <= #(TCQ) out_data_o[128*2+71:128*2+64];
        compl_tag3 <= #(TCQ) out_data_o[128*3+71:128*3+64];
      end // if (attr_straddle_en_i)
    else
      begin
        compl_sop[0] <= #(TCQ) out_tuser_o[64];
        compl_sop[3:1] <= #(TCQ) 3'd0;
        compl_sop0_ptr <= #(TCQ) 2'd0;
        compl_sop1_ptr <= #(TCQ) 2'd0;
        compl_sop2_ptr <= #(TCQ) 2'd0;
        compl_eop[0] <= #(TCQ) out_tlast_reg;
        compl_eop[3:1] <= #(TCQ) 3'd0;
        compl_delivered[0] <= #(TCQ) out_data_o[30] && (out_data_o[15:12] != 4'b0110);  // Exclude invalid tag error
        compl_delivered[3:1] <= #(TCQ) 3'd0;
        compl_tag0 <= #(TCQ) out_data_o[71:64];
        compl_tag1 <= #(TCQ) 8'd0;
        compl_tag2 <= #(TCQ) 8'd0;
        compl_tag3 <= #(TCQ) 8'd0;
      end // else: !if(attr_straddle_en_i)
      end // else: !if(~reset_n_i)
    
  // Keep track of continuing packets
  always @(posedge clk_i)
    if (~reset_n_i)
      pkt_in_progress <= #(TCQ) 1'b0;
    else if (link_down_reset_i)
      pkt_in_progress <= #(TCQ) 1'b0;
    else if (compl_data_valid)
       begin
     if (attr_straddle_en_i)
       begin
         if (~pkt_in_progress)
           pkt_in_progress <= #(TCQ) ~compl_eop[0] |
                  (compl_sop[1] & ~compl_eop[1]) | 
                  (compl_sop[2] & ~compl_eop[2]) | 
                  (compl_sop[3] & ~compl_eop[3]);
         else
           pkt_in_progress <= #(TCQ) ~compl_eop[0] |
                  (compl_sop[0] & ~compl_eop[1]) | 
                  (compl_sop[1] & ~compl_eop[2]) | 
                  (compl_sop[2] & ~compl_eop[3]);
       end // if (attr_straddle_en_i)
     else
       pkt_in_progress <= #(TCQ) ~compl_eop[0];
       end // if (compl_data_valid)
    
  assign sop0_dw0 = compl_sop[0] && (compl_sop0_ptr == 2'd0) && compl_delivered[0];
  assign sop0_dw4 = compl_sop[0] && (compl_sop0_ptr == 2'd1) && compl_delivered[1];
  assign sop0_dw8 = compl_sop[0] && (compl_sop0_ptr == 2'd2) && compl_delivered[2];
  assign sop0_dw12 = compl_sop[0] && (compl_sop0_ptr == 2'd3) && compl_delivered[3];
  assign sop1_dw4 = compl_sop[1] && (compl_sop1_ptr == 2'd1) && compl_delivered[1];
  assign sop1_dw8 = compl_sop[1] && (compl_sop1_ptr == 2'd2) && compl_delivered[2];
  assign sop1_dw12 = compl_sop[1] && (compl_sop1_ptr == 2'd3) && compl_delivered[3];
  assign sop2_dw8 = compl_sop[2] && (compl_sop2_ptr == 2'd2) && compl_delivered[2];
  assign sop2_dw12 = compl_sop[2] && (compl_sop2_ptr == 2'd3) && compl_delivered[3];
  assign sop3_dw12 = compl_sop[3] & compl_delivered[3];

  // Send out tags of delivered Completions
  always @(posedge clk_i)
    if (~reset_n_i)
      begin
     pcie_compl_delivered_o <= #(TCQ) 4'd0;
     pcie_compl_delivered_tag0_o <= #(TCQ) 8'd0;
     pcie_compl_delivered_tag1_o <= #(TCQ) 8'd0;
     pcie_compl_delivered_tag2_o <= #(TCQ) 8'd0;
     pcie_compl_delivered_tag3_o <= #(TCQ) 8'd0;
      end
     else if (compl_data_valid)
       begin
     if (~pkt_in_progress)
       begin
         pcie_compl_delivered_o[0] <= #(TCQ) (sop0_dw0 & compl_eop[0])|
                      (sop1_dw4 & compl_eop[1])| 
                      (sop1_dw8 & compl_eop[1])| 
                      (sop1_dw12 & compl_eop[1])| 
                      (sop2_dw8 & compl_eop[2])| 
                      (sop2_dw12 & compl_eop[2])| 
                      (sop3_dw12 & compl_eop[3]);
         pcie_compl_delivered_tag0_o <= #(TCQ) (sop0_dw0 & compl_eop[0])?
                        compl_tag0:
                        (sop1_dw4 & compl_eop[1])? 
                        compl_tag1:
                        ((sop1_dw8 & compl_eop[1])|
                         (sop2_dw8 & compl_eop[2]))? 
                        compl_tag2:
                        compl_tag3;

         if (sop0_dw0 & compl_eop[0])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) (sop1_dw4 & compl_eop[1])| 
                          (sop1_dw8 & compl_eop[1])| 
                          (sop1_dw12 & compl_eop[1])| 
                          (sop2_dw8 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[2])| 
                          (sop3_dw12 & compl_eop[3]);
         if (sop1_dw4 & compl_eop[1])
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag1;
         else if ((sop1_dw8 & compl_eop[1])| 
              (sop2_dw8 & compl_eop[2]))
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag2;
         else
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop1_dw4 & compl_eop[1])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ)(sop2_dw8 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[2])| 
                          (sop3_dw12 & compl_eop[3]);
         if (sop2_dw8 & compl_eop[2])
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag2;
         else
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop1_dw8 & compl_eop[1])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) sop2_dw12 & compl_eop[2];
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop2_dw8 & compl_eop[2])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) sop3_dw12 & compl_eop[3];
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) 1'b0;
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end

         if (sop0_dw0 & compl_eop[0])
           begin
         if (sop1_dw4 & compl_eop[1])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop2_dw8 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[2])| 
                          (sop3_dw12 & compl_eop[3]);
             if (sop2_dw8 & compl_eop[2])
               pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag2;
             else
               pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else if (sop1_dw8 & compl_eop[1])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop2_dw12 & compl_eop[2])| 
                          (sop3_dw12 & compl_eop[3]);
             pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;
           end // if (sop0_dw0 & compl_eop[0])
         else if (sop1_dw4 & compl_eop[1])
           begin
         if (sop2_dw8 & compl_eop[2])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop3_dw12 & compl_eop[3]);
             pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;
         
         pcie_compl_delivered_o[3] <= #(TCQ) sop0_dw0 & compl_eop[0] &
                      (sop1_dw4 & compl_eop[1]) & 
                      (sop2_dw8 & compl_eop[2]) & 
                      (sop3_dw12 & compl_eop[3]);
         pcie_compl_delivered_tag3_o <= #(TCQ) compl_tag3;
       end // if (~pkt_in_progress)
     else
       begin
         pcie_compl_delivered_o[0] <= #(TCQ) (saved_compl_delivered & compl_eop[0])|
                      (sop0_dw4 & compl_eop[1])| 
                      (sop0_dw8 & compl_eop[1])| 
                      (sop0_dw12 & compl_eop[1])| 
                      (sop1_dw8 & compl_eop[2])| 
                      (sop1_dw12 & compl_eop[2])| 
                      (sop2_dw12 & compl_eop[3]);
         pcie_compl_delivered_tag0_o <= #(TCQ) (saved_compl_delivered & compl_eop[0])?
                        saved_compl_tag:
                        (sop0_dw4 & compl_eop[1])?
                        compl_tag1:
                        ((sop0_dw8 & compl_eop[1])| 
                         (sop1_dw8 & compl_eop[2]))?
                         compl_tag2:
                         compl_tag3;

         if (saved_compl_delivered & compl_eop[0])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) (sop0_dw4 & compl_eop[1])| 
                          (sop0_dw8 & compl_eop[1])| 
                          (sop0_dw12 & compl_eop[1])| 
                          (sop1_dw8 & compl_eop[2])| 
                          (sop1_dw12 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[3]);
         if (sop0_dw4 & compl_eop[1])
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag1;
         else if ((sop0_dw8 & compl_eop[1])| 
              (sop1_dw8 & compl_eop[2]))
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag2;
         else
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop0_dw4 & compl_eop[1])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ)(sop1_dw8 & compl_eop[2])| 
                          (sop1_dw12 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[3]);
         if (sop1_dw8 & compl_eop[2])
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag2;
         else
           pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop0_dw8 & compl_eop[1])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) sop1_dw12 & compl_eop[2];
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else if (sop1_dw8 & compl_eop[2])
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) sop2_dw12 & compl_eop[3];
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end
         else
           begin
         pcie_compl_delivered_o[1] <= #(TCQ) 1'b0;
         pcie_compl_delivered_tag1_o <= #(TCQ) compl_tag3;
           end

         if (saved_compl_delivered & compl_eop[0])
           begin
         if (sop0_dw4 & compl_eop[1])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop1_dw8 & compl_eop[2])| 
                          (sop1_dw12 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[3]);
             if (sop1_dw8 & compl_eop[2])
               pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag2;
             else
               pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else if (sop0_dw8 & compl_eop[1])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop1_dw12 & compl_eop[2])| 
                          (sop2_dw12 & compl_eop[3]);
             pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;
           end // if (saved_compl_delivered & compl_eop[0])
         else if (sop0_dw4 & compl_eop[1])
           begin
         if (sop1_dw8 & compl_eop[2])
           begin
             pcie_compl_delivered_o[2] <= #(TCQ) (sop2_dw12 & compl_eop[3]);
             pcie_compl_delivered_tag2_o <= #(TCQ) compl_tag3;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;
           end
         else
           pcie_compl_delivered_o[2] <= #(TCQ) 1'b0;

         pcie_compl_delivered_o[3] <= #(TCQ) (saved_compl_delivered & compl_eop[0]) &
                      (sop0_dw4 & compl_eop[1]) & 
                      (sop1_dw8 & compl_eop[2]) & 
                      (sop2_dw12 & compl_eop[3]);
         pcie_compl_delivered_tag3_o <= #(TCQ) compl_tag3;
       end // else: !if(~pkt_in_progress)
       end // if (compl_data_valid)
     else
       pcie_compl_delivered_o <= #(TCQ) 4'd0;

  // Save tag for next cycle
   always @(posedge clk_i)
     if (~reset_n_i)
       begin
     saved_compl_delivered <= #(TCQ) 1'b0;
     saved_compl_tag <= #(TCQ) 8'd0;
       end
     else if (compl_data_valid)
       begin
     if (compl_sop[3])
       begin
         saved_compl_delivered <= #(TCQ) compl_delivered[3];
         saved_compl_tag <= #(TCQ) compl_tag3;
       end
     else if (compl_sop[2])
       case(compl_sop2_ptr)
         2'd2:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[2];
         saved_compl_tag <= #(TCQ) compl_tag2;
           end
         default:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[3];
         saved_compl_tag <= #(TCQ) compl_tag3;
           end
       endcase // case(compl_sop2_ptr)
     else if (compl_sop[1])
       case(compl_sop1_ptr)
         2'd1:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[1];
         saved_compl_tag <= #(TCQ) compl_tag1;
           end
         2'd2:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[2];
         saved_compl_tag <= #(TCQ) compl_tag2;
           end
         default:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[3];
         saved_compl_tag <= #(TCQ) compl_tag3;
           end
       endcase // case(compl_sop1_ptr)
     else if (compl_sop[0])
       case(compl_sop0_ptr)
         2'd0:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[0];
         saved_compl_tag <= #(TCQ) compl_tag0;
           end
         2'd1:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[1];
         saved_compl_tag <= #(TCQ) compl_tag1;
           end
         2'd2:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[2];
         saved_compl_tag <= #(TCQ) compl_tag2;
           end
         default:
           begin
         saved_compl_delivered <= #(TCQ) compl_delivered[3];
         saved_compl_tag <= #(TCQ) compl_tag3;
           end
       endcase // case(compl_sop0_ptr)
       end // if (compl_data_valid)

endmodule // pcie_4_0_512b_rc_output_mux
