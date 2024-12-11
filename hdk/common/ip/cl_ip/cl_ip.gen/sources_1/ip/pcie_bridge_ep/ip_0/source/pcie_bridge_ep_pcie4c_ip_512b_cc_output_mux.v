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
// File       : pcie_bridge_ep_pcie4c_ip_512b_cc_output_mux.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_512b_cc_output_mux #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter IN_DATA_WIDTH = 256+33+8+1,    
   parameter OUT_DATA_WIDTH = 256,
   parameter TUSER_WIDTH = 33,
   parameter TKEEP_WIDTH = 8,
   parameter TREADY_WIDTH = 4
   )
  (
    input  wire           clk_i // 500 MHz clock for core-facing interfaces
   ,input  wire           reset_n_i // Reset in the user clock domain
   ,input  wire           link_down_reset_i // Link went down

   ,input wire[IN_DATA_WIDTH-1:0] in_data_i
   ,input wire in_data_valid_i
   ,output wire upstream_ready_o

   ,output reg [OUT_DATA_WIDTH-1:0]  out_data_o
   ,output reg           out_data_valid_o
   ,output reg [TUSER_WIDTH-1:0] out_tuser_o
   ,output reg          out_tlast_o
   ,output reg [TKEEP_WIDTH-1:0] out_tkeep_o
   ,input  wire [TREADY_WIDTH-1:0]  downstream_ready_i
   );


   reg [1:0] output_fifo_occupancy;
  reg          output_fifo_write_ptr;
  reg          output_fifo_read_ptr;
   wire      output_fifo_full;
   wire      output_fifo_empty;

   reg [OUT_DATA_WIDTH-1:0] m_axis_cc_tdata_first_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_cc_tkeep_first_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_cc_tuser_first_reg;
   reg                 m_axis_cc_tlast_first_reg;
   
   reg [OUT_DATA_WIDTH-1:0] m_axis_cc_tdata_second_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_cc_tkeep_second_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_cc_tuser_second_reg;
   reg                 m_axis_cc_tlast_second_reg;
   
   wire             output_reg_mux_sel;
   //---------------------------------------------------------------------------------------------
   // Output FIFO.
   // The main FIFO feeds into two read registers in the core clock domain, which are configured
   // as a 2-entry FIFO.
   // This can be thought of as logical extensions of the main FIFO.
   //---------------------------------------------------------------------------------------------

   assign    upstream_ready_o = ~output_fifo_full;

   // Maintain write and read pointers
   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_write_ptr <= #(TCQ)  1'b0;
     else if (link_down_reset_i)
       output_fifo_write_ptr <= #(TCQ)  1'b0;
     else
       if (in_data_valid_i & ~output_fifo_full)
     output_fifo_write_ptr <= #(TCQ) ~output_fifo_write_ptr;
   
   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_read_ptr <= #(TCQ) 2'd0;
     else if (link_down_reset_i)
       output_fifo_read_ptr <= #(TCQ) 2'd0;
     else
       if ((downstream_ready_i[3] | ~out_data_valid_o) &
       ~output_fifo_empty)
     output_fifo_read_ptr <= #(TCQ) ~output_fifo_read_ptr;

      // Maintain FIFO occupancy
   always @(posedge clk_i)
     if (~reset_n_i)
       output_fifo_occupancy <= #(TCQ)  2'd0;
     else if (link_down_reset_i)
       output_fifo_occupancy <= #(TCQ)  2'd0;
     else
       if ((in_data_valid_i & ~output_fifo_full) &
       ~((downstream_ready_i[3] | ~out_data_valid_o) &
         ~output_fifo_empty))
     output_fifo_occupancy <= #(TCQ) output_fifo_occupancy + 2'd1;
       else
     if (~(in_data_valid_i & ~output_fifo_full) &
         ((downstream_ready_i[3] | ~out_data_valid_o) &
          ~output_fifo_empty))
       output_fifo_occupancy <= #(TCQ) output_fifo_occupancy - 2'd1;
   
   assign output_fifo_full = output_fifo_occupancy[1];
   assign output_fifo_empty = (output_fifo_occupancy == 2'b00);

   // Write data into the Output registers
   always @(posedge clk_i)
     if (~reset_n_i)
       begin
          m_axis_cc_tdata_first_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_cc_tdata_second_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_cc_tkeep_first_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_cc_tkeep_second_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_cc_tuser_first_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_cc_tuser_second_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_cc_tlast_first_reg <= #(TCQ) 1'b0;
          m_axis_cc_tlast_second_reg <= #(TCQ) 1'b0;
       end
     else
        if (in_data_valid_i & ~output_fifo_full)
      begin
        case(output_fifo_write_ptr)
          1'b0:
         begin
            m_axis_cc_tdata_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_cc_tkeep_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_cc_tuser_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_cc_tlast_first_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
         end
           default:
         begin
            m_axis_cc_tdata_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_cc_tkeep_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_cc_tuser_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_cc_tlast_second_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
         end
         endcase // case(output_fifo_write_ptr)
        end // if (in_data_valid_i & ~output_fifo_full)
   
   // Output registers

   assign output_reg_mux_sel = output_fifo_read_ptr;

   always @(posedge clk_i)
     if (~reset_n_i)
       begin
      out_data_o <= #(TCQ)  {OUT_DATA_WIDTH{1'b0}};
      out_tuser_o <= #(TCQ)  {TUSER_WIDTH{1'b0}};
      out_tkeep_o <= #(TCQ)  {TKEEP_WIDTH{1'b0}};
      out_tlast_o <= #(TCQ)  1'b0;
       end
     else
       begin
      if (~out_data_valid_o | downstream_ready_i[0])
        begin
           case(output_reg_mux_sel)
         1'b0:
           begin
              out_data_o[127:0] <= #(TCQ)  m_axis_cc_tdata_first_reg[127:0];
           end
         default:
           begin
              out_data_o[127:0] <= #(TCQ)  m_axis_cc_tdata_second_reg[127:0];
           end
           endcase // case(output_reg_mux_sel)
        end // if (~out_data_valid_o | downstream_ready_i[0])

      if (~out_data_valid_o | downstream_ready_i[1])
        begin
           case(output_reg_mux_sel)
         1'b0:
           begin
              out_data_o[255:128] <= #(TCQ)  m_axis_cc_tdata_first_reg[255:128];
           end
         default:
           begin
              out_data_o[255:128] <= #(TCQ)  m_axis_cc_tdata_second_reg[255:128];
           end
           endcase // case(output_reg_mux_sel)
        end // if (~out_data_valid_o | downstream_ready_i[1])
      
      if (~out_data_valid_o | downstream_ready_i[2])
        begin
           case(output_reg_mux_sel)
         1'b0:
           begin
              out_tuser_o <= #(TCQ)  m_axis_cc_tuser_first_reg;
           end
         default:
           begin
              out_tuser_o <= #(TCQ)  m_axis_cc_tuser_second_reg;
           end
           endcase // case(output_reg_mux_sel)
        end // if (~out_data_valid_o | downstream_ready_i[2])
      
      if (~out_data_valid_o | downstream_ready_i[3])
        begin
           case(output_reg_mux_sel)
         1'b0:         
           begin
              out_tkeep_o <= #(TCQ)  m_axis_cc_tkeep_first_reg;
              out_tlast_o <= #(TCQ)  m_axis_cc_tlast_first_reg;
           end
         default:
           begin
              out_tkeep_o <= #(TCQ)  m_axis_cc_tkeep_second_reg;
              out_tlast_o <= #(TCQ)  m_axis_cc_tlast_second_reg;
           end
           endcase // case(output_reg_mux_sel)
        end // if (~out_data_valid_o | downstream_ready_i[3])
       end // else: !if(~reset_n_i)

   always @(posedge clk_i)
     if (~reset_n_i)
       out_data_valid_o <= #(TCQ) 1'b0;
     else
       if (~out_data_valid_o | downstream_ready_i[0])
     out_data_valid_o <= #(TCQ) ~output_fifo_empty;

endmodule // pcie_4_0_512b_cc_output_mux

