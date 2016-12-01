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
// File       : pcie4_uscale_plus_0_512b_cq_output_mux.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_512b_cq_output_mux #(
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

   ,input  wire [1:0]     pcie_cq_np_req_i // Client request to deliver NP TLP
   ,output reg [5:0]      pcie_cq_np_req_count_o // Current value of interface credit count for NP TLPs
   ,output reg [1:0]      np_credit_received_o // NP credit to TL
   ,output reg [1:0]      posted_req_delivered_o // Signals the delivery of a Posted Req on the CQ interface
   ,output wire           pipeline_empty_o // Indicates that the entire pipeline of the mux is empty
   );


   localparam MAX_CREDIT = 32;

   reg [1:0] output_fifo_occupancy;
   reg          output_fifo_write_ptr;
   reg          output_fifo_read_ptr;
   wire      output_fifo_full;
   wire      output_fifo_empty;

   reg [OUT_DATA_WIDTH-1:0] m_axis_cq_tdata_first_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_cq_tkeep_first_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_cq_tuser_first_reg;
   reg                 m_axis_cq_tlast_first_reg;
   
   reg [OUT_DATA_WIDTH-1:0] m_axis_cq_tdata_second_reg;
   reg [TKEEP_WIDTH-1:0]    m_axis_cq_tkeep_second_reg;
   reg [TUSER_WIDTH-1:0]    m_axis_cq_tuser_second_reg;
   reg                 m_axis_cq_tlast_second_reg;
   
   wire             output_reg_mux_sel;

   wire [3:0]              output_reg_in_req_type0;
   wire [3:0]              output_reg_in_req_type1;
   
   wire              output_reg_in_req_type0_np;
   wire              output_reg_in_req_type1_np;

   wire              output_reg_in_sop0;
   wire              output_reg_in_sop1;
   wire              output_reg_in_eop0;
   wire              output_reg_in_eop1;
   wire              output_reg_in_error;

   reg [1:0]             pcie_cq_np_req_reg;
   reg                 tlp_in_progress;
   reg                 tlp_in_progress_type;

   reg [1:0]             np_tlp_count;
   
   wire [3:0]             out_req_type0;
   wire [3:0]             out_req_type1;
   reg                 m_axis_cq_tvalid_last;
   reg                 m_axis_cq_sop0_last;
   reg                 m_axis_cq_sop1_last;
   reg                 m_axis_cq_eop0_last;
   reg                 m_axis_cq_eop1_last;
   reg                 m_axis_cq_posted_type0_last;
   reg                 m_axis_cq_posted_type1_last;
   reg                 out_ready_reg;
   reg                 posted_tlp_in_progress;
   reg                 posted_tlp_in_progress_type;

  reg                 out_tlast_reg;
  reg [TKEEP_WIDTH-1:0]     out_tkeep_reg;

   //---------------------------------------------------------------------------------------------
   // Output FIFO
   // The main FIFO feeds into two read registers in the user clock domain, which are configured
   // as a 2-entry FIFO.
   // These are termed m_axis_cq_*_reg_first and m_axis_cq_*_reg_second.
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
          m_axis_cq_tdata_first_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_cq_tdata_second_reg <= #(TCQ) {OUT_DATA_WIDTH{1'b0}};
          m_axis_cq_tkeep_first_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_cq_tkeep_second_reg <= #(TCQ) {TKEEP_WIDTH{1'b0}};
          m_axis_cq_tuser_first_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_cq_tuser_second_reg <= #(TCQ) {TUSER_WIDTH{1'b0}};
          m_axis_cq_tlast_first_reg <= #(TCQ) 1'b0;
          m_axis_cq_tlast_second_reg <= #(TCQ) 1'b0;
       end
     else
        if (in_data_valid_i & ~output_fifo_full)
      begin
         case(output_fifo_write_ptr)
           1'b0:
         begin
            m_axis_cq_tdata_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_cq_tkeep_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_cq_tuser_first_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_cq_tlast_first_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
         end
           default:
         begin
            m_axis_cq_tdata_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH-1:0];
            m_axis_cq_tkeep_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH-1:OUT_DATA_WIDTH];
            m_axis_cq_tuser_second_reg <= #(TCQ) in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+TUSER_WIDTH-1:OUT_DATA_WIDTH+TKEEP_WIDTH];
            m_axis_cq_tlast_second_reg <= #(TCQ) in_data_i[IN_DATA_WIDTH-1];
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
           out_data_o <= #(TCQ) m_axis_cq_tdata_first_reg;
           out_tkeep_reg <= #(TCQ) m_axis_cq_tkeep_first_reg;
           out_tuser_o <= #(TCQ) m_axis_cq_tuser_first_reg;
           out_tlast_reg <= #(TCQ) m_axis_cq_tlast_first_reg;
        end
          default:
        begin
           out_data_o <= #(TCQ) m_axis_cq_tdata_second_reg;
           out_tkeep_reg <= #(TCQ) m_axis_cq_tkeep_second_reg;
           out_tuser_o <= #(TCQ) m_axis_cq_tuser_second_reg;
           out_tlast_reg <= #(TCQ) m_axis_cq_tlast_second_reg;
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

   //--------------------------------------------------------------------
   // NP credit management
   //-----------------------------------------------------------------------------------                

   // Decode packet Req Type as Posted/Non-Posted
   assign output_reg_in_req_type0 = in_data_i[78:75];
   assign output_reg_in_req_type1 = in_data_i[256+78:256+75];
   
   assign output_reg_in_req_type0_np = (output_reg_in_req_type0[3:0] != 4'd1) &&
	  (output_reg_in_req_type0[3:2] != 2'b11);
   assign output_reg_in_req_type1_np = (output_reg_in_req_type1[3:0] != 4'd1) &&
	  (output_reg_in_req_type1[3:2] != 2'b11);
  
   assign output_reg_in_sop0 = in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+80];
   assign output_reg_in_sop1 = in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+81];
   assign output_reg_in_eop0 = in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+86];
   assign output_reg_in_eop1 = in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+87];
   assign output_reg_in_error = in_data_i[OUT_DATA_WIDTH+TKEEP_WIDTH+95];  // discontinue  

   // Register the user input pcie_cq_np_req_i
   always @(posedge clk_i)
     if (~reset_n_i)
       pcie_cq_np_req_reg <= #(TCQ) 2'b00;
     else
       pcie_cq_np_req_reg <= #(TCQ) pcie_cq_np_req_i;

   // If a TLP is in progress from last beat, record its type.
  always @(posedge clk_i)
    if (~reset_n_i)
      begin
	tlp_in_progress <= 1'b0;
	tlp_in_progress_type <= 1'b0;
      end
  else if (in_data_valid_i & ~output_fifo_full)
    begin
      if (~tlp_in_progress)
	begin
	  if (output_reg_in_sop0 & ~output_reg_in_eop0)
            begin
              tlp_in_progress <= 1'b1;
              tlp_in_progress_type <= output_reg_in_req_type0_np;
            end
          else if (output_reg_in_sop1 & ~output_reg_in_eop1)
            begin
              tlp_in_progress <= 1'b1;
              tlp_in_progress_type <= output_reg_in_req_type1_np;
            end
          else
            begin
              tlp_in_progress <= 1'b0;
              tlp_in_progress_type <= 1'b0;
            end
	end // if (~tlp_in_progress)
      else
	begin
          if ((output_reg_in_eop0 & ~output_reg_in_sop0)|
	      output_reg_in_eop1)
	    tlp_in_progress <= 1'b0;
          if (output_reg_in_sop0)
	    tlp_in_progress_type <= output_reg_in_req_type1_np;
	end // else: !if(~tlp_in_progress)
    end // if (in_data_valid_i & ~output_fifo_full)
   
   // Determine number of NP TLPs being sent to user
   always @(*)
     begin
    case({output_reg_in_eop1, output_reg_in_eop0})
      2'd0: np_tlp_count = 2'd0;
      2'd1:
        begin
           if (~tlp_in_progress)
             begin
               if (output_reg_in_req_type0_np & ~output_reg_in_error)
		 np_tlp_count = 2'd1;
               else
		 np_tlp_count = 2'd0;
             end
           else
             begin
               if (tlp_in_progress_type & ~output_reg_in_error)
		 np_tlp_count = 2'd1;
               else
		 np_tlp_count = 2'd0;
             end // else: !if(~tlp_in_progress)
	end // case: 2'd1
      
      default: //2'd3
        begin
           if (~tlp_in_progress)
             begin
               if (output_reg_in_req_type0_np & output_reg_in_req_type1_np)
		 np_tlp_count = 2'd2;
               else if (output_reg_in_req_type0_np | output_reg_in_req_type1_np)
		 np_tlp_count = 2'd1;
               else
		 np_tlp_count = 2'd0;
             end
           else
             begin
               if (tlp_in_progress_type & output_reg_in_req_type1_np)
		 np_tlp_count = 2'd2;
               else if (tlp_in_progress_type | output_reg_in_req_type1_np)
		 np_tlp_count = 2'd1;
               else
		 np_tlp_count = 2'd0;
             end // else: !if(~tlp_in_progress)
        end // case: default
    endcase // case({output_reg_in_eop1, output_reg_in_eop0})
     end // always @ (*)

   // Maintain current NP credit
   always @(posedge clk_i)
     if (~reset_n_i)
       begin
      pcie_cq_np_req_count_o <= 6'd0;
       end
     else if (link_down_reset_i)
       begin
      pcie_cq_np_req_count_o <= 6'd0;
       end
     else
       if (in_data_valid_i & ~output_fifo_full)
     begin
        casez({np_tlp_count, pcie_cq_np_req_reg})
          4'b00_01:
        begin
           // No TLPs being delivered, user provided 1 credit
           if (pcie_cq_np_req_count_o != MAX_CREDIT[5:0])
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o + 6'd1;
        end
          4'b00_1?:
        begin
           // No TLPs being delivered, user provided 2 credits
           if (pcie_cq_np_req_count_o <= (MAX_CREDIT-2))
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o + 6'd2;
           else
             pcie_cq_np_req_count_o <= MAX_CREDIT[5:0];
        end
          4'b01_00:
        begin
           // One NP TLP being delivered, user provided no credit
           if (pcie_cq_np_req_count_o != 6'd0)
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o - 6'd1;
        end
          4'b01_1?:
        begin
           // One NP TLP being delivered, user provided 2 credits
           if (pcie_cq_np_req_count_o != MAX_CREDIT[5:0])
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o + 6'd1;
        end
          4'b1?_00:
        begin
           // Two NP TLP being delivered, user provided no credit.
           // Decrement by 2.
           if (pcie_cq_np_req_count_o[5:1] != 5'd0)
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o - 6'd2;
           else
             pcie_cq_np_req_count_o[0] <= 1'b0;
        end          
          4'b1?_01:
        begin
           // Two NP TLP being delivered, user provided 1 credit.
           // Decrement by 1.
           if (pcie_cq_np_req_count_o != 6'd0)
             pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o - 6'd1;
        end
        endcase // casez({np_tlp_count, pcie_cq_np_req_reg})
     end // if (in_data_valid_i & ~output_fifo_full)
       else
     begin
       casez(pcie_cq_np_req_reg)
         2'b01:
           begin
         // No TLPs being delivered, user provided 1 credit
         if (pcie_cq_np_req_count_o != MAX_CREDIT[5:0])
           pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o + 6'd1;
           end
         2'b1?:
           begin
         // No TLPs being delivered, user provided 2 credits
         if (pcie_cq_np_req_count_o <= (MAX_CREDIT-2))
           pcie_cq_np_req_count_o <= pcie_cq_np_req_count_o + 6'd2;
         else
           pcie_cq_np_req_count_o <= MAX_CREDIT[5:0];
           end
         default:
           begin
           end
       endcase // casez(pcie_cq_np_req_reg)
     end // else: !if(in_data_valid_i & ~output_fifo_full)

  // Send indication to Transaction Layer when user issues more credit
   always @(posedge clk_i)
     if (~reset_n_i)
       np_credit_received_o <= 2'b00;
     else
       if (in_data_valid_i & ~output_fifo_full)
     begin
        casez({np_tlp_count, pcie_cq_np_req_reg})
          4'b00_01:
        // No TLPs being delivered, user provided 1 credit
        begin
           // Provide credit to TL when credit count has not saturated
           if (pcie_cq_np_req_count_o == MAX_CREDIT[5:0])
             np_credit_received_o <= 2'b00;
           else
             np_credit_received_o <= 2'b01;
        end
          4'b00_1?:
        // No TLPs being delivered, user provided 2 credits
        begin
           // Provide credit to TL when credit count has not saturated
           if (pcie_cq_np_req_count_o == MAX_CREDIT[5:0])
             np_credit_received_o <= 2'b00;
           else if (pcie_cq_np_req_count_o == (MAX_CREDIT -1))
             // Provide 1 credit.
             np_credit_received_o <= 2'b01;
           else
             // Provide 2 credits.
             np_credit_received_o <= 2'b11;
        end // case: 4'b00_1x
          4'b01_01:
        // 1 TLP being delivered, user provided 1 credit
        begin
           // Always provide 1 credit to TL
           np_credit_received_o <= 2'b01;
        end
          4'b01_1?:
        // 1 TLP being delivered, user provided 2 credits
        begin
           // Provide 1 credit to TL when credit count has not saturated
           if (pcie_cq_np_req_count_o == MAX_CREDIT[5:0])
             np_credit_received_o <= 2'b01;
           else
             np_credit_received_o <= 2'b11;
        end
          4'b1?_01:
        // 2 TLPs being delivered, user provided 1 credit
        begin
           // Always provide 1 credit to TL
           np_credit_received_o <= 2'b01;
        end
          4'b1?_1?:
        // 2 TLPs being delivered, user provided 2 credits
        begin
           // Always provide 2 credits to TL
           np_credit_received_o <= 2'b11;
        end
          default:
        begin
           np_credit_received_o <= 2'b00;
        end
        endcase // casez({np_tlp_count, pcie_cq_np_req_reg})
     end // if (in_data_valid_i & ~output_fifo_full)
       else
     begin
       casez(pcie_cq_np_req_reg)
         2'b01:
           begin
         // No TLPs being delivered, user provided 1 credit
         if (pcie_cq_np_req_count_o != MAX_CREDIT[5:0])
           np_credit_received_o <= 2'b01;
         else
           np_credit_received_o <= 2'b00;
           end
         2'b1?:
           begin
         // No TLPs being delivered, user provided 2 credits.
         // Provide credit to TL when credit count has not saturated
         if (pcie_cq_np_req_count_o == MAX_CREDIT[5:0])
           np_credit_received_o <= 2'b00;
         else if (pcie_cq_np_req_count_o == (MAX_CREDIT -1))
           // Provide 1 credit.
           np_credit_received_o <= 2'b01;
         else
           // Provide 2 credits.
           np_credit_received_o <= 2'b11;
           end // case: 4'b00_1?
         default:
           begin
         np_credit_received_o <= 2'b00;
           end
       endcase // casez(pcie_cq_np_req_reg)
     end // else: !if(in_data_valid_i & ~output_fifo_full)

 //-------------------------------------------------------------------------------------------
   // Generate indication when a Posted request is delivered to the user

   assign out_req_type0 = out_data_o[78:75];
   assign out_req_type1 = out_data_o[256+78:256+75];

   always @(posedge clk_i)
     if (~reset_n_i)
       begin
      m_axis_cq_tvalid_last <= 1'b0;
      m_axis_cq_sop0_last <= 1'b0;
      m_axis_cq_sop1_last <= 1'b0;
      m_axis_cq_eop0_last <= 1'b0;
      m_axis_cq_eop1_last <= 1'b0;
      m_axis_cq_posted_type0_last <= 1'b0;
      m_axis_cq_posted_type1_last <= 1'b0;
       end
     else
       begin
      m_axis_cq_tvalid_last <= out_data_valid_o;
      m_axis_cq_sop0_last <= out_tuser_o[80];
      m_axis_cq_sop1_last <= out_tuser_o[81];
      m_axis_cq_eop0_last <= out_tuser_o[86];
      m_axis_cq_eop1_last <= out_tuser_o[87];
      m_axis_cq_posted_type0_last <= (out_req_type0[3:0] == 4'd1) || (out_req_type0[3:2] == 2'b11);
      m_axis_cq_posted_type1_last <= (out_req_type1[3:0] == 4'd1) || (out_req_type1[3:2] == 2'b11);
       end // else: !if(~reset_n_i)

   // Register ready
   always @(posedge clk_i)
     if (~reset_n_i)
       out_ready_reg <= 1'b0;
     else
       out_ready_reg <= downstream_ready_i;

   always @(posedge clk_i)
     if (~reset_n_i)
       begin
      posted_tlp_in_progress <= 1'b0;
      posted_tlp_in_progress_type <= 1'b0;
       end
     else if (link_down_reset_i)
       posted_tlp_in_progress <= 1'b0;
     else if (m_axis_cq_tvalid_last & out_ready_reg)
       begin
          if (~posted_tlp_in_progress)
        begin
           if (m_axis_cq_sop0_last & ~m_axis_cq_eop0_last)
         begin
            posted_tlp_in_progress <= 1'b1;
            posted_tlp_in_progress_type <=  m_axis_cq_posted_type0_last;
         end
           else if (m_axis_cq_sop1_last & ~m_axis_cq_eop1_last)
         begin
            posted_tlp_in_progress <= 1'b1;
            posted_tlp_in_progress_type <=  m_axis_cq_posted_type1_last;
         end
           else
         posted_tlp_in_progress <= 1'b0;
        end // if (~posted_tlp_in_progress)
      else
        begin
           if ((m_axis_cq_eop0_last & ~m_axis_cq_sop0_last) |
           m_axis_cq_eop1_last)
         posted_tlp_in_progress <= 1'b0;

           if (m_axis_cq_sop0_last)
         posted_tlp_in_progress_type <= m_axis_cq_posted_type1_last;
        end // else: !if(~posted_tlp_in_progress)
       end // if (m_axis_cq_tvalid_last & out_ready_reg)

   always @(posedge clk_i)
     if (~reset_n_i)
       posted_req_delivered_o <= 2'b00;
     else if (m_axis_cq_tvalid_last & out_ready_reg)
       begin
          if (~posted_tlp_in_progress)
        begin
          if ((m_axis_cq_sop0_last & m_axis_cq_posted_type0_last & m_axis_cq_eop0_last) &
          (m_axis_cq_sop1_last & m_axis_cq_posted_type1_last & m_axis_cq_eop1_last))
        // Two Complete TLPs in this beat.
        posted_req_delivered_o <= 2'b11;
          else if ((m_axis_cq_sop0_last & m_axis_cq_posted_type0_last & m_axis_cq_eop0_last) |
               (m_axis_cq_sop1_last & m_axis_cq_posted_type1_last & m_axis_cq_eop1_last))
        // Single TLP beginning and ending in this beat.
        posted_req_delivered_o <= 2'b01;
          else
        // No Posted TLP ending in this beat
        posted_req_delivered_o <= 2'b00;
        end // if (~tlp_in_progress)
      else
        begin
               if ((posted_tlp_in_progress_type & m_axis_cq_eop0_last) &
           (m_axis_cq_sop0_last & m_axis_cq_posted_type1_last & m_axis_cq_eop1_last))
         // TLP in progress ended in this cycle, and a new TLP started and ended.
         posted_req_delivered_o <= 2'b11;
               else if ((posted_tlp_in_progress_type & m_axis_cq_eop0_last) |
            (m_axis_cq_sop0_last & m_axis_cq_posted_type1_last & m_axis_cq_eop1_last))
         posted_req_delivered_o <= 2'b01;
           else
         posted_req_delivered_o <= 2'b00;
        end // else: !if(~posted_tlp_in_progress)
       end // if (m_axis_cq_tvalid_last & out_ready_reg)
     else
       posted_req_delivered_o <= 2'b00;

  assign pipeline_empty_o = output_fifo_empty && ~out_data_valid_o && ~m_axis_cq_tvalid_last && (posted_req_delivered_o == 2'b00);


endmodule // pcie_4_0_512b_cq_output_mux
