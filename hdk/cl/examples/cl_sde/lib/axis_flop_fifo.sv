// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

// Restricted NDA Material
// =============================================================================


module axis_flop_fifo #(parameter IN_FIFO = 0, parameter DATA_WIDTH=512, parameter KEEP_WIDTH=DATA_WIDTH/8, parameter FIFO_DEPTH=3)

   (
    input                         aclk,
    input                         aresetn,
    input                         sync_rst_n,

    input                         s_axis_valid,
    input [DATA_WIDTH-1:0]        s_axis_data,
    input                         s_axis_last,
    input [KEEP_WIDTH-1:0]        s_axis_keep,
    output logic                  s_axis_ready,

    output logic                  m_axis_valid,
    output logic [DATA_WIDTH-1:0] m_axis_data,
    output logic                  m_axis_last,
    output logic [KEEP_WIDTH-1:0] m_axis_keep,
    input                         m_axis_ready

    );
   

  
   
   logic                 misc_full;
   logic                 misc_valid;
   logic [7:0]           w_d_full;
   logic [7:0]           w_d_valid;
   
   
   localparam FIFO_DEPTH_MINUS_1 = FIFO_DEPTH-1;

   generate
      if (IN_FIFO)
        flop_fifo_in #(.DEPTH(FIFO_DEPTH), .WIDTH(KEEP_WIDTH+1)) AXIS_MISC (
                                                             .clk(aclk),
                                                             .rst_n(aresetn),
                                                             .sync_rst_n(sync_rst_n),
                                                             .cfg_watermark(FIFO_DEPTH_MINUS_1),
                                                             .push_data({s_axis_keep, s_axis_last}),
                                                             .push(s_axis_valid & s_axis_ready),
                                                             .watermark(misc_full),
                                                             .pop_data({m_axis_keep, m_axis_last}),
                                                             .half_full(),
                                                             .data_valid(misc_valid),
                                                             .pop(m_axis_valid & m_axis_ready)
                                                            );
      else
        flop_fifo #(.DEPTH(FIFO_DEPTH), .WIDTH(KEEP_WIDTH+1)) AXIS_MISC (
                                                             .clk(aclk),
                                                             .rst_n(aresetn),
                                                             .sync_rst_n(sync_rst_n),
                                                             .cfg_watermark(FIFO_DEPTH_MINUS_1),
                                                             .push_data({s_axis_keep, s_axis_last}),
                                                             .push(s_axis_valid & s_axis_ready),
                                                             .watermark(misc_full),
                                                             .pop_data({m_axis_keep, m_axis_last}),
                                                             .half_full(),
                                                             .data_valid(misc_valid),
                                                             .pop(m_axis_valid & m_axis_ready)
                                                            );
   endgenerate

   generate
      for (genvar gi=0; gi<8; gi++)
        begin: gen_w_d
           if (IN_FIFO) 
             flop_fifo_in #(.DEPTH(FIFO_DEPTH), .WIDTH(DATA_WIDTH/8)) AXIS_D (
                                                                              .clk(aclk),
                                                                              .rst_n(aresetn),
                                                                              .sync_rst_n(sync_rst_n),
                                                                              .cfg_watermark(FIFO_DEPTH_MINUS_1),
                                                                              .push_data(s_axis_data[(gi*(DATA_WIDTH/8))+:(DATA_WIDTH/8)]),
                                                                              .push(s_axis_valid & s_axis_ready),
                                                                              .watermark(w_d_full[gi]),
                                                                              .pop_data(m_axis_data[(gi*(DATA_WIDTH/8))+:(DATA_WIDTH/8)]),
                                                                              .half_full(),
                                                                              .data_valid(w_d_valid[gi]),
                                                                              .pop(m_axis_valid & m_axis_ready)
                                                                              );
           else
             flop_fifo #(.DEPTH(FIFO_DEPTH), .WIDTH(DATA_WIDTH/8)) AXIS_D (
                                                                           .clk(aclk),
                                                                           .rst_n(aresetn),
                                                                           .sync_rst_n(sync_rst_n),
                                                                           .cfg_watermark(FIFO_DEPTH_MINUS_1),
                                                                           .push_data(s_axis_data[(gi*(DATA_WIDTH/8))+:(DATA_WIDTH/8)]),
                                                                           .push(s_axis_valid & s_axis_ready),
                                                                           .watermark(w_d_full[gi]),
                                                                           .pop_data(m_axis_data[(gi*(DATA_WIDTH/8))+:(DATA_WIDTH/8)]),
                                                                           .half_full(),
                                                                           .data_valid(w_d_valid[gi]),
                                                                           .pop(m_axis_valid & m_axis_ready)
                                                                           );
           
        end // block: gen_w_d
   endgenerate
   
   assign s_axis_ready = ~(misc_full | (|w_d_full));
   assign m_axis_valid = misc_valid & (&w_d_valid);

endmodule // axi4_flop_fifo

                           
   

