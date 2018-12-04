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

// flop_fifo_in : Flops the input data right away

module flop_fifo_in #(// --------------------------------------------------
                         // Overridable Parameters
                         // --------------------------------------------------
                         parameter WIDTH      = 32,
                         parameter DEPTH      = 3,
                         parameter OUTPUT_REG = 0
                         )
   (
   // --------------------------------------------------
   // Ports
   // --------------------------------------------------
    input              clk,
    input              rst_n,
    input              sync_rst_n,
    input [31:0]       cfg_watermark,
    input              push,
    input [WIDTH-1:0]  push_data,
    input              pop,
    output [WIDTH-1:0] pop_data,
    output             data_valid,
    output             half_full,
    output             watermark
    );

   // --------------------------------------------------
   // Local Parameters
   // --------------------------------------------------

   // --------------------------------------------------
   // Wires and registers
   // --------------------------------------------------

   logic               ss_data_valid;
   logic [WIDTH-1:0]   ss_pop_data;

   logic               ff_data_valid;
   logic [WIDTH-1:0]   ff_pop_data;
   logic [WIDTH-1:0]   ff_fifo [DEPTH-1:0];
   logic [DEPTH-1:0]   ff_valid;
   
   // For every push, keep pushing data into the ff_fifo array
   // For pop's there is no change
`ifdef FPGA_LESS_RST
   always_ff @(posedge clk)
     if (!sync_rst_n) begin
`else   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) begin
        ff_fifo <= '{default:'0};
     end
     else if (!sync_rst_n) begin
`endif
        ff_fifo <= '{default:'0};
     end
     else begin
       for (int i = 0; i < DEPTH; i++) begin
         if (push) begin
            if (i == 0)
              ff_fifo[i] <= push_data;
            else
              ff_fifo[i] <= ff_fifo[i-1];
         end
         else
           ff_fifo[i] <= ff_fifo[i];
       end // for (int i = 0; i < DEPTH; i++)
     end // else: !if(!rst_n)

   // For push & ~pop, valid[0] gets 1. every thing else shifts.
   // For ~push & pop, the most significant valid gets invalidated
   // For push & pop, valid array stays the same
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) begin
        ff_valid <= '{default:'0};
     end
     else if (!sync_rst_n) begin
        ff_valid <= '{default:'0};
     end
     else begin
       for (int i = 0; i < DEPTH; i++) begin
         if (push & ~pop) begin
            if (i == 0)
              ff_valid[i] <= 1'b1;
            else
              ff_valid[i] <= ff_valid[i-1];
         end
         else if (~push & pop) begin
            if (i == DEPTH - 1)
              ff_valid[i] <= 1'b0;
            else
              ff_valid[i] <= ff_valid[i+1] ? 1'b1 : 1'b0;
         end
         else
            ff_valid[i] <= ff_valid[i];
       end // for (int i = 0; i < DEPTH; i++)
     end // else: !if(!rst_n)

   // Output data is the most significant data (oldest data)
   always_comb begin
      ss_pop_data = ({WIDTH{1'b0}});
      for (int i = 0; i < DEPTH; i++) begin
         if (ff_valid[i]) 
           ss_pop_data = ff_fifo[i];
      end
   end
   
   // Data is valid as long as entry 0 is valid
   assign ss_data_valid = ff_valid[0];

   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n) begin
        ff_pop_data <= '{default:'0};
        ff_data_valid <= 1'b0;
     end
     else if (!sync_rst_n) begin
        ff_pop_data <= '{default:'0};
        ff_data_valid <= 1'b0;
     end
     else begin
        ff_pop_data <= ss_pop_data;
        ff_data_valid <= ss_data_valid;
     end

   generate
      if (OUTPUT_REG) begin
         assign pop_data = ff_pop_data;
         assign data_valid = ff_data_valid;
      end
      else begin
         assign pop_data = ss_pop_data;
         assign data_valid = ss_data_valid;
      end
   endgenerate

   assign half_full = ff_valid[((DEPTH >> 1)-1)];
   assign watermark = ff_valid[cfg_watermark];

endmodule // epipe_flop_fifo

   
