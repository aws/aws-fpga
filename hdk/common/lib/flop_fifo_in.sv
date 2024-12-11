// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
                         parameter OUTPUT_REG = 0,
                         parameter LESS_RST   = 0
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

   logic               ff_data_valid = 'h0;
   logic [WIDTH-1:0]   ff_pop_data = 'h0;
   logic [WIDTH-1:0]   ff_fifo [DEPTH-1:0] = '{default:'0};
   logic [DEPTH-1:0]   ff_valid;

`ifdef FPGA_LESS_RST
   localparam LESS_RST_LOCAL = 1;
`else
   localparam LESS_RST_LOCAL = LESS_RST;
`endif   
                               
   // For every push, keep pushing data into the ff_fifo array
   // For pop's there is no change
   generate
      if (LESS_RST_LOCAL == 1) begin
         
         always @(posedge clk) begin
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
         end // always @ (posedge clk)
      end // if (LESS_RST_LOCAL == 1)
      
      else begin
         
         always @(posedge clk or negedge rst_n)
           if (!rst_n) begin
              ff_fifo <= '{default:'0};
           end
           else if (!sync_rst_n) begin
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
         
      end // if !(LESS_RST_LOCAL == 1)

   endgenerate
   
   // For push & ~pop, valid[0] gets 1. every thing else shifts.
   // For ~push & pop, the most significant valid gets invalidated
   // For push & pop, valid array stays the same
   generate
      
      if (LESS_RST_LOCAL == 1) begin
         
         always @(posedge clk)
           if (!rst_n || !sync_rst_n) begin
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

      end // if (LESS_RST_LOCAL == 1)
      
      else begin
      
         always @(posedge clk or negedge rst_n)
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

      end // else: !if(LESS_RST_LOCAL == 1)

   endgenerate
   
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

   generate
      if (OUTPUT_REG == 1) begin

         if (LESS_RST_LOCAL == 1) begin

            always @(posedge clk) begin
               if (!rst_n || !sync_rst_n) begin
                  ff_data_valid <= 1'b0;
               end
               else begin
                  ff_data_valid <= ss_data_valid;
               end
               ff_pop_data <= ss_pop_data;
            end
            
         end // if (LESS_RST_LOCAL == 1)

         else begin

            always @(posedge clk or negedge rst_n)
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

         end // else: !if(LESS_RST_LOCAL == 1)

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

   
