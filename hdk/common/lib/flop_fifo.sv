// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


//------------------------------------------------------------------------------
//   Description :
//       Simple Flop shifting FIFO
//
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

module flop_fifo
  (
   // Inputs
   clk,
   rst_n,
   sync_rst_n,
   cfg_watermark,
   push,
   push_data,
   pop,
   // Outputs
   pop_data,
   half_full,
   watermark,
   data_valid
   );

   parameter WIDTH = 8;
   parameter DEPTH = 16;

   //-------------------------------
   // Inputs
   //-------------------------------
   input     clk;
   input     rst_n;
   input     sync_rst_n;
   input[31:0] cfg_watermark;
   input     push;
   input [(WIDTH-1):0] 	push_data;
   input 		pop;

   //-------------------------------
   // Outputs
   //-------------------------------
   output [(WIDTH-1):0] pop_data;
   output               half_full;
   output               watermark;
   output 		         data_valid;


logic[WIDTH:0] fifo[0:(DEPTH-1)] = '{default:'0};

logic[WIDTH:0] nxt_fifo[0:(DEPTH-1)];
logic[(DEPTH-1):0] fifo_valid;

//---------------------------------------------------
// MSB of the FIFO is the valid bit, create valid vector
//---------------------------------------------------
always_comb
begin
   for (int i=0;i<DEPTH;i=i+1)
      fifo_valid[i] = fifo[i][WIDTH];
end

always @*
begin

   nxt_fifo[0] = (push && !fifo_valid[0])?   {1'b1, push_data}: fifo[0];

   for (int i=1;i<(DEPTH);i=i+1)
   begin
      if (push && fifo_valid[i-1] && !fifo_valid[i])
         nxt_fifo[i] = {1'b1, push_data};
      else
         nxt_fifo[i] = fifo[i];
   end

end

always @(posedge clk)
begin
   if (!sync_rst_n || !rst_n)
      for (int i=0; i<DEPTH; i++)
         fifo[i][WIDTH] <= 0;
   else if (pop)
   begin
      for (int i=0; i<(DEPTH-1); i=i+1)
         fifo[i] <= nxt_fifo[i+1];
      fifo[DEPTH-1][WIDTH] <= 0;
   end
   else
   begin
      for (int i=0; i<DEPTH; i=i+1)
         fifo[i] <= nxt_fifo[i];
   end

end

assign {data_valid, pop_data} = fifo[0];

assign half_full = fifo_valid[((DEPTH >> 1)-1)];
assign watermark = fifo_valid[cfg_watermark];

endmodule
