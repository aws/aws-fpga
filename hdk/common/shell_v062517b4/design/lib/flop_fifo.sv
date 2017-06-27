//----------------------------------------------------------------------------------
//Copyright (c) 2014
//
//Permission is hereby granted, free of charge, to any person obtaining a copy
//of this software and associated documentation files (the "Software"), to deal
//in the Software without restriction, including without limitation the rights
//to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//copies of the Software, and to permit persons to whom the Software is
//furnished to do so, subject to the following conditions:
//
//The above copyright notice and this permission notice shall be included in
//all copies or substantial portions of the Software.
//
//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//THE SOFTWARE.
//----------------------------------------------------------------------------------

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
      fifo[DEPTH-1] <= 0;
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


