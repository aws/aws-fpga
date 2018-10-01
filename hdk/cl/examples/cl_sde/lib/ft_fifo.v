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
//   
// This is a flow-through FIFO that converts a RAM-based FIFO (1 clock
// latency on the RAM) to what looks like a flop based FIFO.  There is
// no delay between pop and getting the next data.  This sometimes simplifies
// the FIFO pop logic.
//
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

module ft_fifo (
   clk,
   rst_n,

   sync_rst_n,

   ram_fifo_empty,
   ram_fifo_data,
   ft_pop,

   ram_pop,

   ft_valid,
   ft_data
   );

parameter FIFO_WIDTH = 32;

input clk;                          //Global clock
input rst_n;                        //Global reset

input sync_rst_n;                   //Synchronous reset

input ram_fifo_empty;               //RAM FIFO is empty
input[FIFO_WIDTH-1:0] ram_fifo_data;   //RAM FIFO data
input ft_pop;                       //POP FT FIFO

output ram_pop;                     //Pop the RAM FIFO

output ft_valid;                    //FT FIFO is valid
output[FIFO_WIDTH-1:0] ft_data;     //FT FIFO data

////////////////////////////////////////////////////////
//Flow through FIFO to present data to arbiter
reg ram_pop_q;                         //Data is valid one clock after pop
reg[FIFO_WIDTH:0] ft0, ft1;            //Flow through FIFO flops
wire[FIFO_WIDTH:0] nxt_ft0, nxt_ft1;

wire ft0_valid = ft0[FIFO_WIDTH];
wire ft1_valid = ft1[FIFO_WIDTH];

assign ram_pop = !ram_fifo_empty && (!ft1_valid||ft_pop) && (!ft0_valid||!ram_pop_q||ft_pop);

always @(negedge rst_n or posedge clk)
   if (!rst_n)
      ram_pop_q <= 0;   
   else
      ram_pop_q <= ram_pop; 

assign nxt_ft0 = (ram_pop_q && !ft0_valid)? {1'b1, ram_fifo_data}: ft0;
assign nxt_ft1 = (ram_pop_q && ft0_valid )? {1'b1, ram_fifo_data}: ft1;

always @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      ft0 <= 0;
      ft1 <= 0;   
   end
   else if (!sync_rst_n)
   begin
      ft0 <= 0;
      ft1 <= 0;
   end
   else if (ft_pop)
   begin
      ft0 <= nxt_ft1;
      ft1 <= 0;
   end
   else
   begin 
      ft0 <= nxt_ft0;
      ft1 <= nxt_ft1;
   end

assign {ft_valid, ft_data} = ft0;

endmodule

