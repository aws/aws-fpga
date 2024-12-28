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
parameter LESS_RST = 0;

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
reg ram_pop_q = 0;                         //Data is valid one clock after pop
reg[FIFO_WIDTH:0] ft0 = 'h0, ft1 = 'h0;            //Flow through FIFO flops
wire[FIFO_WIDTH:0] nxt_ft0, nxt_ft1;

wire ft0_valid = ft0[FIFO_WIDTH];
wire ft1_valid = ft1[FIFO_WIDTH];

assign ram_pop = !ram_fifo_empty && (!ft1_valid||ft_pop) && (!ft0_valid||!ram_pop_q||ft_pop);

   generate
      if (LESS_RST == 1) begin

         always @(posedge clk)
           ram_pop_q <= ram_pop;

      end
      else begin

         always @(negedge rst_n or posedge clk)
           if (!rst_n)
             ram_pop_q <= 0;
           else
             ram_pop_q <= ram_pop;

      end // else: !if(LESS_RST)
   endgenerate

assign nxt_ft0 = (ram_pop_q && !ft0_valid)? {1'b1, ram_fifo_data}: ft0;
assign nxt_ft1 = (ram_pop_q && ft0_valid )? {1'b1, ram_fifo_data}: ft1;

always @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      ft0[FIFO_WIDTH] <= 'h0;
      ft1[FIFO_WIDTH] <= 'h0;
   end
   else if (!sync_rst_n)
   begin
      ft0[FIFO_WIDTH] <= 'h0;
      ft1[FIFO_WIDTH] <= 'h0;
   end
   else if (ft_pop)
   begin
      ft0[FIFO_WIDTH] <= nxt_ft1[FIFO_WIDTH];
      ft1[FIFO_WIDTH] <= 'h0;
   end
   else
   begin
      ft0[FIFO_WIDTH] <= nxt_ft0[FIFO_WIDTH];
      ft1[FIFO_WIDTH] <= nxt_ft1[FIFO_WIDTH];
   end

   generate
      if (LESS_RST == 1) begin

         always @(posedge clk)
           if (ft_pop)
             begin
                ft0[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
                ft1[FIFO_WIDTH-1:0] <= ft1[FIFO_WIDTH-1:0];
             end
           else
             begin
                ft0[FIFO_WIDTH-1:0] <= nxt_ft0[FIFO_WIDTH-1:0];
                ft1[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
             end

      end // if (LESS_RST)

      else begin

         always @(negedge rst_n or posedge clk)
           if (!rst_n)
             begin
                ft0[FIFO_WIDTH-1:0] <= 'h0;
                ft1[FIFO_WIDTH-1:0] <= 'h0;
             end
           else if (!sync_rst_n)
             begin
                ft0[FIFO_WIDTH-1:0] <= 'h0;
                ft1[FIFO_WIDTH-1:0] <= 'h0;
             end
           else if (ft_pop)
             begin
                ft0[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
                ft1[FIFO_WIDTH-1:0] <= ft1[FIFO_WIDTH-1:0];
             end
           else
             begin
                ft0[FIFO_WIDTH-1:0] <= nxt_ft0[FIFO_WIDTH-1:0];
                ft1[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
             end

      end // else: !if(LESS_RST)
   endgenerate


assign {ft_valid, ft_data} = ft0;

endmodule
