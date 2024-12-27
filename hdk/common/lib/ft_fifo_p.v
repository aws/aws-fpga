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
// This is a flow-through FIFO that converts a RAM-based FIFO (2 clock
// latency on the RAM) to what looks like a flop based FIFO.  There is
// no delay between pop and getting the next data.  This sometimes simplifies
// the FIFO pop logic.
//
// Note the _p stands for pipelined RAM, which means there is a 2 clock
// latency on the RAM (registered out data)
//
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

module ft_fifo_p (
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

input clk;                             //Global clock
input rst_n;                           //Global reset

input sync_rst_n;                      //Synchronous reset

input ram_fifo_empty;                  //RAM FIFO is empty
input[FIFO_WIDTH-1:0] ram_fifo_data;   //RAM FIFO data
input ft_pop;                          //POP FT FIFO

output ram_pop;                        //Pop the RAM FIFO

output ft_valid;                       //FT FIFO is valid
output[FIFO_WIDTH-1:0] ft_data;        //FT FIFO data

////////////////////////////////////////////////////////
//Flow through FIFO to present data to arbiter
reg ram_pop_q = 'h0, ram_pop_qq = 'h0;             //Data is valid two clocks after pop
reg[FIFO_WIDTH:0] ft0 = 'h0, ft1 = 'h0, ft2 = 'h0;       //Flow through FIFO flops
wire[FIFO_WIDTH:0] nxt_ft0, nxt_ft1, nxt_ft2;

wire ft0_valid = ft0[FIFO_WIDTH];
wire ft1_valid = ft1[FIFO_WIDTH];
wire ft2_valid = ft2[FIFO_WIDTH];
reg[1:0] num_valid = 'h0;

//Qualify ft_pop with ft_valid;
wire qual_ft_pop = ft_pop & ft0_valid;

assign ram_pop = !ram_fifo_empty && sync_rst_n && ((num_valid<3) || qual_ft_pop);

//Keep track of how many valid, will use this to determine if can POP or not
always @(negedge rst_n or posedge clk)
   if (!rst_n)
      num_valid <= 0;
   else if (!sync_rst_n)
      num_valid <= 0;
   else
   begin
      case ({ram_pop, qual_ft_pop})
         2'b00, 2'b11:  num_valid <= num_valid;
         2'b01:      num_valid <= num_valid - 1;
         2'b10:      num_valid <= num_valid + 1;
      endcase
   end

   generate
      if (LESS_RST == 1)
        begin
           always @(posedge clk)
             begin
                ram_pop_q <= ram_pop;
                ram_pop_qq <= ram_pop_q;
             end
        end // if (LESS_RST)

      else begin

         always @(negedge rst_n or posedge clk)
           if (!rst_n)
             begin
                ram_pop_q <= 0;
                ram_pop_qq <= 0;
             end
           else
             begin
                ram_pop_q <= ram_pop;
                ram_pop_qq <= ram_pop_q;
             end

      end // else: !if(LESS_RST)

endgenerate

assign nxt_ft0 = (ram_pop_qq && !ft0_valid)? {1'b1, ram_fifo_data}: ft0;
assign nxt_ft1 = (ram_pop_qq && ft0_valid && !ft1_valid )? {1'b1, ram_fifo_data}: ft1;
assign nxt_ft2 = (ram_pop_qq && ft1_valid && !ft2_valid )? {1'b1, ram_fifo_data}: ft2;

   generate

      if (LESS_RST == 1)
        begin

           always @(negedge rst_n or posedge clk)
             if (!rst_n)
               begin
                  ft0[FIFO_WIDTH] <= 'h0;
                  ft1[FIFO_WIDTH] <= 'h0;
                  ft2[FIFO_WIDTH] <= 'h0;
               end
             else if (!sync_rst_n)
               begin
                  ft0[FIFO_WIDTH] <= 'h0;
                  ft1[FIFO_WIDTH] <= 'h0;
                  ft2[FIFO_WIDTH] <= 'h0;
               end
             else if (qual_ft_pop)
               begin
                  ft0[FIFO_WIDTH] <= nxt_ft1[FIFO_WIDTH];
                  ft1[FIFO_WIDTH] <= nxt_ft2[FIFO_WIDTH];
                  ft2[FIFO_WIDTH] <= 'h0;
               end
             else
               begin
                  ft0[FIFO_WIDTH] <= nxt_ft0[FIFO_WIDTH];
                  ft1[FIFO_WIDTH] <= nxt_ft1[FIFO_WIDTH];
                  ft2[FIFO_WIDTH] <= nxt_ft2[FIFO_WIDTH];
               end

           always @(posedge clk)
             if (qual_ft_pop)
               begin
                  ft0[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
                  ft1[FIFO_WIDTH-1:0] <= nxt_ft2[FIFO_WIDTH-1:0];
                  ft2[FIFO_WIDTH-1:0] <= ft2[FIFO_WIDTH-1:0];
               end
             else
               begin
                  ft0[FIFO_WIDTH-1:0] <= nxt_ft0[FIFO_WIDTH-1:0];
                  ft1[FIFO_WIDTH-1:0] <= nxt_ft1[FIFO_WIDTH-1:0];
                  ft2[FIFO_WIDTH-1:0] <= nxt_ft2[FIFO_WIDTH-1:0];
               end

        end // if (LESS_RST)

      else begin

         always @(negedge rst_n or posedge clk)
           if (!rst_n)
             begin
                ft0 <= 0;
                ft1 <= 0;
                ft2 <= 0;
             end
           else if (!sync_rst_n)
             begin
                ft0 <= 0;
                ft1 <= 0;
                ft2 <= 0;
             end
           else if (qual_ft_pop)
             begin
                ft0 <= nxt_ft1;
                ft1 <= nxt_ft2;
                ft2 <= 0;
             end
           else
             begin
                ft0 <= nxt_ft0;
                ft1 <= nxt_ft1;
                ft2 <= nxt_ft2;
             end

      end // else: !if(LESS_RST)

   endgenerate

assign {ft_valid, ft_data} = ft0;


/////////////////////////
//Simulation checks
/////////////////////////
//synopsys translate_off

`ifdef DESIGN_ERROR
`include "design_error.inc"
reg[1:0] num_valid_q;

always @(posedge clk)
begin
   if (!ft0_valid && ft_pop) begin
      design_error("FIFO underflow (pop when not valid)");
   end

   if ((num_valid==0) && (num_valid_q==3) && sync_rst_n)  begin
      design_error("NumValid overflow");
   end

   if ((num_valid==3) && (num_valid_q==0)) begin
      design_error("NumValid underflow");
   end

   num_valid_q <= num_valid;
end
`endif
//synopsys translate_on

endmodule
