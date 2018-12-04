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

//--------------------------------------------------------------------------------------------
// This is a RAM based FIFO that has a FT_FIFO on the output of the RAM so it looks
// like a flop FIFO to the logic doing the POP.
//--------------------------------------------------------------------------------------------

module ram_fifo_ft #(parameter WIDTH=32, parameter PTR_WIDTH=7, parameter WATERMARK= (1'b1 << PTR_WIDTH)-1, parameter PIPELINE = 1 ) (
   input clk,
   input rst_n,

   input push,
   input[WIDTH-1:0] push_data,
   output logic wmark,

   input pop,
   output logic[WIDTH-1:0] pop_data,
   output logic valid,

   output logic[PTR_WIDTH-1:0] free_entries,
   output logic oflow,

   output logic empty                  //Because of ft_fifo empty is different than !valid.  Should only be used
                                       // to see if FIFO is not 
   );

parameter[31:0] NUM_LOC = 1'b1 << PTR_WIDTH;

logic ram_pop;
logic[WIDTH-1:0] ram_rdata;

//Write pointer FIFO
logic[PTR_WIDTH:0] wptr = 0;
logic[PTR_WIDTH:0] rptr = 0;

logic[PTR_WIDTH:0] num_entries;        //Tracks entries in the combined RAM/FT FIFOs
logic[PTR_WIDTH:0] num_entries_nxt; 

wire[PTR_WIDTH:0] ptr_diff = wptr - rptr;

//This is absolutely full
wire fifo_full = (ptr_diff == NUM_LOC);

assign wmark = (ptr_diff > WATERMARK);

wire ram_fifo_empty = (ptr_diff==0);

always @(posedge clk)
begin
   if (push && !fifo_full)
      wptr <= wptr + 1;

   if (ram_pop)
      rptr <= rptr + 1;

   free_entries <= NUM_LOC - ptr_diff;
end

always_comb
begin
   if (!rst_n)
      num_entries_nxt = 0;
   else  
      num_entries_nxt = num_entries + (push & !fifo_full) - (pop & valid);
end

always @(posedge clk)
begin
   num_entries <= num_entries_nxt;
   empty <= (num_entries_nxt==0);
end


//Instantiate RAM
bram_1w1r #(.WIDTH(WIDTH), .ADDR_WIDTH(PTR_WIDTH), .DEPTH(32'h1 << PTR_WIDTH), .PIPELINE(PIPELINE)) FIFO_RAM (
   .clk(clk),
   .wea(push & !fifo_full),
   .ena(push & !fifo_full),
   .addra(wptr[PTR_WIDTH-1:0]),
   .da(push_data),

   .enb(1'b1),
   .addrb(rptr[PTR_WIDTH-1:0]),
   .qb(ram_rdata)
   );

if (PIPELINE)
//Instantiate FT_FIFO - Pipeline version
ft_fifo_p #(.FIFO_WIDTH(WIDTH)) FT_FIFO (
   .clk(clk),
   .rst_n(rst_n),

   .sync_rst_n(1'b1),

   .ram_fifo_empty(ram_fifo_empty),
   .ram_fifo_data(ram_rdata),
   .ft_pop(pop),

   .ram_pop(ram_pop),
   
   .ft_valid(valid),
   .ft_data(pop_data)
   );
else
//Instantiate FT_FIFO - Non-Pipeline version
ft_fifo #(.FIFO_WIDTH(WIDTH)) FT_FIFO (
   .clk(clk),
   .rst_n(rst_n),

   .sync_rst_n(1'b1),

   .ram_fifo_empty(ram_fifo_empty),
   .ram_fifo_data(ram_rdata),
   .ft_pop(pop),

   .ram_pop(ram_pop),
   
   .ft_valid(valid),
   .ft_data(pop_data)
   );
  
always @(negedge rst_n or posedge clk)
   if (!rst_n)
      oflow <= 0;
   else if (push && fifo_full)
      oflow <= 1;

endmodule

   
