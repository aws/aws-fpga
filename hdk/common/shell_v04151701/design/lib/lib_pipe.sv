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

//simple pipeline

//WIDTH is the width of the DATA
//STAGES is the number of stages (flops in the pipeline)
module lib_pipe #(parameter WIDTH=8, parameter STAGES=1) (
   input clk,
   input rst_n,

   input[WIDTH-1:0] in_bus,

   output [WIDTH-1:0] out_bus
   );

//Note the shreg_extract=no directs Xilinx to not infer shift registers which
// defeats using this as a pipeline


`ifdef FPGA_LESS_RST
   (*shreg_extract="no"*) logic [WIDTH-1:0] pipe[STAGES-1:0] = '{default:'0};
`else
   (*shreg_extract="no"*) logic [WIDTH-1:0] pipe[STAGES-1:0];
`endif

//(*srl_style="register"*) logic [WIDTH-1:0] pipe [STAGES-1:0];
// logic [WIDTH-1:0] pipe [STAGES-1:0];
   
 integer i;

`ifdef FPGA_LESS_RST
 always @(posedge clk)
`else
 always @(negedge rst_n or posedge clk)
    if (!rst_n)
    begin
       for (i=0; i<STAGES; i=i+1)
          pipe[i] <= 0;
    end
    else
`endif
    begin
       pipe[0] <= in_bus;
 
       if (STAGES>1)
       begin
          for (i=1; i<STAGES; i=i+1)
             pipe[i] <= pipe[i-1];
       end
    end
 
 assign out_bus = pipe[STAGES-1];

endmodule
   
