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
   (*shreg_extract="no"*) logic [WIDTH-1:0] pipe[STAGES-1:0] = '{default:'0};
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
