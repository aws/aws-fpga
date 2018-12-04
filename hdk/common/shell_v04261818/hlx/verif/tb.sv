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

module tb();

   parameter NUM_HMC = 4;
   parameter NUM_PCIE = 1;
   parameter NUM_GTY = 4;
   parameter NUM_I2C = 2;
   parameter NUM_POWER = 4;


   
   logic [31:0]         sv_host_memory[*];
   logic                use_c_host_memory = 1'b0;
   
`ifdef VCS
initial begin
   if (!$test$plusargs("NO_WAVES")) begin
      $vcdpluson;
      $vcdplusmemon;
   end
end
`endif

`include "sh_dpi_tasks.svh"
   
   card card();
   
`ifdef TEST_NAME
   `TEST_NAME tests();
`endif
      
endmodule // tb

`ifdef XILINX_SIMULATOR
  module short(in1, in1);
    inout in1;
  endmodule
`endif

