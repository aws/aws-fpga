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

//----------------------------------------------------
// This is a single port BRAM
//----------------------------------------------------
module bram_1w1r #(parameter WIDTH=32, parameter ADDR_WIDTH=4, parameter DEPTH=16, parameter PIPELINE=0, parameter MEMORY_TYPE = "auto") 
(
   input clk,
   input wea,
   input ena,
   input[ADDR_WIDTH-1:0] addra,
   input[WIDTH-1:0] da,

   input enb,
   input[ADDR_WIDTH-1:0] addrb,
   output logic[WIDTH-1:0] qb


   );

`ifndef NO_XILINX_XPM_RAM 

   xpm_memory_sdpram # (
   // Common module parameters
   .MEMORY_SIZE (WIDTH*DEPTH), //positive integer
   .MEMORY_PRIMITIVE (MEMORY_TYPE), //string; "auto", "distributed", "block" or "ultra";
   .CLOCKING_MODE ("common_clock"), //string; "common_clock", "independent_clock"
   .MEMORY_INIT_FILE ("none"), //string; "none" or "<filename>.mem"
   .MEMORY_INIT_PARAM ("" ), //string;
   .USE_MEM_INIT (1), //integer; 0,1
   .WAKEUP_TIME ("disable_sleep"), //string; "disable_sleep" or "use_sleep_pin"
   .MESSAGE_CONTROL (0), //integer; 0,1
   // Port A module parameters
   .WRITE_DATA_WIDTH_A (WIDTH), //positive integer
   .BYTE_WRITE_WIDTH_A (WIDTH), //integer; 8, 9, or WRITE_DATA_WIDTH_A value
   .ADDR_WIDTH_A (ADDR_WIDTH), //positive integer
   // Port B module parameters
   .READ_DATA_WIDTH_B (WIDTH), //positive integer
   .ADDR_WIDTH_B (ADDR_WIDTH), //positive integer
   .READ_RESET_VALUE_B ("0"), //vector of READ_DATA_WIDTH_B bits
   .READ_LATENCY_B (PIPELINE+1), //non-negative integer
   .WRITE_MODE_B ("read_first") //string; "write_first", "read_first", "no_change"
   ) xpm_memory_sdpram_inst (
   // Common module ports
   .sleep (1'b0),
   // Port A module ports
   .clka (clk),
   .ena (ena),
   .wea (wea),
   .addra (addra),
   .dina (da),
   .injectsbiterra (1'b0), //do not change
   .injectdbiterra (1'b0), //do not change
   // Port B module ports
   .clkb (clk),
   .rstb (1'b0),
   .enb (enb),
   .regceb (1'b1),
   .addrb (addrb),
   .doutb (qb),
   .sbiterrb (), //do not change
   .dbiterrb () //do not change
   );
   // End of xpm_memory_tdpram instance declaration

`else


  bit[WIDTH-1:0] ram[DEPTH-1:0];

  bit[WIDTH-1:0] rddata_b, rddata_b_q;

  always_ff @(posedge clk)
     if (ena && wea)
     begin
        ram[addra] <= da;
     end

  always_ff @(posedge clk)
     rddata_b_q <= rddata_b;

  always_ff @(posedge clk)
     if (enb)
     begin
        rddata_b <= ram[addrb];
     end

  assign qb = (PIPELINE)? rddata_b_q: rddata_b;

`endif

endmodule  
