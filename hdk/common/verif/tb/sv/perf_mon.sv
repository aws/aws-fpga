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


`timescale 1ns/100ps
module perf_mon 
(
   input clk,

   input vld,
   input[63:0] keep,
   input last,

   input int start_pkt,
   input int end_pkt,

   input enable
);

time start_time;
time end_time;
int all_pkt_count = 0;        //All packets even ones that aren't measured
int pkt_count = 0;            //Measured packets
int byte_count = 0;           //Measured bytes

bit measure_inp;

real pps;                     //Million packets/sec
real bw;                      //GB/s

wire gated_clk = clk & enable;

task reset;
begin
   pkt_count = 0;
   byte_count = 0;
   measure_inp = 0;
   all_pkt_count = 0;
end
endtask

function int num_bytes (input[63:0] in_keep);
   int nb;

   nb = 0;
   for (int i=0; i<64; i++)
      nb = nb + in_keep[i];

   num_bytes = nb;
endfunction

function void calc_perf;

   //Note do the calc in two steps so don't get truncated by int (convert int to real)
   pps = pkt_count;
   pps = (pps / (end_time - start_time)) * 1000;     //million packets/sec
   bw = byte_count;
   bw = bw / (end_time - start_time);               //GB/s
endfunction

function void print_results();
   calc_perf();
   $display ($time,,,"%m: Performance pps=%0f Mpps bw=%0f GB/s, num_pkts=%0d, num_bytes=%0d, time=%0t", pps, bw, pkt_count, byte_count, (end_time-start_time));
endfunction


always @(posedge gated_clk)
begin
   if (vld)
   begin
      if (!measure_inp && (all_pkt_count==start_pkt))
      begin
         measure_inp = 1;
         start_time = $time;
      end

      if (measure_inp)
      begin
         byte_count += num_bytes(keep);
         if (last)
            pkt_count++;
      end

      if (last)
      begin
         all_pkt_count++;
         if (all_pkt_count==end_pkt)
         begin
            measure_inp = 0;
            end_time = $time;
         end
      end
   end
end


endmodule
  

 
