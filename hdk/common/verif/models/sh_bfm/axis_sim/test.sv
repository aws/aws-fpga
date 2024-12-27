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


module test();

   import axis_bfm_pkg::*;

   parameter DATA_WIDTH  = 64;
   parameter USER_WIDTH  = 1;
   parameter KEEP_WIDTH  = (DATA_WIDTH/8);

   logic                   axis_clk;
   logic                   axis_rst_n;
   wire                    axis_valid;
   wire  [DATA_WIDTH-1:0]  axis_data;
   wire                    axis_last;
   wire  [KEEP_WIDTH-1:0]  axis_keep;
   wire  [USER_WIDTH-1:0]  axis_user;
   wire                    axis_ready;

   axis_bfm #(
      .FILE_NAME  ("master"),
      .DATA_WIDTH (DATA_WIDTH),
      .USER_WIDTH (USER_WIDTH))
   master(.*);

   axis_bfm #(
      .FILE_NAME  ("slave"),
      .IS_MASTER  (0),
      .DATA_WIDTH (DATA_WIDTH),
      .USER_WIDTH (USER_WIDTH))
   slave(.*);

   initial begin
      axis_clk = 0;
      forever #5ns axis_clk = ~axis_clk;
   end

   initial begin
      axis_rst_n = 0;
      repeat (10) @ (posedge axis_clk);
      axis_rst_n <= 1;
   end

   initial begin
      wait (axis_rst_n !== 1'b0);
      if ($test$plusargs("GEN_STIM")) begin
         int packets;
         int min_len;
         int max_len;
         if (!$value$plusargs("PACKETS=%d", packets)) begin
            packets = 500;
         end
         if (!$value$plusargs("MIN_LEN=%d", min_len)) begin
            min_len = 64;
         end
         if (!$value$plusargs("MAX_LEN=%d", max_len)) begin
            max_len = 1000;
         end
         for (int p = 0; p < packets; p++) begin
            int idle;
            idle = $urandom_range(100);
            `anp_info($sformatf("Delay=%0d", idle))
            repeat (idle) @ (posedge axis_clk);
            begin
               int size;
               bit [7:0] data[];
               bit [31:0] tmp_data;
               axis_bfm_pkt c = new();
               std::randomize(size) with {size inside {[min_len:max_len]};};
               data = new[size];
               tmp_data = p;
               for (int i = 0; i < size; i++) begin
                  if (i < size) data[i] = tmp_data[8*i[1:0]+:8];
                  if (i[1:0] == 2'b11) tmp_data++;
               end
               c.data = data;
               master.drive_packet(c.data);
            end
         end
      end
      else begin
         wait (master.stim_done == 1);
      end
      repeat (1) @ (posedge axis_clk);
      $finish;
   end

   initial begin
      $vcdpluson;
      $vcdplusmemon;
   end

   final anp_base_pkg::end_of_test();

endmodule : test
