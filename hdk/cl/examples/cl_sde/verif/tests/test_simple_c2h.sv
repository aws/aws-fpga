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

module test_simple_c2h();

timeunit 1ns/100ps;

`define STREAM_BFM tb.card.fpga.CL.STREAM_BFM

`include "test_base.inc"


dma_buf_t tmp_buf;            //Temporary buffer


int buf_size = 4096;
bit desc_type = 0;

bit desc_wc = 0;

logic[31:0] rdata;

initial


begin
   logic[31:0] tmp_data;
   gen_buf_t tmp_pkt_buf;        //Temporary packet buffer

   #10;     //Make sure these default override base test.
   if (!$value$plusargs("cfg_num_pkts=%d", cfg_num_pkts))
   begin
      cfg_num_pkts = 2;
   end

   if (!$value$plusargs("desc_type=%b", desc_type))
   begin
      desc_type = 0;
   end

   if (!$value$plusargs("desc_wc=%d", desc_wc))
     desc_wc = 1;

   $display($time,,,"sd3_c2h_example: test_configuration cfg_num_pkts=%d, desc_type=%d", cfg_num_pkts, desc_type);

   tb.power_up(.clk_recipe_a(ClockRecipe::A1));

   access = new();
   access.wc = desc_wc;
   access.start_mem_access_threads();

   sde = new(.access(access), .page_size(4096), .desc_type(desc_type), .verbose(verbose), .cfg_desc_wc_min(cfg_desc_wc_min), .cfg_desc_wc_max(cfg_desc_wc_max));
   enable_c2h_auto_check = 1;

   sde.c2h_configure();

   //Kick off the C2H WB thread (assembles C2H packets received by the host
   fork : FORK_C2H_SB_THREAD
      sde.process_c2h_wb_thread;
   join_none

   //Post 64 descriptors to begin.
//   for (int i=0; i<64; i++)
   for (int i=0; i<8; i++)
   begin
      //Full size descriptor tmp_buf = new(.access(access), .addr(sde.alloc_page()), .buf_size(buf_size));
      tmp_buf = new(.access(access), .addr(sde.alloc_page()), .buf_size(64));
      // unaligned address//       tmp_buf = new(.access(access), .addr(sde.alloc_page() + 64'h10), .buf_size(buf_size));
      sde.post_c2h_desc(.post_buf(tmp_buf));
   end
   sde.c2h_doorbell();

   //Send packets of complete buffer size
   if (tb.card.fpga.CL.use_stream_bfm==0)
     begin
        // Disable loop back mode
        tb.poke_ocl(.addr('h180), .data(32'h0));

      //Initialize seed
      tb.poke_ocl(.addr('h04), .data(32'haaaa_0000));

      //Set the number of packets
      tb.poke_ocl(.addr('h24), .data(cfg_num_pkts-1));

      //Set the pkt length
      tb.poke_ocl(.addr('h08), .data(cfg_pkt_length_min/64));

      //Start the packets, set the no_scramble, num_pkts_en
      tb.poke_ocl(.addr('h00), .data('h29));

      //Put the expected packets on the expect_q
      tmp_data = 32'haaaa_0000;
      for (int i=0; i<cfg_num_pkts; i++)
      begin
         tmp_pkt_buf = new();
         for (int j=0; j<cfg_pkt_length_min/4; j++)
         begin
            for (int b=0; b<4; b++)
               tmp_pkt_buf.data.push_back(tmp_data[8*b+:8]);

            if (j[3:0]=='hf)
               tmp_data++;
         end
         exp_c2h_pkt_q.push_back(tmp_pkt_buf);
      end
   end
   else
   begin
      fork: FORK_SEND_PKTS
      begin
         for (int i=0; i<cfg_num_pkts; i++)
         begin
            //`STREAM_BFM.stream_tx(.start_data(i<<28 | i<<24 | i<<20 | i<<16), .length(buf_size/64));

            //if (i == 0)
            //  `STREAM_BFM.stream_tx(.start_data(i<<28 | i<<24 | i<<20 | i<<16), .length(4), .last_keep(64'h00000000_000fffff));
            //else
            //  `STREAM_BFM.stream_tx(.start_data(i<<28 | i<<24 | i<<20 | i<<16), .length(4), .last_keep(64'h003fffff_ffffffff));

            //`STREAM_BFM.stream_tx(.start_data(i<<28 | i<<24 | i<<20 | i<<16), .length(4));

            `STREAM_BFM.stream_tx(.start_data(i<<28 | i<<24 | i<<20 | i<<16), .length(128), .user(64'h4444_3333_2222_0000 + i));
            @(`STREAM_BFM.tx_pkt_done);
         end
      end
      begin
         dly_clks(1000 * cfg_num_pkts);
         $display($time,,,"test_simple_c2h: ***ERROR*** waiting for Stream packets timeout");
         $finish;
      end
      join_any
      disable FORK_SEND_PKTS;
   end


   //Wait for all packets to be received (using base C2H self checking)
   fork: FORK_WAIT_PKTS
   begin
      wait (c2h_pkts_checked == cfg_num_pkts);
   end
   begin
      dly_clks(100 * cfg_num_pkts);
      $display($time,,,"test_simple_c2h: ***ERROR*** waiting for C2H packets in Host timeout, num_received=0x%x, expected=0x%x", c2h_pkts_checked, cfg_num_pkts);
      $finish;
   end
   join_any
   disable FORK_WAIT_PKTS;


   end_sim();

end



endmodule





