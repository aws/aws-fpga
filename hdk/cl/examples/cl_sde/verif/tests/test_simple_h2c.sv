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

module test_simple_h2c();

timeunit 1ns/100ps;

`define STREAM_BFM tb.card.fpga.CL.STREAM_BFM

`include "test_base.inc"


   bit desc_type = 0;


int pkt_length = 256;         //packet length.  Currently is constant, can be variable

gen_buf_t cur_pst_pkt;        //Current packet we are posting
dma_buf_t tmp_buf;            //DMA buffer used to post packets (a descriptors worth)

dma_buf_t dbg_buf;

   // Temporraily hardcoding these values
   logic [63:0] c2h_wb_credit_limit_addr  = 64'h10000000_00000000;
   logic [63:0] c2h_wb_desc_cnt_addr = 64'h20000000_00000000;

int pkt_accum_length;            //As allocating buffers track size as use descriptors
int cur_desc_size;               //current descriptor size
int cur_desc_offset;             //descriptor offset.
bit desc_eop;                    //Descriptor EOP bit (current descriptor is last of a packet)


initial
begin
   #10;     //Make sure these default override base test.
   if (!$value$plusargs("cfg_num_pkts=%d", cfg_num_pkts))
   begin
      cfg_num_pkts = 2;
   end

   $display($time,,,"test_h2_example: test_configuration num_pkts=%0d, desc_type=%b", cfg_num_pkts, desc_type);

   tb.power_up(.clk_recipe_a(ClockRecipe::A1));

   //New some classes
   access = new();
   access.wc = cfg_desc_wc;
   access.start_mem_access_threads();

   sde = new(.access(access), .page_size(4096), .desc_type(desc_type), .verbose(verbose), .cfg_desc_wc_min(cfg_desc_wc_min), .cfg_desc_wc_max(cfg_desc_wc_max));
   sde.h2c_configure();

   sde.pc2h_min_offset = cfg_desc_offset_min;
   sde.pc2h_max_offset = cfg_desc_offset_max;
   sde.pc2h_min_length = cfg_desc_length_min;
   sde.pc2h_max_length = cfg_desc_length_max;

   //If doing SRM register mode (not back-door), need to enable INP FIFO backpressure
   if (!tb.card.fpga.CL.use_stream_bfm && !srm_rx_backdoor)
      tb.poke_ocl(.addr(64'h180), .data(32'h0000_0010));

   //If LB mode, configure SRM, and enable the C2H stuff
   if (cfg_srm_lb_mode)
   begin
      enable_c2h_auto_check = 1;
      sde.c2h_configure();
      tb.poke_ocl(.addr(64'h180), .data(32'h0000_0001));
      fork : FORK_C2H_SB_THREAD
         sde.process_c2h_wb_thread;
         sde.post_c2h_desc_thread;
      join_none
   end
   else
      //Enable the H2C auto checking
      enable_h2c_auto_check = 1;

   //Post the packets (cfg_num_pkts)
   for (int i=0; i<cfg_num_pkts; i++)
   begin

      //Create a new packet to post, and initialize the data.  This is just a generic buffer that represents the packet.
      cur_pst_pkt = new();
      cur_pst_pkt.init_inc((i<<28 | i<<24 | i<<20 | i<<16), pkt_length );

      $display($time,,,">>>Post Packet start_data=0x%x", (i<<28 | i<<24 | i<<20 | i<<16));

      //If loopback, packet will get back to Host
      if (cfg_srm_lb_mode)
         exp_c2h_pkt_q.push_back(cur_pst_pkt);
      else
         //Push the packet onto the expect queue for end of sim checking
         exp_h2c_pkt_q.push_back(cur_pst_pkt);

      //Create descriptor(s) for the packet
      desc_eop = 0;
      pkt_accum_length = 0;
      while(!desc_eop)
      begin
         //Descriptor offset
         cur_desc_offset = 7;

         //Make descriptor size the page size for simplicity.  This is not required, can change this and make variable
         //cur_desc_size = sde.page_size;
         cur_desc_size = 64;

         //Make sure desc offset/size is valid, if not reset to offset=0, size=page_size
         if ((cur_desc_size + cur_desc_offset) > sde.page_size)
         begin
            cur_desc_size = sde.page_size;
            cur_desc_offset = 0;
         end

         //If packet doesn't need entire descriptor size make the adjustment
         if ((pkt_accum_length + cur_desc_size) >= pkt_length)
         begin
            cur_desc_size = pkt_length - pkt_accum_length;
            desc_eop = 1;
         end

         //Allocate a buffer for the descriptor in host memory;
         tmp_buf = new(.access(access), .addr(sde.alloc_page()), .buf_size(sde.page_size));

         //Initialize the buffer with 0xff up to the offset -- this is so don't get X's in the sim
         for (int bi=0; bi<cur_desc_offset; bi++)
            tmp_buf.data.push_back(8'hff);

         //Initialize the buffer with the right amount of packet data
         for (int bi=0; bi<cur_desc_size; bi++)
            tmp_buf.data.push_back(cur_pst_pkt.data[pkt_accum_length + bi]);

         //Fill rest of page with 0xff's so don't get X's in SIM
         for (int bi=0; bi<sde.page_size - cur_desc_offset - cur_desc_size; bi++)
            tmp_buf.data.push_back(8'hff);

         //Write the buffer to host memory
         tmp_buf.write_buf_host();

         //Now modify the buffer address to the offset address (didn't do this before because the write_buf_to_host assumes DW aligned)
         // Can do this because from here the address is only used for the descriptor.
         tmp_buf.addr = tmp_buf.addr + cur_desc_offset;
         tmp_buf.buf_size = cur_desc_size;

         //Post the descriptor
         sde.post_h2c_desc(.post_buf(tmp_buf), .eop(desc_eop));
         $display($time,,,">>>   Desc Addr=0x%x, Length=0x%x, EOP=0x%x", tmp_buf.addr, cur_desc_size, desc_eop);

         pkt_accum_length += cur_desc_size;
      end

      //Simplification just do a single doorbell per packet.  For full featured test need to do doorbell at any time and
      // re-claim writeback entries (writeback entries are not as important for H2C)
      sde.h2c_doorbell();

      $display("End of Loop i=%0d", i);
   end

   //Wait for all the packets to be received
   fork
   begin
      if (cfg_srm_lb_mode)
         wait (c2h_pkts_checked == cfg_num_pkts);
      else
         wait (h2c_pkts_checked == cfg_num_pkts);
   end
   begin
      dly_clks(1000 * cfg_num_pkts);
      if (cfg_srm_lb_mode)
         $display($time,,,"test_simple_h2c: ***ERROR*** waiting for RX Stream packets timeout (loopback to is C2H), num_received=0x%x, expected=0x%x", c2h_pkts_checked, cfg_num_pkts);
      else
         $display($time,,,"test_simple_h2c: ***ERROR*** waiting for RX Stream packets timeout, num_received=0x%x, expected=0x%x", h2c_pkts_checked, cfg_num_pkts);
      $finish;
   end
   join_any
   disable fork;

   end_sim();

end

endmodule









