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


`define SRM_PATH tb.card.fpga.CL.CL_SDE_SRM
`define CL_PATH tb.card.fpga.CL
import tb_type_defines_pkg::*;

`define STREAM_BFM `CL_PATH.STREAM_BFM


//This has some base functions/tasks for tests
bit verbose = 0;

bit enable_c2h_auto_check = 0;         //Enable C2H checking
int c2h_err_cnt = 0;                   //Number of C2H errored packets
int c2h_pkts_checked = 0;              //Number of C2H packets that has been received by the host and checked
int c2h_pkts_sent = 0;                 //Number of C2H packets that have been sent by StreamBFM

gen_buf_t exp_c2h_pkt_q[$];
logic[63:0] exp_c2h_pkt_user_q[$];

gen_buf_t cur_c2h_host_pkt;
logic[63:0] cur_c2h_host_pkt_user;
gen_buf_t cur_c2h_stream_pkt;
logic[63:0] cur_c2h_stream_pkt_user;

bit enable_h2c_auto_check = 0;         //Enable H2C checking
int h2c_err_cnt = 0;
int h2c_pkts_checked = 0;

gen_buf_t exp_h2c_pkt_q[$];
logic[63:0] exp_h2c_pkt_user_q[$];

int global_timeout = 1000000;
int watchdog_timeout = 10000;

bit global_timeout_en = 1;
bit watchdog_timeout_en = 1;

int gl_to_count;

bit srm_rx_backdoor = 0;               //Use backdoor to get packets received from SRM block (H2C)

bit cfg_srm_lb_mode;

access_t access;              //Access class to provide capability to move between testbenches
sde_dma_t sde;                //SDE management class

//Random configuration
logic[31:0] cfg_num_pkts;     //Number of packets in the simulation

int cfg_page_size;

int cfg_pkt_length_min;
int cfg_pkt_length_max;

int cfg_desc_offset_min;
int cfg_desc_offset_max;

int cfg_desc_length_min;
int cfg_desc_length_max;

int cfg_pkt_dly_min;          //Min delay between packets
int cfg_pkt_dly_max;          //Max delay between packets

int cfg_desc_dly_min;         //Min delay between descriptor posts
int cfg_desc_dly_max;         //Max delay between descriptor posts

int cfg_max_num_desc;         //Max number of outstanding descritpors

int cfg_desc_before_db_min;   //Min number of descriptors before hit the doorbell
int cfg_desc_before_db_max;   //Max number of descriptors before hit the doorbell

int cfg_desc_type = 0;       //Descriptor size (number of bytes in descriptor)

bit cfg_desc_wc = 1;

int cfg_desc_wc_min = 64;
int cfg_desc_wc_max = 64;

int cfg_perf_h2c_start_pkt;
int cfg_perf_h2c_end_pkt;
int cfg_perf_c2h_start_pkt;
int cfg_perf_c2h_end_pkt;

int cfg_err_cnt_finish = 1;      //How many errors before kill simulatino

bit cfg_perf_mon;

logic [5:0] cfg_wc_cnt = 6'd0;
logic cfg_md_wr_ptr_wc_en = 1; 
logic cfg_pkt_cnt_wc_en = 1; 
logic cfg_desc_cnt_wc_en = 1; 
logic cfg_desc_cdt_wc_en = 1; 
logic [3:0] cfg_wc_to_cnt = 4'd0; 
logic [19:0] cfg_wc_to_rsln = 20'd0;

logic [3:0] cfg_wc_cnt_min = 6'd0;
logic [3:0] cfg_wc_cnt_max = 6'd31;

logic [3:0] cfg_wc_to_cnt_min = 4'd0;
logic [3:0] cfg_wc_to_cnt_max = 4'd15;

logic [19:0] cfg_wc_to_rsln_min = 20'd1000;
logic [19:0] cfg_wc_to_rsln_max = 20'd2000;

logic [15:0] cfg_c2h_num_md_min = 16'd128;
logic [15:0] cfg_c2h_num_md_max = 16'd256;
logic [15:0] cfg_c2h_num_md = 16'd128;

logic [15:0] cfg_c2h_ring_offset_min = 16'd0;
logic [15:0] cfg_c2h_ring_offset_max = 16'd256;
logic [15:0] cfg_c2h_ring_offset = 16'd128;

//--------------------------------------
// Create a clock for delays
//--------------------------------------

logic tb_clk = 1;
always #2 tb_clk = ~tb_clk;

task automatic dly_clks(input int clks);
   repeat(clks)
      @(posedge tb_clk);
endtask

//------------------------------------------------------
// C2H self checking
//------------------------------------------------------

//Record all the packets transitted from Stream BFM (this is the expect queue, all of these packets should be sent to Host)
always @(`STREAM_BFM.tx_pkt_done)
begin
   exp_c2h_pkt_q.push_back(`STREAM_BFM.tx_pkt_done_pkt);
   exp_c2h_pkt_user_q.push_back(`STREAM_BFM.tx_pkt_done_user);
   c2h_pkts_sent++;
end


//When get a Host C2H packet, pop off the expect queue and do compare
always
begin
   wait (enable_c2h_auto_check)
   begin
      wait (sde.c2h_pkt_rx_q.size() != 0);

      cur_c2h_host_pkt = sde.c2h_pkt_rx_q.pop_front();
      cur_c2h_host_pkt_user = sde.c2h_pkt_rq_user_q.pop_front();
      c2h_pkts_checked++;

      if (exp_c2h_pkt_q.size()==0)
      begin
         $display($time,,,"TB_C2H_AutoCheck: ***FATAL*** Got a C2H packet in host, but expect queue is empty");
      end 
      else
      begin
         cur_c2h_stream_pkt = exp_c2h_pkt_q.pop_front();
         cur_c2h_stream_pkt_user = exp_c2h_pkt_user_q.pop_front();
         $display($time,,,"C2H Auto Check, RXPkt:Length=0x%0x, Data=0x%0x, ExpQ:Length=0x%0x, ExpQ:Data=0x%0x, ExpQ:User=0x%x", cur_c2h_host_pkt.data.size(), {cur_c2h_host_pkt.data[3], cur_c2h_host_pkt.data[2], cur_c2h_host_pkt.data[1], cur_c2h_host_pkt.data[0]},
                                                                                                            cur_c2h_stream_pkt.data.size(), {cur_c2h_stream_pkt.data[3], cur_c2h_stream_pkt.data[2], cur_c2h_stream_pkt.data[1], cur_c2h_stream_pkt.data[0]}, cur_c2h_host_pkt_user);
         c2h_err_cnt += cur_c2h_host_pkt.compare(cur_c2h_stream_pkt); 

         if ((cfg_desc_type==0) && (cur_c2h_stream_pkt_user != cur_c2h_host_pkt_user))
         begin
            c2h_err_cnt++;
            $display($time,,,"C2H Auto Check: ***ERROR*** user mismatch.  Expected=0x%x, Actual=0x%x", cur_c2h_stream_pkt_user, cur_c2h_host_pkt_user);
         end
         //else if (verbose)
         //begin
         //   $display($time,,,"C2H Auto Check: user OK.  Expected=0x%x, Actual=0x%x", cur_c2h_stream_pkt_user, cur_c2h_host_pkt_user);
         //end
            
      end
   end
end

// End C2H self checking
//--------------------------------

//---------------------------------
// H2C self checking
//---------------------------------

//Auto checking of H2C packets
always 
begin:h2c_auto_check
   logic[31:0] rdata;
   logic[15:0] srm_inp_wr_ptr = 0;
   logic[15:0] srm_inp_rd_ptr = 0;

   logic[511:0] ins_data;
   logic[63:0] ins_keep;
   logic[63:0] ins_user;
   logic ins_last;
   bit got_init_base_pkt = 0;

   gen_buf_t base_cur_rx_pkt;
   logic[63:0] base_cur_rx_user;

   logic[63:0] exp_rx_user;

      

   logic[(1 + 64 + 64 + 512)-1:0] ins_fifo_data;

   wait (enable_h2c_auto_check)
   begin
      //Stream BFM
      if (`CL_PATH.use_stream_bfm)
      begin
         wait (`STREAM_BFM.rx_pkt_q.size() != 0);
         base_cur_rx_pkt = `STREAM_BFM.rx_pkt_q.pop_front();
         base_cur_rx_user = `STREAM_BFM.rx_pkt_user_q.pop_front();

         $display($time,,,"TB_H2C_AutoCheck: Compare H2C packet[%0d]", h2c_pkts_checked);
         h2c_pkts_checked++;

         if (exp_h2c_pkt_q.size()==0)
         begin
            $display($time,,,"TB_H2C_AutoCheck: ***FATAL*** Got H2C packet in StreamBFM, but expect queue is empty");
         end
         else
         begin
            h2c_err_cnt =+ base_cur_rx_pkt.compare(exp_h2c_pkt_q.pop_front);
            exp_rx_user =  exp_h2c_pkt_user_q.pop_front();
            if ((cfg_desc_type==0) && (base_cur_rx_user != exp_rx_user))
            begin
               $display($time,,,"TB_H2C_AutoCheck: ***ERROR*** user miscompare, expected=0x%x, actual=0x%x", exp_rx_user, base_cur_rx_user);
               h2c_err_cnt++;
            end
         end
      end
      //RTL SRM
      else
      begin
         if (!got_init_base_pkt)
         begin
            base_cur_rx_pkt = new();
            got_init_base_pkt = 1;
         end

         if (srm_rx_backdoor)
         begin
            //Some arbitrary delay to do the polling
            dly_clks(10);
            srm_inp_wr_ptr = `SRM_PATH.inp_wr_ptr;
            //Note backdoor does not update the read pointer in the design, so have to be in non-backpressure mode
            //srm_inp_rd_ptr = `SRM_PATH.inp_rd_ptr;
         end
         else
         begin
            sde.access.peek_ocl(.addr(64'h8c), .data({srm_inp_wr_ptr, srm_inp_rd_ptr}));
            $display($time,,,"TB_H2C_AutoCheck: SRM Poll wr_ptr=0x%0x, rd_ptr=0x%0x", srm_inp_wr_ptr, srm_inp_rd_ptr);
         end

         while (srm_inp_rd_ptr < srm_inp_wr_ptr)
         begin
            if (srm_rx_backdoor)
               ins_fifo_data = `SRM_PATH.INP_FIFO_RAM.xpm_memory_sdpram_inst.xpm_memory_base_inst.mem[srm_inp_rd_ptr];
            else
            begin
               for (int i=0; i<21; i++)
                  sde.access.peek_ocl(.addr(64'h90 + (i*4)), .data(ins_fifo_data[32*i+:32]));
            end

            {ins_last, ins_user, ins_keep, ins_data} = ins_fifo_data;

            for (int i=0; i<64; i++)
            begin
               if (ins_keep[i])
                  base_cur_rx_pkt.data.push_back(ins_data[8*i+:8]);
            end

            //If end of packet, do packet check
            if (ins_last)
            begin
               $display($time,,,"TB_H2C_AutoCheck: Compare H2C packet[%0d]", h2c_pkts_checked);
               h2c_pkts_checked++;

               if (exp_h2c_pkt_q.size()==0)
               begin
                  $display($time,,,"TB_H2C_AutoCheck: ***FATAL*** Got H2C packet in SRM, but expect queue is empty");
               end
               else
               begin
                  h2c_err_cnt =+ base_cur_rx_pkt.compare(exp_h2c_pkt_q.pop_front);
               end

               //Clear out packet data for next packet
               base_cur_rx_pkt.data = {};
            end

            if (srm_rx_backdoor)
            begin
               srm_inp_rd_ptr = (srm_inp_rd_ptr + 1) & ((1 << `SRM_PATH.INP_PTR_WIDTH) - 1);
            end
         end
      end      
   end
end

// End H2C self checking
//----------------------------
         
//-----------------------------------------------------------------------------------------------
// Random descriptor class, this will randomize offset/length of descriptor based on 
// test setup.
//-----------------------------------------------------------------------------------------------
class rnd_desc;
   rand int offset;
   rand int length;
   rand bit eop;              //Note EOP is not really randomized, it is computed based on current length, pkt_length, accum_length

   int min_offset;
   int max_offset;
   int min_length;
   int max_length;
   
   int page_size;
   int pkt_length;

   int accum_length;

   constraint default_c { 
                           offset + length <= page_size;
                           offset + length <= pkt_length - accum_length;
                           offset >= min_offset;
                           offset <= max_offset;
                           if ((pkt_length - accum_length) < min_length)
                              length == (pkt_length - accum_length);
                           else
                              length >= min_length;
                           length <= max_length;

                           eop == ((accum_length + length) == pkt_length);
                        }
                        

   function new (int min_offset=cfg_desc_offset_min, int max_offset=cfg_desc_offset_max, int min_length=cfg_desc_length_min, int max_length=cfg_desc_length_max, int page_size=cfg_page_size, int pkt_length=0, int accum_length=0);

      this.min_offset = min_offset;
      this.max_offset = max_offset;
      this.min_length = min_length;
      this.max_length = max_length;
      this.page_size = page_size;
      this.pkt_length = pkt_length;
      this.accum_length = accum_length;
   endfunction

   function display;
      $display($time,,,"RND_DESC: offset=%0d, length=%0d, page_size=%0d, pkt_length=%0d, accum_length=%0d, eop=%0d", this.offset, this.length, this.page_size, this.pkt_length, this.accum_length, this.eop);
   endfunction

endclass

//----------------------------------------
// Thread to send H2C packets 
//----------------------------------------
task post_h2c_desc_thread;

int desc_cons;
int desc_limit;
int desc_limit_old;
int pkt_cnt;
int desc_cnt;

int credit_diff;

int accum_length;

int cur_pkt_length;

int pkt_count;
int desc_count;

rnd_desc rd;

gen_buf_t cur_pkt_buf;           //Buffer of current packet data
logic[63:0] cur_pkt_user;        //User bits of current packet

dma_buf_t desc_buf;              //Buffer for descriptor in host memory

int tmp;

int desc_pending;                //Descriptors pending (doorbell tracking)

begin

   desc_cons = 0;
   desc_limit = 64;

   pkt_count = 0;

   desc_pending = 0;

   rd = new();

   //Repeat for number of packets in test
   while (pkt_count < cfg_num_pkts)
   begin
      //Get packet length
      cur_pkt_length = $urandom_range(cfg_pkt_length_max, cfg_pkt_length_min);

      //Create a generic buffer to create the packet data
      cur_pkt_buf = new();
      cur_pkt_buf.init_inc((pkt_count<<16), cur_pkt_length);
      cur_pkt_user[31:0] = $urandom;
      cur_pkt_user[63:32] = $urandom;

      //If loopback, packet will get back to Host
      if (cfg_srm_lb_mode)
      begin
         exp_c2h_pkt_q.push_back(cur_pkt_buf);
         exp_c2h_pkt_user_q.push_back(cur_pkt_user);
         if (verbose)
            $display($time,,,"Pushing onto EXP_C2H_Q length=0x%0x, data=0x%x, user=0x%x", cur_pkt_buf.data.size(), {cur_pkt_buf.data[3], cur_pkt_buf.data[2], cur_pkt_buf.data[1], cur_pkt_buf.data[0]}, cur_pkt_user);
      end
      else
      begin
         //Push the packet onto the expect queue for end of sim checking
         exp_h2c_pkt_q.push_back(cur_pkt_buf);
         exp_h2c_pkt_user_q.push_back(cur_pkt_user);
      end

      $display($time,,,"TX_PKT[%0d]: Length=0x%0x (%0d), User=0x%x", pkt_count, cur_pkt_length, cur_pkt_length, cur_pkt_user);
    
      desc_count = 0;
      accum_length = 0;

      rd.pkt_length = cur_pkt_length;
      rd.accum_length = accum_length;

      //Create descriptors for the packet.  Accum length of the descriptors until satisfy packet length
      while (accum_length<cur_pkt_length) 
      begin
         //See if we have descriptor credits
         credit_diff = desc_limit - desc_cons;

         //Poll for descriptor credits.  Make sure have enough based on max number of desc before db
         //FIXME -- For simplicity waiting for enough credits to post max num desc.  In reality could
         //       not check here, and when about to write to SDE, only write as much as have credits for.
         while (credit_diff < cfg_desc_before_db_max)
         begin
            #(sde.wb_poll_interval * 1ns);
            desc_limit_old = desc_limit;
            desc_limit = sde.access.read_host_dw(sde.cfg_h2c_cdt_limit_addr);
            credit_diff = desc_limit - desc_cons;

            //If descriptor limit has changed, print out the value
            if (desc_limit != desc_limit_old)
            begin
               pkt_cnt = sde.access.read_host_dw(sde.cfg_h2c_wb_pkt_cnt_addr);
               desc_cnt = sde.access.read_host_dw(sde.cfg_h2c_wb_desc_cnt_addr);
               if (verbose)
                  $display($time,,,"Poll H2C Status: desc_cons=0x%0x, desc_limit=0x%0x, pkt_cnt=0x%0x, desc_cnt=0x%0x", desc_cons, desc_limit, pkt_cnt, desc_cnt);
            end
            //$display($time,,,"DBG: cons=%0d, limit=%0d, diff=%0d, max=%0d, calc=%0d", desc_cons, desc_limit, credit_diff, cfg_max_num_desc, ((32'h64 - credit_diff) >= cfg_max_num_desc));
         end

         //Randomize descritpor paramters (offset/length)
         rd.randomize(); 
         if (verbose)
            rd.display();

         //Allocate a buffer for the descriptor in host memory
         desc_buf  = new(.access(access), .addr(sde.alloc_page()), .buf_size(sde.page_size));

         //Initialize the buffer with 0xff up to the offset -- this is so don't get X's in the sim
         for (int bi=0; bi<rd.offset; bi++)
            desc_buf.data.push_back(8'hff);

         //Initialize the buffer with the right amount of packet data
         for (int bi=0; bi<rd.length; bi++)
            desc_buf.data.push_back(cur_pkt_buf.data[accum_length + bi]);

         //Fill rest of page with 0xff's so don't get X's in SIM
         for (int bi=0; bi<sde.page_size - rd.offset - rd.length; bi++)
            desc_buf.data.push_back(8'hff);

         //Write the buffer to host memory
         desc_buf.write_buf_host();
         //desc_buf.display();

         //Now modify the buffer address to the offset address (didn't do this before because the write_buf_to_host assumes DW aligned)
         // Can do this because from here the address is only used for the descriptor.
         desc_buf.addr = desc_buf.addr + rd.offset;
         desc_buf.buf_size = rd.length;

         //Post the descriptor
         sde.post_h2c_desc(.post_buf(desc_buf), .eop(rd.eop), .user(cur_pkt_user));
         if (verbose)
            $display($time,,,"   TX_PKT[%0d].DESC[%0d] : Addr=0x%x, length=%0d, eop=%0d, user=0x%x", pkt_count, desc_count, desc_buf.addr, rd.length, rd.eop, cur_pkt_user);

         //Update all the tracking stuff
         accum_length += rd.length;
         desc_count++;
         rd.accum_length = accum_length;
         desc_pending++;

         tmp = $urandom_range(cfg_desc_before_db_max, cfg_desc_before_db_min);
         if (desc_pending >= tmp)
         begin
            sde.h2c_doorbell();
            desc_cons += desc_pending;
            desc_pending = 0;
         end

         //Random delay between descriptor posts
         tmp = $urandom_range(cfg_desc_dly_max, cfg_desc_dly_min);
         #(tmp * 1ns);
      end

      pkt_count++;

       
      //Random delay between packets
      tmp = $urandom_range(cfg_pkt_dly_max, cfg_pkt_dly_min);
      #(tmp * 1ns);
   end   //while (pkt_count < cfg_num_pkts)

   //If finished packets give one more doorbell in case still have desc pending (last packet happened to randomly not do doorbell)
   if (desc_pending > 0)
   begin
      sde.h2c_doorbell();
   end
end
endtask


//------------------------
// Global timeout
//------------------------
initial
begin
   gl_to_count = 0;
      
   while (gl_to_count < global_timeout)
   begin
      @(posedge tb_clk);
      gl_to_count++;
      
      if (global_timeout_en == 0)
      begin
         while (global_timeout_en == 0)
            @(posedge tb_clk);
         gl_to_count = 0;
      end
   end
   $display($time,,,"test_base: ***ERROR*** Global Timeout");
   $finish;
end

int wdog_count;
initial
begin
   wdog_count = 0;

   while (wdog_count < watchdog_timeout)
   begin
      @(posedge `CL_PATH.clk_main_a0);
      if (  (`CL_PATH.cl_sh_pcim_awvalid & `CL_PATH.sh_cl_pcim_arready) || 
            (`CL_PATH.cl_sh_pcim_arvalid & `CL_PATH.sh_cl_pcim_arready) || 
            (`CL_PATH.sh_cl_dma_pcis_awvalid & `CL_PATH.cl_sh_dma_pcis_awready) ||
            (`CL_PATH.sh_cl_dma_pcis_arvalid & `CL_PATH.cl_sh_dma_pcis_arready) ||
            (`CL_PATH.c2h_axis_valid & `CL_PATH.c2h_axis_ready) ||
            (`CL_PATH.h2c_axis_valid & `CL_PATH.h2c_axis_ready)
         )

         wdog_count = 0;
      else
         wdog_count++;

      if (watchdog_timeout_en == 0)
      begin
         while(watchdog_timeout_en == 0)
         begin
            @(posedge `CL_PATH.clk_main_a0);
         end
         wdog_count = 0;
      end
   end
   $display($time,,,"test_base: ***ERROR*** WDOG Timeout wdog_timeout=%0d clocks, c2h_pkts_checked=%0d, h2c_pkts_checked=%0d, cfg_num_pkts=%0d", watchdog_timeout, c2h_pkts_checked, h2c_pkts_checked, cfg_num_pkts);
   $finish;
end
   
// End global timeout
//----------------------------

//------------------------------------------------
// Global initial stuff -- test parameters
//------------------------------------------------
int seed;
initial
begin

   $timeformat(-9, 0, "ns", 10);

   if ($test$plusargs("verbose"))
   begin
      verbose = 1;
      $display($time,,,"test_base: *** VERBOSE MODE ON ***");
   end

   if ($test$plusargs("srm_rx_backdoor"))
   begin
      srm_rx_backdoor = 1;
      $display("test_base: NOTE: Using srm_rx_backdoor");
   end
   else
   begin
      srm_rx_backdoor = 0;
      $display("test_base: NOTE: Using OCL cycles for SRM");
   end

   //Use Stream RTL block instead of Stream BFM
   if (!$test$plusargs("use_srm"))
      `CL_PATH.use_stream_bfm = 1;
   else
      `CL_PATH.use_stream_bfm = 0;

   //Put the Stream RTL block in loopback mode (send H2C packets back to C2H)
   if (!$test$plusargs("cfg_srm_lb_mode"))
      cfg_srm_lb_mode = 0;
   else
   begin
      `CL_PATH.use_stream_bfm = 0;
      cfg_srm_lb_mode = 1;
   end

   if (!$value$plusargs("cfg_num_pkts=%d", cfg_num_pkts))
   begin
      cfg_num_pkts = 100;
   end

   //Note this is the size of the descriptor structure (either 32B or 16B)
   if (!$value$plusargs("cfg_desc_type=%d", cfg_desc_type))
   begin
      cfg_desc_type = 0; 
   end

   if (!$value$plusargs("cfg_page_size=%d", cfg_page_size))
   begin
      cfg_page_size = 4096; 
   end

   if (!$value$plusargs("cfg_max_num_desc=%d", cfg_max_num_desc))
   begin
      cfg_max_num_desc = 64; 
   end


   if (!$value$plusargs("cfg_pkt_length_min=%d", cfg_pkt_length_min))
   begin
      cfg_pkt_length_min = 256; 
   end
   
   if (!$value$plusargs("cfg_pkt_length_max=%d", cfg_pkt_length_max))
   begin
      cfg_pkt_length_max = 256; 
   end

   if (!$value$plusargs("cfg_desc_offset_min=%d", cfg_desc_offset_min))
   begin
      cfg_desc_offset_min = 0; 
   end
   
   if (!$value$plusargs("cfg_desc_offset_max=%d", cfg_desc_offset_max))
   begin
      cfg_desc_offset_max = 256; 
   end

   if (!$value$plusargs("cfg_desc_length_min=%d", cfg_desc_length_min))
   begin
      cfg_desc_length_min = 64; 
   end
   
   if (!$value$plusargs("cfg_desc_length_max=%d", cfg_desc_length_max))
   begin
      cfg_desc_length_max = cfg_page_size; 
   end

   if (!$value$plusargs("cfg_pkt_dly_min=%d", cfg_pkt_dly_min))
   begin
      cfg_pkt_dly_min = 1; 
   end
   
   if (!$value$plusargs("cfg_pkt_dly_max=%d", cfg_pkt_dly_max))
   begin
      cfg_pkt_dly_max = 1; 
   end

   if (!$value$plusargs("cfg_desc_dly_min=%d", cfg_desc_dly_min))
   begin
      cfg_desc_dly_min = 1; 
   end
   
   if (!$value$plusargs("cfg_desc_dly_max=%d", cfg_desc_dly_max))
   begin
      cfg_desc_dly_max = 1; 
   end

   if (!$value$plusargs("cfg_desc_before_db_min=%d", cfg_desc_before_db_min))
   begin
      cfg_desc_before_db_min = 1; 
   end
   
   if (!$value$plusargs("cfg_desc_before_db_max=%d", cfg_desc_before_db_max))
   begin
      cfg_desc_before_db_max = 16; 
   end

   if (!$value$plusargs("cfg_desc_wc=%d", cfg_desc_wc))
     cfg_desc_wc = 1;

   if (!$value$plusargs("cfg_desc_wc_min=%d", cfg_desc_wc_min))
      cfg_desc_wc_min = 64;

   if (!$value$plusargs("cfg_desc_wc_max=%d", cfg_desc_wc_max))
      cfg_desc_wc_max = 64;

   if (!$value$plusargs("cfg_perf_h2c_start_pkt=%d", cfg_perf_h2c_start_pkt))
      cfg_perf_h2c_start_pkt = 0;

   if (!$value$plusargs("cfg_perf_h2c_end_pkt=%d", cfg_perf_h2c_end_pkt))
      cfg_perf_h2c_end_pkt = cfg_num_pkts;

   if (!$value$plusargs("cfg_perf_c2h_start_pkt=%d", cfg_perf_c2h_start_pkt))
      cfg_perf_c2h_start_pkt = 0;

   if (!$value$plusargs("cfg_perf_c2h_end_pkt=%d", cfg_perf_c2h_end_pkt))
      cfg_perf_c2h_end_pkt = cfg_num_pkts;

   if (!$value$plusargs("cfg_err_cnt_finish=%d", cfg_err_cnt_finish))
      cfg_err_cnt_finish = 1;

   if ($test$plusargs("cfg_no_perf_mon"))
      cfg_perf_mon = 0;
   else
      cfg_perf_mon = 1;

   if (!$value$plusargs("cfg_wc_cnt_min=%d", cfg_wc_cnt_min))
      cfg_wc_cnt_min = 6'd0;
   if (!$value$plusargs("cfg_wc_cnt_max=%d", cfg_wc_cnt_max))
      cfg_wc_cnt_max = 6'd31;

   if (!$value$plusargs("cfg_wc_to_cnt_min=%d", cfg_wc_to_cnt_min))
      cfg_wc_to_cnt_min = 4'd0;
   if (!$value$plusargs("cfg_wc_to_cnt_max=%d", cfg_wc_to_cnt_max))
      cfg_wc_to_cnt_max = 4'd15;

   if (!$value$plusargs("cfg_wc_to_rsln_min=%d", cfg_wc_to_rsln_min))
      cfg_wc_to_rsln_min = 20'd50;
   if (!$value$plusargs("cfg_wc_to_rsln_max=%d", cfg_wc_to_rsln_max))
      cfg_wc_to_rsln_max = 20'd200;

   if (!$value$plusargs("cfg_wc_cnt=%d", cfg_wc_cnt))
      cfg_wc_cnt = $urandom_range(cfg_wc_cnt_max, cfg_wc_cnt_min);

   if (!$value$plusargs("cfg_md_wr_ptr_wc_en=%b", cfg_md_wr_ptr_wc_en))
      cfg_md_wr_ptr_wc_en = 1;

   if (!$value$plusargs("cfg_pkt_cnt_wc_en=%b", cfg_pkt_cnt_wc_en))
      cfg_pkt_cnt_wc_en = 1;

   if (!$value$plusargs("cfg_desc_cnt_wc_en=%b", cfg_desc_cnt_wc_en))
      cfg_desc_cnt_wc_en = 1;

   if (!$value$plusargs("cfg_desc_cdt_wc_en=%b", cfg_desc_cdt_wc_en))
      cfg_desc_cdt_wc_en = 1;

   if (!$value$plusargs("cfg_wc_cnt=%d", cfg_wc_cnt))
      cfg_wc_cnt = $urandom_range(cfg_wc_cnt_max, cfg_wc_cnt_min);

   if (!$value$plusargs("cfg_wc_to_cnt=%d", cfg_wc_to_cnt))
      cfg_wc_to_cnt = $urandom_range(cfg_wc_to_cnt_max, cfg_wc_to_cnt_min);

   if (!$value$plusargs("cfg_wc_to_rsln=%d", cfg_wc_to_rsln))
      cfg_wc_to_rsln = $urandom_range(cfg_wc_to_rsln_max, cfg_wc_to_rsln_min);

   if (!$value$plusargs("cfg_c2h_num_md_min=%d", cfg_c2h_num_md_min))
      cfg_c2h_num_md_min = 16'd128;
   if (!$value$plusargs("cfg_c2h_num_md_max=%d", cfg_c2h_num_md_max))
      cfg_c2h_num_md_max = 16'd256;
   if (!$value$plusargs("cfg_c2h_num_md=%d", cfg_c2h_num_md))
      cfg_c2h_num_md = $urandom_range(cfg_c2h_num_md_max, cfg_c2h_num_md_min);

   if (!$value$plusargs("cfg_c2h_ring_offset_min=%d", cfg_c2h_ring_offset_min))
      cfg_c2h_ring_offset_min = 16'd128;
   if (!$value$plusargs("cfg_c2h_ring_offset_max=%d", cfg_c2h_ring_offset_max))
      cfg_c2h_ring_offset_max = 16'd256;
   if (!$value$plusargs("cfg_c2h_ring_offset=%d", cfg_c2h_ring_offset))
      cfg_c2h_ring_offset = $urandom_range(cfg_c2h_ring_offset_max, cfg_c2h_ring_offset_min);


   $display($time,,,"test_reandom_h2c: test_configuration cfg_num_pkts=%0d, cfg_desc_type=%b, cfg_pkt_length_min=%0d, cfg_pkt_length_max=%0d, cfg_desc_offset_min=%0d, cfg_desc_offset_max=%0d, cfg_desc_length_min=%0d, cfg_desc_length_max=%0d, cfg_pkt_dly_min=%0d, cfg_pkt_dly_max=%0d, cfg_max_num_desc=%0d, cfg_desc_dly_min=%0d, cfg_desc_dly_max=%0d",
                  cfg_num_pkts, cfg_desc_type, cfg_pkt_length_min, cfg_pkt_length_max, cfg_desc_offset_min, cfg_desc_offset_max, cfg_desc_length_min, cfg_desc_length_max, cfg_pkt_dly_min, cfg_pkt_dly_max, cfg_max_num_desc,
                  cfg_desc_dly_min, cfg_desc_dly_max);

   
   //$srandom(seed);
end

//---------------------------------------
// Perfromance monitor
//---------------------------------------
perf_mon PERF_MON_H2C (
   .clk(`CL_PATH.clk),
   .vld(`CL_PATH.h2c_axis_valid),
   .keep(`CL_PATH.h2c_axis_keep),
   .last(`CL_PATH.h2c_axis_last),
   .start_pkt(cfg_perf_h2c_start_pkt),
   .end_pkt(cfg_perf_h2c_end_pkt),
   .enable(cfg_perf_mon)
   );

perf_mon PERF_MON_C2H (
   .clk(`CL_PATH.clk),
   .vld(`CL_PATH.c2h_axis_valid),
   .keep(`CL_PATH.c2h_axis_keep),
   .last(`CL_PATH.c2h_axis_last),
   .start_pkt(cfg_perf_c2h_start_pkt),
   .end_pkt(cfg_perf_c2h_end_pkt),
   .enable(cfg_perf_mon)
   );

//----------------------------------
// End of simulation summary/checks
//----------------------------------
task end_sim;
begin
   $display($time,,,"END_SIM: c2h_pkts=%0d (%0d errored), h2c_pkts=%0d (%0d errored)", c2h_pkts_checked, c2h_err_cnt, h2c_pkts_checked, h2c_err_cnt);
   if (cfg_perf_mon)
   begin
      PERF_MON_H2C.print_results();
      PERF_MON_C2H.print_results();
   end
      
   chk_axi_prot_error();

   if ((h2c_err_cnt==0) && (c2h_err_cnt==0))
      $display("!!! TEST PASSED !!!");
   else
      $display("*** TEST FAILED ***");

   $finish;
end
endtask 

//-----------------------------
// Monitor error counts
//-----------------------------
always @*
begin
   if (((h2c_err_cnt+c2h_err_cnt) >= cfg_err_cnt_finish) && cfg_err_cnt_finish!=0)
   begin
      repeat(5)
         @(posedge tb_clk);
      $display($time,,,"ERR_CNT_MON: Number of errors=%0d exceeded threshold=%0d, killing simulation...", (h2c_err_cnt+c2h_err_cnt), cfg_err_cnt_finish);
      $finish;
   end
end

//----------------------------------
// Check protocol errors
//----------------------------------
task chk_axi_prot_error();
   
   logic [31:0] rd_data;
   logic [63:0] err_addr;
   logic [7:0] err_id;
   logic wr_last_incomplete;
   logic wr_last_early;

   sde.access.peek_ocl(.addr(16'h1000), .data(rd_data));
   wr_last_early = rd_data[0];
   wr_last_incomplete = rd_data[1];
   
   if (wr_last_early || wr_last_incomplete) begin
     sde.access.peek_ocl(.addr(16'h1004), .data(rd_data));
     err_addr[31:0] = rd_data[31:0];
     sde.access.peek_ocl(.addr(16'h1008), .data(rd_data));
     err_addr[63:32] = rd_data[31:0];
     sde.access.peek_ocl(.addr(16'h100c), .data(rd_data));
     err_id = rd_data[7:0];
     $display($time,,,"chk_axi_prot_error: AXI Protocol Error: err_addr = 0x%016x, err_id = 0x%02x", err_addr, err_id);

     // Clear the error
     sde.access.poke_ocl(.addr(16'h1000), .data(3'h3));

     sde.access.peek_ocl(.addr(16'h1000), .data(rd_data));
     if (rd_data[1:0] != 2'b00) begin
        $display($time,,,"chk_axi_prot_error: *** ERROR ***: Error bits did not get cleared");
     end

     c2h_err_cnt++;
  end
endtask

//----------------------------------
// Check Write Back Coalesce 
//----------------------------------
   task monitor_h2c_counters();

   logic [31:0] desc_limit_host;
   logic [31:0] desc_limit_hw;
   logic [31:0] max_diff;

      // In every clock, make sure the difference between the host copy of limit 
      // and hardware copy of limit is not off by more than coalesce count
      forever begin
         @(posedge `CL_PATH.clk) 
         if (`CL_PATH.SDE.rst_n) begin
           max_diff = 10;//sde.cfg_h2c_wc_cnt + 3; 
  
           desc_limit_host = sde.access.read_host_dw(sde.cfg_h2c_cdt_limit_addr);
           desc_limit_hw = `CL_PATH.SDE.genblk2.SDE_H2C.SDE_H2C_WB.desc_wb_limit;
           
           if (sde.cfg_c2h_desc_cdt_wc_en) 
             if (desc_limit_hw - desc_limit_hw > max_diff) begin
                $display($time,,,"chk_axi_prot_error: *** ERROR ***: H2C Desc Limit max_diff mismatch. desc_limit_host = 0x%08x, desc_limit_hw = 0x%08x, max_diff = 0x%02x", desc_limit_host, desc_limit_hw, max_diff);
                h2c_err_cnt++;
             end
         end
      end
    endtask


   task monitor_c2h_counters();

   logic [31:0] desc_limit_host;
   logic [31:0] desc_limit_hw;
   logic [31:0] max_diff;

      // In every clock, make sure the difference between the host copy of limit 
      // and hardware copy of limit is not off by more than coalesce count

    forever begin
       @(posedge `CL_PATH.clk) 
       if (`CL_PATH.SDE.rst_n) begin
           max_diff = 10;//sde.cfg_c2h_wc_cnt; 
           
           desc_limit_host = sde.access.read_host_dw(sde.cfg_h2c_cdt_limit_addr);
           desc_limit_hw = `CL_PATH.SDE.genblk1.SDE_C2H.SDE_C2H_WB.desc_wb_limit;
           
           if (sde.cfg_c2h_desc_cdt_wc_en) 
             if (desc_limit_hw - desc_limit_hw > max_diff) begin
                 $display($time,,,"chk_axi_prot_error: *** ERROR ***: C2H Desc Limit max_diff mismatch. desc_limit_host = 0x%08x, desc_limit_hw = 0x%08x, max_diff = 0x%02x", desc_limit_host, desc_limit_hw, max_diff);
                 c2h_err_cnt++;
           end
       end
    end


endtask

