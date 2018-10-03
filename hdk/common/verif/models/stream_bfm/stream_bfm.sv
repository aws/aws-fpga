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

//Note KEEP_WIDTH is same as number of bytes in data bus
module stream_bfm #(parameter DATA_WIDTH=512, parameter KEEP_WIDTH=DATA_WIDTH/8, parameter USER_WIDTH=64)(
   input clk,
   input rst_n,

   input[DATA_WIDTH-1:0] ins_data,
   input[KEEP_WIDTH-1:0] ins_keep,
   input ins_valid,
   input ins_last,
   input[USER_WIDTH-1:0] ins_user,
   output logic ins_ready,
   
   output logic[DATA_WIDTH-1:0] ots_data,
   output logic[KEEP_WIDTH-1:0] ots_keep,
   output logic[USER_WIDTH-1:0] ots_user,
   output logic ots_valid,
   output logic ots_last,
   input ots_ready 
   );

gen_buf_t tx_pkt_q[$];
logic[USER_WIDTH-1:0] tx_pkt_user_q[$];
event tx_pkt_done;
gen_buf_t tx_pkt_done_pkt;       //Recently transmitted packet, can be used for scoreboarding
logic[USER_WIDTH-1:0] tx_pkt_done_user;

gen_buf_t rx_pkt_q[$];
logic[USER_WIDTH-1:0] rx_pkt_user_q[$];
event rx_pkt_done;
gen_buf_t rx_pkt_done_pkt;       //Recently received packet, can be used for scoreboarding

bit disable_rx_pkt_q = 0;        //If doing RX packet queue outside, can disable the BFM's RX packet queue

int rx_pkt_count = 0;
int tx_pkt_count = 0;

bit ins_bp_en = 0;
int ins_bp_stop_min = 1;         //Random INS backpressure.  This is "stop" time (backpressure asserted)
int ins_bp_stop_max = 10;

int ins_bp_go_min = 1;           //Random INS backpressure.  This is "go" time (backpressure de-asserted)
int ins_bp_go_max = 10;

//-----------------------------------------------------------------------
//-----------------------------------------------------------------------
// USER Functions (API)
//-----------------------------------------------------------------------
//-----------------------------------------------------------------------

//-------------------------------------------------------------------------------
//Push tx packet to tx_packet queue
// start_data - Start data DW, will send incrementing data or constant data
// length - Length in bytes, 1-based
// inc_data - use incrementing data (otherwise random)
//-------------------------------------------------------------------------------
function void stream_tx (input[31:0] start_data = 32'h00000000, input int length=1, input inc_data=1, input[USER_WIDTH-1:0] user);

   gen_buf_t cur_pkt;

   cur_pkt = new();
   if (inc_data)
      cur_pkt.init_inc(start_data, length);
   else
      cur_pkt.init_rnd(length);

   tx_pkt_q.push_back(cur_pkt);
   tx_pkt_user_q.push_back(user);
endfunction

//----------------------------------
// Get RX Packet Queue size
//----------------------------------
function int get_rx_pkt_q_size();
   get_rx_pkt_q_size = rx_pkt_q.size(); 
endfunction

//----------------------------------
// Get TX Packet Queue size
//----------------------------------
function int get_tx_pkt_q_size();
   get_tx_pkt_q_size = tx_pkt_q.size(); 
endfunction

//---------------------------------------
// Enable/disable random RX backpressure
//---------------------------------------
function ins_bp_enable(input int go_min=1, input int go_max=10, input int stop_min=1, input int stop_max=10);
   ins_bp_go_min = go_min;
   ins_bp_go_max = go_max;
   ins_bp_stop_min = stop_min;
   ins_bp_stop_max = stop_max;

   ins_bp_en = 1;

endfunction

function ins_bp_disable();
   ins_bp_en = 0;
endfunction


// End USER Functions
//-------------------------------------
//-------------------------------------


//----------------------------------------------------------------------
//----------------------------------------------------------------------
// BFM functionality 
//----------------------------------------------------------------------
//----------------------------------------------------------------------

//----------------------------------------------------------------------------------------
// Thread to transmit packets.  If TX packet queue is not empty then transmit packet
//----------------------------------------------------------------------------------------
task tx_pkt_thread;

   logic[DATA_WIDTH-1:0] data;
   int num_phases;
   logic[KEEP_WIDTH-1:0] last_keep;

   gen_buf_t cur_pkt;
   logic[USER_WIDTH-1:0] cur_user;

   forever
   begin
      while (tx_pkt_q.size()==0)
         @(posedge clk);

      cur_pkt = tx_pkt_q.pop_front;
      cur_user = tx_pkt_user_q.pop_front;

      //Get first DW of data
      data = 0;
      for (int i=0; i<4; i++)
         if (cur_pkt.data.size() > i)
            data[8*i+:8] = cur_pkt.data[i];
      
      num_phases = cur_pkt.data.size()/(KEEP_WIDTH);
      if ((cur_pkt.data.size() % KEEP_WIDTH) != 0)
      begin
         num_phases++;
         last_keep = ~( {KEEP_WIDTH{1'b1}} << (cur_pkt.data.size() % KEEP_WIDTH));
      end
      else
      begin
         last_keep = {KEEP_WIDTH{1'b1}};
      end

      $display($time,,,"stream_bfm.tx_pkt_thread TX_PKT[%0d] start_data[31:0]=0x%x, byte_length=0x%x, num_phases=0x%x, last_keep=0x%x, user=0x%x", tx_pkt_count, data[31:0], cur_pkt.data.size(), num_phases, last_keep, cur_user);

      @(posedge clk);
      for (int i=0; i<num_phases; i++)
      begin
         data = 0;

         //Gather up KEEP_WIDTH bytes
         for (int j=0; j<KEEP_WIDTH; j++)
         begin
            //Make sure not past buffer (i.e. last phase is not full of data)
            if ((i*KEEP_WIDTH) + j < cur_pkt.data.size())
               data[j*8+:8] = cur_pkt.data[(i*KEEP_WIDTH) + j];
         end

         ots_data <= data;
         ots_keep <= (i==(num_phases-1))? last_keep: {KEEP_WIDTH{1'b1}};
         ots_last <= i==(num_phases-1);
         ots_user <= (i==(num_phases-1))? cur_user: $urandom;
         ots_valid <= 1;

         @(posedge clk);
         while (!ots_ready)
            @(posedge clk);
      end

      tx_pkt_done_pkt = cur_pkt;
      tx_pkt_done_user = cur_user;
      tx_pkt_count++;
      ->tx_pkt_done;
      ots_data <= 0;
      ots_keep <= 0;
      ots_last <= 0;
      ots_user <= 0;
      ots_valid <= 0;
   end

endtask

//------------------------------------------------------------------------------------
// Receive packet thread -- Currently don't have any backpressure
//------------------------------------------------------------------------------------
task rx_pkt_thread;

   gen_buf_t cur_pkt;

   bit pkt_inp; 

   logic[31:0] tmp_data;

   pkt_inp = 0;
   @(posedge clk);
   forever
   begin
      while (ins_valid!==1 || ins_ready!==1)
         @(posedge clk);

      //If not currently receiving a packet create a new packet
      if (!pkt_inp)
      begin
         cur_pkt = new();  
         pkt_inp = 1;
      end

      //Gather the data -- Note only support contiguous bytes
      for (int i=0; i<KEEP_WIDTH; i++)
         if (ins_keep[i])
            cur_pkt.data.push_back(ins_data[i*8+:8]);

      if (ins_last)
      begin
         if (!disable_rx_pkt_q)
         begin
            rx_pkt_q.push_back(cur_pkt);
            rx_pkt_user_q.push_back(ins_user);
         end
            
         pkt_inp = 0;
  
         //Get first DW of data for display 
         tmp_data = 0;
         for (int i=0; i<4; i++)
            if (cur_pkt.data.size() > i)
               tmp_data[8*i+:8] = cur_pkt.data[i];

         $display($time,,,"stream_bfm.rx_pkt_thread RX_PKT[%0d] start_data[31:0]=0x%x, byte_length=0x%x", rx_pkt_count, tmp_data, cur_pkt.data.size());
         rx_pkt_done_pkt = cur_pkt;
         rx_pkt_count++;
         ->rx_pkt_done;
      end

      @(posedge clk);
   end

endtask

//------------------------------
// INS backpressure (ins_ready)
//------------------------------
task ins_bp_thread;

   int dly;

   forever 
   begin
      while (!ins_bp_en)
         @(posedge clk);

      //Stop
      ins_ready <= 0;
      dly = $urandom_range(ins_bp_stop_max, ins_bp_stop_min);
      repeat(dly)
         @(posedge clk);

      //Go
      ins_ready <= 1;
      dly = $urandom_range(ins_bp_go_max, ins_bp_go_min);
      repeat(dly)
         @(posedge clk);
   end
endtask

      
//--------------------------------------------------------------------------
// Reaset thread
//--------------------------------------------------------------------------
task rst_thread;

   forever
   begin
      @(negedge rst_n);
      ots_data <= 0;
      ots_keep <= 0;
      ots_last <= 0;
      ots_user <= 0;
      ots_valid <= 0;

      ins_ready <= 1;
   end
endtask

initial
begin
   fork 
      rst_thread;
      tx_pkt_thread;
      rx_pkt_thread;
      ins_bp_thread;
   join_none
end


endmodule

