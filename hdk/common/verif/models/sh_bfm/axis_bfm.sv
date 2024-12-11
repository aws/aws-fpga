//------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//------------------------------------------------------------------------------

`include "anp_base_macros.svh"

//------------------------------------------------------------------------------
// Module: axis_bfm
// Main AXIS BFM module. Both of Master and Slave mode are implemented.
// Shall set the IS_MASTER parameter as below to selet the mode during 
// instantiation.
// Master mode -> IS_MASTER=1 
// Slave mode  -> IS_MASTER=0
//------------------------------------------------------------------------------
module axis_bfm #(
   parameter MSG_ID      = "AXIS_BFM",
   parameter FILE_NAME   = "",
   parameter IS_MASTER   = 1,
   parameter DATA_WIDTH  = 64,
   parameter USER_WIDTH  = 1,
   parameter KEEP_WIDTH  = (DATA_WIDTH/8)
)(
   input  wire                   axis_clk,
   input  wire                   axis_rst_n,
   inout  wire                   axis_valid,
   inout  wire  [DATA_WIDTH-1:0] axis_data, 
   inout  wire                   axis_last,
   inout  wire  [KEEP_WIDTH-1:0] axis_keep,
   inout  wire  [USER_WIDTH-1:0] axis_user,
   inout  wire                   axis_ready
);

   import axis_bfm_pkg::*;

   //---------------------------------------------------------------------------
   // Local variables
   //---------------------------------------------------------------------------
   logic                   m_axis_valid;
   logic [DATA_WIDTH-1:0]  m_axis_data; 
   logic                   m_axis_last;
   logic [KEEP_WIDTH-1:0]  m_axis_keep;
   logic [USER_WIDTH-1:0]  m_axis_user;
   logic                   m_axis_ready;
   // FIFO Queue to store the stimulus packet being read from the text stimulus file
   axis_mbx_t              stim_mbx;
   // FIFO Queue to store the actual packet being driven
   axis_mbx_t              drive_mbx;
   // FIFO Queue to store the monitored sampled packets
   axis_mbx_t              monitor_mbx;
   // Event to indicate the mailboxes are created
   event                   mbx_created_e;
   // File pointer to the input file to read the user stimulus
   int                     fp_i;
   // File pointer to the output file to dump the sampled packet
   int                     fp_o;
   // Knob indicate the output file dump is enabled
   bit                     dump_file;
   // Knob indicate the input stimulus file read is enabled
   bit                     read_file;
   // HDL path of the hierarchy of this BFM's instance
   string                  hdl_path = $sformatf("%m");

   //---------------------------------------------------------------------------
   // Task: reset
   // Reset the output signals
   //---------------------------------------------------------------------------
   task automatic reset();
      if (IS_MASTER) begin
         m_axis_valid <= 0;
         m_axis_data  <= 0;
         m_axis_last  <= 0;
         m_axis_keep  <= 0;
         m_axis_user  <= 0;
      end
      else begin
         m_axis_ready = 0;
      end
   endtask : reset

   always @ (posedge axis_clk, negedge axis_rst_n) begin
      if (axis_rst_n === 1'b0) begin
         while (monitor_mbx.num() > 0) begin
            axis_bfm_pkt np;
            monitor_mbx.get(np);
         end
         reset();
      end
      else if (IS_MASTER == 0) begin
`ifdef VCS
         randcase
         1  : m_axis_ready <= ($test$plusargs("AXIS_RAND_READY") ? 0: 1);
         20 : m_axis_ready <= 1;
         endcase
`else
         m_axis_ready <= 1;
`endif
      end
   end

   //---------------------------------------------------------------------------
   // Create the instance of the mailboxes
   //---------------------------------------------------------------------------
   initial begin
      stim_mbx    = new(1);
      monitor_mbx = new();
      drive_mbx   = new();
      ->mbx_created_e;
   end

   //---------------------------------------------------------------------------
   // Drive Output signals
   //---------------------------------------------------------------------------
   generate 
   if (IS_MASTER == 1)
   begin : MASTER_MODE
      assign axis_valid = m_axis_valid;
      assign axis_data  = m_axis_data;
      assign axis_last  = m_axis_last;
      assign axis_keep  = m_axis_keep;
      assign axis_user  = m_axis_user;
   end : MASTER_MODE
   else
   begin : SLAVE_MODE
      assign axis_ready = m_axis_ready;
   end : SLAVE_MODE
   endgenerate

   //---------------------------------------------------------------------------
   // Open the input stimulus file for data generation and drive the packets
   // based on the provided stimulus
   //---------------------------------------------------------------------------
   bit stim_done;

   generate if (IS_MASTER)
   begin : MASTER
   
      initial 
      begin : READ_TEXT_STIMULUS
         string fname;
   
         wait (mbx_created_e.triggered);
   
         if (FILE_NAME == "") begin
            fname = {hdl_path, ".in"};
         end
         else begin
            fname = {FILE_NAME, ".in"};
         end
         fp_i = $fopen(fname, "r");

         if (fp_i != 0) begin : OPENED
            read_file = 1;
            `anp_info(
               {"read_stim: Driving master packet using stimulus file ", fname}, 
               MSG_ID)

            axis_bfm_pkg::read_stim(
               .mbx_h   (stim_mbx),
               .fp      (fp_i),
               .msg_id  (MSG_ID));

         end : OPENED
   
         stim_done = 1;
         `anp_info("drive_stim: Done", MSG_ID)
      end : READ_TEXT_STIMULUS
   
      initial 
      begin : DRIVE_TEXT_STIMULUS
         string fname;
   
         wait_out_of_reset($sformatf("drive_stim(%0d)", `__LINE__));
   
         forever begin
            axis_bfm_pkt pkt;
            stim_mbx.get(pkt);
            wait_out_of_reset($sformatf("drive_stim(%0d)", `__LINE__));
            wait_clock(pkt.delay);
            drive_packet(pkt.data);
         end
   
      end : DRIVE_TEXT_STIMULUS

   end : MASTER
   endgenerate

   //---------------------------------------------------------------------------
   // Open the output file to dump the monitored packet
   //---------------------------------------------------------------------------
   initial begin
      string fname;
      if ($test$plusargs("AXIS_DUMP_PACKET")) begin
         if (FILE_NAME == "") begin
            fname = {hdl_path, ".out"};
         end
         else begin
            fname = {FILE_NAME, ".out"};
         end
         fp_o = $fopen(fname, "w");
         if (fp_o != 0) begin
            dump_file = 1;
         end
         else begin
            `anp_fatal({"Failed to open ", fname}, MSG_ID)
         end
      end
   end

   //---------------------------------------------------------------------------
   // Close the opened files
   //---------------------------------------------------------------------------
   final begin
      if (dump_file) $fclose(fp_o);
      if (read_file) $fclose(fp_i);
   end

   //---------------------------------------------------------------------------
   // Task: drive_packet
   // Task to send a complete single packet based on the input data array.
   //
   // Parameters:
   // - data : Queue of data array in bytes
   // - user : User data value to be used at the end of packet
   //---------------------------------------------------------------------------
   task automatic drive_packet(input bit [7:0] data[$], input logic user = 0);
      int total_beats = (data.size() + (KEEP_WIDTH - 1)) / KEEP_WIDTH;

      if (IS_MASTER == 0) begin
         `anp_fatal("Calling send task is not supported in slave mode", MSG_ID)
         return;
      end

      wait_out_of_reset($sformatf("drive_packet(%0d)", `__LINE__));

      `anp_info({"drive_packet: ", axis_bfm_pkg::print_array(data)}, MSG_ID)

      if ($test$plusargs("AXIS_CHECK_DRIVE_AND_MONITOR")) begin
         axis_bfm_pkt pkt = new();
         pkt.data = data;
         drive_mbx.put(pkt);
      end

      for (int i = 0; i < total_beats; i++) begin
         bit [DATA_WIDTH-1:0] data_tmp;
         bit [KEEP_WIDTH-1:0] keep_tmp;

         for (int j = 0; j < KEEP_WIDTH; j++) begin
            if (data.size() > 0) begin
               data_tmp[j*8+:8] = data.pop_front();
               keep_tmp[j] = 1'b1;
            end
         end

         @ (posedge axis_clk);
         m_axis_valid <= 1'b1;
         m_axis_data  <= data_tmp;
         m_axis_keep  <= keep_tmp;

         if (data.size() == 0) begin
            m_axis_last <= 1'b1;
            m_axis_user <= 1'b0;
         end

         `anp_debug($sformatf("drive_packet: %0d / %0d", i, total_beats), MSG_ID)

         #1ns;
         while (axis_ready !== 1'b1) begin
            @ (posedge axis_clk);
            #1ns;
         end
      end

      @ (posedge axis_clk);
      reset();

   endtask : drive_packet

   //---------------------------------------------------------------------------
   // Task: monitor
   // Task to monitor the AXI4 Streaming data, sample them and store them
   // into the monitor FIFO
   //---------------------------------------------------------------------------
   int delay;
   bit sampling;
   int packets;

   task automatic monitor_packet();
      wait (mbx_created_e.triggered);
      wait_out_of_reset($sformatf("monitor_packet(%0d)", `__LINE__));

      forever begin
         // Create the new handle of the packet that will be assembled
         axis_bfm_pkt pkt = new();

         wait_out_of_reset($sformatf("monitor_packet(%0d)", `__LINE__));

         @ (posedge axis_clk);
         #1ns;
         if (!sampling) begin
            delay++;
         end

         `anp_debug($sformatf("monitor_packet: Looking for next packet#%0d", 
            packets), MSG_ID)

         while ((axis_valid & axis_ready & axis_last) !== 1'b1) 
         begin : SAMPLE
            if ((axis_valid & axis_ready) === 1'b1) begin
               sampling <= 1;
               for (int i = 0; i < KEEP_WIDTH; i++) begin
                  if (axis_keep[i] === 1'b1) begin
                     pkt.data.push_back(axis_data[i*8+:8]);
                  end
               end
               `anp_debug($sformatf("monitor_packet: Sampling packet#%0d", 
                  packets), MSG_ID)
               @ (posedge axis_clk);
               #1ns;
            end
            else begin
               @ (posedge axis_clk);
               #1ns;
               if (!sampling) begin
                  delay++;
               end
            end
         end : SAMPLE

         // Capture the last beat
         for (int i = 0; i < KEEP_WIDTH; i++) begin
            if (axis_keep[i] === 1'b1) begin
               pkt.data.push_back(axis_data[i*8+:8]);
            end
         end

         // Broadcast the sampled packet into the FIFO
         monitor_mbx.put(pkt);

         // If a dump to text file is selected then DUMP the assembled
         // packet into the text file
         if (dump_file) begin
            pkt.dump(fp_o, delay);
         end

         `anp_info($sformatf("monitor_packet: Complete Sampling packet#%0d. %0s", 
            packets, pkt.print), MSG_ID)

         packets++;
         delay = 0;
         sampling = 0;

      end
   endtask : monitor_packet

   initial monitor_packet();

   //---------------------------------------------------------------------------
   // Wait for number of clock cycles
   //---------------------------------------------------------------------------
   task automatic wait_clock(int clocks);
      repeat (clocks) @ (posedge axis_clk);
   endtask : wait_clock

   //---------------------------------------------------------------------------
   // Wait for number of clock cycles
   //---------------------------------------------------------------------------
   task automatic wait_out_of_reset(string id);
      wait (axis_rst_n === 1'b1);
      wait_clock(1);
      `anp_info({id, ": Out-of-reset"}, MSG_ID)
   endtask : wait_out_of_reset

   //---------------------------------------------------------------------------
   // Self drive and monitor checker
   //---------------------------------------------------------------------------
   initial begin
      if ($test$plusargs("AXIS_CHECK_DRIVE_AND_MONITOR") && IS_MASTER) begin
         int packets;
         forever begin
            axis_bfm_pkt exp, act;
            drive_mbx  .get(exp);
            monitor_mbx.get(act);
            void'(exp.compare(
               .rhs     (act), 
               .message ($sformatf("%0s-SELF-CHECK Pkt-%0d", MSG_ID, packets))));
            packets++;
         end
      end
   end

endmodule : axis_bfm

