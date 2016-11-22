// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

`define CL_PKT_TST_TX_CFG            12'h000
`define CL_PKT_TST_TX_SEED0          12'h004
`define CL_PKT_TST_TX_SEED1          12'h00C
`define CL_PKT_TST_TX_MIN_PKTLEN     12'h008
`define CL_PKT_TST_TX_MAX_PKTLEN     12'h010
`define CL_PKT_TST_TX_PKT_CNT0       12'h014
`define CL_PKT_TST_TX_PKT_CNT1       12'h018
`define CL_PKT_TST_TICK_CNT          12'h01C
`define CL_PKT_TST_TX_TIMER          12'h020

`define CL_PKT_TST_RX_CFG            12'h080
`define CL_PKT_TST_RX_SEED0          12'h084
`define CL_PKT_TST_RX_SEED1          12'h08C
`define CL_PKT_TST_RX_MIN_PKTLEN     12'h088
`define CL_PKT_TST_RX_MAX_PKTLEN     12'h090
`define CL_PKT_TST_RX_PKT_CNT0       12'h094
`define CL_PKT_TST_RX_PKT_CNT1       12'h098
`define CL_PKT_TST_RX_ERR_PKT_CNT0   12'h09C
`define CL_PKT_TST_RX_ERR_PKT_CNT1   12'h0A0
`define CL_PKT_TST_RX_ERR_CNT0       12'h0A4
`define CL_PKT_TST_RX_ERR_CNT1       12'h0A8
`define CL_PKT_TST_RX_TIMER          12'h0AC
`define CL_PKT_TST_RX_RAW_PKT_CNT0   12'h0B0
`define CL_PKT_TST_RX_RAW_PKT_CNT1   12'h0B4
`define CL_PKT_TST_RX_RAW_DATA_CNT0  12'h0B8
`define CL_PKT_TST_RX_RAW_DATA_CNT1  12'h0BC
`define CL_PKT_TST_RX_RAW_ERR_CNT0   12'h0C0
`define CL_PKT_TST_RX_RAW_ERR_CNT1   12'h0C4
`define CL_PKT_TST_RX_DBG_RAM_INDEX  12'h0C8
`define CL_PKT_TST_RX_DBG_RAM_DATA   12'h0CC

task aurora_common_test(
                        input logic [63:0] cl_base = 64'h0
                       );
   begin

      // Test variables
      logic [63:0]  tgt_bar;
      logic [63:0]  base_addr;
      logic [63:0]  pkt_cnt;
      logic [31:0]  write_data;
      logic [31:0]  read_data;
      bit           done;
      bit           rx_lock_err;
      bit           rx_data_err;
      bit           rx_pktlen_err;
      int           error_count;
      int           entry_idx;
      int           dw_idx;
      logic [31:0]  index;
      logic [31:0]  dbg_entry [31:0][18:0];

      bit           prbs_mode;
      bit           pkt_len_mode;
      bit           simple_data_mode;
      logic [31:0]  seed_0;
      logic [31:0]  seed_1;
      logic [31:0]  pktlen_min;
      logic [31:0]  pktlen_max;
      bit           rx_data_chk;
      bit           rx_pktlen_chk;
      logic [63:0]  num_pkts;
      bit           read_dbg_ram;


      if ($test$plusargs("PRBS_MODE")) begin
         prbs_mode = 1'b1;
      end else begin
         prbs_mode = 1'b0;
      end

      if ($test$plusargs("PKT_LEN_MODE")) begin
         pkt_len_mode = 1'b1;
      end else begin
         pkt_len_mode = 1'b0;
      end

      if ($test$plusargs("SIMPLE_DATA_MODE")) begin
         simple_data_mode = 1'b1;
      end else begin
         simple_data_mode = 1'b0;
      end

      if (!$value$plusargs("SEED0=0x%x", seed_0)) begin
         seed_0 = 32'h0000_0000;
      end

      if (!$value$plusargs("SEED1=0x%x", seed_1)) begin
         seed_1 = 32'h0000_0000;
      end

      if (!$value$plusargs("PKT_LEN_MIN=0x%x", pktlen_min)) begin
         pktlen_min = 32'h0000_0000;
      end

      if (!$value$plusargs("PKT_LEN_MAX=0x%x", pktlen_max)) begin
         pktlen_max = 32'h0000_0000;
      end

      if ($test$plusargs("RX_DATA_CHK")) begin
         rx_data_chk = 1'b1;
      end else begin
         rx_data_chk = 1'b0;
      end

      if ($test$plusargs("RX_PKTLEN_CHK")) begin
         rx_pktlen_chk = 1'b1;
      end else begin
         rx_pktlen_chk = 1'b0;
      end

      if (!$value$plusargs("NUM_PKTS=%d", num_pkts)) begin
         num_pkts = 64'd0; // DEBUG: Need a real default value here...
      end

      if ($test$plusargs("READ_DBG_RAM")) begin
         read_dbg_ram = 1'b1;
      end else begin
         read_dbg_ram = 1'b0;
      end


      done = 0;
      error_count = 0;


      sys_init(.error_count(error_count));

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(EP_BUS_DEV_FNS), .bar_addr(tgt_bar));
`else
      get_bar(.bar_num(0), .comp_id(EP_BUS_DEV_FNS), .bar_addr(tgt_bar));
`endif

      base_addr = tgt_bar + cl_base;

      //---------------------------
      // CL PKT Config
      //---------------------------
      // Configure Tick Count
// DEBUG: Make tick count a PLUSARG option?
      write_data = 32'd200;
      $display("[%t] : Write Tick Count (%d)", $realtime, write_data);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TICK_CNT), .write_data(write_data));

      // Configure RX
      $display("[%t] : Write RX Seed 0 (0x%08x)", $realtime, seed_0);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_SEED0), .write_data(seed_0));

      $display("[%t] : Write RX Seed 1 (0x%08x)", $realtime, seed_1);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_SEED1), .write_data(seed_1));

      $display("[%t] : Write RX Pkt Len Min (%d)", $realtime, pktlen_min);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_MIN_PKTLEN), .write_data(pktlen_min));

      $display("[%t] : Write RX Pkt Len Max (%d)", $realtime, pktlen_max);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_MAX_PKTLEN), .write_data(pktlen_max));

      write_data = 32'h0000_0000;
      write_data[9] = rx_pktlen_chk;
      write_data[8] = rx_data_chk;
      write_data[3] = simple_data_mode;
      write_data[2] = pkt_len_mode;
      write_data[1] = prbs_mode;
      write_data[0] = 1'b1;
      $display("[%t] : Write RX Ctl with 0x%08x", $realtime, write_data);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .write_data(write_data));

      // Configure TX
      $display("[%t] : Write TX Seed 0 (0x%08x)", $realtime, seed_0);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_SEED0), .write_data(seed_0));

      $display("[%t] : Write TX Seed 1 (0x%08x)", $realtime, seed_1);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_SEED1), .write_data(seed_1));

      $display("[%t] : Write TX Pkt Len Min (%d)", $realtime, pktlen_min);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_MIN_PKTLEN), .write_data(pktlen_min));

      $display("[%t] : Write TX Pkt Len Max (%d)", $realtime, pktlen_max);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_MAX_PKTLEN), .write_data(pktlen_max));

      // Wait for Channel Ready before enabling TX
      done = 0;
      $display("[%t] : Waiting for Channel Ready", $realtime);
      while (done == 0) begin
         reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_CFG), .read_data(read_data));
         done = read_data[31];
      end
      $display("[%t] : Got Channel Ready", $realtime);

      write_data = 32'h0000_0000;
      write_data[3] = simple_data_mode;
      write_data[2] = pkt_len_mode;
      write_data[1] = prbs_mode;
      write_data[0] = 1'b1;
      $display("[%t] : Write TX Ctl with 0x%08x", $realtime, write_data);
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_CFG), .write_data(write_data));

      // Wait for RX Lock
      done = 0;
      $display("[%t] : Waiting for RX Lock", $realtime);
      while (done == 0) begin
         reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .read_data(read_data));
         done = read_data[31];
      end
      $display("[%t] : Got RX Lock", $realtime);

      // Wait for packets
      $display("[%t] : Waiting for %d RX packets", $realtime, num_pkts);
      done = 0;
      while (done == 0) begin
         reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_PKT_CNT0), .read_data(read_data));
         pkt_cnt[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_PKT_CNT1), .read_data(read_data));
         pkt_cnt[63:32] = read_data;
         done = (pkt_cnt >= num_pkts);
         $display("[%t] : RX pkt_cnt is %d. Waiting for %d packets.", $realtime, pkt_cnt, num_pkts);
      end
      $display("[%t] : Got %d RX packets", $realtime, num_pkts);

// DEBUG: Should we be doing some checks with the following read data?
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_PKT_CNT0), .read_data(read_data));
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_PKT_CNT1), .read_data(read_data));

      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_CNT0), .read_data(read_data));
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_CNT1), .read_data(read_data));

      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_TIMER), .read_data(read_data));
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_TIMER), .read_data(read_data));

// DEBUG: Do we need to write upper 32-bit values with zero also?
      write_data = 32'd0;
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_PKT_CNT0), .write_data(32'd0));

      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_ERR_CNT0), .write_data(32'd0));

      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_TIMER), .write_data(32'd0));
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_TIMER), .write_data(32'd0));


      $display("[%t] : Reading Error bits", $realtime);
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .read_data(read_data));
      rx_data_err = read_data[30];
      rx_lock_err = read_data[29];
      rx_pktlen_err = read_data[28];

// DEBUG: Check significance of writing bit [30]
      write_data = read_data | 32'h40000000;
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .write_data(write_data));

// DEBUG: Do we need to check this read data?
      reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .read_data(read_data));

      if (rx_lock_err) begin
         $display("[%t] : *** ERROR *** rx_lock_error = %b", $realtime, rx_lock_err);
         error_count++;
      end

      if (rx_data_err) begin
         $display("[%t] : *** ERROR *** rx_data_error = %b", $realtime, rx_data_err);
         error_count++;
      end

      if (rx_pktlen_err) begin
         $display("[%t] : *** ERROR *** rx_pktlen_error = %b", $realtime, rx_pktlen_err);
         error_count++;
      end

      // Stop TX
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_TX_CFG), .write_data(32'd0));
      reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_CFG), .write_data(32'd0));


      if (read_dbg_ram) begin
         $display("[%t] : Reading Debug RAM", $realtime);
         // Read the 3 entries of debug RAM 
         for (entry_idx = 0; entry_idx < 32; entry_idx++) begin
//            $display("-------------- Entry %02d ---------------\n", entry_idx);
            for (dw_idx = 0; dw_idx < 2; dw_idx++) begin
               if (dw_idx == 0)
                 // Write index 
                 index = {20'd0, entry_idx[4:0], dw_idx[4:0]};
               else
                 index = {20'd0, entry_idx[4:0], 5'd18};

               reg_write(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_DBG_RAM_INDEX), .write_data(index));

               // Read data
               reg_read(.base_addr(base_addr), .reg_offset(`CL_PKT_TST_RX_DBG_RAM_DATA), .read_data(read_data));

//               $display("  [entry = %02d] [dw = %02d] = 0x%08x", entry_idx, dw_idx, read_data);
               dbg_entry[entry_idx][dw_idx] = read_data[31:0];
            end
         end

         for (entry_idx = 0; entry_idx < 32; entry_idx++) begin
            $display("-------------- Entry %02d ---------------\n", entry_idx);
            for (dw_idx = 0; dw_idx < 2; dw_idx++) begin
               if (dw_idx == 0)
                 $write(" 0x%08x", dbg_entry[entry_idx][dw_idx]); // DEBUG: Usage of $write vs. $display ?
               else begin
                  read_data[31:0] = dbg_entry[entry_idx][dw_idx];
                  $display(" Last: %1b, Phase: %1b", read_data[0], read_data[1]);
               end
            end
         end
      end

      // Report PASS/FAIL status
      if (error_count > 0) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
      end else begin
           $display("[%t] : *** TEST PASSED ***", $realtime);
      end   

      $finish;
   end
endtask


task aurora_test;
   logic [63:0]  base;
   int           plusarg_ret;
   int           aurora_num;
   logic [11:0]  offset;

   plusarg_ret = $value$plusargs("TEST_AURORA=%d", aurora_num);
   if (plusarg_ret == 0) begin
      aurora_num = 99;
   end

   case (aurora_num)
     0 : offset = 12'h000;
     1 : offset = 12'h100;
     2 : offset = 12'h200;
     3 : offset = 12'h300;
     default : offset = 12'h000;
   endcase

   base = 'h900;

aurora_common_test(
                   .cl_base(base + offset)
                  );
endtask

// cl_aurora0_test:
// +SIMPLE_DATA_MODE +SEED0=0x1 +SEED1=0x2 +PKT_LEN_MIN=0x05 +PKT_LEN_MAX=0x30 +RX_DATA_CHK +NUM_PKTS=50

// cl_aurora1_test:
// +PRBS_MODE +PKT_LEN_MODE +SEED0=0x8C010001 +SEED1=0xA1010D01 +PKT_LEN_MIN=0x10 +PKT_LEN_MAX=0x40 +RX_DATA_CHK +RX_PKTLEN_CHK +NUM_PKTS=80

// cl_aurora2_test:
// +PKT_LEN_MODE +SEED0=0xABC995C1 +SEED1=0x7398BC0F +PKT_LEN_MIN=0x30 +PKT_LEN_MAX=0x40 +RX_DATA_CHK +RX_PKTLEN_CHK +NUM_PKTS=40

// cl_aurora3_test:
// +PRBS_MODE +PKT_LEN_MODE +SEED0=0x57498244 +SEED1=0x0847ABDE +PKT_LEN_MIN=0x05 +PKT_LEN_MAX=0x70 +RX_DATA_CHK +RX_PKTLEN_CHK +NUM_PKTS=80
