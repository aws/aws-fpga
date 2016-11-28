// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`timescale 1ns/1ns
task bu_atg_test;
begin

   // Fixed values for initial testing
   logic [7:0]   wr_index = 8'h00;
   logic [7:0]   wr_len = 8'h07; // 512 byte writes
   logic [15:0]  num_inst = 16'h0; // Single write and read
   logic [7:0]   rd_index = 8'h00;
   logic [7:0]   rd_len = 8'h07; // 512 byte reads

   // Test variables
   logic [63:0]  tgt_bar0;
   logic [63:0]  loop_count;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic [63:0]  error_addr;
   logic [3:0]   error_index;

   int to_count;

   // This test performs a 32 bit write to a 32 bit Memory space and performs a read back

//OLD    tb.RP.tx_usrapp.TSK_SIMULATION_TIMEOUT(10050);

   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;

//OLD    tb.RP.tx_usrapp.TSK_BAR_INIT;
//OLD    
//OLD    tgt_bar0 = {tb.RP.tx_usrapp.BAR_INIT_P_BAR[1][31:0],  tb.RP.tx_usrapp.BAR_INIT_P_BAR[0][31:0]};
//OLD 
//OLD    // Set MPS, BusMaster, MemEnable
//OLD    TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'hc8, 32'h505f, 4'hF);
//OLD    TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'h04, 32'h07, 4'hF);

   tgt_bar0 = 64'h0000_1000_0000_0000;

   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

   //----------------------------
   // Program write instructions
   //----------------------------
   // Enable TG0
   $display($time,,,"Setting 0");
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1000), .data(32'h00000001));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1100), .data(32'h00000001));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1200), .data(32'h00000001));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1300), .data(32'h00000001));
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(100000);
   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h10a0), .rdata(read_data));
   $display($time,,,"CYC_COUNT=0x%x", read_data);
   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h10a8), .rdata(read_data));
   $display($time,,,"TIME=0x%x", read_data);

   $finish;
end
endtask


