// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


task hmc_common_test(input logic [63:0] cl_base);

begin


   // Test variables
   logic [63:0]  tgt_bar0;
   logic [63:0]  pkt_cnt;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic done;
   logic rx_lock_err;
   logic rx_data_err;
   logic rx_pktlen_err;

   done = 0;

   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;

//TODO: TEMP   tgt_bar0 = {tb.RP.tx_usrapp.BAR_INIT_P_BAR[1][31:0],  tb.RP.tx_usrapp.BAR_INIT_P_BAR[0][31:0]};
   tgt_bar0 = 64'h0000_1000_0000_0000;

   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

   #50us;

   // Read Version register to get linkup
   done = 0;
   while (done == 0) begin
   
      TSK_MEM_READ_64(tgt_bar0 + cl_base + 64'h4, read_data);
      done = (read_data[11:8] === 4'hF);
   end

   $display("TEST PASSED!!!!");
   
   $finish;
end
endtask


task cl_hmc0_test;

hmc_common_test(.cl_base(64'h0000_0000_0000_0000));


endtask //cl_hmc0_test


