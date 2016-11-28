// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`timescale 1ns/1ns

   

task dev_hmc_test;
begin

   // Test variables
   logic [63:0]  domu_bar;
   logic [63:0]  dom0_bar;
   logic [63:0]  dom0_mbx_bar;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic done;

   TSK_SYSTEM_INITIALIZATION;
   
   TSK_TYPE0_CFG_READ(12'h00, read_data, EP_BUS_DEV_FNS_PF1);
   $display($time,,,"PF1 VendorID/DeviceID=0x%x", read_data);

   //tb.RP.tx_usrapp.TSK_BAR_INIT;
   domu_bar = 64'h1000_0000_0000_0000;
   dom0_bar = 64'h2000_0000_0000_0000;
   dom0_mbx_bar = 64'h3000_0000_0000_0000;
   
   //tgt_bar0 = {tb.RP.tx_usrapp.BAR_INIT_P_BAR[1][31:0],  tb.RP.tx_usrapp.BAR_INIT_P_BAR[0][31:0]};

   TSK_TYPE0_CFG_WRITE(12'h10, domu_bar[31:00], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, domu_bar[63:32], EP_BUS_DEV_FNS);

   TSK_TYPE0_CFG_WRITE(12'h10, dom0_bar[31:00], EP_BUS_DEV_FNS_PF1);
   TSK_TYPE0_CFG_WRITE(12'h14, dom0_bar[63:32], EP_BUS_DEV_FNS_PF1);

   TSK_TYPE0_CFG_WRITE(12'h20, dom0_mbx_bar[31:00], EP_BUS_DEV_FNS_PF1);
   TSK_TYPE0_CFG_WRITE(12'h24, dom0_mbx_bar[63:32], EP_BUS_DEV_FNS_PF1);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07  , EP_BUS_DEV_FNS);

   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS_PF1);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07  , EP_BUS_DEV_FNS_PF1);

   //Make sure all completions have been received
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(100);
   
   $display($time,,,"Waiting for HMC Linkup");

   // Read Version register to get linkup
   done = 0;
   while (done == 0) begin
   
      TSK_MEM_READ_64(dom0_bar + 64'h0, read_data);
      done = (read_data[11:8] === 4'hF);
   end

   $display($time,,,"Got HMC Linkup");

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20);
   $display($time,,,"!!!TEST PASSED!!!");
   $finish;
end
endtask

task dev_hmc0_test;
     dev_hmc_test;
endtask
     
