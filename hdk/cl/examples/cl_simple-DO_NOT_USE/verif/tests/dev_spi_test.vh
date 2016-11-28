// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`timescale 1ns/1ns

task bu_spi_test;
begin

   // Test variables
   logic [63:0]  domu_bar;
   logic [63:0]  dom0_bar;
   logic [63:0]  dom0_mbx_bar;
   logic [31:0]  write_data;
   logic [31:0]  read_data;

   bit[31:0] msg[63:0];              //Max message for this test is 4 DW
   bit[31:0] msg_length;

   int to_count;

   // This test performs a 32 bit write to a 32 bit Memory space and performs a read back

   tb.RP.tx_usrapp.TSK_SIMULATION_TIMEOUT(10050);

   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;
   
   tb.RP.tx_usrapp.TSK_TX_TYPE0_CONFIGURATION_READ_PF1(DEFAULT_TAG, 12'h00, 4'hf);
   tb.RP.tx_usrapp.TSK_WAIT_FOR_READ_DATA;
   $display($time,,,"PF1 VendorID/DeviceID=0x%x", tb.RP.tx_usrapp.P_READ_DATA);

   //tb.RP.tx_usrapp.TSK_BAR_INIT;
   domu_bar = 64'h1000_0000_0000_0000;
   dom0_bar = 64'h2000_0000_0000_0000;
   dom0_mbx_bar = 64'h3000_0000_0000_0000;
   
   //tgt_bar0 = {tb.RP.tx_usrapp.BAR_INIT_P_BAR[1][31:0],  tb.RP.tx_usrapp.BAR_INIT_P_BAR[0][31:0]};

   TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'h10, domu_bar[31:00], 4'hf);
   TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'h14, domu_bar[63:32], 4'hf);

   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'h10, dom0_bar[31:00], 4'hf);
   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'h14, dom0_bar[63:32], 4'hf);

   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'h20, dom0_mbx_bar[31:00], 4'hf);
   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'h24, dom0_mbx_bar[63:32], 4'hf);

   // Set MPS, BusMaster, MemEnable
   TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'hc8, 32'h505f, 4'hF);
   TSK_TX_TYPE0_CONFIGURATION_WRITE(DEFAULT_TAG, 12'h04, 32'h07, 4'hF);

   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'hc8, 32'h505f, 4'hF);
   TSK_TX_TYPE0_CONFIGURATION_WRITE_PF1(DEFAULT_TAG, 12'h04, 32'h07, 4'hF);

   //Make sure all completions have been received
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(100);
   

   //----------------------------
   // Program write instructions
   //----------------------------

   //Read the version register
   UC_SPI_MODEL.spi_rd(.addr(0), .exp_data(0), .compare(0), .rdata(read_data));
   if (read_data[31:16]!=16'hface)
   begin
      $display($time,,,"***ERROR*** Version register compare fail expected [31:16]=0xface, read=0x%x", read_data[31:16]);
      $finish;
   end

   UC_SPI_MODEL.spi_wr(.addr('hf0), .wdata(32'habcd1234));
   UC_SPI_MODEL.spi_wr(.addr('hf4), .wdata(32'h9876fdcb));
  
   UC_SPI_MODEL.spi_rd(.addr('hf0), .exp_data(32'habcd1234), .compare(1), .rdata(read_data));
   UC_SPI_MODEL.spi_rd(.addr('hf4), .exp_data(32'h9876fdcb), .compare(1), .rdata(read_data));
   

   //Dom0 to DomU
   msg[0] = 32'hc111_aaaa;
   msg[1] = 32'hc222_bbbb;
   msg[2] = 32'hc333_cccc;
   msg[3] = 32'hc444_dddd;

   msg_length = 3;

   $display($time,,,"Send MSG from Dom0 to DomU");
   send_msg(.msg(msg), .msg_length(msg_length), .mbx_base(dom0_mbx_bar + 'h20));
   $display($time,,,"Read MSG from Dom0 to DomU");
   poll_rx_status(.bar(domu_bar));
   read_msg(.msg(msg), .msg_length(msg_length), .mbx_base(domu_bar + 'h20)); 
   clear_rx_status(.bar(domu_bar));
   $display($time,,,"Pol TX Status from Dom0 to DomU");
   poll_tx_status(.bar(dom0_mbx_bar));

   //DomU to Dom0
   msg[0] = 32'h1234_abcd;
   msg[1] = 32'h5678_fdcb;
   msg[2] = 32'ha123_f1d2;
   msg[3] = 32'h5103_da1a;

   msg_length = 3;

   $display($time,,,"Send MSG from DomU to Dom0");
   send_msg(.msg(msg), .msg_length(msg_length), .mbx_base(domu_bar + 'h20));
   $display($time,,,"Read MSG from DomU to Dom0");
   poll_rx_status(.bar(dom0_mbx_bar));
   read_msg(.msg(msg), .msg_length(msg_length), .mbx_base(dom0_mbx_bar + 'h20)); 
   clear_rx_status(.bar(dom0_mbx_bar));
   $display($time,,,"Pol TX Status from DomU to Dom0");
   poll_tx_status(.bar(domu_bar));

   //HACK in Temp ICAP stuff
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(dom0_bar + 'h1500), .data(32'h1234_1234));
   tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(dom0_bar + 'h1500), .rdata(read_data));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(dom0_bar + 'h16f0), .data(32'h1234_1234));
   tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(dom0_bar + 'h16fc), .rdata(read_data));

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20);
   $display($time,,,"!!!TEST PASSED!!!");
   $finish;
end
endtask


