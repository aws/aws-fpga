// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`timescale 1ns/1ns

task send_msg (bit[31:0] msg[63:0], bit[31:0] msg_length, bit[63:0] mbx_base);
begin
   //Write index to 0
   TSK_MEM_WRITE_64(.addr(mbx_base + 'h00), .data(32'h0));

   for (int i=0; i<=msg_length; i++)
   begin
      TSK_MEM_WRITE_64(.addr(mbx_base + 'h04), .data(msg[i]));
   end

   //Write the command
   TSK_MEM_WRITE_64(.addr(mbx_base + 'h08), .data(msg_length));
end
endtask

//Wait for TX status
task poll_tx_status(bit[63:0] bar);
logic[31:0] rdata;
begin
   rdata = 0;

   fork
   begin
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(5000);
      $display($time,,,"***ERROR*** Wait for TX status timeout bar=0x%x", bar);
      $finish;
   end
   begin
      while (!rdata[1])
      begin
         TSK_MEM_READ_64 (.addr(bar + 'hc), .rdata(rdata));
         if (|rdata[31:16])
         begin
            $display("***ERROR*** something wrong with poll_tx_status read data (upper bits should always be 0), rdata=0x%x", rdata);
            $finish;
         end
      end
   end
   join_any
   disable fork;

   //Clear TX Status
   TSK_MEM_WRITE_64(.addr(bar + 'hc), .data(32'h1));
end
endtask

//Wait or RX status
task poll_rx_status(bit[63:0] bar);
logic[31:0] rdata;
begin
   rdata = 0;

   fork
   begin
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(1000);
      $display($time,,,"***ERROR*** Wait for RX status timeout bar=0x%x", bar);
      $finish;
   end
   begin
      while (!rdata[0])
      begin
         TSK_MEM_READ_64 (.addr(bar + 'hc), .rdata(rdata));
         if (|rdata[31:16])
         begin
            $display("***ERROR*** something wrong with poll_rx_status read data (upper bits should always be 0), rdata=0x%x", rdata);
            $finish;
         end
      end
   end
   join_any
   disable fork;
end
endtask
      
task read_msg (bit[31:0] msg[63:0], bit[31:0] msg_length, bit[63:0] mbx_base);
logic[31:0] rdata;
begin
   //Read RX CMD and verify length
   TSK_MEM_READ_64 (.addr(mbx_base + 'h18), .rdata(rdata));
   if (rdata!=msg_length)
   begin
      $display($time,,,"***ERROR*** ReadMsg length mismatch expected=0x%x, read=0x%x", msg_length, rdata);
      $finish;
   end

   //Inialize RX index
   TSK_MEM_WRITE_64(.addr(mbx_base + 'h10), .data(0));
   for (int i=0; i<=msg_length; i++)
   begin
      TSK_MEM_READ_64 (.addr(mbx_base + 'h14), .rdata(rdata));
      if (rdata != msg[i])
      begin
         $display($time,,,"***ERROR*** ReadData miscompare index=%d, expected=0x%x, read=0x%x", i, msg[i], rdata);
         $finish;
      end
   end

   
end
endtask

task clear_rx_status (bit[63:0] bar);
begin
   //Clear RX Status
   TSK_MEM_WRITE_64(.addr(bar + 'hc), .data(32'h1));
end
endtask
      
      
      
   

task dev_mbx_test;
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

   TSK_SYSTEM_INITIALIZATION;
   
   TSK_TYPE0_CFG_READ(12'h00, read_data, EP_BUS_DEV_FNS_PF1);
   $display($time,,,"PF1 VendorID/DeviceID=0x%x", read_data);

   //tb.RP.tx_usrapp.TSK_BAR_INIT;
   domu_bar = 64'h1000_0000_0000_0000;
   dom0_bar = 64'h2000_0000_0000_0000;
   dom0_mbx_bar = 64'h3000_0000_0000_0000;
   
   //tgt_bar0 = {tb.RP.tx_usrapp.BAR_INIT_P_BAR[1][31:0],  tb.RP.tx_usrapp.BAR_INIT_P_BAR[0][31:0]};


   TSK_TYPE0_CFG_WRITE(12'h10, domu_bar[31:00], EP_BUS_DEV_FNS_PF1);
   TSK_TYPE0_CFG_WRITE(12'h14, domu_bar[63:32], EP_BUS_DEV_FNS_PF1);

   TSK_TYPE0_CFG_WRITE(12'h10, dom0_bar[31:00], EP_BUS_DEV_FNS_PF2);
   TSK_TYPE0_CFG_WRITE(12'h14, dom0_bar[63:32], EP_BUS_DEV_FNS_PF2);

   TSK_TYPE0_CFG_WRITE(12'h20, dom0_mbx_bar[31:00], EP_BUS_DEV_FNS_PF2);
   TSK_TYPE0_CFG_WRITE(12'h24, dom0_mbx_bar[63:32], EP_BUS_DEV_FNS_PF2);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'h78, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07  , EP_BUS_DEV_FNS);

   TSK_TYPE0_CFG_WRITE(12'h78, 32'h505f, EP_BUS_DEV_FNS_PF1);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07  , EP_BUS_DEV_FNS_PF1);

   TSK_TYPE0_CFG_WRITE(12'h78, 32'h505f, EP_BUS_DEV_FNS_PF2);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07  , EP_BUS_DEV_FNS_PF2);

   
   
   //Make sure all completions have been received
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(100);
   

   //----------------------------
   // Program write instructions
   //----------------------------

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
   TSK_MEM_WRITE_64(.addr(dom0_bar + 'h1500), .data(32'h1234_1234));
   TSK_MEM_READ_64 (.addr(dom0_bar + 'h1500), .rdata(read_data));
   TSK_MEM_WRITE_64(.addr(dom0_bar + 'h16f0), .data(32'h1234_1234));
   TSK_MEM_READ_64 (.addr(dom0_bar + 'h16fc), .rdata(read_data));

   TSK_MEM_READ_64 (.addr(domu_bar + 'h0000), .rdata(read_data));


   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20);
   $display($time,,,"!!!TEST PASSED!!!");
   $finish;
end
endtask


