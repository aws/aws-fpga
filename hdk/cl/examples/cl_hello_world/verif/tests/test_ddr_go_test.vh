// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================


`timescale 1ns/1ns

   

//--------------------------------------------------
// Just write the DDR go bits, then poll stress
//--------------------------------------------------
task test_ddr_go_test;
begin

   // Test variables
   logic [63:0]  tgt_bar0;
   logic[31:0] offset;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic done;
   logic error;

   // This test performs a 32 bit write to a 32 bit Memory space and performs a read back
   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;
   tgt_bar0 = 64'h0000_1000_0000_0000;

   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

   $display("Dummy read of version register");
   TSK_MEM_READ_64(.addr(tgt_bar0 + 64'h0), .rdata(read_data));
   $display("Version register read value - 0x%08x", read_data);

   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1000), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1100), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1200), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1300), .data(32'h1));

   //Temp set the power enables
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'he0), .data(32'h00ffffff));
   
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(3500);

   error =0 ;
   for (int i=0; i<4; i++)
   begin
      offset = 32'h1030 + (256 * i);
      TSK_MEM_READ_64 (.addr(tgt_bar0 + offset), .rdata(read_data));
      if (read_data!=32'h103)
      begin
         $display($time,,,"***ERROR*** Status=0x%x, expected=0x103 status on DDR%d", read_data, i);
         error = 1;
      end

      offset = 32'h1034 + (256 * i);
      TSK_MEM_READ_64 (.addr(tgt_bar0 + offset), .rdata(read_data));
      if (read_data[0]!=0)
      begin
         $display($time,,,"***ERROR*** Error status is not clear on DDR%d", i);
         error = 1;
      end

      offset = 32'h10a0 + (256 * i);
      TSK_MEM_READ_64 (.addr(tgt_bar0 + offset), .rdata(read_data));
      if (read_data==32'h0)
      begin
         $display($time,,,"***ERROR*** Count is 0 for DDR%d", i);
         error = 1;
      end
   
   end
      
   


   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20);
   if (!error)
      $display($time,,,"!!!TEST PASSED!!!");
   $finish;
end
endtask

