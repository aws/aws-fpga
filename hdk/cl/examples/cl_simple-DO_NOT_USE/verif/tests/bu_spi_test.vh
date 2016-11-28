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

   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;

   dom0_bar = 64'h0000_1000_0000_0000;
   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, dom0_bar[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, dom0_bar[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);
  
 
   //Make sure all completions have been received
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(100);
   

   //----------------------------
   // Program write instructions
   //----------------------------

   //Read the version register
   UC_SPI_MODEL.spi_read(.addr(0), .exp_data(0), .compare(0), .read_data(read_data));
   `ifdef FPGA_VERSION
      if (read_data!=`FPGA_VERSION)
      begin
         $display($time,,,"***ERROR*** Version register compare fail expected=0x%x, read=0x%x", `FPGA_VERSION, read_data[31:0]);
         $finish;
      end
   `endif

   UC_SPI_MODEL.spi_write(.addr('hf0), .write_data(32'habcd1234));
   UC_SPI_MODEL.spi_write(.addr('hf4), .write_data(32'h9876fdcb));
  
   UC_SPI_MODEL.spi_read(.addr('hf0), .exp_data(32'habcd1234), .compare(1), .read_data(read_data));
   UC_SPI_MODEL.spi_read(.addr('hf4), .exp_data(32'h9876fdcb), .compare(1), .read_data(read_data));
  
   //Version 
   UC_SPI_MODEL.spi_gen(.cmd('d5), .read_data(read_data));
   `ifdef FPGA_VERSION
      if (read_data!=`FPGA_VERSION)
      begin
         $display($time,,,"***ERROR*** Version register compare fail expected=0x%x, read=0x%x", `FPGA_VERSION, read_data);
         $finish;
      end
   `endif

   //Magic
   UC_SPI_MODEL.spi_gen(.cmd('d6), .read_data(read_data));
   if (read_data!=32'hc001c0de)
   begin
      $display($time,,,"***ERROR*** Version register compare fail expected=0xc001c0de, read=0x%x", read_data);
      $finish;
   end

   $display($time,,,"NOTE: Before clear");
   //LTSSM Status 0,1
   UC_SPI_MODEL.spi_read(.addr('h200), .exp_data(32'h00017ff7), .compare(1), .read_data(read_data), .cmd(8'h08));
   UC_SPI_MODEL.spi_read(.addr('h204), .exp_data(32'h00100300), .compare(1), .read_data(read_data), .cmd(8'h08));

   //Clear status
   UC_SPI_MODEL.spi_write(.addr('h200), .write_data(32'hffffffff), .cmd(8'h07));

   $display($time,,,"NOTE: After clear");
   //LTSSM Status 0,1 -- Again after clear
   UC_SPI_MODEL.spi_read(.addr('h200), .exp_data(32'h00010000), .compare(0), .read_data(read_data), .cmd(8'h08));
   UC_SPI_MODEL.spi_read(.addr('h204), .exp_data(32'h00100000), .compare(0), .read_data(read_data), .cmd(8'h08));

   //Write the divider register
   UC_SPI_MODEL.spi_write(.addr('h80), .write_data(32'h00000010), .cmd(8'h07));
   UC_SPI_MODEL.spi_read(.addr('h80), .exp_data(32'h00000010), .compare(1), .read_data(read_data), .cmd(8'h08));

   UC_SPI_MODEL.spi_write(.addr('h84), .write_data(32'h00550004), .cmd(8'h07));

   //////Dom0 to DomU
   ////msg[0] = 32'hc111_aaaa;
   ////msg[1] = 32'hc222_bbbb;
   ////msg[2] = 32'hc333_cccc;
   ////msg[3] = 32'hc444_dddd;

   ////msg_length = 3;

   ////$display($time,,,"Send MSG from Dom0 to DomU");
   ////send_msg(.msg(msg), .msg_length(msg_length), .mbx_base(dom0_mbx_bar + 'h20));
   ////$display($time,,,"Read MSG from Dom0 to DomU");
   ////poll_rx_status(.bar(domu_bar));
   ////read_msg(.msg(msg), .msg_length(msg_length), .mbx_base(domu_bar + 'h20)); 
   ////clear_rx_status(.bar(domu_bar));
   ////$display($time,,,"Pol TX Status from Dom0 to DomU");
   ////poll_tx_status(.bar(dom0_mbx_bar));

   //////DomU to Dom0
   ////msg[0] = 32'h1234_abcd;
   ////msg[1] = 32'h5678_fdcb;
   ////msg[2] = 32'ha123_f1d2;
   ////msg[3] = 32'h5103_da1a;

   ////msg_length = 3;

   ////$display($time,,,"Send MSG from DomU to Dom0");
   ////send_msg(.msg(msg), .msg_length(msg_length), .mbx_base(domu_bar + 'h20));
   ////$display($time,,,"Read MSG from DomU to Dom0");
   ////poll_rx_status(.bar(dom0_mbx_bar));
   ////read_msg(.msg(msg), .msg_length(msg_length), .mbx_base(dom0_mbx_bar + 'h20)); 
   ////clear_rx_status(.bar(dom0_mbx_bar));
   ////$display($time,,,"Pol TX Status from DomU to Dom0");
   ////poll_tx_status(.bar(domu_bar));

   //////HACK in Temp ICAP stuff
   ////tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(dom0_bar + 'h1500), .data(32'h1234_1234));
   ////tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(dom0_bar + 'h1500), .rdata(read_data));
   ////tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(dom0_bar + 'h16f0), .data(32'h1234_1234));
   ////tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(dom0_bar + 'h16fc), .rdata(read_data));

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(200);
   $display($time,,,"!!!TEST PASSED!!!");
   $finish;
end
endtask


