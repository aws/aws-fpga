`define SPISRR 64'h1440
`define SPICR  64'h1460
`define SPISR  64'h1464
`define SPIDTR 64'h1468
`define SPIDRR 64'h146C
`define SPISSR 64'h1470
`define SPITFO 64'h1474
`define SPIRDO 64'h1478
`define SPIDGIER 64'h141C
`define SPIIPISR 64'h1420
`define SPIIPIER 64'h1428

task reset_fifos(input logic [63:0] tgt_bar0);
     logic [31:0] read_data;

  // Reset Tx and Rx FIFOs
  TSK_MEM_WRITE_64(tgt_bar0 + `SPICR, 32'h6);

  // Wait for 10 axi clocks
  // Just read status register 10 times
  for (int idx = 0; idx < 10; idx++) begin
    TSK_MEM_READ_64 (tgt_bar0 + `SPISR, read_data);
  end
endtask

task reset_qspi(input logic [63:0] tgt_bar0);
     logic [31:0] read_data;

  TSK_MEM_WRITE_64(tgt_bar0 + `SPISRR, 32'hA);

  // Wait for 10 axi clocks
  // Just read status register 10 times
  for (int idx = 0; idx < 10; idx++) begin
    TSK_MEM_READ_64 (tgt_bar0 + `SPISR, read_data);
  end

  reset_fifos(tgt_bar0);
endtask

task transfer_bytes (input logic [63:0] tgt_bar0, input int num_bytes, input logic [7:0] tx_data[], output logic [7:0] rx_data[], input bit no_rx, input bit debug);

  int byte_idx;
  logic tx_empty;
  logic rx_empty;
  logic [31:0] rdata;

  tx_empty = 0;
  rx_empty = 0;

  // Reset QSPI and FIFOs - Start fresh
  reset_qspi(tgt_bar0);
  
  // Write SPICR - Set Master Inhibit Bit
  TSK_MEM_WRITE_64(tgt_bar0 + `SPICR, 32'h100);
  //  fpga_write (SPICR, 0x00000100);
  
  // Write SPISSR - Slave 0 select
  TSK_MEM_WRITE_64(tgt_bar0 + `SPISSR, 32'hFFFFFFFE);
  // fpga_write (SPISSR, 0xFFFFFFFE);

  // Write data bytes to Tx FIFO
  for (byte_idx = 0; byte_idx < num_bytes; byte_idx++) begin
    if (debug) $display("transfer_bytes: Writing into TX FIFO: Byte:%3d, Data:0x%02x", byte_idx, tx_data[byte_idx]);
     TSK_MEM_WRITE_64(tgt_bar0 + `SPIDTR, tx_data[byte_idx]);
    //fpga_write (SPIDTR, tx_data[byte_idx]);
  end
  if (debug) $display("transfer_bytes: Done writing into TX FIFO");
  
  // Write SPICR - Set Enable, Clear Master Inhibit Bit
  //fpga_write (SPICR, 0x00000086);
  TSK_MEM_WRITE_64(tgt_bar0 + `SPICR, 32'h86);

  if (no_rx == 1) begin
    // Poll for TX Empty
    tx_empty = 0;
    if (debug) $display("transfer_bytes: Waiting for TX Complete");
    while (tx_empty == 0) begin
      //rdata = fpga_read(SPISR);
      // tx_empty = (rdata & 0x4) >> 2;
      TSK_MEM_READ_64(tgt_bar0 + `SPISR, rdata);
      tx_empty = rdata[2];
    end
    if (debug) $display("transfer_bytes: Got TX Complete");
  end
  else begin
    // Wait for Rx FIFO not empty
    rx_empty = 1;
    if (debug) $display("transfer_bytes: Waiting for RX Data");
    while (rx_empty == 1) begin
      // rdata = fpga_read(SPISR);
      //rx_empty = rdata & 0x1;
      TSK_MEM_READ_64(tgt_bar0 + `SPISR, rdata);
      rx_empty = rdata[0];
    end
    if (debug) $display("transfer_bytes: Got Data in RX Fifo. Starting to read RX FIFO");

    // Read out the bytes from Rx fifo
    for (byte_idx = 0; byte_idx < num_bytes; byte_idx++) begin
      // Read data
      // rdata = fpga_read(SPIDRR);
      // rx_data[byte_idx] = rdata & 0xFF;
      TSK_MEM_READ_64(tgt_bar0 + `SPIDRR, rdata);
      rx_data[byte_idx] = rdata[7:0];
      if (debug) $display("transfer_bytes: Read from RX FIFO: Byte:%3d, Data:0x%02x", byte_idx, rx_data[byte_idx]);
    end
  end
  
//   // Santiy Check
//   rdata = fpga_read(SPISR);
//   tx_empty = (rdata & 0x4)>>2;
//   if (tx_empty != 1) begin
//       $display("Error: TX FIFO is still Not empty after writing %3d bytes!!", num_bytes);
//   end
// 
//   if (no_rx == 0) begin
//     rx_empty = rdata & 0x1;
//     if (rx_empty != 1) begin
//       $display("Error: RX FIFO is still Not empty after reading %3d bytes!!", num_bytes);
//     end
//   end
//   
//   // Write SPISSR - Slave 0 select
//   fpga_write (SPISSR, 0xFFFFFFFF);
// 
// 
//   // Clear SPI Enable and set Master Inhibit
//   fpga_write (SPICR, 0x00000100);

  
endtask

task read_id (input logic [63:0] tgt_bar0, input bit debug);
  
  logic [7:0] rx_data[];
  logic [7:0] tx_data[];
  int num_bytes;
  int byte_idx;
  
  num_bytes = 2;
  rx_data = new[num_bytes];
  tx_data = new[num_bytes];

  // Command and dummy bytes
  tx_data[0] = 8'h9E;
  $display("read_id : Tx Command = 0x%02x", tx_data[0]);
  for (byte_idx = 1; byte_idx < num_bytes; byte_idx++) begin
    tx_data[byte_idx] = byte_idx & 8'hFF;
  end

  transfer_bytes(tgt_bar0, num_bytes, tx_data, rx_data, 0, debug);

  // Got the following bytes
  // Byte 0 is Junk. Print from byte 1
  for (byte_idx = 1; byte_idx < num_bytes; byte_idx++) begin
    $display("read_id : rx_data[%3d] = 0x%02x", byte_idx, rx_data[byte_idx]);
  end
  
endtask


task qspi_test ();
     

   // Test variables
   logic [63:0]  tgt_bar0;
   logic [63:0]  pkt_cnt;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic done;

   done = 0;

   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;

   tgt_bar0 = 64'h0000_1000_0000_0000;

   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h14, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

   read_id(tgt_bar0, 1);

   $display("QSPI Task is Complete. Test is done");
   $finish;

endtask


