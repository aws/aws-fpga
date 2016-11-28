// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task mbx_test();
   begin

      // Test variables
      logic [63:0]  domu_mbx_bar;
      logic [63:0]  dom0_mbx_bar;

      logic [63:0]  domu_mbx_bar;
      logic [63:0]  dom0_bar;

      logic [15:0]  domu_pf;
      logic [15:0]  dom0_pf;

      bit [31:0]    mbx_msg[63:0]; // Max message for this test is 4 DW
      bit [31:0]    mbx_msg_length;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      bit           check_msix;

      int           entry_idx;
      int           dw_idx;
      logic [31:0]  axis_dbg_entry [31:0][5:0];
      logic [31:0]  axil_dbg_entry [31:0][3:0];

      logic         enable_pci_trace = 0;
      
      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      domu_pf = EP_BUS_DEV_FNS_PF1;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(domu_pf), .bar_addr(domu_mbx_bar));
`ifndef NO_XDMA
      get_bar(.bar_num(2), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`else
      get_bar(.bar_num(4), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`endif
      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_bar));

`ifndef NO_XDMA
      // Dom0 and DomU MSI-X don't exist in XDMA design
      check_msix = 1'b0;
`else
      if ($test$plusargs("NO_MSIX")) begin
         check_msix = 1'b0;
      end else begin
         check_msix = 1'b1;
      end
`endif

      if (enable_pci_trace) begin
         // Enable the AXIS and AXIL tracing for Function 1 and BAR 0
         reg_write(.base_addr(dom0_bar), .reg_offset(12'h400), .write_data(32'h0000_0011), .comp_id(dom0_pf));
         reg_write(.base_addr(dom0_bar), .reg_offset(12'h410), .write_data(32'h0000_0011), .comp_id(dom0_pf));
      end
      
      wait_for_clock(100);

      //----------------------------
      // Program write instructions
      //----------------------------

      // Enable DomU Mailbox 0 RX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data | (1'b1 << 0);  // Mailbox 0 RX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      // Dom0 to DomU
      mbx_msg[0] = 32'hc111_aaaa;
      mbx_msg[1] = 32'hc222_bbbb;
      mbx_msg[2] = 32'hc333_cccc;
      mbx_msg[3] = 32'hc444_dddd;

      mbx_msg_length = 4;

      $display("[%t] : Sending message from Dom0 to DomU (Mailbox 0)", $realtime);
      send_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(dom0_mbx_bar + 'h20), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for DomU RX interrupt (Mailbox 0)...", $realtime);
         wait_for_msix_intr(.comp_id(domu_pf));
      end else begin
         $display("[%t] : DomU polling for Mailbox 0 RX event...", $realtime);
         poll_mbx_rx_status(.bar(domu_mbx_bar), .comp_id(domu_pf), .status_bit(0)); // Bit [0] is Mailbox 0 RX event
      end

      $display("[%t] : DomU reading message from Mailbox 0", $realtime);
      read_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(domu_mbx_bar + 'h20), .comp_id(domu_pf));

      $display("[%t] : DomU clearing Mailbox 0 RX event", $realtime);
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h00c), .write_data(32'h0000_0001), .comp_id(domu_pf));

      $display("[%t] : Dom0 polling for Mailbox 0 TX event...", $realtime);
      poll_mbx_tx_status(.bar(dom0_mbx_bar), .comp_id(dom0_pf), .status_bit(1)); // Bit [1] is Mailbox 0 TX event

      $display("[%t] : Dom0 clearing Mailbox 0 TX event", $realtime);
      reg_write(.base_addr(dom0_mbx_bar), .reg_offset(12'h00c), .write_data(32'h0000_0002), .comp_id(domu_pf));

      // Disable DomU Mailbox 0 RX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data & ~(32'h0000_0001);  // Clear bit [0], Mailbox 0 RX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      // Enable DomU Mailbox 1 TX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data | (1'b1 << 1);  // Mailbox 1 TX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      // DomU to Dom0
      mbx_msg[0] = 32'h1234_abcd;
      mbx_msg[1] = 32'h5678_fdcb;
      mbx_msg[2] = 32'ha123_f1d2;
      mbx_msg[3] = 32'h5103_da1a;

      mbx_msg_length = 4;

      $display("[%t] : Sending message from DomU to Dom0 (Mailbox 1)", $realtime);
      send_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(domu_mbx_bar + 'h20), .comp_id(domu_pf));

      $display("[%t] : Dom0 polling for Mailbox 1 RX event...", $realtime);
      poll_mbx_rx_status(.bar(dom0_mbx_bar), .comp_id(dom0_pf), .status_bit(0)); // Bit [0] is Mailbox 1 RX event

      $display("[%t] : Dom0 reading message from Mailbox 1", $realtime);
      read_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(dom0_mbx_bar + 'h20), .comp_id(dom0_pf));

      $display("[%t] : Dom0 clearing Mailbox 1 RX event", $realtime);
      reg_write(.base_addr(dom0_mbx_bar), .reg_offset(12'h00c), .write_data(32'h0000_0001), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for DomU TX interrupt (Mailbox 1)...", $realtime);
         wait_for_msix_intr(.comp_id(domu_pf));
      end else begin
         $display("[%t] : DomU polling for Mailbox 1 TX event...", $realtime);
         poll_mbx_tx_status(.bar(domu_mbx_bar), .comp_id(domu_pf), .status_bit(1)); // Bit [1] is Mailbox 1 TX event
      end

      $display("[%t] : DomU clearing Mailbox 1 TX event", $realtime);
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h00c), .write_data(32'h0000_0002), .comp_id(domu_pf));

      // Disable DomU Mailbox 1 TX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data & ~(32'h0000_0002);  // Clear bit [1], Mailbox 1 TX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      wait_for_clock(20);

      if (enable_pci_trace) begin
         
         // Read the trace
         reg_write(.base_addr(dom0_bar), .reg_offset(12'h400), .write_data(32'h0000_0011), .comp_id(dom0_pf));
         reg_write(.base_addr(dom0_bar), .reg_offset(12'h410), .write_data(32'h0000_0011), .comp_id(dom0_pf));

         $display("[%t] : Reading AXIS RAM", $realtime);
         // Read the 3 entries of debug RAM 
         for (entry_idx = 0; entry_idx < 8; entry_idx++) begin
            reg_write(.base_addr(dom0_bar), .reg_offset(12'h404), .write_data(entry_idx), .comp_id(dom0_pf));
            for (dw_idx = 0; dw_idx < 6; dw_idx++) begin
               reg_write(.base_addr(dom0_bar), .reg_offset(12'h408), .write_data(dw_idx), .comp_id(dom0_pf));
               reg_read (.base_addr(dom0_bar), .reg_offset(12'h40C), .read_data(read_data), .comp_id(dom0_pf));

               axis_dbg_entry[entry_idx][dw_idx] = read_data[31:0];
            end
         end // for (entry_idx = 0; entry_idx < 4; entry_idx++)
         
         $display("[%t] : Reading AXI-L RAM", $realtime);
         // Read the 3 entries of debug RAM 
         for (entry_idx = 0; entry_idx < 8; entry_idx++) begin
            reg_write(.base_addr(dom0_bar), .reg_offset(12'h414), .write_data(entry_idx), .comp_id(dom0_pf));
            for (dw_idx = 0; dw_idx < 4; dw_idx++) begin
               reg_write(.base_addr(dom0_bar), .reg_offset(12'h418), .write_data(dw_idx), .comp_id(dom0_pf));
               reg_read (.base_addr(dom0_bar), .reg_offset(12'h41C), .read_data(read_data), .comp_id(dom0_pf));

               axil_dbg_entry[entry_idx][dw_idx] = read_data[31:0];
            end
         end // for (entry_idx = 0; entry_idx < 4; entry_idx++)
         
         for (entry_idx = 0; entry_idx < 8; entry_idx++) begin
            $display("\n-------------- AXIS Entry %02d ---------------", entry_idx);
            begin
               logic [159:0] data;
               logic         phase;
               logic         cc_n_cq;
               logic         read_pend;
               logic [191:0] full_entry;
               
               full_entry = {axis_dbg_entry[entry_idx][5], axis_dbg_entry[entry_idx][4], axis_dbg_entry[entry_idx][3], axis_dbg_entry[entry_idx][2], axis_dbg_entry[entry_idx][1], axis_dbg_entry[entry_idx][0]};
               {phase, cc_n_cq, read_pend, data} = full_entry;
               
               $display("Phase : %0b, CC/CQ : %0b, Read Pend : %0b, Data : 0x%08x 0x%08x 0x%08x 0x%08x 0x%08x", phase, cc_n_cq, read_pend, data[159:128], data[127:96], data[95:64], data[63:32], data[31:0]);
               
               //for (dw_idx = 5; dw_idx >= 0; dw_idx--) begin
               //   if (dw_idx < 5)
               //     $write(" 0x%08x", axis_dbg_entry[entry_idx][dw_idx]); // DEBUG: Usage of $write vs. $display ?
               //   else
               //     $write("Phase : %0b, CC/CQ : %0b, Read Pend : %0b, Data : ", axis_dbg_entry[entry_idx][dw_idx][2], axis_dbg_entry[entry_idx][dw_idx][1], axis_dbg_entry[entry_idx][dw_idx][0]);
               //end
            end
         end // for (entry_idx = 0; entry_idx < 8; entry_idx++)

         for (entry_idx = 0; entry_idx < 8; entry_idx++) begin
            $display("\n-------------- AXIL Entry %02d ---------------", entry_idx);
            begin
               logic [127:0] full_entry;
               logic [3:0]   misc;
               logic [31:0]  data;
               logic         rnw;
               logic [63:0]  addr;
               logic         phase;
               
               full_entry = {axil_dbg_entry[entry_idx][3], axil_dbg_entry[entry_idx][2], axil_dbg_entry[entry_idx][1], axil_dbg_entry[entry_idx][0]};
               {phase, misc, data, rnw, addr} = full_entry;
               if (rnw)
                 $display("Phase : %0b, RD: Addr: 0x%016x, Data: 0x%08x, Error: 0x%01x", phase, addr, data, misc[0]);
               else
                 $display("Phase : %0b, WR: Addr: 0x%016x, Data: 0x%08x, Wstrb: 0x%01x", phase, addr, data, misc);
            end
         end // for (entry_idx = 0; entry_idx < 4; entry_idx++)

      end // if (enable_pci_trace)
            
      $display("[%t] : Checking for errors...", $realtime);
      if (error_count > 0) begin
         $display("[%t] : Detected non-zero value for error_count: %d", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        begin
           $display("[%t] : *** TEST PASSED ***", $realtime);
        end

      $finish;
   end
endtask


task send_mbx_msg(
                  input bit [31:0] msg[63:0],
                  bit [31:0]       msg_length,
                  bit [63:0]       mbx_base,
                  logic [15:0]     comp_id = EP_BUS_DEV_FNS
                 );
   begin
      // Write Index
      reg_write(.base_addr(mbx_base), .reg_offset(12'h000), .write_data(32'h0000_0000), .comp_id(comp_id));
      // Write Data
      for (int i = 0; i < msg_length; i++) begin
         reg_write(.base_addr(mbx_base), .reg_offset(12'h004), .write_data(msg[i]), .comp_id(comp_id));
      end
      // TX Cmd
      reg_write(.base_addr(mbx_base), .reg_offset(12'h008), .write_data(msg_length), .comp_id(comp_id));
   end
endtask


task send_spi_mbx_msg(
                      input bit [31:0] msg[63:0],
                      bit [31:0]       msg_length,
                      bit [23:0]       mbx_base
                     );
   begin
      // Write Index
      UC_SPI_MODEL.spi_write(.addr(mbx_base + 24'h000000), .write_data(32'h0000_0000));
      // Write Data
      for (int i = 0; i < msg_length; i++) begin
         UC_SPI_MODEL.spi_write(.addr(mbx_base + 24'h000004), .write_data(msg[i]));
      end
      // TX Cmd
      UC_SPI_MODEL.spi_write(.addr(mbx_base + 24'h000008), .write_data(msg_length));
   end
endtask


task poll_mbx_tx_status(
                        input bit [63:0] bar,
                        logic [15:0]     comp_id = EP_BUS_DEV_FNS,
                        int              status_bit = 0
                       );
   logic [31:0]  read_data;

   begin
      fork
         begin
            wait_for_clock(5000);
            $display("[%t] : *** ERROR *** Timeout waiting for TX status, BAR 0x%016x", $realtime, bar);
            $finish;
         end
         begin
            do begin
               reg_read(.base_addr(bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(comp_id));
            end while (read_data[status_bit] !== 1'b1);
         end
      join_any
      disable fork;
   end
endtask


task poll_spi_mbx_tx_status(
                            int status_bit = 0
                           );
   logic [31:0]  read_data;

   begin
      fork
         begin
            wait_for_clock(5000);
            $display("[%t] : *** ERROR *** Timeout waiting for TX status, SPI", $realtime);
            $finish;
         end
         begin
            do begin
               UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
            end while (read_data[status_bit] !== 1'b1);
         end
      join_any
      disable fork;
   end
endtask


task poll_mbx_rx_status(
                        input bit [63:0] bar,
                        logic [15:0]     comp_id = EP_BUS_DEV_FNS,
                        int              status_bit = 0
                       );
   logic [31:0]  read_data;

   begin
      fork
         begin
            wait_for_clock(1000);
            $display("[%t] : *** ERROR *** Timeout waiting for RX status, BAR 0x%016x", $realtime, bar);
            $finish;
         end
         begin
            do begin
               reg_read(.base_addr(bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(comp_id));
            end while (read_data[status_bit] !== 1'b1);
         end
      join_any
      disable fork;
   end
endtask


task poll_spi_mbx_rx_status(
                            int status_bit = 0
                           );
   logic [31:0]  read_data;

   begin
      fork
         begin
            wait_for_clock(1000);
            $display("[%t] : *** ERROR *** Timeout waiting for RX status, SPI", $realtime);
            $finish;
         end
         begin
            do begin
               UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
            end while (read_data[status_bit] !== 1'b1);
         end
      join_any
      disable fork;
   end
endtask


task read_mbx_msg(
                  input bit [31:0] msg[63:0],
                  bit [31:0]       msg_length,
                  bit [63:0]       mbx_base,
                  logic [15:0]     comp_id = EP_BUS_DEV_FNS
                 );
   logic [31:0]  read_data;

   begin
      // RX Cmd
      reg_read(.base_addr(mbx_base), .reg_offset(12'h018), .read_data(read_data), .comp_id(comp_id));
      if (read_data !== msg_length) begin
         $display("[%t] : *** ERROR *** Length mismatch in mailbox message. Expected: 0x%08x, Actual: 0x%08x", $realtime, msg_length, read_data);
         $finish;
      end
      // Read Index
      reg_write(.base_addr(mbx_base), .reg_offset(12'h010), .write_data(32'h0000_0000), .comp_id(comp_id));
      // Read Data
      for (int i = 0; i < msg_length; i++) begin
         reg_read(.base_addr(mbx_base), .reg_offset(12'h014), .read_data(read_data), .comp_id(comp_id));
         if (read_data !== msg[i])
           begin
              $display("[%t] : *** ERROR *** Data miscompare in mailbox message with index %2d. Expected: 0x%08x, Actual: 0x%08x", $realtime, i, msg[i], read_data);
              $finish;
           end
      end
   end
endtask


task read_spi_mbx_msg(
                      input bit [31:0] msg[63:0],
                      bit [31:0]       msg_length,
                      bit [23:0]       mbx_base
                     );
   logic [31:0]  read_data;

   begin
      // RX Cmd
      UC_SPI_MODEL.spi_read(.addr(mbx_base + 24'h000018), .read_data(read_data));
      if (read_data !== msg_length) begin
         $display("[%t] : *** ERROR *** Length mismatch in mailbox message. Expected: 0x%08x, Actual: 0x%08x", $realtime, msg_length, read_data);
         $finish;
      end

      // Read Index
      UC_SPI_MODEL.spi_write(.addr(mbx_base + 24'h000010), .write_data(32'h0000_0000));
      // Read Data
      for (int i = 0; i < msg_length; i++) begin
         UC_SPI_MODEL.spi_read(.addr(mbx_base + 24'h000014), .read_data(read_data));
         if (read_data !== msg[i])
           begin
              $display("[%t] : *** ERROR *** Data miscompare in mailbox message with index %2d. Expected: 0x%08x, Actual: 0x%08x", $realtime, i, msg[i], read_data);
              $finish;
           end
      end
   end
endtask
