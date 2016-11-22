// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task msix_test();
   begin
      // Test variables
      logic [63:0]  app_cl_bar;
      logic [63:0]  app_msix_bar;

      logic [63:0]  domu_mbx_bar;
      logic [63:0]  domu_msix_bar;

      logic [63:0]  dom0_mgmt_bar;
      logic [63:0]  dom0_msix_bar;
      logic [63:0]  dom0_mbx_bar;

      logic [15:0]  app_pf;
      logic [15:0]  domu_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      bit [31:0]    mbx_msg[63:0];
      bit [31:0]    mbx_msg_length;

      logic [63:0]  addr;
      logic [31:0]  data;
      bit           mask;

      logic [7:0]   max_cl_vector;

      int           polling_count;

      int           error_count;
      logic         fail;

      bit           check_msix;

      error_count = 0;
      fail = 0;

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

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;
      domu_pf = EP_BUS_DEV_FNS_PF1;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
`endif
      get_bar(.bar_num(2), .comp_id(app_pf), .bar_addr(app_msix_bar));

      get_bar(.bar_num(0), .comp_id(domu_pf), .bar_addr(domu_mbx_bar));
`ifdef NO_XDMA
      get_bar(.bar_num(2), .comp_id(domu_pf), .bar_addr(domu_msix_bar));
`endif

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));
`ifndef NO_XDMA
      get_bar(.bar_num(2), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`else
      get_bar(.bar_num(2), .comp_id(dom0_pf), .bar_addr(dom0_msix_bar));
      get_bar(.bar_num(4), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`endif      

      //--------------------
      // Dom0 - RQL Timeout
      //--------------------

      // Enable Dom0 RQL Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 16); // RQL Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      // Enable custom timeout and set timeout value
      $display("[%t] : Programming RQL timeout value of 0x1", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0ec), .write_data(32'h80000001), .comp_id(dom0_pf));

      // Read from unassigned address 0x70, should return 0xdead_beef and trigger MSI-X interrupt
      $display("[%t] : Issuing dummy read from 0x070", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h070), .read_data(read_data), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 RQL Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         polling_count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            polling_count++;
         end while ((read_data[16] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for RQL timeout event", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Disabling the RQL timeout event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0ec), .write_data(32'h00000000), .comp_id(dom0_pf));

      // For extra coverage, check status using SPI
      UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
      if (read_data[16] !== 1'b1) begin
         $display("[%t] : *** ERROR *** SPI status bit not set for RQL timeout event", $realtime);
         error_count++;
      end

      $display("[%t] : Checking and clearing the RQL timeout event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[16] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for RQL timeout event", $realtime);
         error_count++;
      end else begin
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00010000), .comp_id(dom0_pf));
      end

      // Disable Dom0 RQL Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0001_0000);  // Clear bit [16], RQL Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));


      //-----------------
      // Dom0 - Watchdog
      //-----------------

      // Enable Dom0 Watchdog interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 4);  // Watchdog
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Programming watchdog timeout value of 0x100", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .write_data(32'h00000100), .comp_id(dom0_pf));

      $display("[%t] : Enabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000001), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 Watchdog Timer interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         polling_count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            polling_count++;
         end while ((read_data[4] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for Watchdog timeout event", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Disabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000000), .comp_id(dom0_pf));

      $display("[%t] : Clearing the watchdog event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00000010), .comp_id(dom0_pf));

      // Read back value to make sure watchdog is disabled
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 Watchdog interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0010);  // Clear bit [4], Watchdog
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));


      //--------------------------
      // Mailbox 0 (Dom0 to DomU)
      //--------------------------

      // Enable DomU Mailbox 0 RX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data | (1'b1 << 0);  // Mailbox 0 RX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      mbx_msg[0] = $urandom();
      mbx_msg[1] = $urandom();
      mbx_msg[2] = $urandom();
      mbx_msg[3] = $urandom();

      mbx_msg_length = 4;

      $display("[%t] : Sending message from Dom0 to DomU (Mailbox 0)", $realtime);
      send_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(dom0_mbx_bar + 'h20), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for DomU RX interrupt (Mailbox 0)...", $realtime);
         wait_for_msix_intr(.comp_id(domu_pf));
      end else begin
         polling_count = 0;
         do begin
            reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(domu_pf));
            polling_count++;
         end while ((read_data[0] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for Mailbox 0 RX event", $realtime);
            error_count++;
         end
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


      //--------------------------
      // Mailbox 1 (DomU to Dom0)
      //--------------------------

      // Enable DomU Mailbox 1 TX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data | (1'b1 << 1);  // Mailbox 1 TX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));

      mbx_msg[0] = $urandom();
      mbx_msg[1] = $urandom();
      mbx_msg[2] = $urandom();
      mbx_msg[3] = $urandom();

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
         polling_count = 0;
         do begin
            reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(domu_pf));
            polling_count++;
         end while ((read_data[1] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for Mailbox 1 TX event", $realtime);
            error_count++;
         end
      end

      $display("[%t] : DomU clearing Mailbox 1 TX event", $realtime);
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h00c), .write_data(32'h0000_0002), .comp_id(domu_pf));

      // Disable DomU Mailbox 1 TX interrupt
      reg_read(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(domu_pf));
      write_data = read_data & ~(32'h0000_0002);  // Clear bit [1], Mailbox 1 TX
      reg_write(.base_addr(domu_mbx_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(domu_pf));


      //-------------------------
      // Mailbox 2 (Dom0 to SPI)
      //-------------------------

      // Enable Dom0 Mailbox 2 TX interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 3);  // Mailbox 2 TX
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      mbx_msg[0] = $urandom();
      mbx_msg[1] = $urandom();
      mbx_msg[2] = $urandom();
      mbx_msg[3] = $urandom();

      mbx_msg_length = 4;

      $display("[%t] : Sending message from Dom0 to SPI (Mailbox 2)", $realtime);
      send_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(dom0_mgmt_bar + 'h40), .comp_id(dom0_pf));

      $display("[%t] : SPI polling for Mailbox 2 RX event...", $realtime);
      poll_spi_mbx_rx_status(.status_bit(0)); // Bit [0] is Mailbox 2 RX event

      $display("[%t] : SPI reading message from Mailbox 2", $realtime);
      read_spi_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(24'h000020));

      $display("[%t] : SPI clearing Mailbox 2 RX event", $realtime);
      UC_SPI_MODEL.spi_write(.addr(24'h00000c), .write_data(32'h0000_0001));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 TX interrupt (Mailbox 2)...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         polling_count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            polling_count++;
         end while ((read_data[3] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for Mailbox 2 TX event", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Dom0 clearing Mailbox 2 TX event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h0000_0008), .comp_id(domu_pf));

      // Disable Dom0 Mailbox 2 TX interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0008);  // Clear bit [3], Mailbox 2 TX
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));


      //-------------------------
      // Mailbox 3 (SPI to Dom0)
      //-------------------------

      // Enable Dom0 Mailbox 3 RX interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 2);  // Mailbox 3 RX
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      mbx_msg[0] = $urandom();
      mbx_msg[1] = $urandom();
      mbx_msg[2] = $urandom();
      mbx_msg[3] = $urandom();

      mbx_msg_length = 4;

      $display("[%t] : Sending message from SPI to Dom0 (Mailbox 3)", $realtime);
      send_spi_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(24'h000020));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 RX interrupt (Mailbox 3)...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         polling_count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            polling_count++;
         end while ((read_data[2] !== 1'b1) && (polling_count < 100));
         if (polling_count == 100) begin
            $display("[%t] : *** ERROR *** Timeout waiting for status bit to be set for Mailbox 3 RX event", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Dom0 reading message from Mailbox 3", $realtime);
      read_mbx_msg(.msg(mbx_msg), .msg_length(mbx_msg_length), .mbx_base(dom0_mgmt_bar + 'h40), .comp_id(dom0_pf));

      $display("[%t] : Dom0 clearing Mailbox 3 RX event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h0000_0004), .comp_id(dom0_pf));

      $display("[%t] : SPI polling for Mailbox 3 TX event...", $realtime);
      poll_spi_mbx_tx_status(.status_bit(1)); // Bit [1] is Mailbox 3 TX event

      $display("[%t] : SPI clearing Mailbox 3 TX event", $realtime);
      UC_SPI_MODEL.spi_write(.addr(24'h00000c), .write_data(32'h0000_0002));

      // Disable Dom0 Mailbox 3 RX interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0004);  // Clear bit [2], Mailbox 3 RX
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));


      //-------------------------------
      // CL - All vectors
      //-------------------------------
      if (!$value$plusargs("NUM_CL_MSIX_VECTORS=%d", max_cl_vector)) begin
         max_cl_vector = 8'h0;
      end

`ifndef NO_XDMA
      for (logic [7:0] vector_num = 8'h00; vector_num < max_cl_vector; vector_num = vector_num + 8'h01) begin
         write_data = 32'h0;
         write_data |= 1'b1 << vector_num;
         $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector %2d)", $realtime, vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));

         $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
         polling_count = 0;
         do begin
            reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
            polling_count++;
            if (polling_count == 100) begin
               $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector %2d).", $realtime, vector_num);
               error_count++;
            end
         end while ((read_data[16 + vector_num] !== 1'b1) && (polling_count < 100));

         $display("[%t] : Waiting for CL interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(app_pf), .vector_num(vector_num));

         // Clear Vector Done
         write_data = 32'h0;
         write_data |= 1'b1 << (16 + vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));
         reg_read_check(.base_addr(app_cl_bar), .reg_offset(12'hd00), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
      end
`else
      for (logic [7:0] vector_num = 8'h00; vector_num < max_cl_vector; vector_num = vector_num + 8'h01) begin
         $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector %2d)", $realtime, vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data({16'h0000, vector_num, 8'h01}), .comp_id(app_pf));

         $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
         polling_count = 0;
         do begin
            reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
            polling_count++;
            if (polling_count == 100) begin
               $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector %2d).", $realtime, vector_num);
               error_count++;
            end
         end while ((read_data[31] !== 1'b1) && (polling_count < 100));

         if (read_data[30] == 1'b1) begin
            $display("[%t] : *** ERROR *** cl_int_tst control register indicated that interrupt was not sent.", $realtime);
            error_count++;
            $display("[%t] : Clearing Done and Not Sent bits in cl_int_tst register", $realtime);
            reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
         end else begin
            if (check_msix == 1'b1) begin
               $display("[%t] : Waiting for CL interrupt...", $realtime);
               wait_for_msix_intr(.comp_id(app_pf), .vector_num(vector_num));
            end
            $display("[%t] : Clearing Done bit in cl_int_tst register", $realtime);
            reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
         end
      end
`endif

      wait_for_clock(200);

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


task msix_disable_test();
   begin
      // Test variables
      logic [63:0]  app_cl_bar;

      logic [15:0]  app_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           polling_count;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
`endif

      $display("[%t] : Disabling MSI-X interrupts for CL", $realtime);
      disable_msix(.comp_id(app_pf), .error_count(error_count));

      //-------------------------------
      // CL - Vector 0x0
      //-------------------------------

      $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector 0)", $realtime);
      reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(32'h0000_0001), .comp_id(app_pf));

      $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
      polling_count = 0;
      do begin
         reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
         polling_count++;
         if (polling_count == 100) begin
`ifndef NO_XDMA
            $display("[%t] : Done bit was not set (expected since interrupt was disabled).", $realtime);
`else
            $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector 0).", $realtime);
            error_count++;
`endif
         end
`ifndef NO_XDMA
      end while ((read_data[16] !== 1'b1) && (polling_count < 100));
`else
      end while ((read_data[31] !== 1'b1) && (polling_count < 100));
`endif

`ifndef NO_XDMA
      if (polling_count !== 100) begin
         $display("[%t] : *** ERROR *** Done bit was unexpectedly set (vector 0).", $realtime);
         error_count++;
      end
`endif

`ifdef NO_XDMA
      if (read_data[30] == 1'b1) begin
         $display("[%t] : cl_int_tst register indicated that interrupt was not sent (which is expected)", $realtime);
         $display("[%t] : Clearing Done and Not Sent bits in cl_int_tst register", $realtime);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
      end else begin
         $display("[%t] : *** ERROR *** cl_int_tst register indicated that interrupt was sent (should have been disabled)", $realtime);
         error_count++;
         $display("[%t] : Clearing Done bit in cl_int_tst register", $realtime);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
      end
`endif

      wait_for_clock(20);

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


task msix_mask_test();
   begin
      // Test variables
      logic [63:0]  app_cl_bar;
      logic [63:0]  app_xdma_bar;
      logic [63:0]  app_msix_bar;

      logic [15:0]  app_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [63:0]  addr;
      logic [31:0]  data;
      bit           mask;

      int           polling_count;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;

`ifndef NO_XDMA
      get_bar(.bar_num(2), .comp_id(app_pf), .bar_addr(app_xdma_bar));
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
      get_bar(.bar_num(2), .comp_id(app_pf), .bar_addr(app_msix_bar));
`endif

      $display("[%t] : Masking MSI-X interrupts for CL", $realtime);
`ifndef NO_XDMA
      read_msix_table(.bar(app_xdma_bar), .comp_id(app_pf), .addr(addr), .data(data), .mask(mask));
      write_msix_table(.bar(app_xdma_bar), .comp_id(app_pf), .addr(addr), .data(data), .mask(1'b1), .error_count(error_count));
`else
      read_msix_table(.bar(app_msix_bar), .comp_id(app_pf), .addr(addr), .data(data), .mask(mask));
      write_msix_table(.bar(app_msix_bar), .comp_id(app_pf), .addr(addr), .data(data), .mask(1'b1), .error_count(error_count));
`endif

      //-------------------------------
      // CL - Vector 0x0
      //-------------------------------

      $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector 0)", $realtime);
      reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(32'h0000_0001), .comp_id(app_pf));

      $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
      polling_count = 0;
      do begin
         reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
         polling_count++;
         if (polling_count == 100) begin
`ifndef NO_XDMA
            $display("[%t] : Done bit was not set (expected since interrupt was masked).", $realtime);
`else
            $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector 0).", $realtime);
            error_count++;
`endif
         end
`ifndef NO_XDMA
      end while ((read_data[16] !== 1'b1) && (polling_count < 100));
`else
      end while ((read_data[31] !== 1'b1) && (polling_count < 100));
`endif

`ifndef NO_XDMA
      if (polling_count !== 100) begin
         $display("[%t] : *** ERROR *** Done bit was unexpectedly set (vector 0).", $realtime);
         error_count++;
      end
`endif

`ifdef NO_XDMA
      if (read_data[30] == 1'b1) begin
         $display("[%t] : cl_int_tst register indicated that interrupt was not sent (which is expected)", $realtime);
         $display("[%t] : Clearing Done and Not Sent bits in cl_int_tst register", $realtime);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
      end else begin
         $display("[%t] : *** ERROR *** cl_int_tst register indicated that interrupt was sent (should have been masked)", $realtime);
         error_count++;
         $display("[%t] : Clearing Done bit in cl_int_tst register", $realtime);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(read_data), .comp_id(app_pf));
      end
`endif

      wait_for_clock(20);

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


task xdma_msix_int_test;
   begin
`ifdef NO_XDMA
      $display("[%t] : *** ERROR *** Attempted to run xdma_msix_int_test without XDMA defined.", $realtime);
`else
      // Test variables
      logic [63:0]  app_cl_bar;

      logic [15:0]  app_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [7:0]   max_vector;

      int           polling_count;

      int           error_count;
      logic         fail;


      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;

      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));

      //-------------------------------
      // CL - Test specified IRQs
      //-------------------------------

      if (!$value$plusargs("NUM_CL_MSIX_VECTORS=%d", max_vector)) begin
         max_vector = 8'h0;
      end

      for (logic [7:0] vector_num = 8'h00; vector_num < max_vector; vector_num = vector_num + 8'h01) begin
         write_data = 32'h0;
         write_data |= 1'b1 << vector_num;
         $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector %2d)", $realtime, vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));

         $display("[%t] : Waiting for CL interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(app_pf), .vector_num(vector_num));

         $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
         polling_count = 0;
         do begin
            reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
            polling_count++;
            if (polling_count == 100) begin
               $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector %2d).", $realtime, vector_num);
               error_count++;
            end
         end while ((read_data[16 + vector_num] !== 1'b1) && (polling_count < 100));

         // Clear Vector Done
         write_data = 32'h0;
         write_data |= 1'b1 << (16 + vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));
         reg_read_check(.base_addr(app_cl_bar), .reg_offset(12'hd00), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
      end

      wait_for_clock(20);

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

`endif // !`ifdef NO_XDMA
      
      $finish;

   end

   
   
endtask


task xdma_legacy_int_test;
   begin
`ifdef NO_XDMA
      $display("[%t] : *** ERROR *** Attempted to run xdma_legacy_int_test without XDMA defined.", $realtime);
`else
      // Test variables
      logic [63:0]  app_cl_bar;

      logic [15:0]  app_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [7:0]   max_vector;

      int           polling_count;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;

      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));

      // Disable MSIX - PF0
      disable_msix(.comp_id(app_pf), .error_count(error_count));

      // Disable MSI - PF0
      disable_msi(.comp_id(app_pf), .error_count(error_count));
      
      wait_for_clock(20);

      
      //-------------------------------
      // CL - Test specified IRQs
      //-------------------------------

      if (!$value$plusargs("NUM_CL_MSIX_VECTORS=%d", max_vector)) begin
         max_vector = 8'h0;
      end

      for (logic [7:0] vector_num = 8'h00; vector_num < max_vector; vector_num = vector_num + 8'h01) begin
         write_data = 32'h0;
         write_data |= 1'b1 << vector_num;
         $display("[%t] : Writing cl_int_tst register to trigger CL interrupt (vector %2d)", $realtime, vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));

         $display("[%t] : Polling cl_int_tst register for Done bit...", $realtime);
         polling_count = 0;
         do begin
            reg_read(.base_addr(app_cl_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(app_pf));
            polling_count++;
            if (polling_count == 100) begin
               $display("[%t] : *** ERROR *** Timeout waiting for cl_int_tst Done bit to be set (vector 0).", $realtime);
               error_count++;
            end
         end while ((read_data[16 + vector_num] !== 1'b1) && (polling_count < 100));

         // Clear Vector Done
         write_data = 32'h0;
         write_data |= 1'b1 << (16 + vector_num);
         reg_write(.base_addr(app_cl_bar), .reg_offset(12'hd00), .write_data(write_data), .comp_id(app_pf));
         reg_read_check(.base_addr(app_cl_bar), .reg_offset(12'hd00), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
      end
      
      wait_for_clock(20);

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

`endif // !`ifdef NO_XDMA
      
      $finish;

   end

   
   
endtask


