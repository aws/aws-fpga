// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task spi_version_test();
   begin
      // Test variables
      logic [31:0]  read_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      wait(tb.sys_rst_n == 1'b1);

      //---------------------------------------
      // Issue CMD_VER (0x05) to check Version
      //---------------------------------------

      $display("[%t] : Checking Version register...", $realtime);
      UC_SPI_MODEL.spi_gen(.cmd(8'h05), .read_data(read_data));
      if (read_data !== `FPGA_VERSION) begin
         $display("[%t] : *** ERROR *** Read back unexpected SPI Version: 0x%08x (expected 0x%08x)", $realtime, read_data, `FPGA_VERSION);
         error_count++;
      end

      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking for errors...", $realtime);
      if (error_count > 0) begin
         $display("[%t] : Detected non-zero value for error_count: %d", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        $display("[%t] : *** TEST PASSED ***", $realtime);

      $finish;
   end
endtask


task spi_magic_test();
   begin
      // Test variables
      logic [31:0]  read_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      wait(tb.sys_rst_n == 1'b1);

      //----------------------------------------------
      // Issue CMD_MAGIC (0x06) to check magic number
      //----------------------------------------------

      $display("[%t] : Checking Magic Number...", $realtime);
      UC_SPI_MODEL.spi_gen(.cmd(8'h06), .read_data(read_data));
      if (read_data !== 32'hc001_c0de) begin
         $display("[%t] : *** ERROR *** Read back unexpected SPI Magic Number: 0x%08x (expected 0x%08x)", $realtime, read_data, 32'hc001_c0de);
         error_count++;
      end

      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking for errors...", $realtime);
      if (error_count > 0) begin
         $display("[%t] : Detected non-zero value for error_count: %d", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        $display("[%t] : *** TEST PASSED ***", $realtime);

      $finish;
   end
endtask


task spi_test();
   begin
      // Test variables
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [23:0]  test_addr;

      int           loop_count;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values of a few I2C registers...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000080), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data));
      UC_SPI_MODEL.spi_read(.addr(24'h000084), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data));
      UC_SPI_MODEL.spi_read(.addr(24'h000088), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data));
      UC_SPI_MODEL.spi_read(.addr(24'h000098), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data));
      UC_SPI_MODEL.spi_read(.addr(24'h00009c), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data));


      //------------------------------
      // Program some registers
      //------------------------------

      $display("[%t] : Verifying that I2C registers can be programmed...", $realtime);
      write_data = $urandom();
      UC_SPI_MODEL.spi_write(.addr(24'h000080), .write_data(write_data));
      UC_SPI_MODEL.spi_read(.addr(24'h000080), .read_data(read_data));
      if (read_data[15:0] !== write_data[15:0]) begin
         $display("[%t] : *** ERROR *** I2C register at address 0x0080 was not programmed as expected", $realtime);
         error_count++;
      end else begin
         write_data = 32'h0000_0000;
         UC_SPI_MODEL.spi_write(.addr(24'h000080), .write_data(write_data));
      end

      $display("[%t] : Reading lower bits of lat_ltssm_state...", $realtime);
      loop_count = 0;
      do begin
         UC_SPI_MODEL.spi_read(.addr(24'h000200), .read_data(read_data));
         loop_count++;
      end while ((read_data[16] !== 1'b1) && (loop_count < 10));
      if (read_data[16] !== 1'b1) begin
         $display("[%t] : *** ERROR *** LTSSM did not make it to L0 state (0x10) as expected", $realtime);
         error_count++;
      end

      $display("[%t] : Reading current LTSSM state and upper bits of lat_ltssm_state...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000204), .read_data(read_data));
      if (read_data[31:16] !== 16'h0010) begin
         $display("[%t] : *** ERROR *** LTSSM not in L0 state (0x10) as expected", $realtime);
         error_count++;
      end

      $display("[%t] : Clearing lat_ltssm_state...", $realtime);
      UC_SPI_MODEL.spi_write(.addr(24'h000200), .write_data(32'h0000_0000));

      $display("[%t] : Reading lower bits of lat_ltssm_state again...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000200), .exp_data(32'h0001_0000), .compare(1'b1), .read_data(read_data));

      $display("[%t] : Reading current LTSSM state and upper bits of lat_ltssm_state again...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000204), .exp_data(32'h0010_0000), .compare(1'b1), .read_data(read_data));


      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking for errors...", $realtime);
      if (error_count > 0) begin
         $display("[%t] : Detected non-zero value for error_count: %d", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        $display("[%t] : *** TEST PASSED ***", $realtime);

      $finish;
   end
endtask


task spi_xtra_test();
   begin
      // Test variables
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [23:0]  test_addr;

      int           loop_count;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      wait(tb.sys_rst_n == 1'b1);

      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values of a few I2C registers...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000080), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      UC_SPI_MODEL.spi_read(.addr(24'h000084), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      UC_SPI_MODEL.spi_read(.addr(24'h000088), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      UC_SPI_MODEL.spi_read(.addr(24'h000098), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      UC_SPI_MODEL.spi_read(.addr(24'h00009c), .exp_data(32'h0000_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));

      $display("[%t] : Spot checking read values for unmapped register space...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000000), .exp_data(32'hbaad_f002), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      for (logic [24:0] addr = 25'h001000; addr < 25'h0ffffff; addr = addr << 1) begin
         UC_SPI_MODEL.spi_read(.addr(addr[23:0]), .exp_data(32'hbaad_f002), .compare(1'b1), .read_data(read_data), .cmd(8'h08));
      end


      //------------------------------
      // Program some registers
      //------------------------------

      $display("[%t] : Verifying that I2C registers can be programmed...", $realtime);
      write_data = $urandom();
      UC_SPI_MODEL.spi_write(.addr(24'h000080), .write_data(write_data), .cmd(8'h07));
      UC_SPI_MODEL.spi_read(.addr(24'h000080), .read_data(read_data), .cmd(8'h08));
      if (read_data[15:0] !== write_data[15:0]) begin
         $display("[%t] : *** ERROR *** I2C register at address 0x0080 was not programmed as expected", $realtime);
         error_count++;
      end else begin
         write_data = 32'h0000_0000;
         UC_SPI_MODEL.spi_write(.addr(24'h000080), .write_data(write_data), .cmd(8'h07));
      end

      $display("[%t] : Verifying that write to unmapped address doesn't hang...", $realtime);
      do begin
         test_addr = $urandom();
      end while (test_addr[23:12] != 12'h000);
      write_data = $urandom();
      UC_SPI_MODEL.spi_write(.addr(test_addr), .write_data(write_data), .cmd(8'h07));

      $display("[%t] : Reading xtra_state0...", $realtime);
      loop_count = 0;
      do begin
         UC_SPI_MODEL.spi_read(.addr(24'h000200), .read_data(read_data), .cmd(8'h08));
         loop_count++;
      end while ((read_data[16] !== 1'b1) && (loop_count < 10));
      if (read_data[16] !== 1'b1) begin
         $display("[%t] : *** ERROR *** LTSSM did not make it to L0 state (0x10) as expected", $realtime);
         error_count++;
      end

      $display("[%t] : Reading xtra_state1...", $realtime);
      loop_count = 0;
      do begin
         UC_SPI_MODEL.spi_read(.addr(24'h000204), .read_data(read_data), .cmd(8'h08));
      end while ((read_data[31:16] !== 16'h0010) && (loop_count < 10));
      if (read_data[31:16] !== 16'h0010) begin
         $display("[%t] : *** ERROR *** LTSSM not in L0 state (0x10) as expected", $realtime);
         error_count++;
      end

      $display("[%t] : Clearing xtra_ltssm_one_hot...", $realtime);
      UC_SPI_MODEL.spi_write(.addr(24'h000200), .write_data(32'h0000_0000), .cmd(8'h07));

      $display("[%t] : Reading xtra_state0 again...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000200), .exp_data(32'h0001_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));

      $display("[%t] : Reading xtra_state1 again...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000204), .exp_data(32'h0010_0000), .compare(1'b1), .read_data(read_data), .cmd(8'h08));


      //---------------------------
      // Report pass/fail status
      //---------------------------
      $display("[%t] : Checking for errors...", $realtime);
      if (error_count > 0) begin
         $display("[%t] : Detected non-zero value for error_count: %d", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        $display("[%t] : *** TEST PASSED ***", $realtime);

      $finish;
   end
endtask
