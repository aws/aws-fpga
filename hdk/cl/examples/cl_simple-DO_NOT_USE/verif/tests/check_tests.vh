// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task pcie_check_4k_boundary_test();
   begin
      // Test variables
      logic [63:0]  base_addr;
      logic [63:0]  cl_base;

      logic [63:0]  app_cl_bar;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  app_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [63:0]  test_addr;
      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

      bit           check_msix;

      cl_base = 64'h0000_0000_0000_0000;

      exp_status_count = 32'h0;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
`endif

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

      base_addr = app_cl_bar + cl_base;

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


      // Enable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      // Check that enable bit can be set and cleared as expected
      $display("[%t] : Checking that PCIe 4k Boundary Error event can be enabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0080; // Set bit [7], cfg_pcim_4k_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking that PCIe 4k Boundary Error event can be disabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0080); // Clear bit [7], cfg_pcim_4k_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling PCIe 4k Boundary Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0080;  // Set bit [7] : PCIe 4k Boundary Check Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Check 4k crossing for Write
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end

      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[1] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe 4k Boundary error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe 4k Boundary error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000002), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data(test_addr[31:0]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Check 4k crossing for Read
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end

      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[1] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe 4k Boundary error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe 4k Boundary error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000002), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data({test_addr[31:1], 1'b1}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Clear status count and verify that value is 0x0
      $display("[%t] : Clearing the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .write_data($urandom()), .comp_id(dom0_pf));
      exp_status_count = 32'h0;
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));


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


task pcie_check_bme_test();
   begin
      // Test variables
      logic [63:0]  base_addr;
      logic [63:0]  cl_base;

      logic [63:0]  app_cl_bar;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  app_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [63:0]  test_addr;
      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

      bit           check_msix;

      cl_base = 64'h0000_0000_0000_0000;

      exp_status_count = 32'h0;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
`endif

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

      base_addr = app_cl_bar + cl_base;

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


      // Enable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      // Check that enable bit can be set and cleared as expected
      $display("[%t] : Checking that PCIe BME Error event can be enabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0100; // Set bit [8], cfg_pcim_bme_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking that PCIe BME Error event can be disabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0100); // Clear bit [8], cfg_pcim_bme_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling PCIe BME Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0100;  // Set bit [8] : PCIe Bus Master Enable Check
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Clear BME bit
      //-----------------------------

      clear_bme(.comp_id(app_pf), .error_count(error_count));

      //-----------------------------
      // Issue write
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end

      $display("[%t] : Programming CL to issue write", $realtime);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[2] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe BME error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe BME error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000004), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data(test_addr[31:0]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Issue read
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end

      $display("[%t] : Programming CL to issue read", $realtime);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[2] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe BME error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe BME error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000004), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data({test_addr[31:1], 1'b1}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Clear status count and verify that value is 0x0
      $display("[%t] : Clearing the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .write_data($urandom()), .comp_id(dom0_pf));
      exp_status_count = 32'h0;
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));


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


task pcie_check_req_size_test();
   begin
      // Test variables
      logic [63:0]  base_addr;
      logic [63:0]  cl_base;

      logic [63:0]  app_cl_bar;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  app_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [63:0]  test_addr;
      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

      bit           check_msix;

      cl_base = 64'h0000_0000_0000_0000;

      exp_status_count = 32'h0;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(app_pf), .bar_addr(app_cl_bar));
`else
      get_bar(.bar_num(0), .comp_id(app_pf), .bar_addr(app_cl_bar));
`endif

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

      base_addr = app_cl_bar + cl_base;

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


      // Enable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      // Check that enable bit can be set and cleared as expected
      $display("[%t] : Checking that PCIe Request Size Error event can be enabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0200; // Set bit [9], cfg_pcim_size_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking that PCIe Request Size Error event can be disabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0200); // Clear bit [9], cfg_pcim_size_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling PCIe Request Size Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0200;  // Set bit [9] : PCIe Request Size Enable Check
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Issue write
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h08;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h09;
         last_len = 8'h10 - test_addr[5:2];
      end

      $display("[%t] : Programming CL to issue write", $realtime);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[3] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe Request Size error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe Request Size error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000008), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data(test_addr[31:0]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //-----------------------------
      // Issue read
      //-----------------------------

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] <= 12'he00);

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h08;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h09;
         last_len = 8'h10 - test_addr[5:2];
      end

      $display("[%t] : Programming CL to issue read", $realtime);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Protocol Error interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end
      exp_status_count++;

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[3] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe Request Size error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe Request Size error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000008), .comp_id(dom0_pf));
            //  Check that the event status was cleared
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data[19] !== 1'b0) begin
               $display("[%t] : *** ERROR *** PCIe Protocol error event status was not cleared", $realtime);
               error_count++;
            end
            // Write to the Interrupt Status register to set dom0_int_done in mgt_top
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00080000), .comp_id(dom0_pf));
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data({test_addr[31:1], 1'b1}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Clear status count and verify that value is 0x0
      $display("[%t] : Clearing the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .write_data($urandom()), .comp_id(dom0_pf));
      exp_status_count = 32'h0;
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));


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
