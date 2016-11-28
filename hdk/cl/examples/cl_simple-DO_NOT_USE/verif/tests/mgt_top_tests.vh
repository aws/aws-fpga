// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task mgt_misc_reset_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [5:0]   cfg_ltssm_state;
      logic [47:0]  exp_lat_ltssm_state;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values for Misc Ctl Range 1 registers...", $realtime);

      // Need to read value of cfg_ltssm_state[5:0] ([21:16]) first to calculate expected lat_ltssm_state[47:0] value
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h204), .read_data(read_data), .comp_id(dom0_pf));
      cfg_ltssm_state = read_data[21:16];
      exp_lat_ltssm_state = (1'b1 << cfg_ltssm_state);

      // lat_ltssm_state[31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h200), .expected_data(32'hffff_ffff), .data_mask(exp_lat_ltssm_state[31:0]), .comp_id(dom0_pf), .error_count(error_count));
      // lat_ltssm_state[47:32] ([15:0])
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h204), .expected_data({10'h0, cfg_ltssm_state[5:0], 16'hffff}), .data_mask({16'hffff, exp_lat_ltssm_state[47:32]}), .comp_id(dom0_pf), .error_count(error_count));

      // 0x208 -- UNUSED
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h208), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_cl_dev_id, cfg_cl_vndr_id
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h210), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_cl_sub_dev_id, cfg_cl_sub_vndr_id
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h214), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_wstrb_chk_en ([12])
      // cfg_pcim_be_chk_en ([11])
      // cfg_pcim_incomp_chk_en ([10])
      // cfg_pcim_size_chk_en ([9])
      // cfg_pcim_bme_chk_en ([8])
      // cfg_pcim_4k_chk_en ([7])
      // cfg_pcim_len_chk_en ([6])
      // cfg_pcis_to_en ([5])
      // cfg_pcim_pass_en ([4])
      // cfg_pcim_pass_range_en ([3:0])
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(32'h0000_0020), .data_mask(32'h0000_1fff), .comp_id(dom0_pf), .error_count(error_count));

      // 0x21c -- UNUSED
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h21c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_low[0][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h220), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_low[0][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h224), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_high[0][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h228), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_high[0][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h22c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_low[1][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h230), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_low[1][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h234), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_high[1][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h238), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_high[1][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h23c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_low[2][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h240), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_low[2][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h244), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_high[2][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h248), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_high[2][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h24c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_low[3][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h250), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_low[3][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h254), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_pass_addr_high[3][31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h258), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_pass_addr_high[3][63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h25c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcis_to_time (default is 125,000 in decimal)
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .expected_data(32'h0001_e848), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcis_to_rdata
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h264), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcis_to_status_addr[31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h268), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcis_to_status_addr[63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h26c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcis_to_status_count
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_addr_range_status_addr[31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h274), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_addr_range_status_addr[63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h278), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_addr_range_status_count
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // fpga_uctrl_gpio[3:0] ([19:16]) -- Reset values will be X since OE bits are all zero and there are no top level connections
      // fpga_uctrl_oe ([11:8])
      // fpga_uctrl_out ([3:0])
      // Enable all OE bits and cycle through different values to output (0xf, 0xa, 0x5, 0x0)
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .write_data(32'h0000_0f0f), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .expected_data(32'h0000_0f0f), .data_mask(32'h0000_0f0f), .comp_id(dom0_pf), .error_count(error_count));
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .write_data(32'h0000_0f0a), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .expected_data(32'h0000_0f0a), .data_mask(32'h0000_0f0f), .comp_id(dom0_pf), .error_count(error_count));
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .write_data(32'h0000_0f05), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .expected_data(32'h0000_0f05), .data_mask(32'h0000_0f0f), .comp_id(dom0_pf), .error_count(error_count));
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .write_data(32'h0000_0f00), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .expected_data(32'h0000_0f00), .data_mask(32'h0000_0f0f), .comp_id(dom0_pf), .error_count(error_count));
      // Disable all OE bits
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h280), .write_data(32'h0000_0000), .comp_id(dom0_pf));

      // cfg_pcim_len_err_status_addr[31:0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h284), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_pcim_len_err_status_addr[63:32]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h288), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_pcim_len_err_status_count
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // tmp_blk_int
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h290), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_cl_flr_timeout_time
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h294), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_domu_mgt_flr_disable
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h298), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // 0x29c -- UNUSED
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h29c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // {ddr3_stat_int, ddr2_stat_int, ddr1_stat_int, ddr0_stat_int}
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2a0), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // {aurora_stat_int, hmc_stat_int}
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2a4), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // 0x2a8 -- UNUSED
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2a8), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // 0x2ac -- UNUSED
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2a8), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCI Write DW Count Low
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2b0), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCI Write DW Count High
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2b4), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCI Read DW Count Low
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2b8), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCI Read DW Count High
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2bc), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Flush Timeout (default is 125,000 in decimal)
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c0), .expected_data(32'h0001_e848), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Force Uncorrectable Error (write-only, but breaking out for clarity)
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c4), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCIe Error Status
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // PCIe Read Pending ID Array
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2cc), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // cfg_enable_rql_axi_err
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2d0), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // {cfg_pf2_req_count, cfg_pf1_req_count}
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2d4), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[31:16] < 16'd61) begin
         $display("[%t] : *** ERROR *** PF2 Req Count was %3d, expecting a value of at least  61", $realtime, read_data[31:16]);
         error_count++;
      end
      if (read_data[15:0] !== 16'h0000) begin
         $display("[%t] : *** ERROR *** PF1 Req Count was %3d, expecting a value of   0", $realtime, read_data[15:0]);
         error_count++;
      end

      // 0x2d8 - 0x2fc -- UNUSED
      for (logic [11:0] offset = 12'h0d8; offset < 12'h100; offset = offset + 12'h004) begin
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h200 + offset), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
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


task mgt_scratchpad_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values for Scratchpad registers...", $realtime);

      // rql_timeout_address
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d0), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // pwr_out_q
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d4), .expected_data(32'h0000_000f), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[6] alias
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d8), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[7] alias
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0dc), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[0]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e0), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[1]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e4), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[2]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e8), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[3]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0ec), .expected_data(32'h4000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[4]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f0), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[5]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f4), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[6]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f8), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // cfg_scratch[7]
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));


      //------------------------------
      // Program scratchpad registers
      //------------------------------

      // Scratch [0] : Power Management
      // [23:16] : pwr_dsp_en
      // [15: 8] : pwr_bram_en
      // [ 7: 0] : pwr_clk_en
      $display("[%t] : Programming Scratchpad [0]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e0), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [1] : GPIO 0
      // [   30] : I2C control through mgt_misc_ctl in hl.sv (chooses between mgt_i2c and hmc_iic interfaces)
      $display("[%t] : Programming Scratchpad [1]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e4), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [2] : GPIO 1
      $display("[%t] : Programming Scratchpad [2]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0e8), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [3] : Internal Request Timeout
      // [   31] : Enable custom timeout (value in [23:0])
      // [   30] : Enable default timeout value of 10000
      // [23: 0] : Custom timeout value
      $display("[%t] : Programming Scratchpad [3]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0ec), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [4] : Unused
      $display("[%t] : Programming Scratchpad [4]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f0), .comp_id(dom0_pf), .error_count(error_count));

// DEBUG: This may be fixed in the future
      $display("[%t] : Programming Scratchpad [4] using 0x0d0", $realtime);
      // Write through 0x0d0 path and read through 0x0f0 path...
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d0), .reg_rd_offset(12'h0f0), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [5] : SH CL Ctl 0
      // [31: 0] : sh_cl_ctl0
      $display("[%t] : Programming Scratchpad [5]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f4), .comp_id(dom0_pf), .error_count(error_count));

// DEBUG: This may be fixed in the future
      $display("[%t] : Programming Scratchpad [5] using 0x0d4", $realtime);
      // Write through 0x0d4 path and read through 0x0f4 path
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d4), .reg_rd_offset(12'h0f4), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [6] : SH CL Ctl 1
      // [31: 0] : sh_cl_ctl1
      $display("[%t] : Programming Scratchpad [6]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f8), .comp_id(dom0_pf), .error_count(error_count));

// DEBUG: This may be fixed in the future
      $display("[%t] : Programming Scratchpad [6] using 0x0d8", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d8), .comp_id(dom0_pf), .error_count(error_count));

      // Scratch [7] : HMC Reset, QSFP Modsel, PR Isolation
      // [   31] : cfg_pr_isol
      // [   30] : cfg_cl_reset
      // [26:24] : rst_dimm_out
      // [ 7: 4] : ~tmp_qsfp_modsel
      // [ 3: 0] : ~tmp_hmc_rst
      $display("[%t] : Programming Scratchpad [7]", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .comp_id(dom0_pf), .error_count(error_count));

// DEBUG: This may be fixed in the future
      $display("[%t] : Programming Scratchpad [7] using 0x0dc", $realtime);
      check_scratch(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0dc), .comp_id(dom0_pf), .error_count(error_count));


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


task automatic check_scratch(
                             input logic [63:0] base_addr,
                             logic [11:0]       reg_offset,
                             logic [11:0]       reg_rd_offset = reg_offset,
                             logic [31:0]       data_mask = 32'hffff_ffff,
                             logic [15:0]       comp_id,
                             ref int            error_count
                            );
   begin
      logic [31:0]  read_data;
      logic [31:0]  write_data;

      reg_read(.base_addr(base_addr), .reg_offset(reg_rd_offset), .read_data(read_data), .comp_id(comp_id));
      write_data = 32'hffff_ffff;
      reg_write(.base_addr(base_addr), .reg_offset(reg_offset), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(reg_rd_offset), .expected_data(write_data), .data_mask(data_mask), .comp_id(comp_id), .error_count(error_count));
      write_data = 32'h0000_0000;
      reg_write(.base_addr(base_addr), .reg_offset(reg_offset), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(reg_rd_offset), .expected_data(write_data), .data_mask(data_mask), .comp_id(comp_id), .error_count(error_count));
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(reg_offset), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(reg_rd_offset), .expected_data(write_data), .data_mask(data_mask), .comp_id(comp_id), .error_count(error_count));
      write_data = read_data;
      reg_write(.base_addr(base_addr), .reg_offset(reg_offset), .write_data(write_data), .comp_id(comp_id));
      reg_read_check(.base_addr(base_addr), .reg_offset(reg_rd_offset), .expected_data(write_data), .data_mask(data_mask), .comp_id(comp_id), .error_count(error_count));
   end
endtask


task mgt_qspi_test();
   begin
      // Test variables
      logic [63:0]  qspi_base_addr;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

      qspi_base_addr = dom0_mgmt_bar + 64'h1400;


      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values for QSPI registers...", $realtime);

      // SPI Control Register
      reg_read_check(.base_addr(qspi_base_addr), .reg_offset(12'h060), .expected_data(32'h0000_0180), .comp_id(dom0_pf), .error_count(error_count));
      // SPI Status Register
      reg_read_check(.base_addr(qspi_base_addr), .reg_offset(12'h064), .expected_data(32'h0000_00a5), .comp_id(dom0_pf), .error_count(error_count));
      // SPI TX FIFO Occupancy Register
      reg_read_check(.base_addr(qspi_base_addr), .reg_offset(12'h074), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // SPI RX FIFO Occupancy Register
      reg_read_check(.base_addr(qspi_base_addr), .reg_offset(12'h078), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));


      //------------------------------
      // Program QSPI registers
      //------------------------------

      $display("[%t] : Resetting the AXI Quad SPI core", $realtime);
      reg_write(.base_addr(qspi_base_addr), .reg_offset(12'h040), .write_data(32'h0000_000a), .comp_id(dom0_pf));

      $display("[%t] : Writing random entries into TX FIFO", $realtime);
      reg_write(.base_addr(qspi_base_addr), .reg_offset(12'h068), .write_data($urandom()), .comp_id(dom0_pf));
      reg_write(.base_addr(qspi_base_addr), .reg_offset(12'h068), .write_data($urandom()), .comp_id(dom0_pf));
      reg_write(.base_addr(qspi_base_addr), .reg_offset(12'h068), .write_data($urandom()), .comp_id(dom0_pf));

      $display("[%t] : Checking that TX FIFO Occupancy value is non-zero", $realtime);
      reg_read(.base_addr(qspi_base_addr), .reg_offset(12'h074), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data == 32'h0000_0000) begin
         $display("[%t] : *** ERROR *** TX FIFO Occupancy value was zero after writing entries to DTR", $realtime);
         error_count++;
      end

      $display("[%t] : Resetting TX FIFO pointer", $realtime);
      reg_read(.base_addr(qspi_base_addr), .reg_offset(12'h060), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0020;  // Bit [5] is TX FIFO Reset
      reg_write(.base_addr(qspi_base_addr), .reg_offset(12'h060), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Checking that TX FIFO Occupancy value is zero", $realtime);
      reg_read_check(.base_addr(qspi_base_addr), .reg_offset(12'h074), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));


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


task mgt_icap_test();
   begin
      // Test variables
      logic [63:0]  icap_base_addr;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

      icap_base_addr = dom0_mgmt_bar + 64'h1500;


      //---------------------------
      // Check reset values
      //---------------------------

      $display("[%t] : Checking reset values for ICAP registers...", $realtime);
      // ICAP Global Interrupt Enable Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Interrupt Status Register
      // Value of 0x05 indicates that Write FIFO is empty and Write FIFO occupancy is less than half of Write FIFO size
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h020), .expected_data(32'h0000_0005), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Interrupt Enable Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h028), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Control Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h10c), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Status Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h110), .expected_data(32'h0000_0005), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Write FIFO Vacancy Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h114), .expected_data(32'h0000_003f), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Read FIFO Occupancy Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h118), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      // ICAP Abort Status Register
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h11c), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));


      //------------------------------
      // Program ICAP registers
      //------------------------------

      $display("[%t] : Resetting the AXI ICAP registers", $realtime);
      reg_read(.base_addr(icap_base_addr), .reg_offset(12'h10c), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0008;  // Bit [3] is SW Reset
      reg_write(.base_addr(icap_base_addr), .reg_offset(12'h10c), .write_data(write_data), .comp_id(dom0_pf));
// DEBUG: Is reset bit self-clearing?

      $display("[%t] : Writing random entries into Write FIFO", $realtime);
      reg_write(.base_addr(icap_base_addr), .reg_offset(12'h100), .write_data($urandom()), .comp_id(dom0_pf));
      reg_write(.base_addr(icap_base_addr), .reg_offset(12'h100), .write_data($urandom()), .comp_id(dom0_pf));
      reg_write(.base_addr(icap_base_addr), .reg_offset(12'h100), .write_data($urandom()), .comp_id(dom0_pf));

      $display("[%t] : Checking that Write FIFO Vacancy value has changed", $realtime);
      reg_read(.base_addr(icap_base_addr), .reg_offset(12'h114), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data == 32'h0000_003f) begin
         $display("[%t] : *** ERROR *** Write FIFO Vacancy value did not decrease after writing entries to Write FIFO", $realtime);
         error_count++;
      end

      $display("[%t] : Clearing the FIFOs", $realtime);
      reg_read(.base_addr(icap_base_addr), .reg_offset(12'h10c), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0004;  // Bit [2] is FIFO Clear
      reg_write(.base_addr(icap_base_addr), .reg_offset(12'h10c), .write_data(write_data), .comp_id(dom0_pf));
// DEBUG: Is FIFO clear bit self-clearing?

      $display("[%t] : Checking that Write FIFO Vacancy value is correct", $realtime);
      reg_read_check(.base_addr(icap_base_addr), .reg_offset(12'h114), .expected_data(32'h0000_003f), .comp_id(dom0_pf), .error_count(error_count));


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


task mgt_cl_sh_status_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      //---------------------------
      // Read Status values
      //---------------------------

      $display("[%t] : Checking values for cl_sh_status registers...", $realtime);
`ifdef CL_SECOND
      // cl_sh_status0
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h060), .expected_data(32'hb222_2000), .data_mask(32'hffff_f000), .comp_id(dom0_pf), .error_count(error_count));
      // cl_sh_status1
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h064), .expected_data(`CL_VERSION + 32'h0000_0002), .comp_id(dom0_pf), .error_count(error_count));
`else
      // cl_sh_status0
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h060), .expected_data(32'ha111_1000), .data_mask(32'hffff_f000), .comp_id(dom0_pf), .error_count(error_count));
      // cl_sh_status1
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h064), .expected_data(`CL_VERSION), .comp_id(dom0_pf), .error_count(error_count));
`endif

      $display("[%t] : Checking values for cl_sh_id registers...", $realtime);
      // cl_sh_id0
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h068), .expected_data(32'h1d50_6789), .comp_id(dom0_pf), .error_count(error_count));
      // cl_sh_id1
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h06c), .expected_data(32'h1d51_fedc), .comp_id(dom0_pf), .error_count(error_count));


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


task mgt_version_test();
   begin
      // Test variables
      logic [63:0]  domu_mbx_bar;

      logic [63:0]  dom0_mgmt_bar;
      logic [63:0]  dom0_mbx_bar;

      logic [15:0]  domu_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      domu_pf = EP_BUS_DEV_FNS_PF1;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(domu_pf), .bar_addr(domu_mbx_bar));

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));
`ifndef NO_XDMA
      get_bar(.bar_num(2), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`else
      get_bar(.bar_num(4), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`endif      

      //---------------------------
      // Read Version register
      //---------------------------

      $display("[%t] : Checking Version register from Dom0, BAR0...", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h000), .expected_data(`FPGA_VERSION), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking Version register from Dom0, BAR4...", $realtime);
      reg_read_check(.base_addr(dom0_mbx_bar), .reg_offset(12'h000), .expected_data(`FPGA_VERSION), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking Version register from DomU, BAR0...", $realtime);
      reg_read_check(.base_addr(domu_mbx_bar), .reg_offset(12'h000), .expected_data(`FPGA_VERSION), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking Version register from SPI...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000000), .exp_data(`FPGA_VERSION), .compare(1'b1), .read_data(read_data));


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


task mgt_pcie_cfg_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  app_pf;
      logic [15:0]  domu_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [15:0]  exp_device_id;
      logic [15:0]  exp_vendor_id;
      logic [15:0]  exp_sub_device_id;
      logic [15:0]  exp_sub_vendor_id;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      app_pf = EP_BUS_DEV_FNS;
      domu_pf = EP_BUS_DEV_FNS_PF1;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      // Issue regular register reads to check expected reset values for programmed IDs

      //  0x210 - CL Programmed {Device ID, Vendor ID}
      exp_device_id = 16'h0000;
      exp_vendor_id = 16'h0000;
      $display("[%t] : Checking reset values for CL Device ID and CL Vendor ID from Dom0...", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h210), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      $display("[%t] : Checking reset values for CL Device ID and CL Vendor ID from SPI...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000210), .exp_data({exp_device_id, exp_vendor_id}), .compare(1'b1), .read_data(read_data));
      //  0x214 - CL Programmed {Subsystem Device ID, Subsystem Vendor ID}
      exp_sub_device_id = 16'h0000;
      exp_sub_vendor_id = 16'h0000;
      $display("[%t] : Checking reset values for CL Subsystem Device ID and CL Subsystem Vendor ID from Dom0...", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h214), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      $display("[%t] : Checking reset values for CL Subsystem Device ID and CL Subsystem Vendor ID from SPI...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000214), .exp_data({exp_sub_device_id, exp_sub_vendor_id}), .compare(1'b1), .read_data(read_data));

      // Issue PCIe cfg reads to check all of the ID values

      //  0x00 - {Device ID, Vendor ID}
      $display("[%t] : Checking standard Device ID and Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h000), .expected_data(32'h1040_1d0f), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h000), .expected_data(32'h1041_1d0f), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h000), .expected_data(32'h1042_1d0f), .comp_id(app_pf), .error_count(error_count));
      //  0x2c - {Subsystem ID, Subsystem Vendor ID}
      $display("[%t] : Checking standard Subsystem ID and Subsystem Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h02c), .expected_data(32'h0007_10ee), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h02c), .expected_data(32'h0007_10ee), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h02c), .expected_data(32'h0007_10ee), .comp_id(app_pf), .error_count(error_count));

      //  0xb0 - CL Programmed {Device ID, Vendor ID}
      $display("[%t] : Checking CL Device ID and CL Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(app_pf), .error_count(error_count));
      //  0xb4 - CL Programmed {Subsystem Device ID, Subsystem Vendor ID}
      $display("[%t] : Checking CL Subsystem Device ID and CL Subsystem Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(app_pf), .error_count(error_count));

      // Program register values with Dom0, check with SPI

      write_data = $urandom();
      exp_device_id = write_data[31:16];
      exp_vendor_id = write_data[15:0];
      $display("[%t] : Programming CL Device ID (0x%04x) and CL Vendor ID (0x%04x) from Dom0...", $realtime, exp_device_id, exp_vendor_id);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h210), .write_data(write_data), .comp_id(dom0_pf));
      $display("[%t] : Checking CL Device ID and CL Vendor ID values from SPI...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000210), .exp_data({exp_device_id, exp_vendor_id}), .compare(1'b1), .read_data(read_data));

      write_data = $urandom();
      exp_sub_device_id = write_data[31:16];
      exp_sub_vendor_id = write_data[15:0];
      $display("[%t] : Programming CL Subsystem Device ID (0x%04x) and CL Subsystem Vendor ID (0x%04x) from Dom0...", $realtime, exp_sub_device_id, exp_sub_vendor_id);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h214), .write_data(write_data), .comp_id(dom0_pf));
      $display("[%t] : Checking CL Subsystem Device ID and CL Subsystem Vendor ID values from SPI...", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000214), .exp_data({exp_sub_device_id, exp_sub_vendor_id}), .compare(1'b1), .read_data(read_data));

      // Issue PCIe cfg read to check values

      //  0xb0 - CL Programmed {Device ID, Vendor ID}
      $display("[%t] : Checking CL Device ID and CL Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(app_pf), .error_count(error_count));
      //  0xb4 - CL Programmed {Subsystem Device ID, Subsystem Vendor ID}
      $display("[%t] : Checking CL Subsystem Device ID and CL Subsystem Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(app_pf), .error_count(error_count));

      // Program register values with SPI, check with Dom0

      write_data = $urandom();
      exp_device_id = write_data[31:16];
      exp_vendor_id = write_data[15:0];
      $display("[%t] : Programming CL Device ID (0x%04x) and CL Vendor ID (0x%04x) from SPI...", $realtime, exp_device_id, exp_vendor_id);
      UC_SPI_MODEL.spi_write(.addr(24'h000210), .write_data(write_data));
      $display("[%t] : Checking CL Device ID and CL Vendor ID values from Dom0...", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h210), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));

      write_data = $urandom();
      exp_sub_device_id = write_data[31:16];
      exp_sub_vendor_id = write_data[15:0];
      $display("[%t] : Programming CL Subsystem Device ID (0x%04x) and CL Subsystem Vendor ID (0x%04x) from SPI...", $realtime, exp_sub_device_id, exp_sub_vendor_id);
      UC_SPI_MODEL.spi_write(.addr(24'h000214), .write_data(write_data));
      $display("[%t] : Checking CL Subsystem Device ID and CL Subsystem Vendor ID values from Dom0...", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h214), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));

      // Issue PCIe cfg read to check values

      //  0xb0 - CL Programmed {Device ID, Vendor ID}
      $display("[%t] : Checking CL Device ID and CL Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b0), .expected_data({exp_device_id, exp_vendor_id}), .comp_id(app_pf), .error_count(error_count));
      //  0xb4 - CL Programmed {Subsystem Device ID, Subsystem Vendor ID}
      $display("[%t] : Checking CL Subsystem Device ID and CL Subsystem Vendor ID values for all functions...", $realtime);
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(dom0_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(domu_pf), .error_count(error_count));
      cfg_reg_read_check(.reg_addr(12'h0b4), .expected_data({exp_sub_device_id, exp_sub_vendor_id}), .comp_id(app_pf), .error_count(error_count));


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


task mgt_pcie_cfg_access_test();
   begin
      // Test variables
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [11:0]  reg_addr;

      bit           done;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;


      $display("[%t] : Checking read access to registers at byte addresses 0x000 - 0x0a0...", $realtime);
      done = 1'b0;
      reg_addr = 12'h000;
      do begin
         cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(dom0_pf));
         if (reg_addr !== 12'h0a0) begin
            reg_addr += 12'h004;
         end else begin
            done = 1'b1;
         end
      end while (done !== 1'b1);

      $display("[%t] : Checking values for registers at byte addresses 0x0a4 - 0x0fc...", $realtime);
      done = 1'b0;
      reg_addr = 12'h0a4;
      do begin
         cfg_reg_read_check(.reg_addr(reg_addr), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
         if (reg_addr !== 12'h0fc) begin
            reg_addr += 12'h004;
         end else begin
            done = 1'b1;
         end
      end while (done !== 1'b1);

      $display("[%t] : Checking read access to registers at byte addresses 0x100 - 0x378...", $realtime);
      done = 1'b0;
      reg_addr = 12'h100;
      do begin
         cfg_reg_read(.reg_addr(reg_addr), .read_data(read_data), .comp_id(dom0_pf));
         if (reg_addr !== 12'h378) begin
            reg_addr += 12'h004;
         end else begin
            done = 1'b1;
         end
      end while (done !== 1'b1);

      $display("[%t] : Checking values for registers at byte addresses 0x37c - 0xffc...", $realtime);
      done = 1'b0;
      reg_addr = 12'h37c;
      do begin
         cfg_reg_read_check(.reg_addr(reg_addr), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
         if (reg_addr !== 12'hffc) begin
            reg_addr += 12'h004;
         end else begin
            done = 1'b1;
         end
      end while (done !== 1'b1);

      $display("[%t] : Checking that write request into reserved area has no effect...", $realtime);
      cfg_reg_write(.reg_addr(12'h0b0), .write_data($urandom()), .comp_id(dom0_pf));


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


task mgt_sh_cl_ctl_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      // sh_cl_ctl0 (scratchpad[5])
      write_data = $urandom();
      $display("[%t] : Programming sh_cl_ctl0 with random data (0x%08x)", $realtime, write_data);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f4), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f4), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

      // sh_cl_ctl1 (scratchpad[6])
      write_data = $urandom();
      $display("[%t] : Programming sh_cl_ctl1 with random data (0x%08x)", $realtime, write_data);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f8), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0f8), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

      // DEBUG: For now there is no way to check that the above values made it into CL (the ports are not connected to any logic)
      //        Visual verification of the waves was done to make sure the signal connections looked okay (20161021)

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


task mgt_gpi_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [63:0]  gpi_base;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      // GPI [0] : DDR 0 Status Interface
      // GPI [1] : DDR 1 Status Interface
      // GPI [2] : DDR 2 Status Interface
      // GPI [3] : DDR 3 Status Interface
      for (int gpi_num = 0; gpi_num < 4; gpi_num++) begin
         gpi_base = dom0_mgmt_bar + 64'h1800 + (gpi_num << 8);
         $display("[%t] : Checking that GPI[%1d] returns 0x0000_0000 from offsets 0x000 and 0x004", $realtime, gpi_num);
         for (logic [11:0] reg_offset = 12'h000; reg_offset < 12'h008; reg_offset = reg_offset + 12'h004) begin
            reg_read_check(.base_addr(gpi_base), .reg_offset(reg_offset), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
         end

         $display("[%t] : Checking that GPI[%1d] returns 0xdddd_ffff from unmapped offsets", $realtime, gpi_num);
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h018), .expected_data(32'hdddd_ffff), .comp_id(dom0_pf), .error_count(error_count));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h01c), .expected_data(32'hdddd_ffff), .comp_id(dom0_pf), .error_count(error_count));
         for (logic [11:0] reg_offset = 12'h030; reg_offset < 12'h100; reg_offset = reg_offset + 12'h004) begin
            reg_read_check(.base_addr(gpi_base), .reg_offset(reg_offset), .expected_data(32'hdddd_ffff), .comp_id(dom0_pf), .error_count(error_count));
         end

         write_data = $urandom();
         $display("[%t] : Programming GPI[%1d] offset 0x00 with random data (0x%08x)", $realtime, gpi_num, write_data);
         reg_write(.base_addr(gpi_base), .reg_offset(12'h000), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h000), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
         reg_write(.base_addr(gpi_base), .reg_offset(12'h000), .write_data(32'h0000_0000), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h000), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));

         write_data = $urandom();
         $display("[%t] : Programming GPI[%1d] offset 0x04 with random data (0x%08x)", $realtime, gpi_num, write_data);
         reg_write(.base_addr(gpi_base), .reg_offset(12'h004), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h004), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
         reg_write(.base_addr(gpi_base), .reg_offset(12'h004), .write_data(32'h0000_0000), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h004), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
      end

      // GPI [4] : Aurora Status Interface
      for (int gpi_num = 4; gpi_num < 5; gpi_num++) begin
         gpi_base = dom0_mgmt_bar + 64'h1800 + (gpi_num << 8);
// DEBUG: Comment out the test code until Aurora compile issues are resolved
         $display("[%t] : Not checking any GPI[%1d] functionality yet (Aurora)", $realtime, gpi_num);
/*
         $display("[%t] : Checking that GPI[%1d] returns 0x0000_0000 from offsets 0x000 and 0x004", $realtime, gpi_num);
         for (logic [11:0] reg_offset = 12'h000; reg_offset < 12'h008; reg_offset = reg_offset + 12'h004) begin
            reg_read_check(.base_addr(gpi_base), .reg_offset(reg_offset), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
         end

         $display("[%t] : Checking that GPI[%1d] returns 0xaaaa_ffff from offsets other than 0x000 and 0x004", $realtime, gpi_num);
         for (logic [11:0] reg_offset = 12'h008; reg_offset < 12'h100; reg_offset = reg_offset + 12'h004) begin
            reg_read_check(.base_addr(gpi_base), .reg_offset(reg_offset), .expected_data(32'haaaa_ffff), .comp_id(dom0_pf), .error_count(error_count));
         end

         write_data = $urandom();
         $display("[%t] : Programming GPI[%1d] offset 0x00 with random data (0x%08x)", $realtime, gpi_num, write_data);
         reg_write(.base_addr(gpi_base), .reg_offset(12'h000), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h000), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
         reg_write(.base_addr(gpi_base), .reg_offset(12'h000), .write_data(32'h0000_0000), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h000), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));

         write_data = $urandom();
         $display("[%t] : Programming GPI[%1d] offset 0x04 with random data (0x%08x)", $realtime, gpi_num, write_data);
         reg_write(.base_addr(gpi_base), .reg_offset(12'h004), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h004), .expected_data(write_data[7:0]), .comp_id(dom0_pf), .error_count(error_count));
         reg_write(.base_addr(gpi_base), .reg_offset(12'h004), .write_data(32'h0000_0000), .comp_id(dom0_pf));
         reg_read_check(.base_addr(gpi_base), .reg_offset(12'h004), .expected_data(32'h0000_0000), .comp_id(dom0_pf), .error_count(error_count));
*/
      end

      // GPI [5] : HMC Status Interface
      for (int gpi_num = 5; gpi_num < 6; gpi_num++) begin
         gpi_base = dom0_mgmt_bar + 64'h1800 + (gpi_num << 8);
// DEBUG: HMC wrapper with status interface isn't available yet
         $display("[%t] : Not checking any GPI[%1d] functionality yet (HMC)", $realtime, gpi_num);
      end

      // GPI [6] : (unused)
      // GPI [7] : (unused)
      for (int gpi_num = 6; gpi_num < 8; gpi_num++) begin
         gpi_base = dom0_mgmt_bar + 64'h1800 + (gpi_num << 8);
         $display("[%t] : Checking that GPI[%1d] returns 0xbaad_0006 from all offsets", $realtime, gpi_num);
         for (logic [11:0] reg_offset = 12'h000; reg_offset < 12'h100; reg_offset = reg_offset + 12'h004) begin
            reg_read_check(.base_addr(gpi_base), .reg_offset(reg_offset), .expected_data(32'hbaad_0006), .comp_id(dom0_pf), .error_count(error_count));
         end
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


task mgt_pr_isolate_test();
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

      int           error_count;
      logic         fail;

      bit           check_msix;

      cl_base = 64'h0000_0000_0000_0000;

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


      //---------------------------
      // Program timeout registers
      //---------------------------

`ifndef NO_XDMA
      // DEBUG: Need a way to check isolation without using timeout
`else
      // Enable Dom0 PCIe Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 17); // PCIe Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Programming PCIe timeout value of 0x400", $realtime);
      write_data = 32'h0000_0400;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Programming PCIe timeout read data value to 0x7357_da7a", $realtime);
      write_data = 32'h7357_da7a;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h264), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h264), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling PCIe timeout", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data |= (1'b1 << 5);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
`endif

      //---------------------------
      // Enable and test isolation
      //---------------------------

      $display("[%t] : Issuing PCIe slave access to CL register (not isolated yet, expect a valid response)", $realtime);
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      $display("[%t] : Enabling PR Isolation", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h8000_0000; // Set bit [31] to enable PR Isolation
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

`ifndef NO_XDMA
      // DEBUG: Need a way to check isolation without using timeout
      wait_for_clock(200);
`else
      $display("[%t] : Issuing PCIe slave read access to CL register (expect a timeout)", $realtime);
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h7357_da7a), .comp_id(app_pf), .error_count(error_count));

      $display("[%t] : Issuing PCIe slave write access to CL register (expect a timeout)", $realtime);
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data(write_data), .comp_id(app_pf));
`endif

      //---------------------------
      // Wait for interrupt
      //---------------------------

`ifndef NO_XDMA
      // DEBUG: Need a way to check isolation without using timeout
`else
      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end

      $display("[%t] : Clearing the PCIe timeout event status", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00020000), .comp_id(dom0_pf));
`endif

      //---------------------------
      // Check status
      //---------------------------

`ifndef NO_XDMA
      // DEBUG: Need a way to check isolation without using timeout
`else
      // Note: Bits [1:0] in read data reports Read/~Write for transaction
      //        01 : Read
      //        10 : Write
      //        00 : Other (timeout while in ADDR state)
      $display("[%t] : Check the value of cfg_pcis_to_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h268), .expected_data({base_addr[31:2], 2'b00}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h26c), .expected_data(base_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Check the value of cfg_pcis_to_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0002), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Reset the timeout status count
      write_data = $urandom();
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
`endif

      //---------------------------
      // Disable isolation
      //---------------------------

      $display("[%t] : Disabling PR Isolation", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h8000_0000); // Clear bit [31] to disable PR Isolation
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Issuing PCIe slave access to CL register (not isolated anymore, expect a valid response again)", $realtime);
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));


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


task mgt_pr_isolate_active_test();
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

      logic [63:0]  ddr0_test_addr;
      logic [7:0]   ddr0_axi_len;
      logic [7:0]   ddr0_last_len;

      logic [63:0]  ddr1_test_addr;
      logic [7:0]   ddr1_axi_len;
      logic [7:0]   ddr1_last_len;

      logic [63:0]  ddr2_test_addr;
      logic [7:0]   ddr2_axi_len;
      logic [7:0]   ddr2_last_len;

      logic [63:0]  ddr3_test_addr;
      logic [7:0]   ddr3_axi_len;
      logic [7:0]   ddr3_last_len;

      int           exp_dw_count;

      int           error_count;
      logic         fail;

      cl_base = 64'h0000_0000_0000_0000;

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


      //---------------------------
      // Enable and test isolation
      //---------------------------

      exp_dw_count = 128; // 512 bytes
      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] > (12'hfff - (4*exp_dw_count) + 12'h001));

      // Zero out some address bits in preparation for addr loop mode
      test_addr[31:16] = 16'h0000;

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end


      gen_random_access_addr(.addr(ddr0_test_addr));

      // Zero out some address bits in preparation for addr loop mode
      ddr0_test_addr[31:16] = 16'h0000;

      if (ddr0_test_addr[5:2] == 4'h0) begin
         ddr0_axi_len = 8'h07;
         ddr0_last_len = 8'h00;
      end else begin
         ddr0_axi_len = 8'h08;
         ddr0_last_len = 8'h10 - test_addr[5:2];
      end


      gen_random_access_addr(.addr(ddr1_test_addr));

      // Zero out some address bits in preparation for addr loop mode
      ddr1_test_addr[31:16] = 16'h0000;

      if (ddr1_test_addr[5:2] == 4'h0) begin
         ddr1_axi_len = 8'h07;
         ddr1_last_len = 8'h00;
      end else begin
         ddr1_axi_len = 8'h08;
         ddr1_last_len = 8'h10 - test_addr[5:2];
      end


      gen_random_access_addr(.addr(ddr2_test_addr));

      // Zero out some address bits in preparation for addr loop mode
      ddr2_test_addr[31:16] = 16'h0000;

      if (ddr2_test_addr[5:2] == 4'h0) begin
         ddr2_axi_len = 8'h07;
         ddr2_last_len = 8'h00;
      end else begin
         ddr2_axi_len = 8'h08;
         ddr2_last_len = 8'h10 - test_addr[5:2];
      end


      gen_random_access_addr(.addr(ddr3_test_addr));

      // Zero out some address bits in preparation for addr loop mode
      ddr3_test_addr[31:16] = 16'h0000;

      if (ddr3_test_addr[5:2] == 4'h0) begin
         ddr3_axi_len = 8'h07;
         ddr3_last_len = 8'h00;
      end else begin
         ddr3_axi_len = 8'h08;
         ddr3_last_len = 8'h10 - test_addr[5:2];
      end


      wait (`SH_PATH.sh_cl_ddr_is_ready);

      fork
         begin
            // PCIe
            request_bus_control();
            program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));
            release_bus_control();
         end
         begin
            // DDR 0
            request_bus_control();
            program_cl(.base_addr(base_addr + 12'h100), .test_addr(ddr0_test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(ddr0_axi_len), .last_len(ddr0_last_len), .enable_write(1'b1), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));
            release_bus_control();
         end
         begin
            // DDR 1
            request_bus_control();
            program_cl(.base_addr(base_addr + 12'h200), .test_addr(ddr1_test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(ddr1_axi_len), .last_len(ddr1_last_len), .enable_write(1'b1), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));
            release_bus_control();
         end
         begin
            // DDR 2
            request_bus_control();
            program_cl(.base_addr(base_addr + 12'h300), .test_addr(ddr2_test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(ddr2_axi_len), .last_len(ddr2_last_len), .enable_write(1'b1), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));
            release_bus_control();
         end
         begin
            // DDR 3
            request_bus_control();
            program_cl(.base_addr(base_addr + 12'h400), .test_addr(ddr3_test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(ddr3_axi_len), .last_len(ddr3_last_len), .enable_write(1'b1), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));
            release_bus_control();
         end
      join

      // Start CL activity
      reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));
      reg_write(.base_addr(base_addr + 12'h100), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));
      reg_write(.base_addr(base_addr + 12'h200), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));
      reg_write(.base_addr(base_addr + 12'h300), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));
      reg_write(.base_addr(base_addr + 12'h400), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));

      // Enable isolation before PCIe and DDR activity is complete
      wait_for_clock(100);
      $display("[%t] : Enabling PR Isolation", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h8000_0000; // Set bit [31] to enable PR Isolation
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

      // DEBUG: Need to check waves for isolation behavior on PCIe and DDR AXI buses
      wait_for_clock(10000);

      //---------------------------
      // Disable isolation
      //---------------------------

      $display("[%t] : Disabling PR Isolation", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h8000_0000); // Clear bit [31] to disable PR Isolation
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));


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


task mgt_cl_reset_test();
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

      int           error_count;
      logic         fail;

      cl_base = 64'h0000_0000_0000_0000;

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


      //---------------------------
      // Program cl_tst registers
      //---------------------------

      $display("[%t] : Checking initial CL register values", $realtime);
      // PCIe cl_tst
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 0 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h100), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 1 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h200), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // Ext DDR cl_tst
      reg_read_check(.base_addr(base_addr + 12'h300), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 2 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h400), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

/* TODO: Add in HMC checks
      // HMC 0 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h500), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 1 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h600), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 2 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h700), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 3 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h800), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));
*/

/* TODO: Add in Aurora checks
      // Aurora 0 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'h900), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 1 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'ha00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 2 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'hb00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 3 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'hc00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));
*/

      // MSI-X cl_int_tst
      reg_read_check(.base_addr(base_addr + 12'hd00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));


      $display("[%t] : Checking programming for CL registers", $realtime);
      // PCIe cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 0 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h100), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h100), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 1 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h200), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h200), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // Ext DDR cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h300), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h300), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 2 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h400), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h400), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

/* TODO: Add in HMC checks
      // HMC 0 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h500), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h500), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // HMC 1 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h600), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h600), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // HMC 2 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h700), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h700), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));

      // HMC 3 cl_tst
      write_data = $urandom();
      reg_write(.base_addr(base_addr + 12'h800), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h800), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h023f_3ffb), .comp_id(app_pf), .error_count(error_count));
*/

/* TODO: Add in Aurora checks
      // Aurora 0 cl_pkt_tst
      write_data = $urandom() & ~(32'h0000_001f);
      reg_write(.base_addr(base_addr + 12'h900), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'h900), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 1 cl_pkt_tst
      write_data = $urandom() & ~(32'h0000_001f);
      reg_write(.base_addr(base_addr + 12'ha00), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'ha00), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 2 cl_pkt_tst
      write_data = $urandom() & ~(32'h0000_001f);
      reg_write(.base_addr(base_addr + 12'hb00), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'hb00), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 3 cl_pkt_tst
      write_data = $urandom() & ~(32'h0000_001f);
      reg_write(.base_addr(base_addr + 12'hc00), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'hc00), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));
*/

      // MSI-X cl_int_tst
      write_data = $urandom() & ~(32'hffff_f0ff); // Only keep [11:8]
      reg_write(.base_addr(base_addr + 12'hd00), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));
      reg_read_check(.base_addr(base_addr + 12'hd00), .reg_offset(12'h000), .expected_data(write_data), .data_mask(32'h0000_0f00), .comp_id(app_pf), .error_count(error_count));


      //---------------------------
      // Reset CL
      //---------------------------

      $display("[%t] : Resetting CL", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h4000_0000; // Set bit [30] to reset CL
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
      wait_for_clock(100);
      write_data = read_data & ~(32'h4000_0000); // Clear bit [30] to take CL out of reset
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0fc), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));


      //---------------------------
      // Check cl_tst registers
      //---------------------------

      $display("[%t] : Checking CL register values after reset", $realtime);
      // PCIe cl_tst
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 0 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h100), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 1 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h200), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // Ext DDR cl_tst
      reg_read_check(.base_addr(base_addr + 12'h300), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // CL DDR 2 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h400), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

/* TODO: Add in HMC checks
      // HMC 0 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h500), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 1 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h600), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 2 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h700), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));

      // HMC 3 cl_tst
      reg_read_check(.base_addr(base_addr + 12'h800), .reg_offset(12'h000), .expected_data(32'h0100_0000), .comp_id(app_pf), .error_count(error_count));
*/

/* TODO: Add in Aurora checks
      // Aurora 0 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'h900), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 1 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'ha00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 2 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'hb00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));

      // Aurora 3 cl_pkt_tst
      reg_read_check(.base_addr(base_addr + 12'hc00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .data_mask(32'h0000_001f), .comp_id(app_pf), .error_count(error_count));
*/

      // MSI-X cl_int_tst
      reg_read_check(.base_addr(base_addr + 12'hd00), .reg_offset(12'h000), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));


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


task mgt_pcie_spi_access_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      //---------------------------
      // Access mgt_top registers
      //---------------------------

      // In mgt_top, looking for rql_int_sel[1] and rql_valid[0] to be asserted at the same time
      //  (rql_int_sel[1] = 1'b1 indicates SPI access, rql_valid[0] indicates PCIe access)

      fork
         begin
            // PCIe transactions
            for (int pcie_count = 0; pcie_count < 2000; pcie_count++) begin
               // Version
               reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h000), .expected_data(`FPGA_VERSION), .comp_id(dom0_pf), .error_count(error_count));
            end
         end
         begin
            // SPI transactions
            for (int spi_count = 0; spi_count < 400; spi_count++) begin
               // CL SH Status1
               UC_SPI_MODEL.spi_read(.addr(24'h000064), .exp_data(`CL_VERSION), .compare(1'b1), .read_data(read_data));
            end
         end
      join
      

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


task mgt_spi_disable_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));


      //---------------------------
      // Disable SPI access
      //---------------------------
/* DEBUG: cfg_spi_disable is currently tied low in mgt_top.sv, so SPI access can't be disabled
      $display("[%t] : Disabling SPI access", $realtime);
      write_data = 32'h0000_0001;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h000), .write_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h000), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));
*/
      //---------------------------
      // Attempt SPI access
      //---------------------------
      $display("[%t] : Attempting SPI access (expect response with 0x0 data)", $realtime);
      UC_SPI_MODEL.spi_read(.addr(24'h000000), .read_data(read_data));
      if (read_data == `FPGA_VERSION)  begin
         $display("[%t] : *** ERROR *** SPI read access completed while SPI was supposed to be disabled", $realtime);
         error_count++;
      end else if (read_data !== 32'h0000_0000) begin
         $display("[%t] : *** ERROR *** SPI read access returned non-zero data (0x%08x) while SPI was supposed to be disabled", $realtime, read_data);
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


task mgt_decode_test();
   begin
      // Test variables
      logic [63:0]  dom0_mgmt_bar;
      logic [63:0]  dom0_mbx_bar;

      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;

      int           error_count;
      logic         fail;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));
`ifndef NO_XDMA
      get_bar(.bar_num(2), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`else
      get_bar(.bar_num(4), .comp_id(dom0_pf), .bar_addr(dom0_mbx_bar));
`endif


      //---------------------------
      // Check each decode range
      //---------------------------

      $display("[%t] : Issuing Dom0, BAR0 reads for each decode range in mgt_top", $realtime);

      // int_dec_ver
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_its
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_wdg
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_mbx_tx (NOTE: Use Mailbox BAR)
      reg_read(.base_addr(dom0_mbx_bar), .reg_offset(12'h020), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_mbx_rx (NOTE: Use Mailbox BAR)
      reg_read(.base_addr(dom0_mbx_bar), .reg_offset(12'h030), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_mbx1_tx
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h040), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_mbx1_rx
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h050), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_cl_status
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h060), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_i2c
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h080), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_scratch
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h0d0), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_drp_cmd
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h100), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_drp_dat
`ifdef NO_XDMA
// DEBUG: Need to include this again after design is updated
//        (The fix will not be available before KaOS qualification)
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h104), .read_data(read_data), .comp_id(dom0_pf));
`endif
      // int_dec_misc_ctl
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h200), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_pci_cfg
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h300), .read_data(read_data), .comp_id(dom0_pf));

      // Unmapped
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h400), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h500), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h600), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h700), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h800), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h900), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'ha00), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'hb00), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'hc00), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'hd00), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'he00), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf00), .read_data(read_data), .comp_id(dom0_pf));

      // int_dec_atg[0]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1000), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_atg[1]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1100), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_atg[2]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1200), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_atg[3]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1300), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_qspi
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1400), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_icap
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1500), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));

      // Unmapped
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1600), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1700), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));

      // int_dec_gpi[0]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1800), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[1]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1900), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[2]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1a00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[3]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1b00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[4]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1c00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[5]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1d00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[6]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1e00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      // int_dec_gpi[7]
      reg_read(.base_addr(dom0_mgmt_bar + 64'h1f00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      
      // Unmapped
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3800), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3900), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3a00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3b00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3c00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3d00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3e00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));
      reg_read(.base_addr(dom0_mgmt_bar + 64'h3f00), .reg_offset(12'h000), .read_data(read_data), .comp_id(dom0_pf));


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


task mgt_wdg_test();
   begin
      // Test variables
      logic [63:0]  domu_mgmt_bar;

      logic [63:0]  dom0_mgmt_bar;

      logic [15:0]  domu_pf;
      logic [15:0]  dom0_pf;

      logic [31:0]  read_data;
      logic [31:0]  write_data;

      logic [31:0]  watchdog_value;

      int           count;

      int           error_count;
      logic         fail;

      bit           check_msix;

      error_count = 0;
      fail = 0;

      sys_init(.error_count(error_count));

      domu_pf = EP_BUS_DEV_FNS_PF1;
      dom0_pf = EP_BUS_DEV_FNS_PF2;

      get_bar(.bar_num(0), .comp_id(domu_pf), .bar_addr(domu_mgmt_bar));

      get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

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


      //---------------------------
      // Check register access
      //---------------------------

      $display("[%t] : Checking initial Watchdog timer value from Dom0", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));
      $display("[%t] : Checking initial Watchdog timer value from DomU", $realtime);
      reg_read_check(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .expected_data(32'h00000000), .comp_id(domu_pf), .error_count(error_count));

      $display("[%t] : Checking Dom0 access to other Watchdog registers", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking that DomU access to other Watchdog registers is not allowed", $realtime);
      reg_read_check(.base_addr(domu_mgmt_bar), .reg_offset(12'h014), .expected_data(32'hdeadbeef), .comp_id(domu_pf), .error_count(error_count));
      reg_read_check(.base_addr(domu_mgmt_bar), .reg_offset(12'h018), .expected_data(32'hdeadbeef), .comp_id(domu_pf), .error_count(error_count));
      reg_read_check(.base_addr(domu_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'hdeadbeef), .comp_id(domu_pf), .error_count(error_count));


      //---------------------------
      // Check basic functionality
      //---------------------------

      $display("[%t] : Enabling the Dom0 Watchdog interrupt", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 4);  // Watchdog
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .expected_data(write_data), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Programming watchdog timeout value of 0x100", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .write_data(32'h00000100), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .expected_data(32'h00000100), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000101), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000101), .comp_id(dom0_pf), .error_count(error_count));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 Watchdog Timer interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            count++;
         end while ((read_data[4] !== 1'b1) && (count < 200));
         if (count == 200) begin
            $display("[%t] : *** ERROR *** Watchdog interrupt status bit was not set", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Disabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000000), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Verifying that sts_timeout_num value is non-zero", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data == 32'h0) begin
         $display("[%t] : *** ERROR *** sts_timeout_num was 0x%08x after watchdog should have timed out", $realtime, read_data);
         error_count++;
      end

      $display("[%t] : Clearing the watchdog event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00000010), .comp_id(dom0_pf));

      $display("[%t] : Petting the watchdog from DomU to clear sts_timeout_num value", $realtime);
      reg_write(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .write_data(32'h00000000), .comp_id(domu_pf));

      $display("[%t] : Verifying that sts_timeout_num value was cleared", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));


      //---------------------------
      // Verify that writing to register 0xc will clear the sts_timeout_num value (instead of petting from DomU)
      //---------------------------

      $display("[%t] : Enabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000101), .comp_id(dom0_pf));

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 Watchdog Timer interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         count = 0;
         do begin
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
            count++;
         end while ((read_data[4] !== 1'b1) && (count < 200));
         if (count == 200) begin
            $display("[%t] : *** ERROR *** Watchdog interrupt status bit was not set", $realtime);
            error_count++;
         end
      end

      $display("[%t] : Disabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000000), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Verifying that sts_timeout_num value is non-zero", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data == 32'h0) begin
         $display("[%t] : *** ERROR *** sts_timeout_num was 0x%08x after watchdog should have timed out", $realtime, read_data);
         error_count++;
      end

      $display("[%t] : Writing to register to clear sts_timeout_num value", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .write_data(32'h00000000), .comp_id(dom0_pf));

      $display("[%t] : Verifying that sts_timeout_num value was cleared", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Clearing the watchdog event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00000010), .comp_id(dom0_pf));


      //---------------------------
      // Check DomU "pet" functionality
      //---------------------------

      $display("[%t] : Programming watchdog timeout value of 0x55555555", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .write_data(32'h55555555), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .expected_data(32'h55555555), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000101), .comp_id(dom0_pf));

      // Wait for the timer value to increase to a reasonable value
      wait_for_clock(4000);

      $display("[%t] : Reading the watchdog timer value from Dom0", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .read_data(watchdog_value), .comp_id(dom0_pf));

      $display("[%t] : Reading the watchdog timer value from DomU", $realtime);
      reg_read(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(domu_pf));
      if (read_data >= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not less than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Petting the watchdog timer from DomU (should reset timer value)", $realtime);
      reg_write(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .write_data(32'h00000000), .comp_id(domu_pf));

      $display("[%t] : Reading the watchdog timer value from Dom0", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data <= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not greater than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Reading the watchdog timer value from DomU", $realtime);
      reg_read(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(domu_pf));
      if (read_data <= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not greater than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Disabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000000), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Clearing the watchdog event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00000010), .comp_id(dom0_pf));

      $display("[%t] : Writing to register to clear sts_timeout_num value", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .write_data(32'h00000000), .comp_id(dom0_pf));

      $display("[%t] : Verifying that sts_timeout_num value was cleared", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));


      //---------------------------
      // Check DomU "pet" functionality again
      //---------------------------

      $display("[%t] : Programming watchdog timeout value of 0xaaaaaaaa", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .write_data(32'haaaaaaaa), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h018), .expected_data(32'haaaaaaaa), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Enabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000101), .comp_id(dom0_pf));

      // Wait for the timer value to increase to a reasonable value
      wait_for_clock(4000);

      $display("[%t] : Reading the watchdog timer value from Dom0", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .read_data(watchdog_value), .comp_id(dom0_pf));

      $display("[%t] : Reading the watchdog timer value from DomU", $realtime);
      reg_read(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(domu_pf));
      if (read_data >= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not less than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Petting the watchdog timer from DomU (should reset timer value)", $realtime);
      reg_write(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .write_data(32'h00000000), .comp_id(domu_pf));

      $display("[%t] : Reading the watchdog timer value from Dom0", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data <= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not greater than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Reading the watchdog timer value from DomU", $realtime);
      reg_read(.base_addr(domu_mgmt_bar), .reg_offset(12'h010), .read_data(read_data), .comp_id(domu_pf));
      if (read_data <= watchdog_value) begin
         $display("[%t] : *** ERROR *** Watchdog timer value of 0x%08x was not greater than previous value of 0x%08x", $realtime, read_data, watchdog_value);
         error_count++;
      end

      $display("[%t] : Disabling the watchdog timer", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .write_data(32'h00000000), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h014), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Clearing the watchdog event", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00000010), .comp_id(dom0_pf));

      $display("[%t] : Writing to register to clear sts_timeout_num value", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .write_data(32'h00000000), .comp_id(dom0_pf));

      $display("[%t] : Verifying that sts_timeout_num value was cleared", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h01c), .expected_data(32'h00000000), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Disabling the Dom0 Watchdog interrupt", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0010);  // Clear bit [4], Watchdog
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));


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
