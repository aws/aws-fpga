// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

task cl_common_test(
                    input logic [63:0] cl_base = 64'h0,
                    logic [63:0]       test_addr = 64'h0,
                    logic [31:0]       test_data = 32'h6c93_af50,
                    int                hmc_num = 99,
                    int                ddr_num = 99
                   );
   begin

      // Test variables
      bit           addr_loop_mode;
      logic [5:0]   loop_shift;
      bit           iter_mode;
      logic [63:0]  num_iter;

      bit           cont_mode;
      bit           user_id_mode;
      bit           vary_len;
      logic [7:0]   axi_len;
      logic [8:0]   max_num_rd_req;

      logic [15:0]  num_inst;

      bit           check_ram;

      logic [63:0]  tgt_bar;
      logic [63:0]  base_addr;

      logic [63:0]  cycle_count;
      logic [31:0]  write_data;
      logic [31:0]  read_data;
      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [15:0]  wr_user;
      logic [15:0]  rd_user;

      logic [63:0]  running_addr;
      logic [31:0]  running_data;
      logic [4:0]   loop_limit;
      logic [4:0]   outer_loop_index;
      logic [7:0]   inner_loop_index;

      int           error_count;
      logic         fail;


      if ($test$plusargs("ADDR_LOOP_MODE")) begin
         addr_loop_mode = 1'b1;
      end else begin
         addr_loop_mode = 1'b0;
      end

      if (!$value$plusargs("LOOP_SHIFT=0x%x", loop_shift)) begin
         loop_shift = 6'h20;
      end

      if ($test$plusargs("ITER_MODE")) begin
         iter_mode = 1'b1;
      end else begin
         iter_mode = 1'b0;
      end

      if (!$value$plusargs("NUM_ITER=%d", num_iter)) begin
         num_iter = 64'h0400;
      end

      if ($test$plusargs("CONT_MODE")) begin
         cont_mode = 1'b1;
      end else begin
         cont_mode = 1'b0;
      end

      if ($test$plusargs("USER_ID_MODE")) begin
         user_id_mode = 1'b1;
      end else begin
         user_id_mode = 1'b0;
      end

      if (!$value$plusargs("WR_USER=0x%x", wr_user)) begin
         wr_user = 16'h0000;
      end

      if (!$value$plusargs("RD_USER=0x%x", rd_user)) begin
         rd_user = 16'h0000;
      end

      if ($value$plusargs("AXI_LEN=%d", axi_len)) begin
         vary_len = 1'b0;
         if (axi_len > 8'h07) begin
            $display("[%t] : *** WARNING *** Specified AXI_LEN setting of 0x%02x is beyond the supported range.  Using 0x07 instead.", $realtime, axi_len);
            axi_len = 8'h07;
         end
      end else if ($test$plusargs("VARY_LEN")) begin
         vary_len = 1'b1;
         axi_len = 8'h00;
      end else begin
         vary_len = 1'b0;
         axi_len = 8'h07;
      end

      if (!$value$plusargs("MAX_RD_REQ=0x%x", max_num_rd_req)) begin
         max_num_rd_req = 9'h00f;
      end

      if (!$value$plusargs("NUM_INST=%d", num_inst)) begin
         num_inst = 16'h0000;
      end

      if($test$plusargs("CHECK_RAM")) begin
         check_ram = 1'b1;
      end else begin
         check_ram = 1'b0;
      end


      error_count = 0;
      fail = 0;


      sys_init(.error_count(error_count));

`ifndef NO_XDMA
      get_bar(.bar_num(4), .comp_id(EP_BUS_DEV_FNS), .bar_addr(tgt_bar));
`else
      get_bar(.bar_num(0), .comp_id(EP_BUS_DEV_FNS), .bar_addr(tgt_bar));
`endif

      base_addr = tgt_bar + cl_base;

      if (hmc_num != 99)
        begin
           $display("[%t] : *** ERROR *** When hmc_num is specified, HMC_PRESENT must be defined", $realtime);
           $finish;
        end

      //Note all the DDR are ready about the same time, so just need to look at one (SH design is complicated to get ready becuase of one DDR in SH)
      if (ddr_num != 99)
      begin
            wait (`CL_PATH.all_ddr_is_ready[0]);
      end

      // Program CL registers and start reads and writes
      program_cl(.base_addr(base_addr), .addr_loop_mode(addr_loop_mode), .loop_shift(loop_shift), .user_id_mode(user_id_mode), .iter_mode(iter_mode), .cont_mode(cont_mode), .num_iter(num_iter), .max_num_rd_req(max_num_rd_req), .test_addr(test_addr), .test_data(test_data), .axi_len(axi_len), .num_inst(num_inst), .wr_user(wr_user), .rd_user(rd_user), .vary_len(vary_len), .error_count(error_count));

      $display("[%t] : Finished transmission of PCI-Express TLPs", $realtime);

      //---------------------------
      // Check RAM contents
      //---------------------------
      if (check_ram == 1'b1) begin
         $display("[%t] : Checking RAM contents...", $realtime);
         // Read 0x74 to get Read RAM write pointer (5-bit value), used for upper loop limit below
         reg_read(.base_addr(base_addr), .reg_offset(12'h074), .read_data(read_data));
         if (read_data == 32'h0) begin
            $display("[%t] : *** ERROR *** Read RAM write pointer set to 0x0, expecting non-zero value before checking RAM contents", $realtime);
            $finish;
         end
         loop_limit = read_data[4:0];
         // Write index register (0x60), Read RAM contents (0x64 - 0x70)
         running_addr = test_addr;
         running_data = test_data;
         for (outer_loop_index=5'h0; outer_loop_index<loop_limit; outer_loop_index=outer_loop_index+5'h1) begin
            reg_write(.base_addr(base_addr), .reg_offset(12'h060), .write_data({19'h0, outer_loop_index, 8'h0}));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h064), .expected_data(running_addr[31:0]), .error_count(error_count));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h068), .expected_data(running_addr[63:32]), .error_count(error_count));
            running_addr += 64'h40;
            for (inner_loop_index=8'h0; inner_loop_index<8'h10; inner_loop_index=inner_loop_index+8'h1) begin
               reg_write(.base_addr(base_addr), .reg_offset(12'h060), .write_data({19'h0, outer_loop_index, inner_loop_index}));
               reg_read_check(.base_addr(base_addr), .reg_offset(12'h06c), .expected_data(running_data), .error_count(error_count));
               reg_read_check(.base_addr(base_addr), .reg_offset(12'h070), .expected_data(running_data), .error_count(error_count));
               running_data += 32'h1;
            end
         end
      end

      //---------------------------
      // Check timer values
      //---------------------------
      cycle_count = 64'h0;
      // Check that the write timer value is non-zero
      reg_read(.base_addr(base_addr), .reg_offset(12'h0f0), .read_data(read_data));
      cycle_count[31:0] = read_data;
      reg_read(.base_addr(base_addr), .reg_offset(12'h0f4), .read_data(read_data));
      cycle_count[63:32] = read_data;
      if (cycle_count == 64'h0) begin
         $display("[%t] : *** ERROR *** Write Timer value was 0x0 at end of test.", $realtime);
         fail = 1;
      end

      cycle_count = 64'h0;
      // Check that the read timer value is non-zero
      reg_read(.base_addr(base_addr), .reg_offset(12'h0f8), .read_data(read_data));
      cycle_count[31:0] = read_data;
      reg_read(.base_addr(base_addr), .reg_offset(12'h0fc), .read_data(read_data));
      cycle_count[63:32] = read_data;
      if (cycle_count == 64'h0) begin
         $display("[%t] : *** ERROR *** Read Timer value was 0x0 at end of test.", $realtime);
         fail = 1;
      end

      //---------------------------
      // Check for errors
      //---------------------------
      $display("[%t] : Checking for errors...", $realtime);

      if (iter_mode)
        begin
           cycle_count = 64'h0;
           // Check that the write cycle count is correct
           reg_read(.base_addr(base_addr), .reg_offset(12'h080), .read_data(read_data));
           cycle_count[31:0] = read_data;
           reg_read(.base_addr(base_addr), .reg_offset(12'h084), .read_data(read_data));
           cycle_count[63:32] = read_data;
           if (cycle_count != (num_iter * (num_inst + 16'h1)))
             begin
                $display("[%t] : *** ERROR *** Write cycle count of 0x%016x did not match expected value of 0x%016x", $realtime, cycle_count, (num_iter * (num_inst + 16'h1)));
                fail = 1;
             end

           cycle_count = 64'h0;
           // Check that the read cycle count is correct
           reg_read(.base_addr(base_addr), .reg_offset(12'h088), .read_data(read_data));
           cycle_count[31:0] = read_data;
           reg_read(.base_addr(base_addr), .reg_offset(12'h08c), .read_data(read_data));
           cycle_count[63:32] = read_data;
           if (cycle_count != (num_iter * (num_inst + 16'h1)))
             begin
                $display("[%t] : *** ERROR *** Read cycle count of 0x%016x did not match expected value of 0x%016x", $realtime, cycle_count, (num_iter * (num_inst + 16'h1)));
                fail = 1;
             end

           cycle_count = 64'h0;
           // Check that the read response count is correct
           reg_read(.base_addr(base_addr), .reg_offset(12'h0a0), .read_data(read_data));
           cycle_count[31:0] = read_data;
           reg_read(.base_addr(base_addr), .reg_offset(12'h0a4), .read_data(read_data));
           cycle_count[63:32] = read_data;
           if (cycle_count != (num_iter * (num_inst + 16'h1)))
             begin
                $display("[%t] : *** ERROR *** Read response count of 0x%016x did not match expected value of 0x%016x", $realtime, cycle_count, (num_iter * (num_inst + 16'h1)));
                fail = 1;
             end
        end

      // Check for compare error
      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         fail = 1;
      end

      //---------------------------
      // Report pass/fail status
      //---------------------------
      if (error_count > 0) begin
         $display("[%t] : Detected %3d errors during this test", $realtime, error_count);
         fail = 1;
      end

      if (fail)
        $display("[%t] : *** TEST FAILED ***", $realtime);
      else
        begin
           $display("[%t] :   no errors were detected", $realtime);
           $display("[%t] : *** TEST PASSED ***", $realtime);
        end

      $finish;
   end
endtask


task automatic program_cl(
                          input logic [63:0] base_addr,
                          logic [15:0]       comp_id = EP_BUS_DEV_FNS,
                          bit                addr_loop_mode = 1'b0,
                          logic [5:0]        loop_shift = 6'h20,
                          bit                user_id_mode = 1'b0,
                          bit                iter_mode = 1'b0,
                          bit                cont_mode = 1'b0,
                          logic [63:0]       num_iter = 64'h0400,
                          logic [8:0]        max_num_rd_req = 9'h00f,
                          logic [63:0]       test_addr = 64'h0,
                          logic [31:0]       test_data = 32'h6c93_af50,
                          logic [7:0]        axi_len = 8'h07,
                          logic [7:0]        last_len = 8'h00,
                          logic [15:0]       num_inst = 16'h0000,
                          logic [15:0]       wr_user = 16'h0000,
                          logic [15:0]       rd_user = 16'h0000,
                          bit                vary_len = 1'b0,
                          bit                enable_write = 1'b1,
                          bit                enable_read = 1'b1,
                          bit                compare_read = 1'b1,
                          bit                start_cl = 1'b1,
                          bit                wait_for_done = 1'b1,
                          ref int            error_count
                         );
   begin
`ifdef VIVADO_SIM
      automatic bit reg_access_done = 1'b0;
`endif
      logic [31:0]  write_data;
      logic [31:0]  read_data;
      logic [63:0]  running_addr;
      logic [7:0]   running_len;
      logic [7:0]   axi_index;
      logic [15:0]  axi_user;
      logic [63:0]  loop_count;
      int           timeout_count;

      logic [15:0]  num_wr_inst;
      logic [15:0]  num_rd_inst;

      axi_index = 8'h00;

      //---------------------------
      // CL Config
      //---------------------------
      write_data = 32'h0000_0000;
      if (addr_loop_mode == 1) begin
         write_data[21:16] = loop_shift[5:0];
         write_data[13:8] = loop_shift[5:0];
      end
      write_data[24] = 1'b1; // Always enable Incrementing ID mode
      write_data[7] = user_id_mode;
      write_data[6] = addr_loop_mode;
      write_data[5] = iter_mode;
      write_data[4] = (enable_write & enable_read); // Enable Sync Mode when doing both writes and reads
      write_data[3] = compare_read;
      write_data[2] = 1'b0; // PRBS mode not supported
      write_data[1] = 1'b0; // Incrementing Loop Data mode not supported
      write_data[0] = cont_mode;
      reg_write(.base_addr(base_addr), .reg_offset(12'h000), .write_data(write_data), .comp_id(comp_id));

      //---------------------------
      // Iterations
      //---------------------------
      if (iter_mode == 1) begin
         // Number of write iterations
         if (enable_write == 1'b1) begin
            reg_write(.base_addr(base_addr), .reg_offset(12'h0c0), .write_data(num_iter[31:0]), .comp_id(comp_id));
            reg_write(.base_addr(base_addr), .reg_offset(12'h0c4), .write_data(num_iter[63:32]), .comp_id(comp_id));
            // Check values that were written
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c0), .expected_data(num_iter[31:0]), .error_count(error_count), .comp_id(comp_id));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c4), .expected_data(num_iter[63:32]), .error_count(error_count), .comp_id(comp_id));
         end
         // Number of read iterations
         if (enable_read == 1'b1) begin
            reg_write(.base_addr(base_addr), .reg_offset(12'h0c8), .write_data(num_iter[31:0]), .comp_id(comp_id));
            reg_write(.base_addr(base_addr), .reg_offset(12'h0cc), .write_data(num_iter[63:32]), .comp_id(comp_id));
            // Check values that were written
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c8), .expected_data(num_iter[31:0]), .error_count(error_count), .comp_id(comp_id));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0cc), .expected_data(num_iter[63:32]), .error_count(error_count), .comp_id(comp_id));
         end
      end

      // Set the max number of read requests
      reg_write(.base_addr(base_addr), .reg_offset(12'h014), .write_data(max_num_rd_req), .comp_id(comp_id));

      //----------------------------
      // Program write instructions
      //----------------------------
      if (enable_write == 1'b1) begin
         running_addr = test_addr;
         running_len = axi_len;
         // Initial Index (value will be auto-incremented after write to register at offset 0x2c)
         reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data({24'h000000, axi_index}), .comp_id(comp_id));

         for (int i=0; i<=num_inst; i++)
           begin
              // Addr low
              reg_write(.base_addr(base_addr), .reg_offset(12'h020), .write_data(running_addr[31:0]), .comp_id(comp_id));

              // Addr high
              reg_write(.base_addr(base_addr), .reg_offset(12'h024), .write_data(running_addr[63:32]), .comp_id(comp_id));

              // Write data
              reg_write(.base_addr(base_addr), .reg_offset(12'h028), .write_data(test_data[31:0]), .comp_id(comp_id));

              // Write Instruction length/user
              axi_user = user_id_mode ? wr_user : 16'h0000;

              reg_write(.base_addr(base_addr), .reg_offset(12'h02c), .write_data({axi_user, last_len, running_len}), .comp_id(comp_id));

              running_addr = running_addr + (64 * (running_len + 8'h01)); // Multiply by 64 because that is the largest data width (512 bits)
              if (vary_len == 1'b1) begin
                 running_len = (running_len < 8'h07) ? (running_len + 8'h01) : 8'h00;
              end
           end
      end

      //---------------------------
      // Program read instructions
      //---------------------------
      if (enable_read == 1'b1) begin
         running_addr = test_addr;
         running_len = axi_len;
         // Initial Index (value will be auto-incremented after write to register at offset 0x4c)
         reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data({24'h000000, axi_index}), .comp_id(comp_id));

         for (int i=0; i<=num_inst; i++)
           begin
              // Addr low
              reg_write(.base_addr(base_addr), .reg_offset(12'h040), .write_data(running_addr[31:0]), .comp_id(comp_id));

              // Addr high
              reg_write(.base_addr(base_addr), .reg_offset(12'h044), .write_data(running_addr[63:32]), .comp_id(comp_id));

              // Read data (same as write data)
              reg_write(.base_addr(base_addr), .reg_offset(12'h048), .write_data(test_data[31:0]), .comp_id(comp_id));

              // Read User and Instruction Length
              axi_user = user_id_mode ? rd_user : 16'h0000;

              reg_write(.base_addr(base_addr), .reg_offset(12'h04c), .write_data({axi_user, last_len, running_len}), .comp_id(comp_id));

              running_addr = running_addr + (64 * (running_len + 8'h01));
              if (vary_len == 1'b1) begin
                 running_len = (running_len < 8'h07) ? (running_len + 8'h01) : 8'h00;
              end
           end
      end


      if (enable_write == 1'b1) begin
         num_wr_inst = num_inst;
      end else begin
         num_wr_inst = 16'h0000;
      end

      if (enable_read == 1'b1) begin
         num_rd_inst = num_inst;
      end else begin
         num_rd_inst = 16'h0000;
      end

      // Number of instructions ([31:16] for read, [15:0] for write)
      reg_write(.base_addr(base_addr), .reg_offset(12'h010), .write_data({num_rd_inst, num_wr_inst}), .comp_id(comp_id));

      // Start reads and writes ([1] for reads, [0] for writes)
      if (start_cl == 1'b1) begin
         reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data({30'h00000000, enable_read, enable_write}), .comp_id(comp_id));
      end


      if (wait_for_done == 1'b1) begin
         if ((cont_mode == 1'b1) || (iter_mode == 1'b1)) begin
            if (enable_write == 1'b1) begin
               // Wait for specified number of write loops
               loop_count = 64'h0;
               timeout_count = 0;
               while (loop_count < num_iter) begin
                  reg_read(.base_addr(base_addr), .reg_offset(12'h090), .read_data(read_data), .comp_id(comp_id));
                  loop_count[31:0] = read_data;
                  reg_read(.base_addr(base_addr), .reg_offset(12'h094), .read_data(read_data), .comp_id(comp_id));
                  loop_count[63:32] = read_data;
                  timeout_count = timeout_count + 1;
                  if (timeout_count == 100) begin
                     $display("[%t] : *** ERROR *** Timeout (WR) waiting for loop_count=%d to equal num_iter=%d", $realtime, loop_count, num_iter);
                     $finish;
                  end
               end
            end
            if (enable_read == 1'b1) begin
               // Wait for specified number of read loops
               loop_count = 64'h0;
               timeout_count = 0;
               while (loop_count < num_iter) begin
                  reg_read(.base_addr(base_addr), .reg_offset(12'h098), .read_data(read_data), .comp_id(comp_id));
                  loop_count[31:0] = read_data;
                  reg_read(.base_addr(base_addr), .reg_offset(12'h09c), .read_data(read_data), .comp_id(comp_id));
                  loop_count[63:32] = read_data;
                  timeout_count = timeout_count + 1;
                  if (timeout_count == 100) begin
                     $display("[%t] : *** ERROR *** Timeout (RD) waiting for loop_count=%d to equal num_iter=%d", $realtime, loop_count, num_iter);
                     $finish;
                  end
               end
            end
            // Allow more time for transactions to complete if read tag interleaving is enabled in BFM
            if ($test$plusargs("INTERLEAVE_READ_TAGS")) begin
               wait_for_clock(4000);
            end
         end else begin
            // Wait for writes and reads to complete
            wait_for_clock(2000);
`ifdef VIVADO_SIM
            // Vivado does not support "disable fork"
            fork
               begin
                  do begin
                     reg_read(.base_addr(base_addr), .reg_offset(12'h008), .read_data(read_data), .comp_id(comp_id));
                  end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
                  reg_access_done = 1'b1;
               end
               begin
                  wait_for_clock(20000);
                  if (reg_access_done == 1'b0) begin
                     $display("[%t] : *** ERROR *** Timeout waiting for writes and reads to complete.", $realtime);
                     $finish;
                  end
               end
            join_any
`else
            fork
               begin
                  do begin
                     reg_read(.base_addr(base_addr), .reg_offset(12'h008), .read_data(read_data), .comp_id(comp_id));
                  end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
               end
               begin
                  wait_for_clock(20000);
                  $display("[%t] : *** ERROR *** Timeout waiting for writes and reads to complete.", $realtime);
                  $finish;
               end
            join_any
            disable fork;
`endif
         end
         // Stop reads and writes ([1] for reads, [0] for writes)
         reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(32'h00000000), .comp_id(comp_id));
      end

   end
endtask


task cl_reg_test(
                 input logic [63:0] cl_base = 64'h0
                );
   begin

      // Test variables
      logic [63:0]  tgt_bar;
      logic [63:0]  base_addr;

      int           error_count;

      error_count = 0;

      sys_init(.error_count(error_count));

      get_bar(.bar_num(0), .comp_id(EP_BUS_DEV_FNS), .bar_addr(tgt_bar));
      base_addr = tgt_bar + cl_base;

      //---------------------------
      // Check reset values
      //---------------------------
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h008), .expected_data(32'h0000_0000), .error_count(error_count));
// DEBUG: Currently register 0x0c returns {14'h0, wr_state[1:0], rd_tag_avail[15:0]}
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h00c), .expected_data(32'h0000_ffff), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h010), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h014), .expected_data(32'h0000_000f), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h018), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0000), .error_count(error_count));

      // NOTE: Registers 0x20 - 0x2c do not have a reset value
      //       These are tested below after writing to the associated index register

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h030), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h034), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h038), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0000), .error_count(error_count));

      // NOTE: Registers 0x40 - 0x4c do not have a reset value
      //       These are tested below after writing to the associated index register

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h050), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h054), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h058), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h05c), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h060), .expected_data(32'h0000_0000), .error_count(error_count));

      // NOTE: Registers 0x64 - 0x70 do not have a reset value
      //       These are tested below after writing to the associated index register

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h074), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h078), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h07c), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h080), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h084), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h088), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h08c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h090), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h094), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h098), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h09c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0a0), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0a4), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0a8), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ac), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b4), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b8), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0bc), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c0), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c4), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c8), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0cc), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0d0), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0d4), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0d8), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0dc), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e0), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e4), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e8), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ec), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0f0), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0f4), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0f8), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0fc), .expected_data(32'h0000_0000), .error_count(error_count));

      //---------------------------
      // Check RW field behavior
      //---------------------------
      reg_write(.base_addr(base_addr), .reg_offset(12'h000), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h033f_3ffb), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h000), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h000), .expected_data(32'h0100_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h004), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h004), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h004), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(32'hffff_fff8));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h008), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h008), .expected_data(32'h0000_0000), .error_count(error_count));

// DEBUG: Need a check for register 0x0c once read data logic is sorted out

      reg_write(.base_addr(base_addr), .reg_offset(12'h010), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h010), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h010), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h010), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h014), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h014), .expected_data(32'h0000_003f), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h014), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h014), .expected_data(32'h0000_0000), .error_count(error_count));
      // Restore reset value
      reg_write(.base_addr(base_addr), .reg_offset(12'h014), .write_data(32'h0000_000f));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h014), .expected_data(32'h0000_000f), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h018), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h018), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h018), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h018), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_00ff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h020), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h024), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h028), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h02c), .write_data(32'hffff_ffff));
      // Check that index register value was auto-incremented
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0001), .error_count(error_count));
      // Write previous index value before performing read checks
      reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0000), .error_count(error_count));
      // Perform read checks
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h020), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h024), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h028), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h02c), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h020), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h024), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h028), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h02c), .write_data(32'h0000_0000));
      // Check that index register value was auto-incremented
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0001), .error_count(error_count));
      // Write previous index value before performing read checks
      reg_write(.base_addr(base_addr), .reg_offset(12'h01c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h01c), .expected_data(32'h0000_0000), .error_count(error_count));
      // Perform read checks
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h020), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h024), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h028), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h02c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h030), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h030), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h030), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h030), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h034), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h034), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h034), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h034), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h038), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h038), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h038), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h038), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_00ff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h040), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h044), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h048), .write_data(32'hffff_ffff));
      reg_write(.base_addr(base_addr), .reg_offset(12'h04c), .write_data(32'hffff_ffff));
      // Check that index register value was auto-incremented
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0001), .error_count(error_count));
      // Write previous index value before performing read checks
      reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0000), .error_count(error_count));
      // Perform read checks
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h040), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h044), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h048), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h04c), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h040), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h044), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h048), .write_data(32'h0000_0000));
      reg_write(.base_addr(base_addr), .reg_offset(12'h04c), .write_data(32'h0000_0000));
      // Check that index register value was auto-incremented
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0001), .error_count(error_count));
      // Write previous index value before performing read checks
      reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h03c), .expected_data(32'h0000_0000), .error_count(error_count));
      // Perform read checks
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h040), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h044), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h048), .expected_data(32'h0000_0000), .error_count(error_count));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h04c), .expected_data(32'h0000_0000), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h050), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h050), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h050), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h050), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h054), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h054), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h054), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h054), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h058), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h058), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h058), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h058), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h05c), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h05c), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h05c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h05c), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h060), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h060), .expected_data(32'h0000_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h060), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h060), .expected_data(32'h0000_0000), .error_count(error_count));

      // NOTE: Registers 0x64 - 0x74 tested in cl_common_test

      reg_write(.base_addr(base_addr), .reg_offset(12'h078), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h078), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h078), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h078), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h07c), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h07c), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h07c), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h07c), .expected_data(32'hffff_ffff), .error_count(error_count));

      // NOTE: Registers 0x80 - 0x8c tested in cl_common_test

      // NOTE: Registers 0x90 - 0x9c tested in cl_common_test

      // NOTE: Registers 0xa0 - 0xa4 tested in cl_common_test

      reg_write(.base_addr(base_addr), .reg_offset(12'h0a8), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0a8), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0a8), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0a8), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h0ac), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ac), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0ac), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ac), .expected_data(32'hffff_ffff), .error_count(error_count));

// DEBUG: Add Read Compare error checking (including write-to-clear functionality for errors reported in 0xb0)

      // NOTE: Registers 0xb0 - 0xbc partially tested in cl_common_test

      // NOTE: Registers 0xc0 - 0xcc tested in cl_common_test

// DEBUG: Need to cause write response error to check 0xd0, 0xd4

// DEBUG: Need to cause read response error to check 0xd8, 0xdc

      reg_write(.base_addr(base_addr), .reg_offset(12'h0e0), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e0), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0e0), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e0), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h0e4), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e4), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0e4), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e4), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h0e8), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e8), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0e8), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0e8), .expected_data(32'hffff_ffff), .error_count(error_count));

      reg_write(.base_addr(base_addr), .reg_offset(12'h0ec), .write_data(32'hffff_ffff));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ec), .expected_data(32'hffff_ffff), .error_count(error_count));
      reg_write(.base_addr(base_addr), .reg_offset(12'h0ec), .write_data(32'h0000_0000));
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h0ec), .expected_data(32'hffff_ffff), .error_count(error_count));

      // NOTE: Registers 0xf0 - 0xfc tested in cl_common_test


      //---------------------------
      // Report pass/fail status
      //---------------------------
      if (error_count > 0)
        begin
           $display("[%t] : Detected %3d errors during this test", $realtime, error_count);
           $display("[%t] : *** TEST FAILED ***", $realtime);
        end
      else
        begin
           $display("[%t] : *** TEST PASSED ***", $realtime);
        end

      $finish;
   end
endtask


task pcie_timeout_test();
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

      logic [63:0]  error_addr;

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

      // Enable Dom0 PCIe Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 17); // PCIe Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

`ifndef NO_XDMA
      $display("[%t] : Programming PCIe timeout value of 0x6", $realtime);
      write_data = 32'h1000_0004;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

`else
      $display("[%t] : Programming PCIe timeout value of 0x1", $realtime);
      write_data = 32'h0000_0001;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h260), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

`endif // !`ifndef NO_XDMA
      
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

      //---------------------------
      // Trigger timeouts
      //---------------------------

      error_addr = base_addr + 12'h010;
      $display("[%t] : Issuing CL read and checking for timeout read data value", $realtime);
`ifndef NO_XDMA
      // Read data not implemented for XDMA yet
      reg_read(.base_addr(error_addr), .reg_offset(12'h000), .read_data(read_data), .comp_id(app_pf));
`else
      reg_read_check(.base_addr(error_addr), .reg_offset(12'h000), .expected_data(32'h7357_da7a), .comp_id(app_pf), .error_count(error_count));
`endif
      
      $display("[%t] : Issuing CL write and expecting timeout", $realtime);
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(12'h03c), .write_data(write_data), .comp_id(app_pf));

      $display("[%t] : Issuing CL read and checking for timeout read data value", $realtime);
`ifndef NO_XDMA
      // Read data not implemented for XDMA yet
      reg_read(.base_addr(base_addr), .reg_offset(12'h094), .read_data(read_data), .comp_id(app_pf));
`else
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h094), .expected_data(32'h7357_da7a), .comp_id(app_pf), .error_count(error_count));
`endif
      
      $display("[%t] : Issuing CL write and expecting timeout", $realtime);
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(12'h048), .write_data(write_data), .comp_id(app_pf));

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end

      // For extra coverage, check status using SPI
      UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
      if (read_data[17] !== 1'b1) begin
         $display("[%t] : *** ERROR *** SPI status bit not set for PCIe timeout error", $realtime);
         error_count++;
      end

      $display("[%t] : Checking and clearing the PCIe timeout event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[17] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe timeout error", $realtime);
         error_count++;
      end else begin
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00020000), .comp_id(dom0_pf));
      end

      //---------------------------
      // Check status
      //---------------------------

      // Timeout address not implemented for XDMA yet
`ifdef NO_XDMA
      // Note: Bits [1:0] in read data reports Read/~Write for transaction
      //        01 : Read
      //        10 : Write
      //        00 : Other (timeout while in ADDR state)
      $display("[%t] : Check the value of cfg_pcis_to_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h268), .expected_data({error_addr[31:2], 2'b01}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h26c), .expected_data(error_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
`endif
      
      $display("[%t] : Check the value of cfg_pcis_to_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0004), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Reset the timeout status count
      write_data = $urandom();
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Trigger timeouts (again)
      //---------------------------

      error_addr = base_addr + 12'h01c;
      $display("[%t] : Issuing CL write and expecting timeout", $realtime);
      write_data = $urandom();
      reg_write(.base_addr(error_addr), .reg_offset(12'h000), .write_data(write_data), .comp_id(app_pf));

      // Read data not implemented for XDMA yet
      $display("[%t] : Issuing CL read and checking for timeout read data value", $realtime);
`ifndef NO_XDMA
      reg_read(.base_addr(base_addr), .reg_offset(12'h098), .read_data(read_data), .comp_id(app_pf));
`else
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h098), .expected_data(32'h7357_da7a), .comp_id(app_pf), .error_count(error_count));
`endif
      
      $display("[%t] : Issuing CL write and expecting timeout", $realtime);
      write_data = $urandom();
      reg_write(.base_addr(base_addr), .reg_offset(12'h014), .write_data(write_data), .comp_id(app_pf));

      // Read data not implemented for XDMA yet
      $display("[%t] : Issuing CL read and checking for timeout read data value", $realtime);
`ifndef NO_XDMA
      reg_read(.base_addr(base_addr), .reg_offset(12'h090), .read_data(read_data), .comp_id(app_pf));
`else
      reg_read_check(.base_addr(base_addr), .reg_offset(12'h090), .expected_data(32'h7357_da7a), .comp_id(app_pf), .error_count(error_count));
`endif
      
      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end

      $display("[%t] : Checking and clearing the PCIe timeout event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[17] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe timeout error", $realtime);
         error_count++;
      end else begin
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00020000), .comp_id(dom0_pf));
      end

      //---------------------------
      // Check status
      //---------------------------

      // Timeout address not implemented for XDMA yet
`ifdef NO_XDMA
      // Note: Bits [1:0] in read data reports Read/~Write for transaction
      //        01 : Read
      //        10 : Write
      //        00 : Other (timeout while in ADDR state)
      $display("[%t] : Check the value of cfg_pcis_to_status_addr", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h268), .expected_data({error_addr[31:2], 2'b10}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h26c), .expected_data(error_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

`endif //  `ifdef NO_XDMA
      $display("[%t] : Check the value of cfg_pcis_to_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0004), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      
      //---------------------------
      // Disable event and interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe timeout event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0020); // Clear bit [5], cfg_pcis_to_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0002_0000);  // Clear bit [17], PCIe Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      // Reset the timeout status count
      write_data = $urandom();
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h270), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

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


task pcie_flush_timeout_test();
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

      logic [63:0]  error_addr;

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

      // Enable Dom0 PCIe Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 26); // PCIe Flush Timeout
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Programming PCIe flush timeout value of 0x1", $realtime);
      write_data = 32'h0000_0001;
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c0), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c0), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Trigger timeout
      //---------------------------

      error_addr = base_addr + 12'h010;
`ifndef NO_XDMA
      $display("[%t] : Issuing CL read, flush timeout should not occur for XDMA design", $realtime);
      reg_read(.base_addr(error_addr), .reg_offset(12'h000), .read_data(read_data), .comp_id(app_pf));
`else
      $display("[%t] : Issuing CL read and expecting flush timeout", $realtime);
      reg_read(.base_addr(error_addr), .reg_offset(12'h000), .read_data(read_data), .comp_id(app_pf));
`endif

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Flush Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end

      // For extra coverage, check status using SPI
      UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
`ifndef NO_XDMA
      if (read_data[26] == 1'b1) begin
         $display("[%t] : *** ERROR *** SPI status bit was set for PCIe flush timeout error", $realtime);
         error_count++;
      end
`else
      if (read_data[26] !== 1'b1) begin
         $display("[%t] : *** ERROR *** SPI status bit not set for PCIe flush timeout error", $realtime);
         error_count++;
      end
`endif

      $display("[%t] : Checking the PCIe flush timeout event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
`ifndef NO_XDMA
      if (read_data[26] == 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit was set for PCIe flush timeout error", $realtime);
         error_count++;
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h04000000), .comp_id(dom0_pf));
      end
`else
      if (read_data[26] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe flush timeout error", $realtime);
         error_count++;
      end else begin
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h04000000), .comp_id(dom0_pf));
      end
`endif

      //---------------------------
      // Trigger timeout (again)
      //---------------------------

      error_addr = base_addr + 12'h01c;
`ifndef NO_XDMA
      $display("[%t] : Issuing CL read, flush timeout should not occur for XDMA design", $realtime);
      reg_read(.base_addr(base_addr), .reg_offset(12'h098), .read_data(read_data), .comp_id(app_pf));
`else
      $display("[%t] : Issuing CL read and expecting flush timeout", $realtime);
      reg_read(.base_addr(base_addr), .reg_offset(12'h098), .read_data(read_data), .comp_id(app_pf));
`endif

      //---------------------------
      // Wait for interrupt
      //---------------------------

      if (check_msix == 1'b1) begin
         $display("[%t] : Waiting for Dom0 PCIe Flush Timeout interrupt...", $realtime);
         wait_for_msix_intr(.comp_id(dom0_pf));
      end else begin
         wait_for_clock(200);
      end

      $display("[%t] : Checking the PCIe flush timeout event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
`ifndef NO_XDMA
      if (read_data[26] == 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit was set for PCIe flush timeout error", $realtime);
         error_count++;
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h04000000), .comp_id(dom0_pf));
      end
`else
      if (read_data[26] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe flush timeout error", $realtime);
         error_count++;
      end else begin
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h04000000), .comp_id(dom0_pf));
      end
`endif

      //---------------------------
      // Disable event and interrupt
      //---------------------------

      // Disable Dom0 PCIe Timeout interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0400_0000);  // Clear bit [26], PCIe Flush Timeout
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


task pcie_access_test();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

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

      // Enable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 18); // PCIe Access
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      //---------------------------
      // Program Address Ranges
      //---------------------------

      // If addr[61] is 1'b0, address is allowed

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      $display("[%t] : Programming PCIe Address Ranges", $realtime);
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b00), .range_addr_low(64'h0000_0000_0000_0000), .range_addr_high(64'h1fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b01), .range_addr_low(64'h4000_0000_0000_0000), .range_addr_high(64'h5fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b10), .range_addr_low(64'h8000_0000_0000_0000), .range_addr_high(64'h9fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b11), .range_addr_low(64'hc000_0000_0000_0000), .range_addr_high(64'hdfff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Access invalid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin

         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Trigger interrupt (write)
         //---------------------------

         $display("[%t] : Issuing write access from CL outside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b0), .align(64'h003f), .region(region)); // Writes must be 64-byte aligned
         end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
         axi_len = 8'h07;
         last_len = 8'h00;
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Wait for interrupt
         //---------------------------

         if (check_msix == 1'b1) begin
            $display("[%t] : Waiting for Dom0 PCIe Access interrupt...", $realtime);
            wait_for_msix_intr(.comp_id(dom0_pf));
         end else begin
            wait_for_clock(200);
         end
         exp_status_count++;

         // For extra coverage, check status using SPI
         UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
         if (read_data[18] !== 1'b1) begin
            $display("[%t] : *** ERROR *** SPI status bit not set for PCIe access error", $realtime);
            error_count++;
         end

         $display("[%t] : Checking and clearing the PCIe access event status", $realtime);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[18] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe access error", $realtime);
            error_count++;
         end else begin
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00040000), .comp_id(dom0_pf));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_addr", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h274), .expected_data(test_addr[31:0]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h278), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Trigger interrupt (read)
         //---------------------------

         $display("[%t] : Issuing read access from CL outside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b0), .region(region));
         end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : Detected expected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end else begin
            $display("[%t] : *** ERROR *** Did not detect expected read compare error", $realtime);
            fail = 1;
         end

         //---------------------------
         // Wait for interrupt
         //---------------------------

         if (check_msix == 1'b1) begin
            $display("[%t] : Waiting for Dom0 PCIe Access interrupt...", $realtime);
            wait_for_msix_intr(.comp_id(dom0_pf));
         end else begin
            wait_for_clock(200);
         end
         exp_status_count++;

         $display("[%t] : Checking and clearing the PCIe access error event status", $realtime);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[18] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe access error", $realtime);
            error_count++;
         end else begin
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .write_data(32'h00040000), .comp_id(dom0_pf));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_addr", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h274), .expected_data({test_addr[31:1], 1'b1}), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h278), .expected_data(test_addr[63:32]), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions


      $display("[%t] : Clearing the value of cfg_pcim_addr_range_status_count", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .write_data(32'h0000_0001), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      exp_status_count = 32'h0;

      //---------------------------
      // Access valid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin
         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue write
         //---------------------------

         $display("[%t] : Issuing write access from CL inside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .align(64'h003f), .region(region)); // Writes must be 64-byte aligned
         end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
         axi_len = 8'h07;
         last_len = 8'h00;
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue read
         //---------------------------

         $display("[%t] : Issuing read access from CL inside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .region(region));
         end while (test_addr[11:0] > 12'hc00);  // Need to prevent 4k crossing, transaction will cover 1024 bytes
         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         // Before issuing read, issue writes to populate the memory
         //  - Issue writes that span two consecutive 128-byte regions
         //  - Read will only check a 128-byte subset of the 256-byte write data
         program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0000), .error_count(error_count), .axi_len(8'h07), .last_len(8'h00), .enable_write(1'b1), .enable_read(1'b0));
         // Have to set test_data for second write (use default value plus number of DW already written)
         program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(8'h07), .last_len(8'h00), .enable_write(1'b1), .enable_read(1'b0));
         // Issue read
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            fail = 1;
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Access event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_001f); // Clear bits [4:0], cfg_pcim_pass_en and cfg_pcim_pass_range_en[3:0]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0004_0000);  // Clear bit [18], PCIe Access
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


task pcie_access_len_test();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;
      bit           user_id_mode;
      logic [15:0]  wr_user;
      logic [15:0]  rd_user;

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
      $display("[%t] : Checking that PCIe Length Error event can be enabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | 32'h0000_0040; // Set bit [6], cfg_pcim_len_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking that PCIe Length Error event can be disabled", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0040); // Clear bit [6], cfg_pcim_len_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Check invalid length
      //---------------------------

      $display("[%t] : Enabling PCIe Length Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0040;  // Set bit [6] : PCIe Length Check Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Trigger interrupt (write)
      //---------------------------

      $display("[%t] : Issuing write access with invalid length setting", $realtime);

      do begin
         gen_random_access_addr(.addr(test_addr), .align(64'h003f)); // Writes must be 64-byte aligned
      end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
      axi_len = 8'h08; // Valid setting would be 0x07
      user_id_mode = 1'b1;
      wr_user = 16'h0080;
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .user_id_mode(user_id_mode), .wr_user(wr_user), .enable_write(1'b1), .enable_read(1'b0));

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

      // For extra coverage, check status using SPI
      UC_SPI_MODEL.spi_read(.addr(24'h00000c), .read_data(read_data));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** SPI status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end

      $display("[%t] : Checking the PCIe Protocol error event status", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data[19] !== 1'b1) begin
         $display("[%t] : *** ERROR *** Status bit not set for PCIe Protocol error", $realtime);
         error_count++;
      end else begin
         // Read Protocol Error Status
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
         if (read_data[0] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe Length error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe Length error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000001), .comp_id(dom0_pf));
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

      //---------------------------
      // Trigger interrupt (read)
      //---------------------------

      $display("[%t] : Issuing read access with invalid length setting", $realtime);

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
      if (test_addr[5:2] !== 4'h0) begin
         axi_len = 8'h09; // Valid setting would be 0x08
         user_id_mode = 1'b1;
         rd_user = 16'h0080; // DW count
      end else begin
         axi_len = 8'h08; // Valid setting would be 0x07
         user_id_mode = 1'b1;
         rd_user = 16'h0080;
      end
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .user_id_mode(user_id_mode), .rd_user(rd_user), .enable_write(1'b0), .enable_read(1'b1));

      //---------------------------
      // Check for compare error
      //---------------------------

      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
         error_index = read_data[3:0];
         $display("[%t] : Detected expected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         // Clear error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
         reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
      end else begin
         $display("[%t] : *** ERROR *** Did not detect expected read compare error", $realtime);
         fail = 1;
      end

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
         if (read_data[0] !== 1'b1) begin
            $display("[%t] : *** ERROR *** Status bit not set for PCIe Length error", $realtime);
            error_count++;
         end else begin
            $display("[%t] : Clearing the PCIe Length error event status", $realtime);
            reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .write_data(32'h00000001), .comp_id(dom0_pf));
            // Check that the event status was cleared
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

      //---------------------------
      // Clear status
      //---------------------------

      $display("[%t] : Clearing the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .write_data(32'h0000_0001), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(32'h0000_0000), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));
      exp_status_count = 32'h0;

      //---------------------------
      // Check valid length
      //---------------------------

      //---------------------------
      // Issue write
      //---------------------------

      $display("[%t] : Issuing write access with valid length", $realtime);

      do begin
         gen_random_access_addr(.addr(test_addr), .align(64'h003f)); // Writes must be 64-byte aligned
      end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
      axi_len = 8'h07;
      last_len = 8'h00;
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Issue read
      //---------------------------

      $display("[%t] : Issuing read access with valid length", $realtime);

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] > 12'hc00);  // Need to prevent 4k crossing, transaction will cover 1024 bytes
      if (test_addr[5:2] !== 4'h0) begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end else begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end
      // Before issuing read, issue writes to populate the memory
      //  - Issue writes that span two consecutive 128-byte regions
      //  - Read will only check a 128-byte subset of the 256-byte write data
      program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0000), .error_count(error_count), .axi_len(8'h07), .last_len(8'h00), .enable_write(1'b1), .enable_read(1'b0));
      // Have to set test_data for second write (use default value plus number of DW already written)
      program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(8'h07), .last_len(8'h00), .enable_write(1'b1), .enable_read(1'b0));
      // Issue read
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

      //---------------------------
      // Check for compare error
      //---------------------------

      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         fail = 1;
         // Clear error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
         reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Length Error event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0040); // Clear bit [6], cfg_pcim_len_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0008_0000);  // Clear bit [19], PCIe Protocol Error
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


task pcie_rd_tag_interleave_test();
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

      int           exp_dw_count;

      logic [31:0]  exp_status_count;

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Enabling PCIe Length Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0040;  // Set bit [6] : PCIe Length Check Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Issue writes and reads
      //---------------------------

      exp_dw_count = 128; // 512 bytes
      do begin
         gen_random_access_addr(.addr(test_addr));
      end while ((test_addr[11:0] > (12'hfff - (4*exp_dw_count) + 12'h001)) || (test_addr[8] !== 1'b1));

      // Zero out some address bits in preparation for addr loop mode
      test_addr[31:16] = 16'h0000;

      if (test_addr[5:2] == 4'h0) begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end else begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end

      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .iter_mode(1'b1), .num_iter(64'h008), .addr_loop_mode(1'b1), .loop_shift(6'h10), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1));

      // Check for compare error
      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(dom0_pf));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         error_count++;
         // Clear the error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001));
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Length Error event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0040); // Clear bit [6], cfg_pcim_len_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Protocol Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0008_0000);  // Clear bit [19], PCIe Protocol Error
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


task pcie_addr_len_test();
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

      logic [1:0]   addr_bits;

      logic [63:0]  test_addr;

      logic [7:0]   last_len_start;

      int           exp_dw_count;

      logic [31:0]  exp_status_count;

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      int           error_count;
      logic         fail;

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

      //---------------------------
      // Enable interrupts
      //---------------------------

      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
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

      $display("[%t] : Enabling various PCIe Protocol checks", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
// DEBUG: Comment out WSTRB checking until RTL is fixed
//      write_data |= 32'h0000_1000;  // Set bit [12] : PCIe WSTRB Check
      write_data |= 32'h0000_0800;  // Set bit [11] : PCIe Byte Enable Check
      write_data |= 32'h0000_0400;  // Set bit [10] : PCIe Incomplete Write Check
      write_data |= 32'h0000_0200;  // Set bit [ 9] : PCIe Request Size Check
      write_data |= 32'h0000_0100;  // Set bit [ 8] : PCIe BME Check
      write_data |= 32'h0000_0080;  // Set bit [ 7] : PCIe 4k Boundary Check
      write_data |= 32'h0000_0040;  // Set bit [ 6] : PCIe Length Check
      write_data |= 32'h0000_0020;  // Set bit [ 5] : PCIe Slave Timeout Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Issue writes and reads
      //---------------------------

      if (!$value$plusargs("CL_ADDR_BITS=%b", addr_bits)) begin
         addr_bits = $urandom_range(3,0);
      end

      for (logic [7:0] axi_len = 8'h00; axi_len < 8'h03; axi_len = axi_len + 8'h01) begin
         if (axi_len == 8'h00) begin
            last_len_start = (8'h0f - {addr_bits, 2'b00});
         end else begin
            last_len_start = 8'h0f;
         end
         for (logic [7:0] last_len = last_len_start; (last_len >= 0) && (last_len < 8'h10); last_len = last_len - 8'h01) begin
            exp_dw_count = 16*(axi_len + 1) - last_len - (addr_bits[1:0] << 2);
            do begin
               gen_random_access_addr(.addr(test_addr), .align(64'h000f));
            end while ((test_addr[11:0] > (12'hfff - (4*exp_dw_count) + 12'h001)) || (test_addr[5:4] !== addr_bits[1:0]));
            $display("[%t] : Issuing %2d DW write and read accesses with addr[5:4] = 2'b%02b  (axi_len = 8'h%02x, last_len = 8'h%02x)", $realtime, exp_dw_count, test_addr[5:4], axi_len, last_len);
            program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1));
            // Check for compare error
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data != 32'h0000_0000) begin
               reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(dom0_pf));
               error_addr[31:0] = read_data;
               reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(dom0_pf));
               error_addr[63:32] = read_data;
               reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(dom0_pf));
               error_index = read_data[3:0];
               $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
               error_count++;
               // Clear the error
               reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001));
            end
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking the interrupt status register value", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data !== 32'h0) begin
         $display("[%t] : *** ERROR *** Interrupt status bits were set to 0x%08x (expected 0x0)", $realtime, read_data);
         error_count++;
         if (read_data[19] == 1'b1) begin
            // Read Protocol Error Status
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
            $display("[%t] : *** ERROR *** PCIe Protocol Error Status 0x%08x", $realtime, read_data);
         end
      end

      //---------------------------
      // Disable interrupts
      //---------------------------

      $display("[%t] : Disabling PCIe Protocol Error events", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_1fe0); // Clear bits [12:5]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Timeout and Protocol Error interrupts
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0008_0000);  // Clear bit [19], PCIe Protocol Error
      write_data &= ~(32'h0002_0000);  // Clear bit [17], PCIe Timeout
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


task pcie_addr_len_dw_test();
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

      logic [3:0]   addr_bits;

      logic [63:0]  test_addr;

      logic [7:0]   last_len_start;

      int           exp_dw_count;

      logic [31:0]  exp_status_count;

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      int           error_count;
      logic         fail;

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

      //---------------------------
      // Enable interrupts
      //---------------------------

      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Protocol Error
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

      $display("[%t] : Enabling various PCIe Protocol checks", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
// DEBUG: Comment out WSTRB checking until RTL is fixed
//      write_data |= 32'h0000_1000;  // Set bit [12] : PCIe WSTRB Check
      write_data |= 32'h0000_0800;  // Set bit [11] : PCIe Byte Enable Check
      write_data |= 32'h0000_0400;  // Set bit [10] : PCIe Incomplete Write Check
      write_data |= 32'h0000_0200;  // Set bit [ 9] : PCIe Request Size Check
      write_data |= 32'h0000_0100;  // Set bit [ 8] : PCIe BME Check
      write_data |= 32'h0000_0080;  // Set bit [ 7] : PCIe 4k Boundary Check
      write_data |= 32'h0000_0040;  // Set bit [ 6] : PCIe Length Check
      write_data |= 32'h0000_0020;  // Set bit [ 5] : PCIe Slave Timeout Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Issue writes and reads
      //---------------------------

      if (!$value$plusargs("CL_ADDR_BITS=%b", addr_bits)) begin
         addr_bits = $urandom_range(15,0);
      end

      for (logic [7:0] axi_len = 8'h00; axi_len < 8'h03; axi_len = axi_len + 8'h01) begin
         if (axi_len == 8'h00) begin
            last_len_start = (8'h0f - addr_bits);
         end else begin
            last_len_start = 8'h0f;
         end
         for (logic [7:0] last_len = last_len_start; (last_len >= 0) && (last_len < 8'h10); last_len = last_len - 8'h01) begin
            exp_dw_count = 16*(axi_len + 1) - last_len - addr_bits;
            do begin
               gen_random_access_addr(.addr(test_addr), .align(64'h0003));
            end while ((test_addr[11:0] > (12'hfff - (4*exp_dw_count) + 12'h001)) || (test_addr[5:2] !== addr_bits[3:0]));
            $display("[%t] : Issuing %2d DW write and read accesses with addr[5:2] = 4'b%04b  (axi_len = 8'h%02x, last_len = 8'h%02x)", $realtime, exp_dw_count, test_addr[5:2], axi_len, last_len);
            program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1));
            // Check for compare error
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(dom0_pf));
            if (read_data != 32'h0000_0000) begin
               reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(dom0_pf));
               error_addr[31:0] = read_data;
               reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(dom0_pf));
               error_addr[63:32] = read_data;
               reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(dom0_pf));
               error_index = read_data[3:0];
               $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
               error_count++;
               // Clear the error
               reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001));
            end
         end
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_prot_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      $display("[%t] : Checking the interrupt status register value", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h00c), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data !== 32'h0) begin
         $display("[%t] : *** ERROR *** Interrupt status bits were set to 0x%08x (expected 0x0)", $realtime, read_data);
         error_count++;
         if (read_data[19] == 1'b1) begin
            // Read Protocol Error Status
            reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h2c8), .read_data(read_data), .comp_id(dom0_pf));
            $display("[%t] : *** ERROR *** PCIe Protocol Error Status 0x%08x", $realtime, read_data);
         end
      end

      //---------------------------
      // Disable interrupts
      //---------------------------

      $display("[%t] : Disabling PCIe Protocol Error events", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_1fe0); // Clear bits [12:5]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Timeout and Protocol Error interrupts
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0008_0000);  // Clear bit [19], PCIe Protocol Error
      write_data &= ~(32'h0002_0000);  // Clear bit [17], PCIe Timeout
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


// DEBUG: Remove this task once debug work is complete
task pcie_addr_len_debug_test();
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

      int           exp_dw_count;

      logic [31:0]  exp_status_count;

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Length Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 19); // PCIe Length Error
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      $display("[%t] : Enabling PCIe Length Error checking", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data;
      write_data &= ~(32'h0000_001f);  // Clear any range enable checking
      write_data |= 32'h0000_0040;  // Set bit [6] : PCIe Length Check Enable
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Issue writes and reads
      //---------------------------

      // Fixed for 4 DW transfer
      axi_len = 8'h00;
      last_len = 8'h08;
      test_addr = 64'hdb8a_74d7_ac89_ebd0;
      exp_dw_count = 16*(axi_len + 1) - last_len - test_addr[5:2];
      $display("[%t] : Issuing %2d DW write and read accesses with addr[5:4] = 2'b%02b  (axi_len = 8'h%02x, last_len = 8'h%02x)", $realtime, exp_dw_count, test_addr[5:4], axi_len, last_len);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1));

      // Check for compare error
      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(dom0_pf));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         error_count++;
         // Clear the error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(dom0_pf));
      end

      // Fixed for 9 DW transfer
      axi_len = 8'h01;
      last_len = 8'h0f;
      test_addr = 64'h46e8_2aae_3f61_9260;
      exp_dw_count = 16*(axi_len + 1) - last_len - test_addr[5:2];
      $display("[%t] : Issuing %2d DW write and read accesses with addr[5:4] = 2'b%02b  (axi_len = 8'h%02x, last_len = 8'h%02x)", $realtime, exp_dw_count, test_addr[5:4], axi_len, last_len);
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b1));

      // Check for compare error
      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(dom0_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(dom0_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(dom0_pf));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         error_count++;
         // Clear the error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(dom0_pf));
      end

      //---------------------------
      // Check status
      //---------------------------

      $display("[%t] : Check the value of cfg_pcim_len_err_status_count", $realtime);
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h28c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Length Error event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_0040); // Clear bit [6], cfg_pcim_len_chk_en
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Length Error interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0008_0000);  // Clear bit [19], PCIe Length Error
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


// DEBUG: Remove this task once debug work is completed
task pcie_access_test_debug_partial();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 18); // PCIe Access
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      //---------------------------
      // Program Address Ranges
      //---------------------------

      // If addr[61] is 1'b0, address is allowed

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      $display("[%t] : Programming PCIe Address Ranges", $realtime);
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b00), .range_addr_low(64'h0000_0000_0000_0000), .range_addr_high(64'h1fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b01), .range_addr_low(64'h4000_0000_0000_0000), .range_addr_high(64'h5fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b10), .range_addr_low(64'h8000_0000_0000_0000), .range_addr_high(64'h9fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b11), .range_addr_low(64'hc000_0000_0000_0000), .range_addr_high(64'hdfff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Access valid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin
         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue write
         //---------------------------

         $display("[%t] : Issuing write access from CL inside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .region(region));
         end while (test_addr[11:0] > 12'he00);  // Need to prevent 4k crossing, transaction will cover 512 bytes
         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue read
         //---------------------------

         $display("[%t] : Issuing read access from CL inside of programmed range", $realtime);

         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            fail = 1;
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Access event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & 32'hffff_ffe0; // Clear bits [4:0], cfg_pcim_pass_en and cfg_pcim_pass_range_en[3:0]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0004_0000);  // Clear bit [18], PCIe Access
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


// DEBUG: Remove this task once debug work is completed
task pcie_access_test_debug_dw();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 18); // PCIe Access
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      //---------------------------
      // Program Address Ranges
      //---------------------------

      // If addr[61] is 1'b0, address is allowed

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      $display("[%t] : Programming PCIe Address Ranges", $realtime);
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b00), .range_addr_low(64'h0000_0000_0000_0000), .range_addr_high(64'h1fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b01), .range_addr_low(64'h4000_0000_0000_0000), .range_addr_high(64'h5fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b10), .range_addr_low(64'h8000_0000_0000_0000), .range_addr_high(64'h9fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b11), .range_addr_low(64'hc000_0000_0000_0000), .range_addr_high(64'hdfff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Access valid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin
         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue write
         //---------------------------

         $display("[%t] : Issuing write access from CL inside of programmed range", $realtime);

         do begin
            gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .region(region));
         end while (test_addr[11:0] > 12'hc00);
         axi_len = 8'h07;
         // Use masked version of random address to force 64-byte alignment for the write
         program_cl(.base_addr(base_addr), .test_addr(test_addr & ~(64'h003f)), .error_count(error_count), .axi_len(axi_len), .enable_write(1'b1), .enable_read(1'b0));
         program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(axi_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue read
         //---------------------------

         $display("[%t] : Issuing read access from CL inside of programmed range", $realtime);

         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            fail = 1;
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Access event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_001f); // Clear bits [4:0], cfg_pcim_pass_en and cfg_pcim_pass_range_en[3:0]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & 32'hfffb_ffff;  // Clear bit [18], PCIe Access
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


// DEBUG: Remove this task once debug work is completed
task pcie_access_test_debug_len();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 18); // PCIe Access
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      //---------------------------
      // Program Address Ranges
      //---------------------------

      // If addr[61] is 1'b0, address is allowed

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      $display("[%t] : Programming PCIe Address Ranges", $realtime);
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b00), .range_addr_low(64'h0000_0000_0000_0000), .range_addr_high(64'h1fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b01), .range_addr_low(64'h4000_0000_0000_0000), .range_addr_high(64'h5fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b10), .range_addr_low(64'h8000_0000_0000_0000), .range_addr_high(64'h9fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b11), .range_addr_low(64'hc000_0000_0000_0000), .range_addr_high(64'hdfff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Access valid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin
         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue write
         //---------------------------

         $display("[%t] : Issuing write access from CL inside of programmed range", $realtime);

         gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .region(region));
         axi_len = 8'h07;
         last_len = 8'h00;
         program_cl(.base_addr(base_addr), .test_addr(test_addr & ~(64'h003f)), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));
         program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue read
         //---------------------------

         $display("[%t] : Issuing read access from CL inside of programmed range", $realtime);

         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            fail = 1;
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Access event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_001f); // Clear bits [4:0], cfg_pcim_pass_en and cfg_pcim_pass_range_en[3:0]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & 32'hfffb_ffff;  // Clear bit [18], PCIe Access
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


// DEBUG: Remove this task once debug work is completed
task pcie_access_test_debug_resp();
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

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;

      logic [31:0]  exp_status_count;

      int           error_count;
      logic         fail;

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

      // Enable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data | (1'b1 << 18); // PCIe Access
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .write_data(write_data), .comp_id(dom0_pf));

      //---------------------------
      // Program Address Ranges
      //---------------------------

      // If addr[61] is 1'b0, address is allowed

      // Region 0:
      // 0x0000_0000_0000_0000 - 0x1fff_ffff_ffff_fffc : ALLOWED
      // 0x2000_0000_0000_0000 - 0x3fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 1:
      // 0x4000_0000_0000_0000 - 0x5fff_ffff_ffff_fffc : ALLOWED
      // 0x6000_0000_0000_0000 - 0x7fff_ffff_ffff_fffc : NOT ALLOWED

      // Region 2:
      // 0x8000_0000_0000_0000 - 0x9fff_ffff_ffff_fffc : ALLOWED
      // 0xa000_0000_0000_0000 - 0xbfff_ffff_ffff_fffc : NOT ALLOWED

      // Region 3:
      // 0xc000_0000_0000_0000 - 0xdfff_ffff_ffff_fffc : ALLOWED
      // 0xe000_0000_0000_0000 - 0xffff_ffff_ffff_fffc : NOT ALLOWED

      $display("[%t] : Programming PCIe Address Ranges", $realtime);
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b00), .range_addr_low(64'h0000_0000_0000_0000), .range_addr_high(64'h1fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b01), .range_addr_low(64'h4000_0000_0000_0000), .range_addr_high(64'h5fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b10), .range_addr_low(64'h8000_0000_0000_0000), .range_addr_high(64'h9fff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));
      program_cl_addr_range(.base_addr(dom0_mgmt_bar), .range_num(2'b11), .range_addr_low(64'hc000_0000_0000_0000), .range_addr_high(64'hdfff_ffff_ffff_fffc), .comp_id(dom0_pf), .error_count(error_count));

      //---------------------------
      // Access valid addresses
      //---------------------------

      for (int region = 0; region < 4; region++) begin
         //---------------------------
         // Enable Region
         //---------------------------

         $display("[%t] : Enabling PCIe Address Range checking for region %1d", $realtime, region);
         reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
         write_data = read_data;
         write_data &= ~(32'h0000_000f);  // Clear previous range enable
         write_data |= 32'h0000_0010;  // [4] : PCIe Pass Master Enable
         write_data |= (1'b1 << region);  // [3:0] : Enables for each range
         reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue write
         //---------------------------

         $display("[%t] : Issuing write access from CL inside of programmed range", $realtime);

         gen_random_access_addr(.addr(test_addr), .allowed(1'b1), .region(region));
         axi_len = 8'h07;
         last_len = 8'h00;
         program_cl(.base_addr(base_addr), .test_addr(test_addr & ~(64'h003f)), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));
         program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

         //---------------------------
         // Issue read
         //---------------------------

         $display("[%t] : Issuing read access from CL inside of programmed range", $realtime);

         if (test_addr[5:2] !== 4'h0) begin
            axi_len = 8'h08;
            last_len = 8'h10 - test_addr[5:2];
         end else begin
            axi_len = 8'h07;
            last_len = 8'h00;
         end
         program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1));

         //---------------------------
         // Check for compare error
         //---------------------------

         reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
         if (read_data != 32'h0000_0000) begin
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
            error_addr[31:0] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
            error_addr[63:32] = read_data;
            reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
            error_index = read_data[3:0];
            $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
            fail = 1;
            // Clear error
            reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
            reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
         end

         //---------------------------
         // Check status
         //---------------------------

         $display("[%t] : Check the value of cfg_pcim_addr_range_status_count", $realtime);
         reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h27c), .expected_data(exp_status_count), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      end // End of for loop that cycles through regions

      //---------------------------
      // Disable interrupt
      //---------------------------

      $display("[%t] : Disabling PCIe Access event", $realtime);
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & ~(32'h0000_001f); // Clear bits [4:0], cfg_pcim_pass_en and cfg_pcim_pass_range_en[3:0]
      reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .write_data(write_data), .comp_id(dom0_pf));
      reg_read_check(.base_addr(dom0_mgmt_bar), .reg_offset(12'h218), .expected_data(write_data), .data_mask(32'hffff_ffff), .comp_id(dom0_pf), .error_count(error_count));

      // Disable Dom0 PCIe Access interrupt
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h008), .read_data(read_data), .comp_id(dom0_pf));
      write_data = read_data & 32'hfffb_ffff;  // Clear bit [18], PCIe Access
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


task pcie_ar_aw_test();
   begin

`ifdef VIVADO_SIM
      automatic bit reg_access_done = 1'b0;
`endif
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
      logic [63:0]  test_addr2;

      logic [63:0]  error_addr;
      logic [3:0]   error_index;

      logic [7:0]   axi_len;
      logic [7:0]   last_len;

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
      // Issue writes
      //---------------------------

      $display("[%t] : Issuing writes to populate memory", $realtime);

      do begin
         gen_random_access_addr(.addr(test_addr));
      end while (test_addr[11:0] > 12'hc00); // Need to prevent 4k crossing, transaction will cover 1024 bytes
      axi_len = 8'h07;
      last_len = 8'h00;
      program_cl(.base_addr(base_addr), .test_addr(test_addr & ~(64'h003f)), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));
      program_cl(.base_addr(base_addr), .test_addr((test_addr & ~(64'h003f)) + 64'h0200), .test_data(32'h6c93_af50 + 32'h0000_0080), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0));

      //---------------------------
      // Issue reads and more writes
      //---------------------------

      $display("[%t] : Issuing reads and unrelated writes", $realtime);

      if (test_addr[5:2] !== 4'h0) begin
         axi_len = 8'h08;
         last_len = 8'h10 - test_addr[5:2];
      end else begin
         axi_len = 8'h07;
         last_len = 8'h00;
      end
      program_cl(.base_addr(base_addr), .test_addr(test_addr), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b0), .enable_read(1'b1), .start_cl(1'b0), .wait_for_done(1'b0));

      do begin
         gen_random_access_addr(.addr(test_addr2), .align(64'h003f));
      end while (test_addr2[11:0] > 12'he00); // Need to prevent 4k crossing, transaction will cover 512 bytes
      axi_len = 8'h07;
      last_len = 8'h00;
      program_cl(.base_addr(base_addr), .test_addr(test_addr2), .error_count(error_count), .axi_len(axi_len), .last_len(last_len), .enable_write(1'b1), .enable_read(1'b0), .start_cl(1'b0), .wait_for_done(1'b0));

      // Start CL activity
      reg_write(.base_addr(base_addr), .reg_offset(12'h008), .write_data(32'h0000_0003), .comp_id(app_pf));

      // Wait for writes and reads to complete
      wait_for_clock(2000);
`ifdef VIVADO_SIM
      // Vivado does not support "disable fork"
      fork
         begin
            do begin
               reg_read(.base_addr(base_addr), .reg_offset(12'h008), .read_data(read_data), .comp_id(app_pf));
            end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
            reg_access_done = 1'b1;
         end
         begin
            wait_for_clock(5000);
            if (reg_access_done == 1'b0) begin
               $display("[%t] : *** ERROR *** Timeout waiting for writes and reads to complete.", $realtime);
               $finish;
            end
         end
      join_any
`else
      fork
         begin
            do begin
               reg_read(.base_addr(base_addr), .reg_offset(12'h008), .read_data(read_data), .comp_id(app_pf));
            end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
         end
         begin
            wait_for_clock(5000);
            $display("[%t] : *** ERROR *** Timeout waiting for writes and reads to complete.", $realtime);
            $finish;
         end
      join_any
      disable fork;
`endif

      //---------------------------
      // Check for compare error
      //---------------------------

      reg_read(.base_addr(base_addr), .reg_offset(12'h0b0), .read_data(read_data), .comp_id(app_pf));
      if (read_data != 32'h0000_0000) begin
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b4), .read_data(read_data), .comp_id(app_pf));
         error_addr[31:0] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0b8), .read_data(read_data), .comp_id(app_pf));
         error_addr[63:32] = read_data;
         reg_read(.base_addr(base_addr), .reg_offset(12'h0bc), .read_data(read_data), .comp_id(app_pf));
         error_index = read_data[3:0];
         $display("[%t] : *** ERROR *** Detected unexpected read compare error from address 0x%016x, index 0x%1x", $realtime, error_addr, error_index);
         fail = 1;
         // Clear error
         reg_write(.base_addr(base_addr), .reg_offset(12'h0b0), .write_data(32'h0000_0001), .comp_id(app_pf));
         reg_read_check(.base_addr(base_addr), .reg_offset(12'h0b0), .expected_data(32'h0000_0000), .comp_id(app_pf), .error_count(error_count));
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


task pcie_test;
   cl_common_test(
                  .cl_base(64'h0000_0000_0000_0000),
                  .test_addr(64'ha987_6543_2100_0000)
                 );
endtask


task pcie_ext_cfg_test;

   logic [63:0]  dom0_mgmt_bar;

   logic [15:0]  dom0_pf;

   logic [31:0]  read_data;
   logic [31:0]  write_data;

   logic         fail;
   int           error_count;

   logic [11:0]  ext_cfg_reg_addr_base;
   logic [11:0]  dom0_reg_addr_base;



   fail = 0;
   error_count = 0;

   sys_init(.error_count(error_count));

   dom0_pf = EP_BUS_DEV_FNS_PF2;

   get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

   ext_cfg_reg_addr_base = 12'hB0;
   dom0_reg_addr_base = 12'h210;

   // Write to 2 register 0x10 and 0x14
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(dom0_reg_addr_base), .write_data(32'h1A2B_3C4D), .comp_id(dom0_pf));
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(dom0_reg_addr_base + 12'h04), .write_data(32'h5C6D_7E8F), .comp_id(dom0_pf));

   wait_for_clock(1000);

   // Read these 2 registers from ext cfg space
   cfg_reg_read(.reg_addr(ext_cfg_reg_addr_base), .read_data(read_data), .comp_id(dom0_pf));
   if (read_data != 32'h1A2B_3C4D) begin
      $display("[%t] : *** ERROR *** Incorrect data read from ext cfg register 0x%03x : Actual = 0x%08x, Expected = 0x%08x", $realtime, ext_cfg_reg_addr_base, read_data, 32'h1A2B_3C4D);
      fail = 1;
   end

   cfg_reg_read(.reg_addr(ext_cfg_reg_addr_base + 12'h04), .read_data(read_data), .comp_id(dom0_pf));
   if (read_data != 32'h5C6D_7E8F) begin
      $display("[%t] : *** ERROR *** Incorrect data read from ext cfg register 0x%03x : Actual = 0x%08x, Expected = 0x%08x", $realtime, ext_cfg_reg_addr_base + 12'd04, read_data, 32'h5C6D_7E8F);
      fail = 1;
   end

//   for (logic [11:0] addr = 12'hB0; addr < 12'h100; addr+=12'h04) begin
//      cfg_reg_read(.reg_addr(addr), .read_data(read_data), .comp_id(dom0_pf));
//   end
//
//   wait_for_clock(1000);
//
//   for (logic [11:0] addr = 12'h400; addr < 12'hFFF; addr+=12'h04) begin
//      cfg_reg_read(.reg_addr(addr), .read_data(read_data), .comp_id(dom0_pf));
//   end
//
//   reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(dom0_reg_addr_base), .read_data(read_data), .comp_id(dom0_pf));
//   reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(dom0_reg_addr_base + 12'h04), .read_data(read_data), .comp_id(dom0_pf));


   if (fail)
     $display("[%t] : *** TEST FAILED ***", $realtime);
   else
     $display("[%t] : *** TEST PASSED ***", $realtime);

   $finish;
endtask


task pcie_reg_test;
   cl_reg_test(
               .cl_base(64'h0000_0000_0000_0000)
              );
endtask


task ddr_test;
   int plusarg_ret;
   int ddr_num;
   logic [11:0] offset;

   plusarg_ret = $value$plusargs("TEST_DDR=%d", ddr_num);
   if (plusarg_ret == 0) begin
      ddr_num = 99;
   end

   case (ddr_num)
     0 : offset = 12'h100;
     1 : offset = 12'h200;
     2 : offset = 12'h300;
     3 : offset = 12'h400;
     default : offset = 12'h100;
   endcase

   cl_common_test(
                  .cl_base(64'h0000_0000_0000_0000 + offset),
                  .ddr_num(ddr_num),
                  .test_addr(64'ha987_6543_2100_0000)
                 );
   
endtask


task hmc_test;
   int plusarg_ret;
   int hmc_num;
   logic [11:0] offset;

   plusarg_ret = $value$plusargs("TEST_HMC=%d", hmc_num);
   if (plusarg_ret == 0) begin
      hmc_num = 99;
   end

   case (hmc_num)
     0 : offset = 12'h000;
     1 : offset = 12'h100;
     2 : offset = 12'h200;
     3 : offset = 12'h300;
     default : offset = 12'h000;
   endcase

   cl_common_test(
                  .cl_base(64'h0000_0000_0000_3000 + offset),
                  .hmc_num(hmc_num),
                  .test_addr(64'h0000_0000_0000_ab00)
                 );
endtask // hmc_test

task scrub_test;

   logic [63:0]  dom0_mgmt_bar;

   logic [15:0]  dom0_pf;

   logic [31:0]  read_data;
   logic [31:0]  write_data;

   logic         fail;
   int           error_count;

   logic         done;



   fail = 0;
   error_count = 0;

   sys_init(.error_count(error_count));

   dom0_pf = EP_BUS_DEV_FNS_PF2;
   
   get_bar(.bar_num(0), .comp_id(dom0_pf), .bar_addr(dom0_mgmt_bar));

     $display("[%t] : Starting all scrubbers", $realtime);
   // Enable DDR0 Scrubber
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_0001), .comp_id(dom0_pf));
   // Wait for a while
   wait_for_clock(40);

   // Enable DDR1 Scrubber
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_0003), .comp_id(dom0_pf));
   // Wait for a while
   wait_for_clock(40);

   // Enable DDR2 Scrubber
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_0007), .comp_id(dom0_pf));
   // Wait for a while
   wait_for_clock(40);

   // Enable DDR3 Scrubber
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_000F), .comp_id(dom0_pf));
   // Wait for a while
   wait_for_clock(40);

   
   // Wait for done from all memories
   done = 0;
   while (done == 0) begin
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h60), .read_data(read_data), .comp_id(dom0_pf));

      done = (read_data[7:4] == 4'hF);
   end

   // Clear all Scrub start enables
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_0000), .comp_id(dom0_pf));
   wait_for_clock(40);

   // Make sure the scrubber done bits are deasserted
   reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h60), .read_data(read_data), .comp_id(dom0_pf));
   
   if (read_data[7:4] != 4'h0)
     begin
        $display("[%t] : Scrubber Done did not get Cleared. Addr 0x60 = 0x%08x", $realtime, read_data);
        $display("[%t] : *** TEST FAILED ***", $realtime);
        $finish;
     end

   $display("[%t] : Restarting all scrubbers again", $realtime);
   
   // Enable DDR0 Scrubber
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_000F), .comp_id(dom0_pf));

   
   // Wait for done from all memories
   done = 0;
   while (done == 0) begin
      reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h60), .read_data(read_data), .comp_id(dom0_pf));

      done = (read_data[7:4] == 4'hF);
   end

   // Clear all Scrub start enables
   reg_write(.base_addr(dom0_mgmt_bar), .reg_offset(12'hf4), .write_data(32'h0000_0000), .comp_id(dom0_pf));
   wait_for_clock(40);

   reg_read(.base_addr(dom0_mgmt_bar), .reg_offset(12'h60), .read_data(read_data), .comp_id(dom0_pf));
   
   if (read_data[7:4] != 4'h0)
     begin
        $display("[%t] : Scrubber Done did not get Cleared. Addr 0x60 = 0x%08x", $realtime, read_data);
        $display("[%t] : *** TEST FAILED ***", $realtime);
        $finish;
     end
   else
     $display("[%t] : *** TEST PASSED ***", $realtime);

   $finish;

endtask // scrub_test

// Task to Fill or Check 8K of DDR - 
// TODO: Add this to scrubber test - 
// TODO: Fill DDR before scrub with non-zero value before scrub
// TODO: Check DDR after scrub to make sure scrub cleared the DDR 
//  task fill_ddr (input [31:0] fill_data,
//                 input [11:0] base_addr,
//                 input        scrb_chk,
//                 input [63:0] domu_bar,
//                 input [15:0] domu_pf,
//                 input [63:0] dom0_bar,
//                 input [15:0] dom0_pf,
//                 output       success);
//  
//     logic [31:0]             ddr_addr;
//     logic [31:0]             ddr_data;
//     logic [31:0]             i;
//     logic [31:0]             cmd;
//     logic                    done;
//     // 8 instructions, each instruction is 16 data phases (1024B)
//     // Total 8KB 
//     for (i=0; i<8; i++)
//     begin
//        ddr_addr = 32'h400 * i;
//        if (scrb_chk) 
//          ddr_data = 0;
//        else
//          ddr_data = fill_data;
//        
//        // Instruction index 
//        //poke(base_addr + 12'h1c, i);
//        
//        // Instruction lower address
//        // poke(base_addr + 12'h20, ddr_addr);
//        
//        // Instruction upper address
//        //poke(base_addr + 12'h24, 32'h0);
//        
//        // Instruction data
//        // poke(base_addr + 12'h28, ddr_data);
//        
//        // Instruction length
//        // poke(base_addr + 12'h2c, 32'hf);
//  
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h1c), .write_data(i), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h20), .write_data(ddr_addr), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h24), .write_data(32'h0), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h28), .write_data(ddr_data), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h2c), .write_data(32'hf), .comp_id(domu_pf));
//        
//        // poke(base_addr + 12'h3c, i);
//        // poke(base_addr + 12'h40, ddr_addr);
//        // poke(base_addr + 12'h44, 32'h0);
//        // poke(base_addr + 12'h48, ddr_data);
//        // poke(base_addr + 12'h4c, 32'hf);
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h3c), .write_data(i), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h40), .write_data(ddr_addr), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h44), .write_data(32'h0), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h48), .write_data(ddr_data), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h4c), .write_data(32'hf), .comp_id(domu_pf));
//        
//        //Set iteration mode, loop higher address enable.  Loop shift count 18 (256KB)
//        //     cmd =  (1 << 5) |        #Iteration mode
//        //            (1 << 6) |        #Loop higher address enable(enable shift for upper address)
//        //            (18 << 8) |       #Write address loop shift (18-bits)
//        //            (18 << 16) |      #Read address loop shift (18-bits)
//        //            (1  << 25);       #Constant data mode
//        cmd = 32'h0212_1260;
//     
//        //Write command
//        //poke(base_addr + 0x0, cmd);
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h0), .write_data(cmd), .comp_id(domu_pf));
//  
//        //Write/Read loop number 16GB/256KB = 64
//        // poke(base_addr + 0xc0, 64);
//        // poke(base_addr + 0xc8, 64);
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'hc0), .write_data(32'h1), .comp_id(domu_pf));
//        reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'hc8), .write_data(32'h1), .comp_id(domu_pf));
//  
//        //Set the GO bit
//        if (scrb_chk) 
//          // poke(base_addr + 0x8, 0x2);
//          reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h8), .write_data(32'h2), .comp_id(domu_pf));
//        else begin
//           // poke(base_addr + 0x8, 0x1);
//           // poke(base_addr + 0x8, 0x3);
//           reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h8), .write_data(32'h1), .comp_id(domu_pf));
//           reg_write(.base_addr(domu_bar), .reg_offset(base_addr + 12'h8), .write_data(32'h3), .comp_id(domu_pf));
//        end
//     
//        done = 0;
//        while (done == 0) begin
//           reg_read(.base_addr(domu_bar), .reg_offset(base_addr + 12'h8), .read_data(read_data), .comp_id(domu_pf));
//           done = (read_data == 32'd0);
//        end
//  
//        //See there are no miscompares
//     //read_data = peek(base_addr + 0xb0);
//       reg_read(.base_addr(domu_bar), .reg_offset(base_addr + 12'hb0), .read_data(read_data), .comp_id(domu_pf));
//     if (read_data != 32'd0) begin
//        $display ("***ERROR*** miscompare");
//        success = 1'b0;
//     end
//     else
//        success = 1'b1;
//  }   

   
