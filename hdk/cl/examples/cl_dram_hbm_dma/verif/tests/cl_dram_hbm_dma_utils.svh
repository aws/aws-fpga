// Amazon FPGA Hardware Development Kit
//
// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.


task initialize_ddr();
   $display("[%t] Initializing DDR", $realtime);
   tb.poke_stat(.addr(8'h0c), .intf("ddr"), .data(32'h0000_0000));
   tb.poke_stat(.addr(8'h0c), .intf("ddr"), .data(32'h0000_0001));
   tb.poke_stat(.addr(8'h0c), .intf("ddr"), .data(32'h0000_0000));

   // AXI_MEMORY_MODEL is used to bypass DDR micron models and run with AXI memory models.
   //		More information can be found in the readme.md
   `ifndef AXI_MEMORY_MODEL
      tb.nsec_delay(27000);
   `endif
   $display("[%t] Finished DDR Initialization", $realtime);

   verify_ddr_dimm();
endtask

task verify_ddr_dimm();
   automatic logic [511:0] level_1_data = 'h00AA_BBFF_CC00;
   automatic logic [511:0] level_2_data = 'h9988_BB77_2200;
   automatic logic [511:0] level_3_data = 'h1122_4433_6655;
   automatic logic [63:0] level_1_addr = `DDR_BASE_ADDR + `DDR_LEVEL_1;
   automatic logic [63:0] level_2_addr = `DDR_BASE_ADDR + `DDR_LEVEL_2;
   automatic logic [63:0] level_3_addr = `DDR_BASE_ADDR + `DDR_LEVEL_3;

   $display("[%t] Verifying DDR DIMM and Offsets", $realtime);
   $display("[%t] DDR DIMM Verification: Level 1 - Level 2", $realtime);
   check_overwrite(level_1_addr, level_1_data, level_2_addr, level_2_data);
   $display("[%t] DDR DIMM Verification: Level 1 - Level 3", $realtime);
   check_overwrite(level_1_addr, level_1_data, level_3_addr, level_3_data);
   $display("[%t] DDR DIMM Verification: Level 3 - Level 2", $realtime);
   check_overwrite(level_3_addr, level_3_data, level_2_addr, level_2_data);
   $display("[%t] DDR DIMM Verification: Level 3 - Level 1", $realtime);
   check_overwrite(level_3_addr, level_3_data, level_1_addr, level_1_data);
   $display("[%t] DDR DIMM Verification: Level 2 - Level 1", $realtime);
   check_overwrite(level_2_addr, level_2_data, level_1_addr, level_1_data);
   $display("[%t] DDR DIMM Verification: Level 2 - Level 3", $realtime);
   check_overwrite(level_2_addr, level_2_data, level_3_addr, level_3_data);
   $display("[%t] Finished Verifying DDR DIMM and Offsets", $realtime);
endtask

task check_overwrite(logic [63:0] addr0, logic [511:0] data0, logic [63:0] addr1, logic [511:0] data1);
    automatic logic [511:0] rdata = 0;

    check_peek_poke(.addr(addr0), .data(data0), .size(DataSize::UINT512));
    check_peek_poke(.addr(addr1), .data(data1), .size(DataSize::UINT512));

    tb.peek(.addr(addr0), .data(rdata), .size(DataSize::UINT512));
    if (rdata != data0) begin
        $error("[%t] Data Mismatch - Addr: %0x Expected: %0x Actual: %0x", $realtime, addr0, data0, rdata);
        $fatal("[%t] DDR Memory was overwritten. Please verify the DIMM simulation model", $realtime);
    end

    check_peek_poke(.addr(addr0), .data(data0), .size(DataSize::UINT512));
    tb.peek(.addr(addr1), .data(rdata), .size(DataSize::UINT512));
    if (rdata != data1) begin
        $error("[%t] Data Mismatch -Addr: %0x Expected: %0x Actual: %0x", $realtime, addr1, data1, rdata);
        $fatal("[%t] DDR Memory was overwritten. Please verify the DIMM simulation model", $realtime);
    end
endtask

task initialize_hbm();
   automatic int timeout_count = 0;
   logic [31:0] read_data;

   $display("[%t] Initializing HBM", $realtime);
   do begin
         timeout_count++;
         tb.nsec_delay(5000);
      tb.peek_stat(.addr(8'h0), .intf("hbm"), .data(read_data[31:0]));
   end while (((read_data & 32'hE) != 32'h6) && (timeout_count < 100));

   if (timeout_count >= 100) begin
      $fatal("[%t] Timeout waiting for HBM to initialize", $realtime);
   end else begin
      $display("[%t] : HBM Initialization Successful", $realtime);
   end
endtask

task deselect_cl_tst_hw();
   $display("De-selecting CL TST hardware");
   tb.poke_ocl(.addr(64'h130), .data(0)); // DDR
   tb.poke_ocl(.addr(64'h230), .data(0)); // HBM
   // Offset 16 GB NOT UTILIZED IN DESIGN tb.poke_ocl(.addr(64'h330), .data(0));
   // Offset 24 GB NOT UTILIZED IN DESIGN tb.poke_ocl(.addr(64'h430), .data(0));
   tb.nsec_delay(1000);
   $display("Finished de-selecting CL TST hardware");
endtask


task load_host_memory(int chan, logic [63:0] host_addr, logic [63:0] cl_addr, logic [7:0] data_pattern, int num_bytes);
   automatic logic [63:0] host_memory_buffer_address = host_addr;
   tb.que_buffer_to_cl(.chan(chan), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr), .len(num_bytes));

   for (int i = 0 ; i < num_bytes ; i++) begin
      tb.hm_put_byte(.addr(host_memory_buffer_address), .d(data_pattern));
      host_memory_buffer_address++;
   end
endtask

task check_host_memory(logic [63:0] addr, logic [7:0] expected_data_pattern, int num_bytes);
   logic [7:0] current_byte;

   for (int i = 0 ; i< num_bytes ; i++) begin
      current_byte = tb.hm_get_byte(.addr(addr));
      if (current_byte !== expected_data_pattern) begin
         $error("[%t] : *** ERROR *** Data mismatch, addr:%0x Expected: %0x Actual: %0x",
                  $realtime, (addr + i), expected_data_pattern, current_byte);
         error_count++;
      end
   end
endtask

task wait_for_dma_transfer_from_buffer_to_cl(int chan);
   automatic int timeout_count = 0;
   do begin
      #10ns;
      timeout_count++;
   end while ((tb.is_dma_to_cl_done(.chan(chan)) != 1'b1) && (timeout_count < 4000));

   if (timeout_count >= 5000) begin
      $error("[%t] : *** ERROR *** Timeout waiting for H2C dma transfers from cl", $realtime);
      error_count++;
   end
endtask

task wait_for_dma_transfer_from_cl_to_buffer(int chan);
   automatic int timeout_count = 0;
   do begin
      #10ns;
      timeout_count++;
   end while ((tb.is_dma_to_buffer_done(.chan(chan)) != 1'b1) && (timeout_count < 1000));

   if (timeout_count >= 1000) begin
      $error("[%t] : *** ERROR *** Timeout waiting for C2H dma transfers from cl", $realtime);
      error_count++;
   end
endtask

task ocl_peek_poke_peek(input logic [11:0] register, logic [31:0] expected_default_data = 32'h0, logic [31:0] new_data = 32'h0, bit is_missing_reg = 1'b0, bit is_read_only = 1'b0);
   if (is_missing_reg == 1'b0) begin
      check_peek_ocl(.addr(register), .data(expected_default_data));

      if (is_read_only == 1'b0) begin
         tb.poke_ocl(.addr(register), .data(new_data));
         check_peek_ocl(.addr(register), .data(new_data));
      end
   end else begin
      check_peek_ocl(.addr(register), .data(32'hBAAD_DEC0));

      if (is_read_only == 1'b0) begin
         tb.poke_ocl(.addr(register), .data(32'hDEAD_BEEF));
         check_peek_ocl(.addr(register), .data(32'hBAAD_DEC0));
      end
   end
endtask

task check_peek_ocl(logic [63:0] addr, logic [31:0] data);
   logic [31:0] rdata;
   tb.peek_ocl(.addr(addr), .data(rdata));

   if (rdata !== data) begin
      $error("[%t] : *** ERROR *** Data mismatch, addr:%0x read data is: %0x rather than %0x",
                  $realtime, addr, rdata, data);
      error_count++;
   end
endtask

task check_peek_poke(logic [63:0] addr, logic [511:0] data, DataSize::DATA_SIZE size);
   logic [511:0] rdata;
   tb.poke(.addr(addr), .data(data), .size(size));
   #1us;
   tb.peek(.addr(addr), .data(rdata), .size(DataSize::UINT64));

   compare_data(.exp_data(data), .act_data(rdata), .addr(addr));
endtask

task program_cl_tst(
                                     input logic [63:0] base_addr,
                                     bit                addr_loop_mode = 1'b0,
                                     logic [5:0]        loop_shift = 6'h10,
                                     bit                user_id_mode = 1'b0,
                                     bit                iter_mode = 1'b0,
                                     bit                cont_mode = 1'b0,
                                     logic [63:0]       num_iter = 64'h0400,
                                     logic [8:0]        max_num_rd_req = 9'h01f,
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
                                     bit                wait_for_done = 1'b1
                                     );
    automatic logic [7:0]  axi_index = 8'h00;
    automatic logic [15:0] num_wr_inst = 16'h0000;
    automatic logic [15:0] num_rd_inst = 16'h0000;
	automatic logic [31:0] atg_error = 32'h0;
	automatic logic [63:0] addr = 64'h0;

	`define START_EXEC base_addr + 64'h008
	`define RD_TAG_RESET base_addr + 64'h00c
	`define NUM_RD_WR_INSTR base_addr + 64'h010
	`define MAX_RD_COUNT base_addr + 64'h014
	`define ATG_ENABLE_REG base_addr + 64'h030
	`define ATG_ERROR_REG base_addr + 64'h0b0

    tb.poke_ocl(.addr(`ATG_ENABLE_REG), .data(32'h0000_0001));
	// Clear error register
	tb.poke_ocl(.addr(`ATG_ERROR_REG), .data(32'h0000_0001));

	program_atg_config(.base_addr(base_addr), .addr_loop_mode(addr_loop_mode), .loop_shift(loop_shift), .user_id_mode(user_id_mode),
					   .iter_mode(iter_mode), .cont_mode(cont_mode), .enable_write(enable_write), .enable_read(enable_read), .compare_read(compare_read));

    // Set the max number of read requests
    tb.poke_ocl(.addr(`MAX_RD_COUNT), .data({23'h0, max_num_rd_req}));

    if (enable_write == 1'b1) begin
		program_write_instructions(.base_addr(base_addr), .running_addr(test_addr), .axi_index(axi_index),
							       .running_len(axi_len), .test_data(test_data), .iter_mode(iter_mode), .num_iter(num_iter),
      							   .num_inst(num_inst), .user_id_mode(user_id_mode), .wr_user(wr_user), .last_len(last_len), .vary_len(vary_len));
	    num_wr_inst = num_inst;
    end

    if (enable_read == 1'b1) begin
		program_read_instructions(.base_addr(base_addr), .running_addr(test_addr), .axi_index(axi_index),
							      .running_len(axi_len), .test_data(test_data), .iter_mode(iter_mode), .num_iter(num_iter),
       							  .num_inst(num_inst), .user_id_mode(user_id_mode), .rd_user(rd_user), .last_len(last_len), .vary_len(vary_len));
        num_rd_inst = num_inst;
    end

    // Number of instructions ([31:16] for read, [15:0] for write)
    tb.poke_ocl(.addr(`NUM_RD_WR_INSTR), .data({num_rd_inst, num_wr_inst}));

    // Start reads and writes ([1] for reads, [0] for writes)
    if (start_cl == 1'b1) begin
        tb.poke_ocl(.addr(`RD_TAG_RESET), .data(32'h0000_0001));
        tb.poke_ocl(.addr(`START_EXEC), .data({30'h0000_0000, enable_read, enable_write}));

        if (wait_for_done == 1'b1) begin
            wait_for_atg_done(.base_addr(base_addr), .cont_mode(cont_mode), .iter_mode(iter_mode),
	            .enable_write(enable_write), .enable_read(enable_read), .num_iter(num_iter));

    		tb.peek_ocl(.addr(`ATG_ERROR_REG), .data(atg_error));
            if (atg_error != 0) begin
               tb.peek_ocl(.addr(`ATG_ERROR_REG + 12'h004), .data(atg_error));
               addr[31:0] = atg_error;
               tb.peek_ocl(.addr(`ATG_ERROR_REG + 12'h008), .data(atg_error));
               addr[63:32] = atg_error;

               error_count++;
               $error("[%t] : *** ERROR *** Address of error: %x", $realtime, addr);
               tb.peek_ocl(.addr(`ATG_ERROR_REG + 12'h00c), .data(atg_error));
               $error("[%t] : *** ERROR *** Rd RAM index of error data: %x", $realtime, atg_error);
               $error("[%t] : *** ERROR *** ATG Reports Errors", $realtime);
	        end
        end
    end

    $display("[%t] Completed ATG Program", $realtime);
endtask

task program_atg_config(logic [63:0] base_addr, bit addr_loop_mode, logic [5:0] loop_shift,
										 bit user_id_mode, bit iter_mode, bit cont_mode, bit enable_write, bit enable_read, bit compare_read);
	`define MODE_CFG base_addr + 64'h000

    automatic logic [31:0] write_data  = 32'h0000_0000;

    if (addr_loop_mode == 1'b1) begin
        write_data[21:16] = loop_shift[5:0];
        write_data[13:8] = loop_shift[5:0];
    end
    write_data[26] = 1'b1; // Always enable Incrementing AWID mode
    write_data[24] = 1'b1; // Always enable Incrementing ID mode
    write_data[7] = user_id_mode;
    write_data[6] = addr_loop_mode;
    write_data[5] = iter_mode;
    write_data[4] = (enable_write & enable_read); // Enable Sync Mode when doing both writes and reads
    write_data[3] = compare_read;
    write_data[2] = 1'b0; // PRBS mode not supported
    write_data[1] = 1'b0; // Incrementing Loop Data mode not supported
    write_data[0] = cont_mode;
    tb.poke_ocl(.addr(`MODE_CFG), .data(write_data));
endtask


task program_write_instructions(logic [63:0] base_addr, logic [63:0] running_addr, logic [7:0] running_len,
								logic [7:0] axi_index, logic [31:0] test_data, bit iter_mode, logic [63:0] num_iter,
								logic [15:0] num_inst, bit user_id_mode, logic [15:0] wr_user, logic [7:0] last_len, bit vary_len);
	`define RAM_WR_INDEX base_addr + 64'h01c
	`define WR_ADDR_LOWER base_addr + 64'h020
	`define WR_ADDR_HIGHER base_addr + 64'h024
	`define WR_DATA base_addr + 64'h028
	`define WR_METADATA base_addr + 64'h02c

	automatic logic [15:0] axi_user = user_id_mode ? wr_user : 16'h0000;

    // Initial Index (value will be auto-incremented after write to register at offset 0x2c)
    tb.poke_ocl(.addr(`RAM_WR_INDEX), .data({24'h000000, axi_index}));

    for (int i=0; i<=num_inst; i++) begin
      tb.poke_ocl(.addr(`WR_ADDR_LOWER), .data(running_addr[31:0]));
      tb.poke_ocl(.addr(`WR_ADDR_HIGHER), .data(running_addr[63:32]));
      tb.poke_ocl(.addr(`WR_DATA), .data(test_data[31:0]));
      tb.poke_ocl(.addr(`WR_METADATA), .data({axi_user, last_len, running_len}));

      running_addr = running_addr + (64 * (running_len + 8'h01)); // Multiply by 64 because that is the largest data width (512 bits)
      if (vary_len == 1'b1) begin
          running_len = (running_len < 8'h07) ? (running_len + 8'h01) : 8'h00;
      end
    end

//    if (iter_mode == 1) begin
//        tb.poke_ocl(.addr(base_addr + 64'h0c0), .data(num_iter[31:0]));
//        tb.poke_ocl(.addr(base_addr + 64'h0c4), .data(num_iter[63:32]));
//        reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c0), .expected_data(num_iter[31:0]));
//        reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c4), .expected_data(num_iter[63:32]));
//	end
endtask

task program_read_instructions(logic [63:0] base_addr, logic [63:0] running_addr, logic [7:0] running_len,
							   logic [7:0] axi_index, logic [31:0] test_data, bit iter_mode, logic [63:0] num_iter,
							   logic [15:0] num_inst, bit user_id_mode, logic [15:0] rd_user, logic [7:0] last_len, bit vary_len);

	`define RAM_RD_INDEX base_addr + 64'h03c
	`define RD_ADDR_LOWER base_addr + 64'h040
	`define RD_ADDR_HIGHER base_addr + 64'h044
	`define RD_DATA base_addr + 64'h048
	`define RD_METADATA base_addr + 64'h04c

	automatic logic [15:0] axi_user = user_id_mode ? rd_user : 16'h0000;

    // Initial Index (value will be auto-incremented after write to register at offset 0x4c)
    tb.poke_ocl(.addr(`RAM_RD_INDEX), .data({24'h000000, axi_index}));

    for (int i=0; i<=num_inst; i++) begin
      tb.poke_ocl(.addr(`RD_ADDR_LOWER), .data(running_addr[31:0]));
      tb.poke_ocl(.addr(`RD_ADDR_HIGHER), .data(running_addr[63:32]));
      tb.poke_ocl(.addr(`RD_DATA), .data(test_data[31:0]));
      tb.poke_ocl(.addr(`RD_METADATA), .data({axi_user, last_len, running_len}));

      running_addr = running_addr + (64 * (running_len + 8'h01));
      if (vary_len == 1'b1) begin
          running_len = (running_len < 8'h07) ? (running_len + 8'h01) : 8'h00;
      end
  	end

//    if (iter_mode == 1) begin
//        tb.poke_ocl(.addr(base_addr + 64'h0c8), .data(num_iter[31:0]));
//        tb.poke_ocl(.addr(base_addr + 64'h0cc), .data(num_iter[63:32]));
//        reg_read_check(.base_addr(base_addr), .reg_offset(12'h0c8), .expected_data(num_iter[31:0]));
//        reg_read_check(.base_addr(base_addr), .reg_offset(12'h0cc), .expected_data(num_iter[63:32]));
//    end
endtask

task wait_for_atg_done(logic [63:0] base_addr, bit cont_mode, bit iter_mode, bit enable_write, bit enable_read,
										logic [63:0] num_iter);
	`define WR_LOOP_LOW base_addr + 64'h090
	`define WR_LOOP_HIGH base_addr + 64'h094
	`define RD_LOOP_LOW base_addr + 64'h098
	`define RD_LOOP_HIGH base_addr + 64'h09c

    logic [63:0] read_data;
    automatic logic [63:0] loop_count = 64'h0;
    automatic int timeout_count = 0;

	if ((cont_mode == 1'b1) || (iter_mode == 1'b1)) begin
        if (enable_write == 1'b1) begin
            // Wait for specified number of write loops
            while (loop_count < num_iter) begin
                tb.peek_ocl(.addr(`WR_LOOP_LOW), .data(read_data));
                loop_count[31:0] = read_data[31:0];
                tb.peek_ocl(.addr(`WR_LOOP_HIGH), .data(read_data));
                loop_count[63:32] = read_data[31:0];
                timeout_count = timeout_count + 1;
                #100ns;
    	    if (timeout_count == 1000) begin
                    error_count++;
                    $error("[%t] : *** ERROR *** Timeout waiting for write loop_count (%3d) to equal num_iter (%3d)", $realtime, loop_count, num_iter);
               end
            end
        end
        if (enable_read == 1'b1) begin
            // Wait for specified number of read loops
            loop_count = 64'h0;
            timeout_count = 0;
            while (loop_count < num_iter) begin
                tb.peek_ocl(.addr(`RD_LOOP_LOW), .data(read_data));
                loop_count[31:0] = read_data[31:0];
                tb.peek_ocl(.addr(`RD_LOOP_HIGH), .data(read_data));
                loop_count[63:32] = read_data[31:0];
                timeout_count = timeout_count + 1;
                #100ns;
    	    if (timeout_count == 1000) begin
                    error_count++;
                    $error("[%t] : *** ERROR *** Timeout waiting for read loop_count (%3d) to equal num_iter (%3d)", $realtime, loop_count, num_iter);
                end
            end
        end
    end else begin
        // Wait for writes and reads to complete
        #2000ns;
        // NOTE: Adding outer fork to avoid issues caused by "disable fork" in inner fork
        fork
            begin
                fork
                    begin
                        do begin
                            tb.peek_ocl(.addr(`START_EXEC), .data(read_data));
                        end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
                    end
                    begin
                        #20000ns;
	                    error_count++;
               			$error("[%t] : *** ERROR *** Timeout waiting for writes and reads to complete.", $realtime);
                    end
                join_any
                disable fork;
            end
        join
    end
endtask
