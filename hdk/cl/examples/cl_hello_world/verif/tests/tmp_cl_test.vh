// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

 `define HMC_WRAPPER_PATH tb.TOP.CL.HMC_WRAPPER
 `define SH_PATH tb.TOP.SH


task tmp_cl_common_test(input logic [63:0] cl_base = 64'h0, logic [63:0] test_addr = 64'h0, logic [31:0] wr_data = 32'h6c93_af50, bit addr_loop_mode = 1'b0, logic [5:0] loop_shift = 6'h20, bit iter_mode = 1'b0, logic [63:0] num_iter = 64'h0400, bit prbs_mode = 1'b0, bit cont_mode = 1'b0, bit user_id_mode=1'b0, logic[7:0] wr_len=8'h07, logic[7:0] rd_len=8'h07, logic[15:0] max_num_rd_req=16, logic inc_id_mode=0, logic[3:0] hmc_num='hf);


begin

   // Fixed values for initial testing
   logic fail;
   logic [7:0]   wr_index;
   logic [15:0]  num_inst;
   logic [7:0]   rd_index;

   // Test variables
   logic [63:0]  tgt_bar0;
   logic [63:0]  loop_count;
   logic [31:0]  write_data;
   logic [31:0]  read_data;
   logic [63:0]  error_addr;
   logic [3:0]   error_index;

   logic[15:0] wr_user;

   int to_count;

   fail = 0;

   wr_index = 8'h00;
   num_inst = 16'h0; // Single write and read
   rd_index = 8'h00;

   // This test performs a 32 bit write to a 32 bit Memory space and performs a read back
   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;
   tgt_bar0 = 64'h0000_1000_0000_0000;

   // Write BAR4 
   TSK_TYPE0_CFG_WRITE(12'h20, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h24, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
   TSK_TYPE0_CFG_WRITE(12'hc8, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

      if (hmc_num!='hf)
      begin
         $display($time,"***FATAL*** Don't have HMC_PRESENT defined");
         $finish;
      end

   //---------------------------
   // CL Config
   //---------------------------
   write_data = 32'h0000_0000;
   if (addr_loop_mode == 1) begin
      write_data[21:16] = loop_shift[5:0];
      write_data[13:8] = loop_shift[5:0];
   end
   write_data[24] = inc_id_mode;
   write_data[7] = user_id_mode;
   write_data[6] = addr_loop_mode;
   write_data[5] = iter_mode;
   write_data[4] = 1'b1; // Always enable Sync Mode
   write_data[3] = 1'b1; // Always enable Read Compare
   write_data[2] = prbs_mode;
   write_data[1] = 1'b0; // Don't enable Incrementing Loop Data
   write_data[0] = cont_mode;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h00), .data(write_data));

   //---------------------------
   // Iterations
   //---------------------------
   if (iter_mode == 1) begin
      // Number of write iterations
      tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'hc0), .data(num_iter[31:0]));
      tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'hc4), .data(num_iter[63:32]));
      // Number of read iterations
      tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'hc8), .data(num_iter[31:0]));
      tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'hcc), .data(num_iter[63:32]));
   end

   //Set the max number of read requests
   if (max_num_rd_req != 15)
   begin
      tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h14), .data(max_num_rd_req));
   end
   

   //----------------------------
   // Program write instructions
   //----------------------------
  
   wr_user = 0; 
   test_addr[63:32] = 32'habcd_0000;
   wr_data[31:16] = 16'h1111;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h1c), .data({32'h0}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h20), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h24), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h28), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h2c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0010;
   wr_data[31:16] = 16'h2222;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h1c), .data({32'h1}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h20), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h24), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h28), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h2c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0020;
   wr_data[31:16] = 16'h3333;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h1c), .data({32'h2}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h20), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h24), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h28), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h2c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0030;
   wr_data[31:16] = 16'h3333;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h1c), .data({32'h3}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h20), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h24), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h28), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h2c), .data({wr_user, 8'h00, wr_len}));        //Length


   //---------------------------
   // Program read instructions
   //---------------------------
   test_addr[63:32] = 32'habcd_0000;
   wr_data[31:16] = 16'h1111;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h3c), .data({32'h0}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h40), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h44), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h48), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h4c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0010;
   wr_data[31:16] = 16'h2222;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h3c), .data({32'h1}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h40), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h44), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h48), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h4c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0020;
   wr_data[31:16] = 16'h3333;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h3c), .data({32'h2}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h40), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h44), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h48), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h4c), .data({wr_user, 8'h00, wr_len}));        //Length

   test_addr[63:32] = test_addr + 32'h0000_0030;
   wr_data[31:16] = 16'h3333;
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h3c), .data({32'h3}));
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h40), .data(test_addr[31:0]));                 //Addr low
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h44), .data(test_addr[63:32]));                //Addr high
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h48), .data(wr_data[31:0]));                   //Write data
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h4c), .data({wr_user, 8'h00, wr_len}));        //Length


   // Number of instructions ([31:16] for read, [15:0] for write)
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h10), .data({16'h3, 16'h3}));

   // Start reads and writes ([1] for reads, [0] for writes)
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h08), .data(32'h00000003));


   if ((cont_mode == 1'b1) || (iter_mode == 1'b1)) begin
      // Wait for specified number of write loops
      loop_count = 64'h0;
      to_count = 0;
      while (loop_count < num_iter) begin
         tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h90), .rdata(read_data));
         loop_count[31:0] = read_data;
         tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h94), .rdata(read_data));
         loop_count[63:32] = read_data;
         to_count = to_count + 1;
         if (to_count == 40)
            $display($time,,,"***ERROR*** timeout (WR) waiting for loop_count=%d to equal num_iter=%d", loop_count, num_iter);
      end
      // Wait for specified number of read loops
      loop_count = 64'h0;
      to_count = 0;
      while (loop_count < num_iter) begin
         tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h98), .rdata(read_data));
         loop_count[31:0] = read_data;
         tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h9c), .rdata(read_data));
         loop_count[63:32] = read_data;
         to_count = to_count + 1;
         if (to_count == 40)
            $display($time,,,"***ERROR*** timeout (RD) waiting for loop_count=%d to equal num_iter=%d", loop_count, num_iter);
      end
      
   end else begin
      // Wait for writes and reads to complete
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(2000);
      do begin
         tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h08), .rdata(read_data));
      end while (read_data[2:0] !== 3'b000); // [2]: Read response pending, [1]: Read in progress, [0]: Write in progress
   end

   // Stop reads and writes ([1] for reads, [0] for writes)
   tb.RP.tx_usrapp.S_MEMORY_WRITE_64(.addr(tgt_bar0 + cl_base + 64'h08), .data(32'h00000000));

   $display("[%t] : Finished transmission of PCI-Express TLPs", $realtime);

   //---------------------------
   // Check for errors
   //---------------------------
   $display("[%t] : Checking for errors...", $realtime);
   ////Check that the count is correct
   //if (iter_mode)
   //begin
   //   tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h80), .rdata(read_data));
   //   if (read_data!=num_iter)
   //   begin
   //      $display($time,,,"***ERROR*** write iter_count not correct expected=0x%x, actual=0x%x", num_iter, read_data);
   //      fail = 1;
   //   end

   //   tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'h88), .rdata(read_data));
   //   if (read_data!=num_iter)
   //   begin
   //      $display($time,,,"***ERROR*** read iter_count not correct expected=0x%x, actual=0x%x", num_iter, read_data);
   //      fail = 1;
   //   end
   //end
  
   //See if got compare error 
   tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'hb0), .rdata(read_data));

   if (read_data != 32'h0000_0000) begin
      tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'hb4), .rdata(read_data));
      error_addr[31:0] = read_data;
      tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'hb8), .rdata(read_data));
      error_addr[63:32] = read_data;
      tb.RP.tx_usrapp.S_MEMORY_READ_64_RET (.addr(tgt_bar0 + cl_base + 64'hbc), .rdata(read_data));
      error_index = read_data[3:0];
      $display("*** ERROR *** : Read compare error from address 0x%016x, index 0x%1x", error_addr, error_index);

      fail = 1;
   end

   if (fail)
      $display("[%t] : TEST FAILED", $realtime);
   else
      $display("[%t] : TEST PASSED", $realtime);

   $finish;
end
endtask



task tmp_cl_pcie_iter_test;
//tmp_cl_common_test(.cl_base(64'h0000_0000_0000_0000), .test_addr(64'h0000_0000_0000_0000), .iter_mode(1'b1), .num_iter(64'h0064), .addr_loop_mode(1'b0), .loop_shift(6'h0));

logic [63:0]  tgt_bar0;
logic [63:0]  dom0_bar;
logic[31:0] length;
logic[31:0] read_data;

string subtest;

begin
   // This test performs a 32 bit write to a 32 bit Memory space and performs a read back
   tb.RP.tx_usrapp.TSK_SYSTEM_INITIALIZATION;
   tgt_bar0 = 64'h0000_1000_0000_0000;
   dom0_bar = 64'h0000_2000_0000_0000;

   // Write BAR4 
   TSK_TYPE0_CFG_WRITE(12'h20, tgt_bar0[31:0], EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h24, tgt_bar0[63:32], EP_BUS_DEV_FNS);

   // Set MPS, BusMaster, MemEnable
      TSK_TYPE0_CFG_WRITE(12'h78, 32'h505f, EP_BUS_DEV_FNS);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS);

   //Enumerate PF2 (Dom0)
   // Write BAR0 
   TSK_TYPE0_CFG_WRITE(12'h10, dom0_bar[31:0], EP_BUS_DEV_FNS_PF2);
   TSK_TYPE0_CFG_WRITE(12'h14, dom0_bar[63:32], EP_BUS_DEV_FNS_PF2);

   // Set MPS, BusMaster, MemEnable
      TSK_TYPE0_CFG_WRITE(12'h78, 32'h505f, EP_BUS_DEV_FNS_PF2);
   TSK_TYPE0_CFG_WRITE(12'h04, 32'h07, EP_BUS_DEV_FNS_PF2);

   length = 3;
   $value$plusargs("SUBTEST=%s", subtest);
   
   case (subtest)
      "hmc_lab_test":      hmc_lab_test(tgt_bar0);
      "stop_stress":       stop_stress(tgt_bar0);
      "hmc_xilinx":        hmc_xilinx(tgt_bar0);
      "ddr_lab_test":      ddr_lab_test(tgt_bar0); 
      "tmp_aur_reg":       tmp_aur_reg(tgt_bar0);
      "tmp_cl_ddr2_lab":   tmp_cl_ddr2_lab(tgt_bar0);
      "pci_lab_test":      pci_lab_test(tgt_bar0, length);
      "pci_inc":           tmp_pci_inc(.tgt_bar0(tgt_bar0), .tst_base(16'h0000), .max_length(7));
      "tmp_pcie_misaligned":   tmp_pcie_misaligned(.tgt_bar0(tgt_bar0), .tst_base(16'h0000));
      "pci_drp":   pci_drp(.dom0_bar(dom0_bar));
      default:
      begin
         $display("***FATAL*** Unrecognized subtest=%s", subtest);
         $finish;
      end
   endcase

      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(500);
      $finish;
end
endtask

task stop_stress (input[63:0] tgt_bar0 );
logic[31:0] read_data;
logic[31:0] count;
begin
   $display("SUBTEST: STOP STRESS");
   scratch_check(tgt_bar0);
   fork 
   begin
      count = 0;
      repeat(2000)
      begin
         count = count + 1;
         $display($time,,,"Count=%d", count);

	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1000), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1100), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1200), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1300), .data(32'h0));

	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h100c), .data(32'h1));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h110c), .data(32'h1));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h120c), .data(32'h1));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h130c), .data(32'h1));

	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h100c), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h110c), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h120c), .data(32'h0));
	      TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h130c), .data(32'h0));
	      TSK_MEM_READ_64 (.addr(tgt_bar0 + 64'hf0), .rdata(read_data));
      end

      $display("!!!TEST PASSED!!!");
      $finish;
   end
   begin
      while(1)
         UC_SPI_MODEL.spi_read(.addr('h20), .exp_data(32'habcd1234), .compare(0), .read_data(read_data));
   end
   join

end
endtask

task scratch_check(input[63:0] tgt_bar0);
logic[31:0] read_data;
begin

	
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'hf0), .data(32'habcd1234));
	TSK_MEM_READ_64 (.addr(tgt_bar0 + 64'hf0), .rdata(read_data));
	
	if (read_data!=32'habcd1234)
	begin
	   $display($time,,,"***ERROR*** read miscompare on 0xf0 exp abcd1234 got 0x%x", read_data);
	   $finish;
	end
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'hf4), .data(32'haaaa1111));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'hf8), .data(32'hbbbb2222));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'hfc), .data(32'hcccc3333));
	
	TSK_MEM_READ_64 (.addr(tgt_bar0 + 64'hf4), .rdata(read_data));
	if (read_data!=32'haaaa1111)
	begin
	   $display($time,,,"***ERROR*** read miscompare on 0xf0 exp aaaa1111 got 0x%x", read_data);
	   $finish;
	end
	
	TSK_MEM_READ_64 (.addr(tgt_bar0 + 64'hfc), .rdata(read_data));
	if (read_data!=32'hcccc3333)
	begin
	   $display($time,,,"***ERROR*** read miscompare on 0xf0 exp cccc3333 got 0x%x", read_data);
	   $finish;
	end
end
endtask
   


task pci_lab_test(input[63:0] tgt_bar0, input[15:0] length);
logic[31:0] read_data;
begin

	
	
   $display("SUBTEST: PCI LAB TEST");
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h1));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0100));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h11110000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h2));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0200));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h22220000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h3));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0300));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h33330000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h4));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0400));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h44440000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h5));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0500));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h55550000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h6));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0600));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h66660000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data('h7));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0700));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h77770000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h8));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0800));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h88880000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'h9));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0900));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'h99990000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'ha));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0a00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'haaaa0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'hb));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0b00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'hbbbb0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'hc));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0c00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'hcccc0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'hd));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0d00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'hdddd0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'he));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0e00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'heeee0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h181c), .data(32'hf));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1820), .data(32'habcd0f00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1824), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1828), .data(32'hffff0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h182c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h1));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0100));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h11110000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h2));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0200));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h22220000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h3));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0300));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h33330000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h4));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0400));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h44440000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h5));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0500));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h55550000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h6));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0600));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h66660000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data('h7));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0700));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h77770000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h8));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0800));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h88880000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'h9));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0900));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'h99990000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'ha));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0a00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'haaaa0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'hb));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0b00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'hbbbb0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'hc));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0c00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'hcccc0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'hd));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0d00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'hdddd0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'he));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0e00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'heeee0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h183c), .data(32'hf));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1840), .data(32'habcd0f00));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1844), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1848), .data(32'hffff0000));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h184c), .data(length));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1808), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1880), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1884), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1888), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h188c), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18a0), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18a4), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18f0), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18f4), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18f8), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h18fc), .data(32'h0));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1800), .data(32'h01000019));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1810), .data(32'hf000f));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1810), .data(32'hf000f));
	TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h1808), .data(32'h3));
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(1000);

   //Do some reads of the Data
   $finish;

end
endtask

task hmc_lab_test(input[63:0] tgt_bar0);
logic[31:0] read_data;
begin
//Base: 0x0, NumInst=0, Length=0, Cont=0, ReadCompare=0, TstBase=0x3000
   $display("SUBTEST: HMC LAB TEST");
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h11110000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h22220000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h33330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h44440000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h55550000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h66660000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h77770000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h88880000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'h99990000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'haaaa0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'hb));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'hbbbb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'hcccc0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'hdddd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'heeee0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h301c), .data(32'hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3020), .data(32'hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3024), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3028), .data(32'hffff0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h302c), .data(32'h1b0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h11110000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h22220000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h33330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h44440000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h55550000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h66660000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h77770000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h88880000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'h99990000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'haaaa0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'hb));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'hbbbb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'hcccc0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'hdddd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'heeee0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h303c), .data(32'hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3040), .data(32'hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3044), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3048), .data(32'hffff0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h304c), .data(32'h330000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3008), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3080), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3084), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3088), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h308c), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30a0), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30a4), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30f0), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30f4), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30f8), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h30fc), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3000), .data(32'h80));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3010), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h3008), .data(32'h3));

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(3000);
   
end
endtask

task hmc_xilinx(input[63:0] tgt_bar0);
logic[31:0] read_data;

logic[31:0] timeout;
begin
//Base: 0x0, NumInst=0, Length=0, Cont=0, ReadCompare=0, TstBase=0x3000
   $display("SUBTEST: HMC XILINX ");
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h0e8), .data(32'h64));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h0e4), .data(32'hf));

   

   timeout = 0;

   read_data = 0;
   while (read_data[3:0]!=4'hf)
   begin
	   TSK_MEM_READ_64 (.addr(tgt_bar0 + 64'h8), .rdata(read_data));
      timeout = timeout + 1;
      if (timeout==10000)
      begin
         $display($time,,,"***ERROR*** Waiting for done timeout");
         $finish;
      end
   end
    
   if (read_data[11:4]!=8'h0f)
   begin
      $display($time,,,"***ERROR*** HMC status incorrect expected=0x0f, got=0x%x", read_data[11:4]);
   end

   $finish;
end
endtask


task ddr_lab_test(input[63:0] tgt_bar0);
begin
   $display("SUBTEST: DDR LAB TEST");
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc00000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc10000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc20000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc30000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc40000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc50000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc60000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc70000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc80000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habc90000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habca0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('hb));
   
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habcb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habcc0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habcd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habce0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h11c), .data('hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h120), .data('hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h124), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h128), .data('habcf0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h12c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc00000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc10000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc20000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc30000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc40000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc50000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc60000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc70000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc80000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habc90000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habca0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('hb));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habcb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habcc0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habcd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habce0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h13c), .data('hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h140), .data('hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h144), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h148), .data('habcf0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h14c), .data('h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h108), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h180), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h184), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h188), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h18c), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1a0), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1a4), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1f0), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1f4), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1f8), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h1fc), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h100), .data('h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h110), .data('hf000f));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h108), .data('h1));

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(1000);
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h108), .data('h3));
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(1000);

   $finish;

end
endtask

task tmp_aur_reg(input[63:0] tgt_bar0);
logic[31:0] rdata;

begin
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h3404), .data('habcd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h3504), .data('habcd1111));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h3604), .data('habcd2222));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 'h3704), .data('habcd3333));

   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h3404), .rdata(rdata));
   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h3504), .rdata(rdata));
   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h3604), .rdata(rdata));
   TSK_MEM_READ_64 (.addr(tgt_bar0 + 'h3704), .rdata(rdata));
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(500);
   $finish;
      
end
endtask

task tmp_cl_ddr2_lab(input[63:0] tgt_bar0);
logic[31:0] rdata;
begin
   $display("SUBTEST: DDR 2 LAB TEST");

   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h214 ), .data(32'hffffffff));
//Base: 0x0, NumInst=15, Length=3, Cont=0, ReadCompare=0, TstBase=0x200
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdddd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hddde0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdddf0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde00000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde10000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde20000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde30000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde40000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde50000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde60000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde70000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'hb));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde80000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hdde90000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hddea0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hddeb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h21c ), .data(32'hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h220 ), .data(32'hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h224 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h228 ), .data(32'hddec0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h22c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdddd0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h1));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h100));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hddde0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h2));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h200));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdddf0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h300));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde00000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h4));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h400));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde10000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h5));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h500));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde20000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h6));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h600));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde30000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h7));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h700));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde40000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h8));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h800));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde50000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'h9));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'h900));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde60000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'ha));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'ha00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde70000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'hb));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'hb00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde80000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'hc));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'hc00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hdde90000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'hd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'hd00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hddea0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'he));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'he00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hddeb0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h23c ), .data(32'hf));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h240 ), .data(32'hf00));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h244 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h248 ), .data(32'hddec0000));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h24c ), .data(32'h3));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h208 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h280 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h284 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h288 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h28c ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2a0 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2a4 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2f0 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2f4 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2f8 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h2fc ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h200 ), .data(32'h0));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h210 ), .data(32'hf000f));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h208 ), .data(32'h1));
   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(2000);
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + 64'h208 ), .data(32'h3));

   tb.RP.tx_usrapp.TSK_TX_CLK_EAT(4000);

   for (int i=0; i<32; i++)
   begin
      ddr_print_entry(.tgt_bar0(tgt_bar0), .tst_base(16'h200), .entry(i));
   end
   $finish;
end
endtask
      


task ddr_print_entry (input[63:0] tgt_bar0, input[15:0] tst_base, input[7:0] entry);
logic[31:0] read_data;

logic[63:0] addr;
logic[63:0] rd_data;
logic[63:0] exp_data;
begin
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 8'h60), .data(entry << 8));
 
   TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h64), .rdata(read_data));
   addr[31:0] = read_data;

   TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h68), .rdata(read_data));
   addr[63:32] = read_data;

   $display("CL_TST_PE: Entry=0x%x, Addr= 0x%x_%x", entry, addr[63:32], addr[31:0]);

   for (int i=0; i<16; i++)
   begin
      TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 8'h60), .data((entry << 8) + i));
      TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h6c), .rdata(rd_data)); 
      TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h70), .rdata(exp_data)); 

      $write("   CL_TST_PE: RdData=0x%x, ExpData=0x%x", rd_data, exp_data);
      if (rd_data != exp_data)
         $display("    *** MISCOMPARE ***");
      else
         $display("");
   end
end
endtask

task tmp_cfg_inst(input[63:0] tgt_bar0, input[15:0] tst_base, input[63:0] addr, input[31:0] start_data, input[7:0] len, input write=0, input[7:0] index=0, input[7:0] lst_adj=0);

bit[63:0] index_offset;
bit[63:0] inst_offset;
bit[15:0] user_bits;          //User bits for HMC (don't care for others
begin
   index_offset = tgt_bar0 + tst_base;
   inst_offset = tgt_bar0 + tst_base;

   index_offset = (write)? index_offset + 'h1c: index_offset + 'h3c;
   inst_offset = (write)? inst_offset + 'h20: inst_offset + 'h40;

   user_bits = (write && (len==1))?    16'h001f:
               (write && (len==0))?    16'h001b:
               (len==1)?               16'h0037:
                                       16'h0033;
                  

   if (write)
      $display($time,,,"WriteInst: index=0x%x, tst_base=0x%x, addr=0x%x_0x%x, start_data=0x%x, len=0x%x, lst_adj=0x%x", index, tst_base, addr[63:32], addr[31:0], start_data, len, lst_adj);
   else
      $display($time,,,"ReadInst: index=0x%x, tst_base=0x%x, addr=0x%x_0x%x, start_data=0x%x, len=0x%x, lst_adj=0x%x", index, tst_base, addr[63:32], addr[31:0], start_data, len, lst_adj);

   TSK_MEM_WRITE_64(.addr(index_offset), .data(index));                       //Index
   TSK_MEM_WRITE_64(.addr(inst_offset + 'h00), .data(addr[31:0]));            //Addr low
   TSK_MEM_WRITE_64(.addr(inst_offset + 'h04), .data(addr[63:32]));           //Addr high
   TSK_MEM_WRITE_64(.addr(inst_offset + 'h08), .data(start_data));            //Start data
   TSK_MEM_WRITE_64(.addr(inst_offset + 'h0c), .data({user_bits, lst_adj, len}));      //Length

end
endtask

task tmp_tst_go (input[63:0] tgt_bar0, input[15:0] tst_base, input wr_go=1, input rd_go=1);
begin
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'h08), .data({rd_go, wr_go}));
end
endtask

task tmp_tst_setup (input[63:0] tgt_bar0, input[15:0] tst_base, input cfg_cont=0, input cfg_iter_mode=0, input[31:0] cfg_iter_num=0, cfg_user_id=0, input[7:0] cfg_num_inst=0, input[15:0] cfg_max_rd=16'hffff);

bit[31:0] wrdata;
begin
   wrdata = 0;
   wrdata = cfg_cont |
            (1'b1 << 3) |              //Always set compare enable
            (cfg_iter_mode << 5) |
            (cfg_user_id << 7);

   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'h00), .data(wrdata));

   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'h10), .data({cfg_num_inst, 8'h00, cfg_num_inst})); 
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'h14), .data(cfg_max_rd));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'hc0), .data(cfg_iter_num));
   TSK_MEM_WRITE_64(.addr(tgt_bar0 + tst_base + 'hc8), .data(cfg_iter_num));
   
end 
endtask

task tmp_chk (input[63:0] tgt_bar0, input[15:0] tst_base, input iter_num_en=0, input[15:0] exp_num_iter=0);
logic[31:0] read_data;
logic error;
begin

   error = 0;
   if (iter_num_en)
   begin
      TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h80), .rdata(read_data));
      if (read_data != exp_num_iter)
       begin
         $display($time,,,"***ERROR*** Write NumIter miscompare expected=0x%x, actual=0x%x", exp_num_iter, read_data);
         error =1 ;
      end
      
      TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h88), .rdata(read_data));
      if (read_data != exp_num_iter)
       begin
         $display($time,,,"***ERROR*** Read NumIter miscompare expected=0x%x, actual=0x%x", exp_num_iter, read_data);
         error =1 ;
      end
   end

   TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'hb0), .rdata(read_data));
   if (read_data !=0 )
   begin
      $display($time,,, "***ERROR*** Got miscompare");
      error = 1;
   end

   if (!error)
   begin
      $display("!!!!!!!!!!!!!!!!!!!!!!!");
      $display("!!!!  TEST PASSED  !!!!");
      $display("!!!!!!!!!!!!!!!!!!!!!!!");
   end
end
endtask

//-----------------------------------------------------------------------------
// This is incrementing size test.  Loop twice through all the sizes
//-----------------------------------------------------------------------------
task tmp_pci_inc(input[63:0] tgt_bar0, input[15:0] tst_base, input[15:0] max_length=0);
logic[31:0] read_data;
begin
   tmp_tst_setup(.tgt_bar0(tgt_bar0), .tst_base(tst_base), .cfg_cont(0), .cfg_iter_mode(1), .cfg_iter_num(2), .cfg_user_id(0), .cfg_num_inst(max_length));
   for (int i=0; i<=max_length; i++)
   begin
      tmp_cfg_inst (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .addr(64'habcd0000_00000000 + (i << 32)), .start_data(32'h12300000 + (i<<16)), .len(i), .write(1), .index(i)); 
      tmp_cfg_inst (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .addr(64'habcd0000_00000000 + (i << 32)), .start_data(32'h12300000 + (i<<16)), .len(i), .write(0), .index(i)); 
   end

   tmp_tst_go(.tgt_bar0(tgt_bar0), .tst_base(tst_base));

  
   read_data = 32'hffffffff;
   fork
   begin
      while (read_data!=0)
         TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h08), .rdata(read_data));
   end
   begin
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20000);
      $display("***ERROR*** TImeout waiting for in-progress bits to clear"); $finish;
   end
   join_any
   disable fork;

   tmp_chk (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .iter_num_en(1), .exp_num_iter(16));

   $finish;
end
endtask
         

//-------------------------------------------------------
// Sanity testing of misalinged
//-------------------------------------------------------
task tmp_pcie_misaligned(input[63:0] tgt_bar0, input[15:0] tst_base);
logic[31:0] read_data;
begin
   tmp_tst_setup(.tgt_bar0(tgt_bar0), .tst_base(tst_base), .cfg_cont(0), .cfg_iter_mode(0), .cfg_iter_num(0), .cfg_user_id(0), .cfg_num_inst(15));
   for (int i=0; i<16; i++)
   begin
      tmp_cfg_inst (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .addr(64'habcd0000_00000000 + (i << 2)), .start_data(32'h12300000 + (i<<32)), .len(3), .write(1), .index(i), .lst_adj(i)); 
      tmp_cfg_inst (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .addr(64'habcd0000_00000000 + (i << 2)), .start_data(32'h12300000 + (i<<32)), .len(3), .write(0), .index(i), .lst_adj(i)); 
   end

   tmp_tst_go(.tgt_bar0(tgt_bar0), .tst_base(tst_base));

  
   read_data = 32'hffffffff;
   fork
   begin
      while (read_data!=0)
         TSK_MEM_READ_64 (.addr(tgt_bar0 + tst_base + 8'h08), .rdata(read_data));
   end
   begin
      tb.RP.tx_usrapp.TSK_TX_CLK_EAT(20000);
      $display("***ERROR*** TImeout waiting for in-progress bits to clear"); $finish;
   end
   join_any
   disable fork;

   tmp_chk (.tgt_bar0(tgt_bar0), .tst_base(tst_base), .iter_num_en(1), .exp_num_iter(16));

   $finish;
end
endtask

//---------------------------------------
// Verify DRP functionality
//---------------------------------------
task pci_drp (input[63:0] dom0_bar);
logic[31:0] wdata;
logic[31:0] rdata;
begin
   //TSK_MEM_WRITE_64(.addr(dom0_bar + 'h00), .data(wdata));
   //TSK_MEM_READ_64 (.addr(dom0_bar + 'hf0), .rdata(rdata));

   //DRP Address (7:0-Select, 23:8-Address)
   TSK_MEM_WRITE_64(.addr(dom0_bar + 'h100), .data(32'h6400));
   TSK_MEM_READ_64(.addr(dom0_bar + 'h104), .rdata(rdata));
   $display($time,,"DRP Offset 100: 0x%x", rdata);

   TSK_MEM_WRITE_64(.addr(dom0_bar + 'h100), .data(32'h6500));
   TSK_MEM_READ_64(.addr(dom0_bar + 'h104), .rdata(rdata));
   $display($time,,"DRP Offset 101: 0x%x", rdata);

end
endtask
    
   
      
   
   
    

    
    
   
