// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

module test_dram_dma();

    int            error_count;
    int            timeout_count;
    int            fail;
    logic [3:0]    status;
   
    initial begin

       logic [63:0] host_memory_buffer_address;
       
       logic [7:0] desc_buf [];
       logic [63:0] base_addr = 64'h0000_0000_0000_0000;

       tb.sh.power_up();
       tb.sh.delay(500);
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

       // de-select the ATG hardware
       tb.sh.poke(.addr(64'h130), .data(0), .intf(2));

       // allow memory to initialize
       tb.sh.delay(25000);

       $display("[%t] : Initializing buffers", $realtime);

       host_memory_buffer_address = 64'h0;

       //Queue data to be transfered to CL DDR
       tb.que_buffer_to_cl(.chan(0), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_0000_0000), .len(64) );  // move buffer to DDR 0

       // Put test pattern in host memory       
       for (int i = 0 ; i < 64 ; i++) begin
          tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hAA));
          host_memory_buffer_address++;
       end
       
       host_memory_buffer_address = 64'h0_0000_1000;
       tb.que_buffer_to_cl(.chan(1), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_1000_0000), .len(64) );  // move buffer to DDR 0

       for (int i = 0 ; i < 64 ; i++) begin
          tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hBB));
          host_memory_buffer_address++;
       end

       host_memory_buffer_address = 64'h0_0000_2000;
       tb.que_buffer_to_cl(.chan(2), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_2000_0000), .len(64) );  // move buffer to DDR 0

       for (int i = 0 ; i < 64 ; i++) begin
          tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hCC));
          host_memory_buffer_address++;
       end

       host_memory_buffer_address = 64'h0_0000_3000;
       tb.que_buffer_to_cl(.chan(3), .src_addr(host_memory_buffer_address), .cl_addr(64'h0000_3000_0000), .len(64) );  // move buffer to DDR 0

       for (int i = 0 ; i < 64 ; i++) begin
          tb.hm_put_byte(.addr(host_memory_buffer_address), .d(8'hDD));
          host_memory_buffer_address++;
       end

       $display("[%t] : starting H2C DMA channels ", $realtime);
       
       //Start transfers of data to CL DDR
       tb.start_que_to_cl(.chan(0));   
       tb.start_que_to_cl(.chan(1));   
       tb.start_que_to_cl(.chan(2));   
       tb.start_que_to_cl(.chan(3));   

       // wait for dma transfers to complete
       timeout_count = 0;       
       do begin
          status[0] = tb.sh.is_dma_to_cl_done(0);
          status[1] = tb.sh.is_dma_to_cl_done(1);
          status[2] = tb.sh.is_dma_to_cl_done(2);
          status[3] = tb.sh.is_dma_to_cl_done(3);
          #10ns;
          timeout_count++;
       end while ((status != 4'hf) && (timeout_count < 50));
       
       if (timeout_count >= 50) begin
          $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
          error_count++;
       end

       $display("[%t] : starting C2H DMA channels ", $realtime);

       //Start transfers of data from CL DDR
       tb.start_que_to_buffer(.chan(0));   
       tb.start_que_to_buffer(.chan(1));   
       tb.start_que_to_buffer(.chan(2));   
       tb.start_que_to_buffer(.chan(3));   

       // wait for dma transfers to complete
       timeout_count = 0;       
       do begin
          status[0] = tb.sh.is_dma_to_buffer_done(0);
          status[1] = tb.sh.is_dma_to_buffer_done(1);
          status[2] = tb.sh.is_dma_to_buffer_done(2);
          status[3] = tb.sh.is_dma_to_buffer_done(3);
          #10ns;
          timeout_count++;          
       end while ((status != 4'hf) && (timeout_count < 50));
       
       if (timeout_count >= 50) begin
          $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
          error_count++;
       end


       // DDR 0
       $display("[%t] : DMA buffer from DDR 0", $realtime);

       host_memory_buffer_address = 64'h0_0000_0800;
       for (int i = 0 ; i<64 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hAA) begin
           $display("[%t] : *** ERROR *** DDR0 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 1
       $display("[%t] : DMA buffer from DDR 1", $realtime);
   
       host_memory_buffer_address = 64'h0_0000_1800;
       for (int i = 0 ; i< 64 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hBB) begin
           $display("[%t] : *** ERROR *** DDR1 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 2
       $display("[%t] : DMA buffer from DDR 2", $realtime);
   
       host_memory_buffer_address = 64'h0_0000_2800;
       for (int i = 0 ; i< 64 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hCC) begin
           $display("[%t] : *** ERROR *** DDR2 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 3
       $display("[%t] : DMA buffer from DDR 3", $realtime);

       host_memory_buffer_address = 64'h0_0000_3800;
       for (int i = 0 ; i< 64 ; i++) begin
         if (tb.hm_get_byte(.addr(host_memory_buffer_address)) !== 8'hDD) begin
           $display("[%t] : *** ERROR *** DDR3 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end

       
       // Power down
       #500ns;
       tb.sh.power_down();

       //---------------------------
       // Report pass/fail status
       //---------------------------
       $display("[%t] : Checking total error count...", $realtime);
       if (error_count > 0) begin
         fail = 1;
       end
       $display("[%t] : Detected %3d errors during this test", $realtime, error_count);

       if (fail) begin
         $display("[%t] : *** TEST FAILED ***", $realtime);
       end else begin
         $display("[%t] : *** TEST PASSED ***", $realtime);
       end

       $finish;
    end // initial begin

endmodule // test_dram_dma
   
