// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// =============================================================================

module test_dram_dma();

    int            error_count;
    int            fail;
   
    initial begin

       logic [7:0] desc_buf [];
       logic [63:0] base_addr = 64'h0000_0000_0000_0000;

       tb.sh.power_up();
       tb.sh.delay(500);
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
       tb.sh.poke_stat(.stat_addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

       //tb.sh.poke(.addr(base_addr + 64'h000), .data(32'h00000000));
       //Forcing cfg_atg_enable for now, once we have AXI_L interface we will
       //do a config write
       
//       tb.CL.gen_ddr_tst[0].genblk1.CL_TST_DDR.CL_TST.cfg_atg_enable = 0;
       tb.sh.poke(.addr(64'h130), .data(0), .intf(2));

       tb.sh.delay(25000);

       // DDR 0
       $display("[%t] : DMA buffer to DDR 0", $realtime);

       desc_buf = new[64];
       
       for (int i = 0 ; i<= 63 ; i++) begin
         desc_buf[i] = 'hAA;
       end

       que_to_cl_ddr(0, 64'h0, desc_buf);

       // DDR 1
       $display("[%t] : DMA buffer to DDR 1", $realtime);

       for (int i = 0 ; i<= 63 ; i++) begin
         desc_buf[i] = 'hBB;
       end
   
       que_to_cl_ddr(1, 64'h100, desc_buf);

       // DDR 2
       $display("[%t] : DMA buffer to DDR 2", $realtime);

       for (int i = 0 ; i<= 63 ; i++) begin
         desc_buf[i] = 'hCC;
       end
   
       que_to_cl_ddr(2, 64'h200, desc_buf);

       // DDR 3
       $display("[%t] : DMA buffer to DDR 3", $realtime);

       for (int i = 0 ; i<= 63 ; i++) begin
         desc_buf[i] = 'hDD;
       end
   
       que_to_cl_ddr(3, 64'h300, desc_buf);
       
       // DDR 0
       $display("[%t] : DMA buffer from DDR 0", $realtime);

       dma_from_cl_ddr(0, 64'h0, desc_buf);
       for (int i = 0 ; i<= 63 ; i++) begin
         if (desc_buf[i] !== 'hAA) begin
           $display("[%t] : *** ERROR *** DDR0 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 1
       $display("[%t] : DMA buffer from DDR 1", $realtime);
   
       dma_from_cl_ddr(1, 64'h100, desc_buf);
       for (int i = 0 ; i<= 63 ; i++) begin
         if (desc_buf[i] !== 'hBB) begin
           $display("[%t] : *** ERROR *** DDR1 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 2
       $display("[%t] : DMA buffer from DDR 2", $realtime);
   
       dma_from_cl_ddr(2, 64'h200, desc_buf);
       for (int i = 0 ; i<= 63 ; i++) begin
         if (desc_buf[i] !== 'hCC) begin
           $display("[%t] : *** ERROR *** DDR2 Data mismatch, read data is: %0x", $realtime, desc_buf[i]);
           error_count++;
         end    
       end
       
       // DDR 3
       $display("[%t] : DMA buffer from DDR 3", $realtime);

       dma_from_cl_ddr(3, 64'h300, desc_buf);
       for (int i = 0 ; i<= 63 ; i++) begin
         if (desc_buf[i] !== 'hDD) begin
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

   task automatic que_to_cl_ddr(input int chan, input logic [63:0] base_addr, input logic [7:0] data []);
      
      logic status;
      int   timeout_count;

      //Queue data to be transfered to CL DDR
      tb.que_buffer_to_cl(chan, data, base_addr);

      //Start transfer of data to CL DDR
      tb.start_que_to_cl(chan);

      timeout_count = 0;
      status = 0;
      
      #10ns;
      
      do begin
         status = tb.sh.is_dma_to_cl_done(chan);
         timeout_count++;
         #1ns;
      end while ((!status) && (timeout_count < 100)); 

      if ((timeout_count == 100) && (status !== 1'b1)) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfer to cl", $realtime);
         error_count++;
      end
   endtask

   task automatic dma_from_cl_ddr(input int chan, input logic [63:0] base_addr, ref logic [7:0] data []);
      
      logic status;
      int   timeout_count;

      //Queue data to be transfered from CL DDR
      tb.que_cl_to_buffer(chan, data, base_addr);

      //Start transfer of data from CL DDR
      tb.start_que_to_buffer(chan);

      timeout_count = 0;
      status = 0;
      #10ns;
      do begin
         status = tb.sh.is_dma_to_buffer_done(chan);
         timeout_count++;
         #1ns;
      end while ((!status) && (timeout_count < 500)); 

      if ((timeout_count >= 200) && (status !== 1'b1)) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfer from cl", $realtime);
         error_count++;
      end
      else 
        tb.data_cl_to_buffer(chan, data);
   endtask

endmodule // test_dram_dma
   
