// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//This file has DMA transfer task commonly used in all the DRAM backdoor loading tests.

   int error_count;
   int timeout_count;
   int fail;
   logic [3:0] status;
   logic [7:0] data;
   logic [511:0] rd_data_t;


   task dma_c2h_transfers(logic [63:0] addr, int num_xfers, int len0, logic [511:0] rd_data);

      logic [63:0] bdr_addr, host_memory_buffer_address;
      //Front Door read data
      for ( int i=0; i<num_xfers; i++) begin
         bdr_addr = addr << i;
         // tb.peek(.addr(bdr_addr), .data(read_data), .size(DataSize::UINT512));
         // if (read_data != 64'h1122334455667788) begin
         //    $display("Read Data mismatch for Addr %h: Exp %h, Act %h", bdr_addr, 64'h1122334455667788, read_data);
         //    error_count++;
         // end
         //read the data from cl and put it in the host memory
         host_memory_buffer_address = 64'h0_0001_0000;
         tb.que_cl_to_buffer(.chan(0), .dst_addr(host_memory_buffer_address), .cl_addr(bdr_addr), .len(len0) ); // move DDR0 to buffer

         //Start transfers of data from CL DDR
         tb.start_que_to_buffer(.chan(0));

         // wait for dma transfers to complete
         timeout_count = 0;
         do begin
            status[0] = tb.is_dma_to_buffer_done(.chan(0));
            #10ns;
            timeout_count++;
         end while ((status != 4'hf) && (timeout_count < 1000));

         if (timeout_count >= 1000) begin
            $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
            error_count++;
         end

         #500ns;

         // DDR 0
         // Compare the data in host memory with the expected data
         $display("[%t] : DMA buffer from DDR for Addr %h", $realtime, bdr_addr);

         host_memory_buffer_address = 64'h0_0001_0000;
         rd_data_t = rd_data;
         for (int i = 0 ; i<len0 ; i++) begin
            data = rd_data_t[7:0];
            if (tb.hm_get_byte(.addr(host_memory_buffer_address + i)) !== data) begin
               $display("[%t] : *** ERROR *** DDR Data mismatch, addr:%0x Actual read data is: %0x Expected is: %0x",
                        $realtime, (host_memory_buffer_address + i), tb.hm_get_byte(.addr(host_memory_buffer_address + i)), data);
               error_count++;
            end
            rd_data_t = rd_data >> 8;
         end
      end // for ( int i=0; i<6; i++)
   endtask// dma_c2h_transfers