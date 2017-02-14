// Amazon FGPA Hardware Development Kit
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

`ifndef SV_SH_DPI_TASKS
`define SV_SH_DPI_TASKS

   import "DPI-C" context task test_main(output int unsigned exit_code);
   import "DPI-C" context function void  host_memory_putc(input longint unsigned addr, byte data);         // even though a int is used, only the lower 8b are used
   import "DPI-C" context function byte  host_memory_getc(input longint unsigned addr);

   export "DPI-C" task sv_printf;
   export "DPI-C" task sv_map_host_memory;
   export "DPI-C" task cl_peek;
   export "DPI-C" task cl_poke;
   export "DPI-C" task sv_pause;

   static int h2c_desc_index = 0;
   static int c2h_desc_index = 0;
   
   task sv_printf(input string msg);
      $display("%S", msg);
   endtask

   task sv_map_host_memory(input longint unsigned addr);
      tb.sh.map_host_memory(addr);
   endtask

   task cl_peek(input longint unsigned addr, output int unsigned data);
      tb.sh.peek(addr, data);
   endtask
   
   task cl_poke(input longint unsigned addr, int unsigned data);
      tb.sh.poke(addr, data);
   endtask

   task sv_pause(input int x);
      repeat (x) #1us;
   endtask

   function void hm_put_byte(input longint unsigned addr, byte d);
      if (tb.use_c_host_memory)
         host_memory_putc(addr, d);
      else begin
         int unsigned t;
         
         if (tb.sv_host_memory.exists({addr[63:2], 2'b00})) begin
            t = tb.sv_host_memory[{addr[63:2], 2'b00}];
         end
         else
            t = 32'hffff_ffff;
         
         t = t & ~(32'h0000_00ff  << (addr[1:0] * 8) );
         t = t | ({24'h000000, d} << (addr[1:0] * 8) );
         tb.sv_host_memory[{addr[63:2], 2'b00}] = t;
      end
   endfunction

   function byte hm_get_byte(input longint unsigned addr);
      byte d;

      if (tb.use_c_host_memory)
         d = host_memory_getc(addr);
      else begin
         int unsigned t;
         if (tb.sv_host_memory.exists({addr[63:2], 2'b00})) begin
            t = tb.sv_host_memory[{addr[63:2], 2'b00}];
            t = t >> (addr[1:0] * 8);
            d = t[7:0];
         end
         else
            d = 'hff;
      end
      return d;
   endfunction

   function void que_buffer_to_cl(input int chan, logic [7:0] data[], logic [63:0] cl_addr);
      tb.sh.dma_buffer_to_cl(chan, data, cl_addr);
   endfunction

   function automatic void que_cl_to_buffer(input int chan, ref logic [7:0] data[], input logic [63:0] cl_addr);
      tb.sh.dma_cl_to_buffer(chan, data, cl_addr);
   endfunction

   function void start_que_to_cl(input int chan);
      tb.sh.start_dma_to_cl(chan);
   endfunction

   function void start_que_to_buffer(input int chan);
      tb.sh.start_dma_to_buffer(chan);
   endfunction

   function automatic void data_cl_to_buffer(input int chan, ref logic [7:0] data[]);
      tb.sh.dma_cl_data_to_buffer(chan, data);
   endfunction

`endif
