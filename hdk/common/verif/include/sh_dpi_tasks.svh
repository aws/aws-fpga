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

`ifndef SV_SH_DPI_TASKS
`define SV_SH_DPI_TASKS

import tb_type_defines_pkg::*;

   import "DPI-C" context task test_main(output int unsigned exit_code);
   import "DPI-C" context task int_handler(input int unsigned int_num);
   import "DPI-C" context function void  host_memory_putc(input longint unsigned addr, byte data);         // even though a int is used, only the lower 8b are used
   import "DPI-C" context function byte  host_memory_getc(input longint unsigned addr);

`ifdef DMA_TEST
   import "DPI-C" context task send_rdbuf_to_c(input string a);
`endif
      
   export "DPI-C" task sv_printf;
   export "DPI-C" task sv_map_host_memory;
   export "DPI-C" task cl_peek;
   export "DPI-C" task cl_poke;
   export "DPI-C" task sv_int_ack;
   export "DPI-C" task sv_pause;
   export "DPI-C" task sv_fpga_pci_peek;
   export "DPI-C" task sv_fpga_pci_poke;
`ifdef DMA_TEST
   export "DPI-C" task sv_fpga_start_buffer_to_cl;
   export "DPI-C" task sv_fpga_start_cl_to_buffer;
`endif
   export "DPI-C" task init_ddr;
   
   static int h2c_desc_index = 0;
   static int c2h_desc_index = 0;
   
   task sv_printf(input string msg);
      $display("%S", msg);
   endtask

   task sv_map_host_memory(input longint unsigned addr);
      tb.card.fpga.sh.map_host_memory(addr);
   endtask

   task cl_peek(input longint unsigned addr, output int unsigned data);
      tb.card.fpga.sh.peek(.addr(addr), .data(data), .intf(AxiPort::PORT_OCL));
   endtask
   
   task cl_poke(input longint unsigned addr, int unsigned data);
      tb.card.fpga.sh.poke(.addr(addr), .data(data), .intf(AxiPort::PORT_OCL));
   endtask

   task sv_int_ack(input int unsigned int_num);
      tb.card.fpga.sh.set_ack_bit(int_num);
   endtask
   
   task sv_pause(input int x);
      repeat (x) #1us;
   endtask

   task sv_fpga_pci_peek(input int handle, input longint unsigned offset, output int unsigned value);
      tb.card.fpga.sh.peek(.addr(offset), .data(value), .intf(AxiPort::PORT_OCL));
   endtask
   
   task sv_fpga_pci_poke(input int handle, input longint unsigned addr, int unsigned data);
      tb.card.fpga.sh.poke(.addr(addr), .data(data), .intf(AxiPort::PORT_OCL));
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

`define SLOT_MACRO_TASK(ARG) \
begin \
   case (slot_id) \
   0: tb.card.fpga.sh.ARG; \
`ifdef SLOT_1 \
   1: tb.`SLOT_1.fpga.sh.ARG; \
`endif \
`ifdef SLOT_2 \
   2: tb.`SLOT_2.fpga.sh.ARG; \
`endif \
`ifdef SLOT_3 \
   3: tb.`SLOT_3.fpga.sh.ARG; \
`endif \
`ifdef SLOT_4 \
   4: tb.`SLOT_4.fpga.sh.ARG; \
`endif \
`ifdef SLOT_5 \
   5: tb.`SLOT_5.fpga.sh.ARG; \
`endif \
`ifdef SLOT_6 \
   6: tb.`SLOT_6.fpga.sh.ARG; \
`endif \
`ifdef SLOT_7 \
   7: tb.`SLOT_7.fpga.sh.ARG; \
`endif \
   default: begin \
      $display("Error: Invalid Slot ID specified."); \
      $finish; \
   end \
   endcase \
end

`define SLOT_MACRO_FUNC(ARG) \
begin \
   case (slot_id) \
   0: return tb.card.fpga.sh.ARG; \
`ifdef SLOT_1 \
   1: return tb.`SLOT_1.fpga.sh.ARG; \
`endif \
`ifdef SLOT_2 \
   2: return tb.`SLOT_2.fpga.sh.ARG; \
`endif \
`ifdef SLOT_3 \
   3: return tb.`SLOT_3.fpga.sh.ARG; \
`endif \
`ifdef SLOT_4 \
   4: return tb.`SLOT_4.fpga.sh.ARG; \
`endif \
`ifdef SLOT_5 \
   5: return tb.`SLOT_5.fpga.sh.ARG; \
`endif \
`ifdef SLOT_6 \
   6: return tb.`SLOT_6.fpga.sh.ARG; \
`endif \
`ifdef SLOT_7 \
   7: return tb.`SLOT_7.fpga.sh.ARG; \
`endif \
   default: begin \
      $display("Error: Invalid Slot ID specified."); \
      $finish; \
   end \
   endcase \
end

   function void que_buffer_to_cl(input int slot_id = 0, int chan, logic [63:0] src_addr, logic [63:0] cl_addr, logic [27:0] len);
      `SLOT_MACRO_TASK(dma_buffer_to_cl(.chan(chan), .src_addr(src_addr), .cl_addr(cl_addr), .len(len)))
   endfunction

   function void que_cl_to_buffer(input int slot_id = 0, int chan, logic [63:0] dst_addr, logic [63:0] cl_addr, logic [27:0] len);
      `SLOT_MACRO_TASK(dma_cl_to_buffer(.chan(chan), .dst_addr(dst_addr), .cl_addr(cl_addr), .len(len)))
   endfunction

   function void start_que_to_cl(input int slot_id = 0, int chan);
      `SLOT_MACRO_TASK(start_dma_to_cl(chan))
   endfunction

   function void start_que_to_buffer(input int slot_id = 0, int chan);
      `SLOT_MACRO_TASK(start_dma_to_buffer(chan))
   endfunction

   //DPI task to initialize DDR
   task init_ddr();
      power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));

      nsec_delay(1000);
      poke_stat(.addr(8'h0c), .ddr_idx(0), .data(32'h0000_0000));
      poke_stat(.addr(8'h0c), .ddr_idx(1), .data(32'h0000_0000));
      poke_stat(.addr(8'h0c), .ddr_idx(2), .data(32'h0000_0000));

      //de-select the ATG hardware

      poke_ocl(.addr(64'h130), .data(0));
      poke_ocl(.addr(64'h230), .data(0));
      poke_ocl(.addr(64'h330), .data(0));
      poke_ocl(.addr(64'h430), .data(0));

      // allow memory to initialize
      nsec_delay(27000);
   endtask // initialize_sh_model

`ifdef DMA_TEST
   //DPI task to transfer HOST to CL data.
   task sv_fpga_start_buffer_to_cl(input int slot_id = 0, int chan, input int buf_size, input string wr_buffer, input longint unsigned cl_addr);
      int timeout_count, status, error_count;
      logic [63:0] host_memory_buffer_address;
      
      host_memory_buffer_address = 64'h0 + chan*64'h0_0000_3000;
      que_buffer_to_cl(.slot_id(0), .chan(chan), .src_addr(host_memory_buffer_address), .cl_addr(cl_addr), .len(buf_size));
      // Put test pattern in host memory
      for (int i = 0 ; i < buf_size ; i++) begin
         hm_put_byte(.addr(host_memory_buffer_address), .d(wr_buffer[i]));
         host_memory_buffer_address++;
      end
      start_que_to_cl(.slot_id(0), .chan(chan));
      timeout_count = 0;
      do begin
         status[chan] = tb.is_dma_to_cl_done(.chan(chan));
         #10ns;
         timeout_count++;
      end while ((status[chan] != 1) && (timeout_count < 4000)); // UNMATCHED !!
      
      if (timeout_count >= 4000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers to cl", $realtime);
         error_count++;
      end
   endtask // sv_fpga_start_buffer_to_cl
   
   //DPI task to transfer CL to HOST data.
   task sv_fpga_start_cl_to_buffer(input int slot_id = 0, input int chan, input int buf_size, input longint unsigned cl_addr);
      int timeout_count, status, error_count;
      logic [63:0] host_memory_buffer_address;
      byte         rd_buf_t;
      string       rd_buffer_t, rd_buffer;
      
      host_memory_buffer_address = 64'h0 + (chan+1)*64'h0_0001_3000;
      
      que_cl_to_buffer(.slot_id(0), .chan(chan), .dst_addr(host_memory_buffer_address), .cl_addr(cl_addr), .len(buf_size));
      start_que_to_buffer(.slot_id(0), .chan(chan));
      timeout_count = 0;
      do begin
         status[chan] = is_dma_to_buffer_done(.chan(chan));
         #10ns;
         timeout_count++;
      end while ((status[chan] != 1) && (timeout_count < 4000)); // UNMATCHED !!
      
      if (timeout_count >= 4000) begin
         $display("[%t] : *** ERROR *** Timeout waiting for dma transfers from cl", $realtime);
         error_count++;
      end
      //For Questa simulator the first 8 bytes are not transmitted correctly, so the buffer is transferred with 8 extra bytes and those bytes are removed here.
      for (int i = 0 ; i < 8; i++) begin
         rd_buffer = {rd_buffer, "A"};
      end
      for (int i = 0 ; i < buf_size ; i++) begin
         rd_buf_t = hm_get_byte(.addr(host_memory_buffer_address + i));
         //Change the ascii characters back to string.
         $sformat(rd_buffer_t, "%s", rd_buf_t);
         //Construct the rd_buffer.
         rd_buffer = {rd_buffer, rd_buffer_t};
      end
      //This function is needed to update buffer on C side.
      send_rdbuf_to_c(rd_buffer);
   endtask // sv_fpga_start_cl_to_buffer
`endif
   
   task power_up(input int slot_id = 0, 
                       ClockRecipe::A_RECIPE clk_recipe_a = ClockRecipe::A0,
                       ClockRecipe::B_RECIPE clk_recipe_b = ClockRecipe::B0,
                       ClockRecipe::C_RECIPE clk_recipe_c = ClockRecipe::C0);
   `SLOT_MACRO_TASK(power_up(.clk_recipe_a(clk_recipe_a),
                             .clk_recipe_b(clk_recipe_b),
                             .clk_recipe_c(clk_recipe_c)))
   endtask

   task power_down(input int slot_id = 0);
   `SLOT_MACRO_TASK(power_down())
   endtask

   //=================================================
   //
   // set_virtual_dip_switch
   //
   //   Description: writes virtual dip switches
   //   Outputs: None
   //
   //=================================================
   function void set_virtual_dip_switch(input int slot_id = 0, int dip);
      `SLOT_MACRO_TASK(set_virtual_dip_switch(dip))
   endfunction

   //=================================================
   //
   // get_virtual_dip_switch
   //
   //   Description: reads virtual dip switch status
   //   Outputs: dip_status
   //
   //=================================================
   function logic [15:0] get_virtual_dip_switch(input int slot_id = 0);
      `SLOT_MACRO_FUNC(get_virtual_dip_switch())
   endfunction

   //=================================================
   //
   // get_virtual_led
   //
   //   Description: reads virtual led status
   //   Outputs: led status
   //
   //=================================================
   function logic[15:0] get_virtual_led(input int slot_id = 0);
      `SLOT_MACRO_FUNC(get_virtual_led())
   endfunction

   //=================================================
   //
   // Kernel_reset
   //
   //   Description: sets kernel_reset
   //   Outputs: None
   //
   //=================================================
   function void kernel_reset(input int slot_id = 0, logic d = 1);
      `SLOT_MACRO_TASK(kernel_reset(d))
   endfunction

   //=================================================
   //
   // poke
   //
   //   Description: used to write a single beat of data at addr into one of the four CL AXI ports specified by intf.
   //        Intf
   //         0 = PCIS
   //         1 = SDA
   //         2 = OCL
   //         3 = BAR1
   //
   //        id - AXI bus ID
   //
   //        Size
   //         0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes (32 bits), 3 = 8 bytes (64 bits)
   //
   //   Outputs: None
   //
   //=================================================
   task poke(input int slot_id = 0,
             logic [63:0] addr, 
             logic [511:0] data, 
             logic [5:0] id = 6'h0, 
             DataSize::DATA_SIZE size = DataSize::UINT32, 
             AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS); 
       `SLOT_MACRO_TASK(poke(.addr(addr), .data(data), .id(id), .size(size), .intf(intf)))
   endtask

   //=================================================
   //
   // poke_pcis
   //
   //   Description: used to write a single beat of data at addr into CL PCIS port.
   //   Outputs: None
   //
   //=================================================
   task poke_pcis(input int slot_id = 0,
                  logic [63:0] addr,     
                  logic [511:0] data,     
                  logic [63:0] strb,     
             logic [5:0] id = 6'h0); 
       `SLOT_MACRO_TASK(poke_pcis(.addr(addr), .data(data), .id(id), .strb(strb)))
   endtask

   //===========================================================================
   //
   // poke_pcis_wc
   //
   //   Description: Write combine version of poke (will only work on PCIS Intf)
   //        id - AXI bus ID
   //        addr - Address for transfer
   //        data[$][31:0] - Queue of DWs
   //        size - AXI size
   //   Outputs: None
   //
   //==========================================================================
   task poke_pcis_wc(input int slot_id = 0,
                     input logic [63:0] addr, 
                     logic [31:0] data [$], 
                     logic [5:0]  id = 6'h0,
                     logic [2:0]  size = 3'd6
                     );
      `SLOT_MACRO_TASK(poke_pcis_wc(.addr(addr), .data(data), .id(id), .size(size)))
   endtask

   //=================================================
   //
   // peek
   //
   //   Description: used to read a single beat of data at addr from one of the four CL AXI ports specified by intf.
   //        Intf
   //         0 = PCIS
   //         1 = SDA
   //         2 = OCL
   //         3 = BAR1
   //
   //        id - AXI bus ID
   //
   //        Size
   //         0 = 1 byte, 1 = 2 bytes, 2 = 4 bytes (32 bits), 3 = 8 bytes (64 bits)
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek(input int slot_id = 0,
             logic [63:0] addr, 
             output logic [511:0] data, 
             input logic [5:0] id = 6'h0, 
             DataSize::DATA_SIZE size = DataSize::UINT32, 
             AxiPort::AXI_PORT intf = AxiPort::PORT_DMA_PCIS); 
       `SLOT_MACRO_TASK(peek(.addr(addr), .data(data), .id(id), .size(size), .intf(intf)))
   endtask

   //=================================================
   //
   // peek_pcis
   //
   //   Description: used to read a single beat of data at addr from the CL PCIS AXI port.
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek_pcis(input int slot_id = 0,
             logic [63:0] addr, 
             output logic [511:0] data, 
             input logic [5:0] id = 6'h0);
       `SLOT_MACRO_TASK(peek_pcis(.addr(addr), .data(data), .id(id)))
   endtask

   //=================================================
   //
   // set_ack_bit
   //
   //   Description: used to acknowledge an interrupt and clear pending bit
   //   Outputs: None
   //
   //=================================================
   function void set_ack_bit(input int slot_id = 0,
                             int int_num);
      `SLOT_MACRO_TASK(set_ack_bit(.int_num(int_num)))
   endfunction

   //=================================================
   //
   // issue_flr
   //
   //   Description: issue a FLR command
   //   Outputs: None
   //
   //=================================================
   task issue_flr(input int slot_id = 0);
       `SLOT_MACRO_TASK(issue_flr())
   endtask

   //=================================================
   //
   // nsec_delay
   //
   //   Description: sets a delay in nsec
   //   Outputs: None
   //
   //=================================================
   task nsec_delay(int dly = 10000);
      tb.card.fpga.sh.nsec_delay(dly);
   endtask

   //=================================================
   //
   // poke_ocl
   //
   //   Description: used to write a single 32b of data at addr into the OCL interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: None
   //
   //=================================================
   task poke_ocl(input int slot_id = 0,
             logic [63:0] addr, 
             logic [31:0] data, 
             logic [5:0] id = 6'h0); 
       `SLOT_MACRO_TASK(poke(.addr(addr), .data({32'h0, data}), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_OCL)))
   endtask

   //=================================================
   //
   // peek_ocl
   //
   //   Description: used to read a single 32b of data at addr from the OCL interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek_ocl(input int slot_id = 0,
             logic [63:0] addr, 
             output logic [63:0] data, 
             input logic [5:0] id = 6'h0); 
       logic [63:0] tmp;
       `SLOT_MACRO_TASK(peek(.addr(addr), .data(tmp), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_OCL)))
      data = {32'h0, tmp[31:0]};
   endtask

   //=================================================
   //
   // poke_sda
   //
   //   Description: used to write a single 32b of data at addr into the SDA interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: None
   //
   //=================================================
   task poke_sda(input int slot_id = 0,
             logic [63:0] addr, 
             logic [31:0] data, 
             logic [5:0] id = 6'h00);
       `SLOT_MACRO_TASK(poke(.addr(addr), .data({32'h0, data}), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA)))
   endtask

   //=================================================
   //
   // peek_sda
   //
   //   Description: used to read a single 32b of data at addr from the OCL interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek_sda(input int slot_id = 0,
             logic [63:0] addr, 
             output logic [63:0] data, 
             input logic [5:0] id = 6'h0); 
       logic [63:0] tmp;

       `SLOT_MACRO_TASK(peek(.addr(addr), .data(tmp), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_SDA)))
      data = {32'h0, tmp[31:0]};
   endtask

   //=================================================
   //
   // poke_bar1
   //
   //   Description: used to write a single 32b of data at addr into the BAR1 interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: None
   //
   //=================================================
   task poke_bar1(input int slot_id = 0,
             logic [63:0] addr, 
             logic [31:0] data, 
             logic [5:0] id = 6'h0);
       `SLOT_MACRO_TASK(poke(.addr(addr), .data({32'h0, data}), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)))
   endtask

   //=================================================
   //
   // peek_bar1
   //
   //   Description: used to read a single 32b of data at addr from the BAR1 interface.
   //
   //        id - AXI bus ID
   //
   //   Outputs: Read Data Value
   //
   //=================================================
   task peek_bar1(input int slot_id = 0,
             logic [63:0] addr, 
             output logic [63:0] data, 
             input logic [5:0] id = 6'h0); 
      logic [63:0] tmp;
      `SLOT_MACRO_TASK(peek(.addr(addr), .data(tmp), .id(id), .size(DataSize::UINT32), .intf(AxiPort::PORT_BAR1)))
      data = {32'h0, tmp[31:0]};
   endtask

   function bit is_dma_to_cl_done(input int slot_id = 0, input int chan);
      `SLOT_MACRO_FUNC(is_dma_to_cl_done(chan))   
   endfunction // is_dma_to_cl_done

   function bit is_dma_to_buffer_done(input int slot_id = 0, input int chan);
      `SLOT_MACRO_FUNC(is_dma_to_buffer_done(chan))
   endfunction // is_dma_to_buffer_done

   function bit is_ddr_ready(input int slot_id = 0);
      `SLOT_MACRO_TASK(is_ddr_ready())
   endfunction // is_dma_to_buffer_done
   
   task poke_stat(input int slot_id = 0,
                  input logic [7:0] addr, logic [1:0] ddr_idx, logic[31:0] data);
      `SLOT_MACRO_TASK(poke_stat(.addr(addr), .ddr_idx(ddr_idx), .data(data)))
   endtask // poke_stat
   //=================================================
   //
   //   set_chk_clk_freq
   //
   //   Description: starts clock frequency checks
   //   Outputs: None
   //
   //=================================================
   function void set_chk_clk_freq(input int slot_id = 0, logic chk_freq = 1'b1);
     `SLOT_MACRO_TASK(set_chk_clk_freq(chk_freq))
   endfunction // chk_clk_freq
   
   //=================================================
   //
   //   chk_prot_err_stat
   //
   //   Description: Check for protocol checker violations
   //   Outputs: None
   //
   //=================================================
   function logic chk_prot_err_stat(input int slot_id = 0);
     `SLOT_MACRO_FUNC(chk_prot_err_stat());
   endfunction // chk_prot_err_stat

   //=================================================
   //
   //   chk_clk_err_cnt
   //
   //   Description: Check for protocol checker violations
   //   Outputs: None
   //
   //=================================================
   function logic chk_clk_err_cnt(input int slot_id = 0);
     `SLOT_MACRO_FUNC(chk_clk_err_cnt());
   endfunction // chk_clk_err_cnt
   
   //=================================================
   //
   //   get_global_counter_0
   //
   //   Description: Get global counter 0 value.
   //   Outputs: 64 bit counter
   //
   //=================================================
   function logic [63:0] get_global_counter_0(input int slot_id = 0);
     `SLOT_MACRO_FUNC(get_global_counter_0());
   endfunction // get_global_counter_0

   //=================================================
   //
   //   get_global_counter_1
   //
   //   Description: Get global counter 1 value.
   //   Outputs: 64 bit counter
   //
   //=================================================
   function logic [63:0] get_global_counter_1(input int slot_id = 0);
     `SLOT_MACRO_FUNC(get_global_counter_1());
   endfunction // get_global_counter_1
   
`endif
