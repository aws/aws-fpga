`ifndef SH_DPI_TASKS
`define SH_DPI_TASKS

   import "DPI-C" context task test_main(output int unsigned exit_code);
   import "DPI-C" context function void  host_memory_putc(input longint unsigned addr, byte data);         // even though a int is used, only the lower 8b are used
   import "DPI-C" context function byte  host_memory_getc(input longint unsigned addr);

   export "DPI-C" task sv_printf;
   export "DPI-C" task sv_map_host_memory;
   export "DPI-C" task cl_peek;
   export "DPI-C" task cl_poke;
   export "DPI-C" task sv_pause;

   task sv_printf(input string msg);
      $display("%S", msg);
   endtask // sv_printf

   task sv_map_host_memory(input longint unsigned addr);
      tb.sh.map_host_memory(addr);
   endtask // sv_printf

   task cl_peek(input longint unsigned addr, output int unsigned data);
      tb.sh.peek(addr, data);
   endtask // centaur_peek
   
   task cl_poke(input longint unsigned addr, int unsigned data);
      tb.sh.poke(addr, data);
   endtask // centaur_peek

   task sv_pause(input int x);
      repeat (x) #1us;
   endtask

   function void hm_put_byte(input longint unsigned addr, byte d);
      if (tb.use_c_host_memory)
         host_memory_putc(addr, d);
      else begin
         int unsigned t;
         t = tb.sv_host_memory[{addr[63:2], 2'b00}];
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
         t = tb.sv_host_memory[{addr[63:2], 2'b00}];
         t = t >> (addr[1:0] * 8);
         d = t[7:0];
      end
      return d;
   endfunction

`endif
