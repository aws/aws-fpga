`ifndef SH_DPI_TASKS
`define SH_DPI_TASKS

   import "DPI-C" context task test_main(output int unsigned exit_code);
   import "DPI-C" context task host_memory_putc(input longint unsigned addr, byte data);         // even though a int is used, only the lower 8b are used
   import "DPI-C" context task host_memory_getc(input longint unsigned addr, output byte data);

   export "DPI-C" task sv_printf;
   export "DPI-C" task sv_map_host_memory;
   export "DPI-C" task cl_peek;
   export "DPI-C" task cl_poke;
   export "DPI-C" task pause;

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

   task pause(input int x);
      repeat (x) #1us;
   endtask

`endif
