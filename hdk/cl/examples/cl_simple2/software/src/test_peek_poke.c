#include <stdio.h>
#include "sh_dpi_tasks.h"

int test_main(int *i) {
  long long addr;
  unsigned char *buffer;
  int j;

  buffer = (char *)malloc(1024);

  sv_map_host_memory(buffer);

  log_printf("test_main: %02x", buffer[0]);

  addr = 0x0l;

  cl_peek(addr, i);

  log_printf("test_main: %lx %x", addr , *i);

  cl_poke(0x1cL, 0);                                   // write index
  cl_poke(0x20L,  (long)buffer & 0xffffffff);          // write address low
  cl_poke(0x24L, ((long)buffer >> 32) & 0xffffffff);   // write address high
  cl_poke(0x28L, 0);                                   // write data
  cl_poke(0x2cL, 2);                                   // write 32b

  cl_poke(0x3cL, 0);
  cl_poke(0x40L,  (long)buffer & 0xffffffff);
  cl_poke(0x44L, ((long)buffer >> 32) & 0xffffffff);
  cl_poke(0x48L, 0);
  cl_poke(0x4cL, 2);

  cl_poke(0x8L, 0x3);                                  // start read & write

  pause(5);                                            // wait 5us

  // for fun print out the incrementing pattern
  // written by the CL
  for (j=0; j<64; j++)
    printf("buffer[%d] = %0x\n", j, buffer[j]);

}
