#include <stdio.h>
#include "sh_dpi_task.h"

int test_main(int *i) {
  long long addr;

  addr = 0x0l;

  cl_peek(addr, i);

  log_printf("%lx %x", addr , *i);

  cl_poke(0x28l, 0x55);
  cl_poke(0x8l, 0x3);

}
