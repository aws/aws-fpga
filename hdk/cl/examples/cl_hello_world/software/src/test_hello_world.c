#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "sh_dpi_tasks.h"

#define HELLO_WORLD_REG_ADDR UINT64_C(0x00)

void test_main(uint32_t *exit_code) {

  uint32_t rdata;

  log_printf("Writing 0xDEAD_BEEF to address 0x%x", HELLO_WORLD_REG_ADDR);
  cl_poke(HELLO_WORLD_REG_ADDR, 0xDEADBEEF);
  cl_peek(HELLO_WORLD_REG_ADDR, &rdata);

  log_printf("Reading 0x%x from address 0x%x", rdata, HELLO_WORLD_REG_ADDR);

  if (rdata == 0xEFBEADDE) {
    log_printf("Test PASSED");
  } else {
    log_printf("Test FAILED");
  }

  sv_pause(2);                                         // wait 2us

  *exit_code = 0;
}
