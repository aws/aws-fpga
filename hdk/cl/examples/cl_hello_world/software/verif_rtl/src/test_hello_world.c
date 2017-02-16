#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif
#endif

#include "sh_dpi_tasks.h"

#define HELLO_WORLD_REG_ADDR UINT64_C(0x00)

void test_main(uint32_t *exit_code) {

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
  svScope scope;
#endif
#endif

  uint32_t rdata;

// Vivado does not support svGetScopeFromName
#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif
#endif

  log_printf("Writing 0xDEAD_BEEF to address 0x%x", HELLO_WORLD_REG_ADDR);
  cl_poke(HELLO_WORLD_REG_ADDR, 0xDEADBEEF);
  cl_peek(HELLO_WORLD_REG_ADDR, &rdata);

  log_printf("Reading 0x%x from address 0x%x", rdata, HELLO_WORLD_REG_ADDR);

  if (rdata == 0xEFBEADDE) {
    log_printf("Test PASSED");
  } else {
    log_printf("Test FAILED");
  }

  *exit_code = 0;
}
