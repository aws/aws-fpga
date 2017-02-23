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

void test_main(uint32_t *exit_code) {

  // NULL Test

  *exit_code = 0;
}
