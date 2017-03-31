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
