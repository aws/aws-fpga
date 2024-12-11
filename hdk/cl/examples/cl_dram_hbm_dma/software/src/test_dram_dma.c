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
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif

#include "sh_dpi_tasks.h"

#include "cl_dram_dma.h"

XDMA_DESC *h2c_desc_list_head;



void test_main(uint32_t *exit_code) {

// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
  svScope scope;
#endif

  uint64_t cycle_count;
  uint64_t error_addr;

  uint8_t error_index;

  int timeout_count;

  int error_count;
  int fail;

  XDMA_DESC *h2c_desc;

  error_count = 0;
  fail = 0;

// Vivado does not support svGetScopeFromName
#ifndef VIVADO_SIM
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif

  {
    uint8_t *buf;

    buf = (uint8_t *)malloc(64);
    que_buffer_to_cl(0, buf, 64);

    buf = (uint8_t *)malloc(128);
    que_buffer_to_cl(0, buf, 128);

    start_move_to_cl(0);
  }

  sv_pause(50);

  // Report pass/fail status
  log_printf("Checking total error count...\n");
  if (error_count > 0) {
    fail = 1;
  }
  log_printf("Detected %3d errors during this test\n", error_count);

  if (fail != 0) {
    log_printf("*** TEST FAILED ***\n");
  } else {
    log_printf("*** TEST PASSED ***\n");
  }

  *exit_code = 0;
}
