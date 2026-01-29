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
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>

// Vivado does not support svGetScopeFromName
//#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
#include "svdpi.h"
#endif
//#endif

#include "sh_dpi_tasks.h"

void test_main(uint32_t *exit_code) {

// Vivado does not support svGetScopeFromName
//#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
    svScope scope;
#endif
//#endif

    uint32_t rdata;

// Vivado does not support svGetScopeFromName
//#ifdef INCLUDE_DPI_CALLS
#ifndef VIVADO_SIM
    scope = svGetScopeFromName("tb");
    svSetScope(scope);
#endif
//#endif

    printf("TESTING WRITE!\n");
    uint32_t addr = 0;
    uint64_t val = 0xDEADBEEF;
    cl_poke(addr, val);
    val = 0;
    printf("TESTING READ!\n");
    cl_peek(addr, &val);
    printf("READ BACK 0x%lx\n", val);

    *exit_code = 0;
}
