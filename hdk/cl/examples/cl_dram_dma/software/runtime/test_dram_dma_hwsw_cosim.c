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
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#include <utils/sh_dpi_tasks.h>

#ifdef SV_TEST
   #include "fpga_pci_sv.h"
#endif

#include "common_dma.h"

#ifndef SV_TEST
/* use the stdout logger */
const struct logger *logger = &logger_stdout;
#endif

//Main will be different for different simulators and also for C. The definition is in sdk/userspace/utils/include/sh_dpi_tasks.h file
#ifdef SV_TEST
//For cadence and questa simulators the main has to return some value
   #ifdef INT_MAIN
   int test_main(uint32_t *exit_code) {
   #else 
   void test_main(uint32_t *exit_code) {
   #endif 
#else 
    int main(int argc, char **argv) {
#endif
    //The statements within SCOPE ifdef below are needed for HW/SW co-simulation with VCS
#ifdef SCOPE
  svScope scope;
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif

    int rc;
    int slot_id = 0;

#ifndef SV_TEST
    switch (argc) {
    case 1:
        break;
    case 3:
        sscanf(argv[2], "%x", &slot_id);
        break;
    default:
        usage(argv[0]);
        return 1;
    }

    channel = 0;
    error_count = 0;

    /* setup logging to print to stdout */
    rc = log_init("test_dram_dma_hwsw_cosim");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    /* initialize the fpga_plat library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

#endif

    rc = dma_example_hwsw_cosim(slot_id);

    fail_on(rc, out, "DMA example failed");

out:

#ifndef SV_TEST
   return rc;
#else
   if (error_count > 0) {
      printf("TEST FAILED \n");
   }
   else {
      printf("TEST PASSED \n");
   }
   //For cadence and questa simulators the main has to return some value
   #ifdef INT_MAIN
   *exit_code = 0;
   return 0;
   #else 
   *exit_code = 0;
   #endif
#endif
}

/* 
 * Write 4 identical buffers to the 4 different DRAM channels of the AFI
 * using fsync() between the writes and read to insure order
 */

int dma_example_hwsw_cosim(int slot_id) {
    int fd, rc;

    read_buffer = NULL;
    write_buffer = NULL;
    fd = -1;

    write_buffer = (char *)malloc(buffer_size);
    read_buffer = (char *)malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = ENOMEM;
        goto out;
    }

#ifndef SV_TEST
    fd = open_dma_queue(slot_id);
#else
    init_ddr();
#endif

    rand_string(write_buffer, buffer_size);

    for (channel=0; channel < 4; channel++) {
      fpga_write_buffer_to_cl(slot_id, channel, fd, buffer_size, (0x10000000 + channel*MEM_16G));
    }

    /* fsync() will make sure the write made it to the target buffer 
     * before read is done
     */
#ifndef SV_TEST
    rc = fsync(fd);
    fail_on((rc = (rc < 0)? errno:0), out, "call to fsync failed.");
#endif

    for (channel=0; channel < 4; channel++) {
      fpga_read_cl_to_buffer(slot_id, channel, fd, buffer_size, (0x10000000 + channel*MEM_16G));
    }

out:

#ifndef SV_TEST
    if (write_buffer != NULL) {
        free(write_buffer);
    }
    if (read_buffer != NULL) {
        free(read_buffer);
    }
    if (fd >= 0) {
        close(fd);
    }
    /* if there is an error code, exit with status 1 */
    return (rc != 0 ? 1 : 0);
#else
    return 0;
#endif
}
