/*
 * Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may
 * not use this file except in compliance with the License. A copy of the
 * License is located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/*
 * This example demonstrates how an application can configure the Streaming Data Engine (SDE)
 * for card-to-host (C2H) DMA and read data into a user-allocated buffer.
 * 0. Prerequisites: This example must be run on an F2 instance with an FPGA at the FPGA image slot matching the command-
 *    line option. Source the sdk by navigating to the root of this repo and running `source ./sdk_setup.sh`. The CL_SDE
 *    must be loaded on the FPGA that matches the slot_id passed in on the commandline to this program. The APP_PF of the
 *    FPGA card must have bus mastering enabled. This can checked by running `lspci -d 1d0f:f002 -vv` assuming that the
 *    CL_SDE is loaded on the FPGA. The `BusMaster+` on the line starting with `Control:` indicates that bus mastering is
 *    enabled, whereas `BusMaster-` indicates that bus mastering is disabled. To enable bus mastering run
 *    `sudo setpci -s <Device:Bus:Device.Function> 4.w=6`. Note that Device:Bus:Device.Function is the DBDF for your FPGA.
 *    If using pkt_size greater than 4096, hugepages will need to be allocated and free for this example to use. To
 *    allocate a hugepage, run `sudo sysctl -w vm.nr_hugepages=<number_of_pages>`.
 * 1. Compile the example:
 *    `make sde_c2h_simple`
 * 2. Run the example:
 *    Note: The sde_c2h_simple example should only be run after a fresh load of the CL_SDE. Otherwise, you will see
 *    an `Error: (4100) metadata-valid-timeout` when running this example with a larger pkt_size than what was previously
 *    run with this example.
 *    `sudo ./sde_c2h_simple <num_packets> <packet_size> <slot_id>`
 * 3. Example output:
 *    `sudo ./sde_c2h_simple 1 1024 0`
 *    Start Time = 0, Current Time = 0
 *    Total Run time: 0 secs
 *    Total Number of Packets: 1
 *    c2h_mpps: 0 MPPS
 *    c2h BW: 0 GB/s
 */

#include <stdio.h>
#include <sys/time.h>
#include <fcntl.h>

#include <hal/fpga_common.h>
#include <fpga_pci.h>

#include <sde_mgmt.h>
#include <sde_utility.h>
#include <utils/log.h>
#include <string.h>
#include <stdlib.h>

#define C2H_DESC_COALESCE_CNT 32

int main(int argc, char **argv) {

  struct sde_parameters params;
  double start_time, end_time;
  int ret = 0;

  ret = sde_parse_args(argc, argv, &params, "sde_c2h_simple");
  fail_on(ret, err, "Unable to parse arguments");

  fail_on_with_code(params.slot_id >= FPGA_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid slot_id %d", params.slot_id);

  ret = sde_mgmt_init_and_cfg(params.slot_id, SDE_EXAMPLE_DIR_C2H, params.pkt_size);
  fail_on(ret, err, "Unable to initialize SDE");

  size_t num_descriptors = params.pkt_cnt < C2H_DESC_COALESCE_CNT ? params.pkt_cnt : C2H_DESC_COALESCE_CNT;
  size_t num_packets = 0;

  // Allocate one large buffer to store all of the data requested by the user (max 32 packets of data).
  uint8_t* data_ptr = malloc(params.pkt_size * num_descriptors);
  fail_on_with_code(!data_ptr, cleanup, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Unable to allocate memory");
  // Zero out the user read buffer.
  memset(data_ptr, 0, params.pkt_size * num_descriptors);

  // Starting the timer after the SDE is already configured although it is not yet running.
  start_time = sde_get_curr_time();

  while (num_packets < (params.pkt_cnt)) {
    ret = sde_mgmt_check_status(params.slot_id, SDE_SUBSYSTEM_C2H);
    fail_on(ret, cleanup, "Error checking status");

    // Start the card to host DMA (read) by posting the descriptors for the buffers.
    ret = sde_mgmt_start_read(params.slot_id, params.pkt_size * num_descriptors);
    fail_on(ret, cleanup, "Error starting read");

    // Read the data from the DMA buffers. This function will ensure that the descriptor
    // for the buffer is complete before copying the DMA-ed data into the user's buffer.
    ret = sde_mgmt_read_data(params.slot_id, data_ptr, num_descriptors * params.pkt_size);
    fail_on(ret, cleanup, "Error reading data");

    num_packets+=num_descriptors;
  }

  end_time = sde_get_curr_time();
  print_timing(start_time, end_time, params.pkt_size, num_packets, SDE_EXAMPLE_DIR_C2H);

cleanup:
  free(data_ptr);
  ret |= sde_mgmt_close(params.slot_id);

err:
  if (ret) {
    printf("Error: (%d) %s\n", ret, sde_mgmt_strerror(ret));
    const char *long_help = sde_mgmt_strerror_long(ret);
    if (long_help) {
      printf("%s\n", long_help);
    }
  }

  return ret;
}
