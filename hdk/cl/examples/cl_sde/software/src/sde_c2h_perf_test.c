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
 * This example demonstrates the maximum performance of the card to host SDE.
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
 *    `make sde_c2h_perf_test`
 * 2. Run the example:
 *    `sudo ./sde_c2h_perf_test <num_millions_packets> <packet_size> <slot_id>`
 * 3. Example output:
 *    `sudo ./sde_c2h_perf_test 5 1024 0`
 *    Start Time = 0, Current Time = 0
 *    Total Run time: 0 secs
 *    Total Number of Packets: 5000000
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

#define C2H_DESC_COALESCE_CNT 32

int main(int argc, char **argv) {

  struct sde_parameters params;
  double start_time, end_time;
  int ret = 0;

  ret = sde_parse_args(argc, argv, &params, "sde_c2h_perf_test");
  fail_on(ret, err, "Unable to parse arguments");

  fail_on_with_code(params.slot_id >= FPGA_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid slot_id %d", params.slot_id);

  ret = sde_mgmt_init_and_cfg(params.slot_id, SDE_EXAMPLE_DIR_C2H, params.pkt_size);
  fail_on(ret, err, "Unable to initialize SDE");

  size_t num_descriptors = 64;
  // Wait for the ability to post 64 buffer descriptors to the SDE.
  ret = sde_mgmt_wait_desc_credit(params.slot_id, SDE_SUBSYSTEM_C2H, num_descriptors);
  fail_on(ret, cleanup, "Error waiting for descriptor credit");

  // Post the maximum number of descriptors (64). This will provide the SDE
  // with the buffers to be DMA-ed from the SDE automatic test generator to
  // host memory. It will also simultaneously start the DMA from card to host.
  ret = sde_mgmt_post_desc(params.slot_id, SDE_SUBSYSTEM_C2H, &num_descriptors);
  fail_on(ret, cleanup, "Error posting descriptors");

  size_t num_packets = 0;
  // Starting the timer after the SDE is already configured and running through
  // the first 64 descriptors. None of these count toward the total packets
  // requested by mpkt_cnt.
  start_time = sde_get_curr_time();

  while (num_packets < (params.pkt_cnt * 1000000)) {
    ret = sde_mgmt_check_status(params.slot_id, SDE_SUBSYSTEM_C2H);
    fail_on(ret, cleanup, "Error checking status");

    num_descriptors = C2H_DESC_COALESCE_CNT;
    // Wait for the ability to post 32 buffer descriptors to the SDE. The SDE is updating
    // the status counters as descriptors are serviced by the SDE.
    ret = sde_mgmt_wait_desc_credit(params.slot_id, SDE_SUBSYSTEM_C2H, num_descriptors);
    fail_on(ret, cleanup, "Error waiting for descriptor credit");

    // Post the 32 buffer descriptors to the SDE.
    ret = sde_mgmt_post_desc(params.slot_id, SDE_SUBSYSTEM_C2H, &num_descriptors);
    fail_on(ret, cleanup, "Error posting descriptors");

    num_packets+=num_descriptors;
  }

  end_time = sde_get_curr_time();
  print_timing(start_time, end_time, params.pkt_size, num_packets, SDE_EXAMPLE_DIR_C2H);

cleanup:
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
