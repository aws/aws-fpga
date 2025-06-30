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
 * This example demonstrates how an application can configure the SDE for host to card DMA and write data from a user
 * allocated buffer to the SDE.
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
 *    `make sde_h2c_simple`
 * 2. Run the example:
 *    `sudo ./sde_h2c_simple <num_packets> <packet_size> <slot_id>`
 * 3. Example output:
 *    `sudo ./sde_h2c_simple 1 1024 0`
 *    Start Time = 0, Current Time = 0
 *    Total Run time: 0 secs
 *    Total Number of Packets: 1
 *    h2c_mpps: 0 MPPS
 *    h2c BW: 0 GB/s
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

#define H2C_DESC_COALESCE_CNT 32

int main(int argc, char **argv) {

  struct sde_parameters params;
  double start_time, end_time;
  int ret = 0;

  ret = sde_parse_args(argc, argv, &params, "sde_h2c_simple");
  fail_on(ret, err, "Unable to parse arguments");

  fail_on_with_code(params.slot_id >= FPGA_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid slot_id %d", params.slot_id);

  ret = sde_mgmt_init_and_cfg(params.slot_id, SDE_EXAMPLE_DIR_H2C, params.pkt_size);
  fail_on(ret, err, "Unable to initialize SDE");

  size_t num_descriptors = params.pkt_cnt < H2C_DESC_COALESCE_CNT ? params.pkt_cnt : H2C_DESC_COALESCE_CNT;
  size_t num_packets = 0;

  // Allocate one large buffer to store all of the data to be DMA-ed to the SDE (max 32 packets of data).
  uint8_t* data_ptr = malloc(params.pkt_size * num_descriptors);
  fail_on_with_code(!data_ptr, cleanup, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Unable to allocate memory");

  // Fill the user buffer with patterned data.
  ret = sde_fill_pkt_data(data_ptr, params.pkt_size * num_descriptors, START_DOUBLE_WORD);
  fail_on(ret, cleanup, "Unable to fill data");

  // Starting the timer after the SDE is already configured although it is not yet running.
  start_time = sde_get_curr_time();

  while (num_packets < (params.pkt_cnt)) {
    ret = sde_mgmt_check_status(params.slot_id, SDE_SUBSYSTEM_H2C);
    fail_on(ret, cleanup, "Error checking status");

    // Write the data from the user buffer to the DMA buffers.
    ret = sde_mgmt_prepare_write(params.slot_id, data_ptr, params.pkt_size * num_descriptors);
    fail_on(ret, cleanup, "Error starting write");

    // Start the host to card DMA (write) by posting the descriptors for the buffers. This function
    // will wait until there is availability for the descriptors before posting them.
    ret = sde_mgmt_write(params.slot_id, num_descriptors * params.pkt_size);
    fail_on(ret, cleanup, "Error writing data");

    num_packets+=num_descriptors;
  }

  end_time = sde_get_curr_time();
  print_timing(start_time, end_time, params.pkt_size, num_packets, SDE_EXAMPLE_DIR_H2C);

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
