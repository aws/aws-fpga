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
 * This example demonstrates how to configure the SDE for card to host DMA using user-managed DMA buffers instead of
 * library-allocated buffers. It shows how to allocate a hugepage, partition it into multiple buffers, and use them for DMA operations.
 *
 * 0. Prerequisites:
 *    - Must be run on an F2 instance with an FPGA at the FPGA image slot matching the command-line option
 *    - Source the sdk by navigating to the root of this repo and running `source ./sdk_setup.sh`
 *    - The CL_SDE must be loaded on the FPGA that matches the slot_id passed to this program
 *    - The APP_PF of the FPGA card must have bus mastering enabled (check with `lspci -d 1d0f:f002 -vv`,
 *      should show `BusMaster+`)
 *    - To enable bus mastering if needed: `sudo setpci -s <Device:Bus:Device.Function> 4.w=6`
 *    - Hugepages must be allocated as this example uses them for DMA buffer management
 *    - To allocate hugepages: `sudo sysctl -w vm.nr_hugepages=<number_of_pages>`
 *
 * 1. Compile the example:
 *    `make sde_c2h_user_buffers`
 *
 * 2. Run the example:
 *    `sudo ./sde_c2h_user_buffers <num_packets> <packet_size> <slot_id>`
 *
 * 3. Example output:
 *    `sudo ./sde_c2h_user_buffers 1 1024 0`
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
#include <fpga_dma_mem.h>

#include <sde_mgmt.h>
#include <sde_utility.h>
#include <utils/log.h>
#include <string.h>
#include <stdlib.h>

#define C2H_DESC_COALESCE_CNT 32
#define NUM_BUFFERS 64
#define HUGEPAGE_SIZE 2097152

int partition_user_buffers(struct sde_buffer* sde_buffers, size_t num_buffers, size_t pkt_size, uint64_t physical_address);

int main(int argc, char **argv) {

  struct sde_parameters params;
  double start_time, end_time;
  int ret = 0;

  ret = sde_parse_args(argc, argv, &params, "sde_c2h_simple");
  fail_on(ret, err, "Unable to parse arguments");

  fail_on_with_code(params.slot_id >= FPGA_SLOT_MAX, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid slot_id %d", params.slot_id);

  uint64_t dma_buffer_va = 0;
  uint64_t dma_buffer_pa = 0;
  ret = fpga_dma_mem_map_huge(&dma_buffer_va, &dma_buffer_pa);
  size_t dma_buffer_size = HUGEPAGE_SIZE;

  struct sde_buffer sde_buffers[NUM_BUFFERS];
  ret = partition_user_buffers(sde_buffers, NUM_BUFFERS, params.pkt_size, dma_buffer_pa);

  ret = sde_mgmt_init(params.slot_id, SDE_EXAMPLE_DIR_C2H, params.pkt_size, SDE_BUFFER_USER_MANAGED);
  fail_on(ret, err, "failed to init sde_mgmt");

  ret = sde_mgmt_reset(params.slot_id);
  fail_on(ret, err, "failed to reset sde_mgmt");

  ret = sde_mgmt_set_dma_buffers(params.slot_id, SDE_SUBSYSTEM_C2H, sde_buffers, NUM_BUFFERS);

  ret = sde_mgmt_cfg(params.slot_id);
  fail_on(ret, err, "failed to cfg sde_mgmt");

  size_t num_descriptors = params.pkt_cnt < C2H_DESC_COALESCE_CNT ? params.pkt_cnt : C2H_DESC_COALESCE_CNT;
  size_t num_packets = 0;

  // Starting the timer after the SDE is already configured although it is not yet running.
  start_time = sde_get_curr_time();
  struct sde_md c2h_metadata;
  while (num_packets < (params.pkt_cnt)) {
    ret = sde_mgmt_check_status(params.slot_id, SDE_SUBSYSTEM_C2H);
    fail_on(ret, cleanup, "Error checking status");

    // Start the card to host DMA (read) by posting the descriptors for the buffers.
    size_t descriptors_posted = num_descriptors;
    ret = sde_mgmt_post_desc(params.slot_id, SDE_SUBSYSTEM_C2H, &descriptors_posted);
    fail_on(ret, cleanup, "Error posting descriptors");;

    for (size_t i = 0; i < descriptors_posted; ++i) {
      ret = sde_mgmt_read_md(params.slot_id, &c2h_metadata);
      fail_on(ret, cleanup, "Error reading metadata for each descriptor written.");
      fail_on(!c2h_metadata.valid, cleanup, "c2h_metadata is not valid");
      // user_bits and eop can also be checked before processing the data in the buffer.
    }

    num_packets+=descriptors_posted;
  }

  end_time = sde_get_curr_time();
  print_timing(start_time, end_time, params.pkt_size, num_packets, SDE_EXAMPLE_DIR_C2H);

cleanup:
  ret |= sde_mgmt_close(params.slot_id);
  ret |= fpga_dma_mem_unmap(&dma_buffer_va, dma_buffer_size);

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

int partition_user_buffers(struct sde_buffer* sde_buffers, size_t num_buffers, size_t pkt_size, uint64_t physical_address) {
  int ret = 0;
  fail_on_with_code(sde_buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid buffer pointer");
  fail_on_with_code(num_buffers == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid number of buffers");
  fail_on_with_code(pkt_size == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid packet size");
  fail_on_with_code(physical_address == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid physical address");
  fail_on_with_code(pkt_size * num_buffers > HUGEPAGE_SIZE, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Packet size * number of buffers exceeds hugepage size");

  memset(sde_buffers, 0, sizeof(struct sde_buffer) * num_buffers);

  // Partition the hugepage into NUM_BUFFERS buffers.
  for (size_t i = 0; i < num_buffers; ++i) {
    sde_buffers[i].data_pa = (pkt_size * i) + physical_address;
    sde_buffers[i].length = pkt_size;
  }

err:
  return ret;
}
