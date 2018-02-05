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
#ifndef COMMON_DMA_H_
#define COMMON_DMA_H_

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <poll.h>

#ifdef SV_TEST
   #include <fpga_pci_sv.h>
#else
   #include <fpga_pci.h>
   #include <fpga_mgmt.h>
   #include <utils/lcd.h>
#endif


static const size_t buffer_size = 128;
int channel;
int error_count;
char *write_buffer, *read_buffer;

#define	MEM_16G		(1ULL << 34)

void usage(const char* program_name);

void rand_string(char *str, size_t size);

int dma_example(int slot_id);

int interrupt_example(int slot_id, int interrupt_number);

int axi_mstr_example(int slot_id);

int axi_mstr_ddr_access(int slot_id, pci_bar_handle_t pci_bar_handle, uint32_t ddr_hi_addr, uint32_t ddr_lo_addr, uint32_t  ddr_data);

int fpga_driver_write_buffer_to_cl(int slot_id, int channel, int fd, size_t buffer_size, size_t address);

int fpga_driver_read_cl_to_buffer(int slot_id, int channel, int fd, size_t buffer_size, size_t address);

void fpga_write_buffer_to_cl(int slot_id, int channel, int fd, size_t buffer_size, size_t address);

void fpga_read_cl_to_buffer(int slot_id, int channel, int fd, size_t buffer_size, size_t address);

int dma_example_hwsw_cosim(int slot_id);

int dma_memcmp (size_t buffer_size);

int open_dma_queue(int slot_id);

#endif
