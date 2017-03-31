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

#include "xdma_utils.h"

static XDMA_DESC *h2c_desc_table;
static int h2c_desc_index = 0;

uint32_t dma_reg_addr(uint32_t target, uint32_t channel, uint32_t offset) {
  return ((target << 12) | (channel << 8) | offset);
}

void que_buffer_to_cl(int chan, uint8_t *buf, size_t len) {

  // setup descriptor table if this is first call
  if (h2c_desc_index == 0) {
    h2c_desc_table = (XDMA_DESC *)memalign(4096, 4096);  // allocate 4k aligned to a 4k boundary
    
    sv_map_host_memory(h2c_desc_table);
  
  }

  h2c_desc_table[h2c_desc_index].header.word = 0; // make sure reserved bits and unused bits are 0
  h2c_desc_table[h2c_desc_index].header.fields.control = 0x01;
  h2c_desc_table[h2c_desc_index].header.fields.nxt_adj = 0;
  h2c_desc_table[h2c_desc_index].header.fields.magic = 0xad4b;
  h2c_desc_table[h2c_desc_index].len = len;
  h2c_desc_table[h2c_desc_index].src_adr_lo = LOW_32b(buf);
  h2c_desc_table[h2c_desc_index].src_adr_hi = HIGH_32b(buf);
  h2c_desc_table[h2c_desc_index].dst_adr_lo = 0;
  h2c_desc_table[h2c_desc_index].dst_adr_hi = 0;
  h2c_desc_table[h2c_desc_index].nxt_adr_lo = 0;
  h2c_desc_table[h2c_desc_index].nxt_adr_hi = 0;

  // remove stop bit from previous descriptor
  if (h2c_desc_index > 0) {
    h2c_desc_table[h2c_desc_index-1].header.fields.control &= 0xfe;
  }

  h2c_desc_index++;
}

void que_cl_to_buffer(int chan, uint8_t *buf, size_t len) {
}

void start_move_to_cl(int chan) {
  uint64_t base_addr;
  uint32_t data;

  get_base_addr_of_func(2, 0, &base_addr);
  log_printf("base_addr: %16lx", base_addr);

  reg_read(base_addr, &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+4, &data);
  log_printf("data: %08x", data);

  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x80), LOW_32b(h2c_desc_table));
  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x84), HIGH_32b(h2c_desc_table));

  reg_write(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x88), h2c_desc_index-1);  // don't count the first entry

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x80), &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x84), &data);
  log_printf("data: %08x", data);

  reg_read(base_addr+dma_reg_addr(H2C_SGDMA_TGT, 0, 0x88), &data);
  log_printf("data: %08x", data);

  // sett pollmode_wb, ie_completed & run bit
  reg_write(base_addr+dma_reg_addr(H2C_TGT, 0, H2C_CTRL0), 0x04000005);
  reg_read(base_addr+dma_reg_addr(H2C_TGT, 0, H2C_CTRL0), &data);
  log_printf("data: %08x", data);

}

void start_move_to_buffer(int chan) {
}

void is_move_to_cl_done(int chan) {
}

void is_move_to_buffer_done(int chan) {
}
