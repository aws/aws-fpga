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

#include <sde_dma_buffer.h>
#include <utils/log.h>
#include <hal/fpga_common.h>
#include <stdlib.h>
#include <fpga_dma_mem.h>
#include <string.h>
#include <sde_hw_regs.h>
#include <sde_utility.h>

int sde_dma_buffer_init(struct sde_dma_buffer* dma_buffer, enum SDE_BUFFER_LAYOUT layout, enum SDE_SUBSYSTEM subsystem, size_t pkt_size, struct sde_mem* mem, struct sde_hw_ctrl* ctrl) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");

  memset(dma_buffer, 0, sizeof(struct sde_dma_buffer));
  dma_buffer->layout = layout;
  dma_buffer->subsystem = subsystem;
  dma_buffer->pkt_size = pkt_size;
  dma_buffer->desc_element_size = subsystem == SDE_SUBSYSTEM_C2H ? sizeof(struct c2h_desc) : sizeof(struct h2c_desc);
  dma_buffer->ctrl = ctrl;

  ret = sde_mem_get_desc(mem, dma_buffer->subsystem, &dma_buffer->desc_va, &dma_buffer->desc_pa);
  fail_on(ret, err, "Failed to get descriptor");

  if (dma_buffer->layout != SDE_BUFFER_USER_MANAGED) {
    dma_buffer->num_desc = SDE_NUM_DESC;
    ret = sde_mem_get_buffers(mem, dma_buffer->subsystem, &dma_buffer->buffers, &dma_buffer->num_buffers);
  }

err:
  return ret;
}

int sde_dma_buffer_close(struct sde_dma_buffer* dma_buffer) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");

  memset(dma_buffer, 0, sizeof(struct sde_dma_buffer));

err:
  return ret;
}

static uint32_t get_next_start_dw(uint32_t curr_start_dw) {
  uint8_t curr_start_dw_byte;
  uint32_t next_start_dw;

  curr_start_dw_byte = (curr_start_dw >> 16) & 0xf;
  curr_start_dw_byte++;
  curr_start_dw_byte &= 0xf;
  next_start_dw = ((curr_start_dw_byte << 16) |
                   (curr_start_dw_byte << 20) |
                   (curr_start_dw_byte << 24) |
                   (curr_start_dw_byte << 28));

  return(next_start_dw);
}

int sde_dma_buffer_set_dma_buffers(struct sde_dma_buffer* dma_buffer, struct sde_buffer* sde_buffers, size_t num_buffers) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");
  fail_on_with_code(sde_buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "sde_buffer_descriptors is NULL");
  fail_on_with_code(num_buffers == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_descriptors is 0");
  fail_on_with_code(dma_buffer->layout != SDE_BUFFER_USER_MANAGED, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer->layout is not SDE_BUFFER_USER_MANAGED");

  log_debug("dma_buffer->subsystem = %d", dma_buffer->subsystem);
  log_debug("dma_buffer->num_buffers = %ld", dma_buffer->num_buffers);

  dma_buffer->buffers = sde_buffers;
  dma_buffer->num_buffers = num_buffers;
  dma_buffer->num_desc = num_buffers;

err:
  return ret;
}

int sde_dma_init_desc_buffer(struct sde_dma_buffer* dma_buffer) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");
  fail_on_with_code(dma_buffer->num_buffers == 0, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer->num_buffers is 0");
  fail_on_with_code(dma_buffer->buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer->buffers is NULL");

  if (dma_buffer->subsystem == SDE_SUBSYSTEM_C2H) {
    struct c2h_desc* desc = (struct c2h_desc*) dma_buffer->desc_va;
    for (size_t i = 0; i < dma_buffer->num_desc; ++i) {
      size_t buffer_index = i % dma_buffer->num_buffers;
      desc[i].length = dma_buffer->buffers[buffer_index].length;
      desc[i].phys_addr = dma_buffer->buffers[buffer_index].data_pa;
      desc[i].reserved = 0;
    }
  } else {
    uint32_t current_dw = START_DOUBLE_WORD;
    uint32_t next_dw = get_next_start_dw(current_dw);

    struct h2c_desc* desc = (struct h2c_desc*) dma_buffer->desc_va;
    for (size_t i = 0; i < dma_buffer->num_desc; ++i) {
      size_t buffer_index = i % dma_buffer->num_buffers;
      desc[i].length = dma_buffer->buffers[buffer_index].length;
      desc[i].phys_addr = dma_buffer->buffers[buffer_index].data_pa;
      SDE_SET_BITFIELD(DESC_CFG_BITS_EOP, 1, &desc[i].cfg_bits);
      SDE_SET_BITFIELD(DESC_CFG_BITS_SPB, 0, &desc[i].cfg_bits);
      desc[i].reserved = 0;

      if (i != 0) {
        current_dw = next_dw;
        next_dw = get_next_start_dw(current_dw);
      }

      desc[i].user = (uint64_t)(next_dw) << 32 | current_dw;
    }
  }

  dma_buffer->curr_desc_index_to_post = 0;
  dma_buffer->current_buffer_index = 0;

err:
  return ret;
}

int sde_dma_post_desc(struct sde_dma_buffer* dma_buffer, size_t* num_desc) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");
  fail_on_with_code(num_desc == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_desc is NULL");

  uint64_t virtual_address = 0;
  size_t available_desc = 0;
  size_t num_desc_to_post = 0;
  size_t posted_desc = 0;
  size_t remaining_desc_to_post = 0;
  while (*num_desc > posted_desc) {
    virtual_address = dma_buffer->desc_va + dma_buffer->curr_desc_index_to_post * dma_buffer->desc_element_size;
    available_desc = dma_buffer->num_desc - dma_buffer->curr_desc_index_to_post;
    remaining_desc_to_post = *num_desc - posted_desc;
    num_desc_to_post = remaining_desc_to_post > available_desc ? available_desc : remaining_desc_to_post;

    ret = sde_hw_post_descriptor(dma_buffer->ctrl, virtual_address, num_desc_to_post, dma_buffer->subsystem);
    fail_on(ret, err, "Failed to post descriptor");

    dma_buffer->curr_desc_index_to_post += num_desc_to_post;
    dma_buffer->curr_desc_index_to_post %= dma_buffer->num_desc;
    posted_desc += num_desc_to_post;
  }
  *num_desc = posted_desc;

err:
  return ret;
}

int sde_dma_read_data(struct sde_dma_buffer* dma_buffer, void* data, size_t size) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");
  fail_on_with_code(data == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "data is NULL");

  uint8_t* data_ptr = (uint8_t*)data;

  size_t size_in_buffer = 0;
  size_t iteration_copy_size = 0;

  do {
    size_in_buffer = dma_buffer->buffers[dma_buffer->current_buffer_index].length;
    iteration_copy_size = size_in_buffer > size ? size : size_in_buffer;
    memcpy(data_ptr, (uint8_t*)dma_buffer->buffers[dma_buffer->current_buffer_index].data_va, iteration_copy_size);
    log_info("Copying %ld bytes from 0x%lx", iteration_copy_size, dma_buffer->buffers[dma_buffer->current_buffer_index].data_va);

    size -= iteration_copy_size;
    data_ptr += iteration_copy_size;

    ++dma_buffer->current_buffer_index;
    dma_buffer->current_buffer_index %= dma_buffer->num_buffers;
  } while (size > 0);

err:
  return ret;
}

int sde_dma_write_data(struct sde_dma_buffer* dma_buffer, void* data, size_t size) {
  int ret = 0;

  fail_on_with_code(dma_buffer == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "dma_buffer is NULL");
  fail_on_with_code(data == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "data is NULL");

  uint8_t* data_ptr = (uint8_t*)data;

  size_t size_in_buffer = 0;
  size_t iteration_copy = 0;

  do {
    size_in_buffer = dma_buffer->buffers[dma_buffer->current_buffer_index].length;
    iteration_copy = size_in_buffer > size ? size : size_in_buffer;
    memcpy((uint8_t*)dma_buffer->buffers[dma_buffer->current_buffer_index].data_va, data_ptr, iteration_copy);
    log_info("Copying %ld bytes to 0x%lx", iteration_copy, dma_buffer->buffers[dma_buffer->current_buffer_index].data_va);

    size -= iteration_copy;
    data_ptr += iteration_copy;

    ++dma_buffer->current_buffer_index;
    dma_buffer->current_buffer_index %= dma_buffer->num_buffers;
  } while (size > 0);

err:
  return ret;
}
