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

#include <sde_mem.h>
#include <fpga_dma_mem.h>
#include <sde_utility.h>
#include <utils/log.h>
#include <hal/fpga_common.h>
#include <sde_hw_regs.h>
#include <string.h>
#include <stdlib.h>

#include <fcntl.h>
#include <string.h>
#include <unistd.h>

static int writeback_init(struct sde_writeback_mem* writeback_mem, enum SDE_SUBSYSTEM subsystem) {
  int ret = 0;

  fail_on_with_code(writeback_mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "writeback_mem ptr is NULL");
  fail_on_with_code(subsystem != SDE_SUBSYSTEM_H2C && subsystem != SDE_SUBSYSTEM_C2H, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "Invalid subsystem");

  // Metadata Writeback is a only a card to host feature, so no memory needs to be allocated for it for host to card subsystems.
  size_t metadata_size = 0;
  size_t metadata_ring_size = 0;
  if (subsystem == SDE_SUBSYSTEM_C2H) {
    metadata_size = sizeof(struct c2h_wb_metadata);
    metadata_ring_size = sde_aligned_size(metadata_size * C2H_NUM_MD_IN_RING, SDE_ALIGN);
    writeback_mem->metadata_offset = 0;
  }

  size_t desc_size = (subsystem == SDE_SUBSYSTEM_C2H) ? sizeof(struct c2h_desc) : sizeof(struct h2c_desc);
  size_t desc_ring_size = sde_aligned_size(desc_size * SDE_NUM_DESC, SDE_ALIGN);
  writeback_mem->desc_offset = metadata_ring_size;

  size_t status_size = sde_aligned_size(sizeof(struct c2h_status), SDE_ALIGN);
  writeback_mem->status_offset = metadata_ring_size + desc_ring_size;

  writeback_mem->memory_size = desc_ring_size + metadata_ring_size + status_size;
  ret = fpga_dma_mem_map_anon(writeback_mem->memory_size, &writeback_mem->memory_va, &writeback_mem->memory_pa);
  fail_on(ret, err, "fpga_dma_mem_map_anon failed");

err:
  return ret;
}

static int dma_buffer_init(enum SDE_BUFFER_LAYOUT layout, size_t pkt_size, struct sde_buffer** buffers, size_t* num_buffers) {
  int ret = 0;

  fail_on_with_code(buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "buffer ptr is NULL");
  fail_on_with_code(num_buffers == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "num_buffers ptr is NULL");

  if (layout == SDE_BUFFER_LAYOUT_SINGLE) {
    *num_buffers = 1;
  } else if (layout == SDE_BUFFER_LAYOUT_MULTI) {
    *num_buffers = SDE_NUM_DESC;
  }

  // Allocate enough space for *num_buffers sde_buffers.
  *buffers = malloc(*num_buffers * sizeof(struct sde_buffer));
  fail_on_with_code(*buffers == NULL, err, ret, SDE_ALLOCATION_FAILURE, "malloc failed");

  struct sde_buffer* current_buffer = NULL;
  for (size_t i = 0; i < *num_buffers; ++i) {
    // Map memory for each buffer.
    current_buffer = (*buffers + i);
    if (pkt_size > 0x1000 /*4k*/) {
      // If the pkt_size is larger than 4k, it cannot fit on a single memory page.
      // Use a hugepage for the mapping.
      current_buffer->length = pkt_size;
      current_buffer->alloc_length = 2 * 1024 * 1024;
      ret = fpga_dma_mem_map_huge(&current_buffer->data_va, &current_buffer->data_pa);
      fail_on(ret, err, "fpga_dma_mem_alloc_huge failed");
    } else {
      current_buffer->length = pkt_size;
      current_buffer->alloc_length = pkt_size;
      ret = fpga_dma_mem_map_anon(current_buffer->length, &current_buffer->data_va, &current_buffer->data_pa);
      fail_on(ret, err, "fpga_dma_mem_map_anon failed");
    }
  }

err:
  return ret;
}

int sde_mem_init(struct sde_mem* mem, enum SDE_BUFFER_LAYOUT c2h_layout, enum SDE_BUFFER_LAYOUT h2c_layout, enum SDE_EXAMPLE_DIR direction, size_t pkt_size) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");
  fail_on_with_code(pkt_size > 0x200000 /*2M*/, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "pkt_size is too large");

  memset(mem, 0, sizeof(struct sde_mem));

  ret = writeback_init(&mem->c2h_writeback, SDE_SUBSYSTEM_C2H);
  fail_on(ret, err, "writeback_init c2h failed");

  ret = writeback_init(&mem->h2c_writeback, SDE_SUBSYSTEM_H2C);
  fail_on(ret, err, "writeback_init h2c failed");

  mem->c2h_layout = c2h_layout;
  mem->c2h_num_buffers = 0;

  if (direction != SDE_EXAMPLE_DIR_H2C && c2h_layout != SDE_BUFFER_USER_MANAGED) {
    ret = dma_buffer_init(c2h_layout, pkt_size, &mem->c2h_buffers, &mem->c2h_num_buffers);
    fail_on(ret, err, "dma_buffer_init c2h failed");
  }

  mem->h2c_layout = h2c_layout;
  mem->h2c_num_buffers = 0;

  if (direction != SDE_EXAMPLE_DIR_C2H && h2c_layout != SDE_BUFFER_USER_MANAGED) {
    ret = dma_buffer_init(h2c_layout, pkt_size, &mem->h2c_buffers, &mem->h2c_num_buffers);
    fail_on(ret, err, "dma_buffer_init h2c failed");
  }

err:
  return ret;
}

int sde_mem_close(struct sde_mem* mem) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");

  ret |= fpga_dma_mem_unmap(&mem->c2h_writeback.memory_va, mem->c2h_writeback.memory_size);
  ret |= fpga_dma_mem_unmap(&mem->h2c_writeback.memory_va, mem->h2c_writeback.memory_size);


  if (mem->c2h_buffers != NULL) {
    for (size_t i = 0; i < mem->c2h_num_buffers; ++i) {
      ret |= fpga_dma_mem_unmap(&mem->c2h_buffers[i].data_va, mem->c2h_buffers[i].alloc_length);
    }
  }

  if (mem->h2c_buffers != NULL) {
    for (size_t i = 0; i < mem->h2c_num_buffers; ++i) {
      ret |= fpga_dma_mem_unmap(&mem->h2c_buffers[i].data_va, mem->h2c_buffers[i].alloc_length);
    }
  }

  free(mem->c2h_buffers);
  free(mem->h2c_buffers);

  fail_on(ret, err, "fpga_dma_mem_unmap failed");

err:
  return ret;
}

int sde_mem_get_desc(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");
  fail_on_with_code(subsystem != SDE_SUBSYSTEM_C2H && subsystem != SDE_SUBSYSTEM_H2C, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "subsystem is not C2H or H2C");
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address ptr is NULL");
  fail_on_with_code(physical_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "physical_address ptr is NULL");

  if (subsystem == SDE_SUBSYSTEM_C2H) {
    *virtual_address = mem->c2h_writeback.desc_offset + mem->c2h_writeback.memory_va;
    *physical_address = mem->c2h_writeback.desc_offset + mem->c2h_writeback.memory_pa;
  } else {
    *virtual_address = mem->h2c_writeback.desc_offset + mem->h2c_writeback.memory_va;
    *physical_address = mem->h2c_writeback.desc_offset + mem->h2c_writeback.memory_pa;
  }

err:
  return ret;
}

int sde_mem_get_status(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");
  fail_on_with_code(subsystem != SDE_SUBSYSTEM_C2H && subsystem != SDE_SUBSYSTEM_H2C, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "subsystem is not C2H or H2C");
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address ptr is NULL");
  fail_on_with_code(physical_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "physical_address ptr is NULL");

  if (subsystem == SDE_SUBSYSTEM_C2H) {
    *virtual_address = mem->c2h_writeback.status_offset + mem->c2h_writeback.memory_va;
    *physical_address = mem->c2h_writeback.status_offset + mem->c2h_writeback.memory_pa;
  } else {
    *virtual_address = mem->h2c_writeback.status_offset + mem->h2c_writeback.memory_va;
    *physical_address = mem->h2c_writeback.status_offset + mem->h2c_writeback.memory_pa;
  }

err:
  return ret;
}

int sde_mem_get_metadata(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");
  fail_on_with_code(subsystem != SDE_SUBSYSTEM_C2H, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "subsystem is not C2H or H2C");
  fail_on_with_code(virtual_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "virtual_address ptr is NULL");
  fail_on_with_code(physical_address == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "physical_address ptr is NULL");

  // Writeback metadata is only available for the card to host subsystem.
  *virtual_address = mem->c2h_writeback.metadata_offset + mem->c2h_writeback.memory_va;
  *physical_address = mem->c2h_writeback.metadata_offset + mem->c2h_writeback.memory_pa;

err:
  return ret;
}

int sde_mem_get_buffers(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, struct sde_buffer** buffers, size_t *num_buffers) {
  int ret = 0;

  fail_on_with_code(mem == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "mem ptr is NULL");
  fail_on_with_code(subsystem != SDE_SUBSYSTEM_C2H && subsystem != SDE_SUBSYSTEM_H2C, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "subsystem is not C2H or H2C");

  *buffers = (subsystem == SDE_SUBSYSTEM_C2H) ? mem->c2h_buffers : mem->h2c_buffers;
  *num_buffers = (subsystem == SDE_SUBSYSTEM_C2H) ? mem->c2h_num_buffers : mem->h2c_num_buffers;

err:
  return ret;
}
