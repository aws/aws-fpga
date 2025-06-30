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

/**
 * The sde_mem library contains a structure for managing memory used by the other objects in the SDE examples.
 */

#pragma once

#include <stdint.h>
#include <sde_enums.h>
#include <stddef.h>

struct sde_writeback_mem {
  uint64_t memory_va;
  uint64_t memory_pa;
  size_t memory_size;

  size_t metadata_offset;
  size_t desc_offset;
  size_t status_offset;
};

struct sde_mem {
  struct sde_writeback_mem c2h_writeback;
  struct sde_writeback_mem h2c_writeback;

  enum SDE_BUFFER_LAYOUT c2h_layout;
  struct sde_buffer* c2h_buffers;
  size_t c2h_num_buffers;

  enum SDE_BUFFER_LAYOUT h2c_layout;
  struct sde_buffer* h2c_buffers;
  size_t h2c_num_buffers;
};

#define SDE_ALIGN 64

int sde_mem_init(struct sde_mem* mem, enum SDE_BUFFER_LAYOUT c2h_layout, enum SDE_BUFFER_LAYOUT h2c_layout, enum SDE_EXAMPLE_DIR direction, size_t pkt_size);
int sde_mem_close(struct sde_mem* mem);

int sde_mem_get_desc(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address);
int sde_mem_get_status(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address);
int sde_mem_get_metadata(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, uint64_t* virtual_address, uint64_t* physical_address);

int sde_mem_get_buffers(struct sde_mem* mem, enum SDE_SUBSYSTEM subsystem, struct sde_buffer** buffers, size_t* num_buffers);