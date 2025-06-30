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
 * The sde_dma_buffer library contains a structure for managing the buffer descriptors
 * and the data buffers used by the SDE.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <sde_enums.h>
#include <sde_mem.h>
#include <sde_hw_ctrl.h>

struct sde_dma_buffer {
  enum SDE_BUFFER_LAYOUT layout;
  enum SDE_SUBSYSTEM subsystem;
  struct sde_hw_ctrl* ctrl;

  uint64_t desc_va;
  uint64_t desc_pa;
  size_t num_desc;
  size_t desc_element_size;

  struct sde_buffer* buffers;
  size_t num_buffers;

  size_t pkt_size;

  size_t current_buffer_index;

  size_t curr_desc_index_to_post;
};

int sde_dma_buffer_init(struct sde_dma_buffer* dma_buffer, enum SDE_BUFFER_LAYOUT layout, enum SDE_SUBSYSTEM subsystem, size_t pkt_size, struct sde_mem* mem, struct sde_hw_ctrl* ctrl);
int sde_dma_buffer_close(struct sde_dma_buffer* dma_buffer);

int sde_dma_buffer_set_dma_buffers(struct sde_dma_buffer* dma_buffer, struct sde_buffer* sde_buffers, size_t num_buffers);
int sde_dma_init_desc_buffer(struct sde_dma_buffer* dma_buffer);
int sde_dma_post_desc(struct sde_dma_buffer* dma_buffer, size_t* num_desc);
int sde_dma_read_data(struct sde_dma_buffer* dma_buffer, void* data, size_t size);

int sde_dma_write_data(struct sde_dma_buffer* dma_buffer, void* data, size_t size);
