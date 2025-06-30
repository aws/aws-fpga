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
 * The sde_mgmt library provides a struct and set of functions to manage the other SDE
 * structs in the SDE examples.
 */

#pragma once

#include <sde_enums.h>
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

int sde_mgmt_init(int slot_id, enum SDE_EXAMPLE_DIR direction, size_t packet_size, enum SDE_BUFFER_LAYOUT layout);
int sde_mgmt_init_and_cfg(int slot_id, enum SDE_EXAMPLE_DIR direction, size_t packet_size);
int sde_mgmt_close(int slot_id);

int sde_mgmt_reset(int slot_id);
int sde_mgmt_check_status(int slot_id, enum SDE_SUBSYSTEM subsystem);

int sde_mgmt_set_dma_buffers(int slot_id, enum SDE_SUBSYSTEM subsystem, struct sde_buffer* sde_buffers, size_t num_buffers);
int sde_mgmt_cfg(int slot_id);
int sde_mgmt_wait_desc_credit(int slot_id, enum SDE_SUBSYSTEM subsystem, size_t num_desc);

int sde_mgmt_post_desc(int slot_id, enum SDE_SUBSYSTEM subsystem, size_t* num_desc);

struct sde_md {
  uint32_t length;
  bool valid;
  bool eop;
  uint32_t user_bits[2];
};

int sde_mgmt_start_read(int slot_id, size_t size);
int sde_mgmt_read_md(int slot_id, struct sde_md* md);
int sde_mgmt_read_data(int slot_id, void *data, size_t size);

int sde_mgmt_prepare_write(int slot_id, void *data, size_t size);
int sde_mgmt_write(int slot_id, size_t size);
