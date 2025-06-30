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

#pragma once

#include <stdint.h>

enum SDE_EXAMPLE_DIR {
  SDE_EXAMPLE_DIR_C2H,
  SDE_EXAMPLE_DIR_H2C,
  SDE_EXAMPLE_DIR_LOOPBACK,
};

enum SDE_BUFFER_LAYOUT {
    SDE_BUFFER_LAYOUT_SINGLE,
    SDE_BUFFER_LAYOUT_MULTI,
    SDE_BUFFER_USER_MANAGED,
};

enum SDE_SUBSYSTEM {
  SDE_SUBSYSTEM_C2H,
  SDE_SUBSYSTEM_H2C
};

enum SDE_ERROR {
  SDE_UNEXPECTED_REGISTER_VALUE = 0x1000,
  SDE_ALLOCATION_FAILURE = 0x1001,
  SDE_STATUS_COUNTER_ERROR = 0x1002,
  SDE_DESC_LIMIT_TIMEOUT = 0x1003,
  SDE_METADATA_VALID_TIMEOUT = 0x1004,
};

struct sde_buffer {
  uint64_t data_va;
  uint64_t data_pa;
  uint32_t length;
  uint32_t alloc_length;
};

#define SDE_ERR2STR(error) \
  ((error) == SDE_UNEXPECTED_REGISTER_VALUE) ? "unexpected-register-value" : \
  ((error) == SDE_ALLOCATION_FAILURE) ? "allocation-failure" : \
  ((error) == SDE_STATUS_COUNTER_ERROR) ? "sde-status-counter-error" : \
  ((error) == SDE_DESC_LIMIT_TIMEOUT) ? "descriptor-limit-timeout" : \
  ((error)  == SDE_METADATA_VALID_TIMEOUT) ? "metadata-valid-timeout" : "unknown-error"

#define START_DOUBLE_WORD 0x11110000
