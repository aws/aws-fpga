// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================

#pragma once

#include <stddef.h>
#include <stdint.h>

/**
 * Fills the input buffer with random bytes.
 */
int fill_buffer_urandom(uint8_t *buf, size_t size);

/**
 * Dumps buffer contents in hex format for debugging.
 *
 * @param prefix Label to print before the buffer contents
 * @param buffer Pointer to buffer data
 * @param size Total size of the buffer
 * @param offset Starting offset within buffer to dump from
 */
int dump_buffer(const char *prefix, uint8_t *buffer, size_t size, size_t offset);

/**
 * Compares two buffers and reports detailed information about differences.
 * Reports first mismatch location with context, periodic progress for large
 * differences, and total difference count with percentage.
 *
 * @param bufa First buffer (expected data)
 * @param bufb Second buffer (actual data)
 * @param buffer_size Size of buffers to compare
 * @returns Number of bytes which differ (0 if buffers match)
 */
uint64_t buffer_compare(uint8_t *bufa, uint8_t *bufb, size_t buffer_size);

#if !defined(SV_TEST)
/**
 * Checks to make sure that the slot has a recognized AFI loaded.
 */
int check_slot_config(int slot_id);

/**
 * Deassert resets from AWS_CLK_GEN block using the AWS FPGA SDK
 * management function.
 */
int deassert_clk_resets(int slot_id);
#else
int send_rdbuf_to_c(char *rd_buf);
#endif
