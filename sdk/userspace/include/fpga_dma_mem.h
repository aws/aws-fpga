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
 * The fpga_dma_mem library contains a helper function for allocating and
 * deallocating memory.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

//============================================================================================================
//
// fpga_dma_mem_alloc() : Allocate size_bytes memory using the provided file descriptor.
// arguements:
// -----------
// int fd                      : The file descriptor to use for allocating the memory.
// size_t size_bytes           : The number of bytes that will be allocated for the memory buffer.
// uint64_t* virtual_address   : The virtual address that the application can use for accessing the allocated memory.
// uint64_t* physical_address  : The physical address that can be programmed into a custom dma engine on a card.
//
//=============================================================================================================
int fpga_dma_mem_alloc(int fd, size_t size_bytes, uint64_t* virtual_address, uint64_t* physical_address);

//============================================================================================================
//
// fpga_dma_mem_dealloc() : Deallocate memory using the provided virtual address.
// arguements:
// -----------
// uint64_t* virtual_address  : The virtual address that was returned from fpga_dma_mem_alloc().
// size_t size_bytes          : The number of bytes that were allocated for the memory buffer.
//
//=============================================================================================================
int fpga_dma_mem_dealloc(uint64_t* virtual_address, size_t size_bytes);

#ifdef __cplusplus
}
#endif
