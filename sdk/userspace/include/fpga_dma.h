/*
 * Copyright 2015-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * The fpga_dma library contains helper functions for interacting with AWS
 * provided DMA drivers. It can be used as is or as an example for implementing
 * your own interfaces to DMA drivers, optimized for your own application.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

#define FPGA_DEVICE_FILE_NAME_MAX_LEN (256)

enum fpga_dma_driver {
    FPGA_DMA_EDMA,
    FPGA_DMA_XDMA,
};

/**
 * Open a file descriptor for DMA traffic. This is a high level API to open a
 * DMA queue file descriptor.
 *
 * @param which_driver     - specifies which DMA driver to use. See
 * @param slot_id          - fpga_dma_driver_e which FPGA slot to use; this uses
 *                           the same slot order as fpga_pci_get_resource_map
 * @param channel          - which DMA channel to use (ex 0-3 for XDMA)
 * @param is_read          - set to true to get the file for reading, or to
 *                           false for writing
 *
 * @returns the file descriptor on success or an error code less than 0 on
 * failure.
 */
int fpga_dma_open_queue(enum fpga_dma_driver which_driver, int slot_id,
    int channel, bool is_read);

/**
 * This returns the path to DMA device file corresponding to the driver, slot,
 * and DMA channel you requested. The function fpga_dma_open_queue uses this
 * function as a helper function.
 *
 * @param which_driver     - specifies which DMA driver to use. See
 * @param slot_id          - fpga_dma_driver_e which FPGA slot to use; this uses
 *                           the same slot order as fpga_pci_get_resource_map
 * @param channel          - which DMA channel to use (ex 0-3 for XDMA)
 * @param is_read          - set to true to get the file for reading, or to
 *                           false for writing
 * @param[out] device_file - an out parameter for returning the device file path
 *
 * @returns 0 on success, non-zero on failure
 */
int fpga_dma_device_id(enum fpga_dma_driver which_driver, int slot_id,
    int channel, bool is_read,
    char device_file[static FPGA_DEVICE_FILE_NAME_MAX_LEN]);

/**
 * Use this function to copy an entire buffer from the FPGA into a buffer in
 * host memory. This can be useful if the buffer is larger than the maximum
 * DMA size; this function will start another transaction until the entire
 * buffer has been transferred.
 *
 * @param fd      - the file descriptor for the DMA queue to use (obtained with
 *                  fpga_dma_open_queue)
 * @param buffer  - a pointer in host memory to place the DMA'd data into
 * @param xfer_sz - DMA transfer size, it is the caller's responsibility to
 *                  ensure the buffer is large enough
 * @param address - address of memory in the FPGA
 *
 * @returns 0 on success, non-zero on failure
 */
int fpga_dma_burst_read(int fd, uint8_t *buffer, size_t xfer_sz,
    size_t address);

/**
 * Use this function to copy an entire buffer from host memory to the FPGA. It
 * behaves similarly to fpga_dma_burst_read.
 *
 * @param fd      - the file descriptor for the DMA queue to use (obtained with
 *                  fpga_dma_open_queue)
 * @param buffer  - a pointer in host memory to source the DMA'd data
 * @param xfer_sz - DMA transfer size, it is the caller's responsibility to
 *                  ensure the buffer is large enough
 * @param address - address of memory in the FPGA
 *
 * @returns 0 on success, non-zero on failure
 */
int fpga_dma_burst_write(int fd, uint8_t *buffer, size_t xfer_sz,
    size_t address);

/**
 * The EDMA and XDMA drivers use a device number which does not map directly
 * onto the slot number. Use this function to map a slot number onto this device
 * number. The device number is the number used in the files found in /dev.
 *
 * @param which_driver     - specifies which DMA driver to use. See
 * @param slot_id          - fpga_dma_driver_e which FPGA slot to use; this uses
 *                           the same slot order as fpga_pci_get_resource_map
 * @param[out] device_num  - an out parameter for returning the device number
 *                           requested
 *
 * @returns 0 on success, non-zero on failure
 */
int fpga_pci_get_dma_device_num(enum fpga_dma_driver which_driver,
    int slot_id, int *device_num);

#ifdef __cplusplus
}
#endif
