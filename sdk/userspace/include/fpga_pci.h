/*
 * Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <hal/fpga_common.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * FPGA_PCI_BARS_MAX:
 *  -compile time tunable via mkall_fpga_mgmt_tools.sh, with the below default.
 *  -set this to the max number of FPGA BARs that the application plans
 *   to attach at any one time.
 *  -the upper limit is FPGA_SLOT_MAX * FPGA_BARS_MAX.
 *  -FPGA_SLOT_MAX is driven by the EC2 FPGA system design and instance type.
 *  -FPGA_BARS_MAX is driven by the FPGA Shell release.
 */
#if ! defined(FPGA_PCI_BARS_MAX)
#define FPGA_PCI_BARS_MAX	(FPGA_SLOT_MAX * FPGA_PF_MAX * FPGA_BAR_PER_PF_MAX)
#endif

/*
 *  Notes on platform vs application locking:
 *
 *  Platform Locking:
 *  -attach/detach are protected via a pthread mutex to allow for use cases
 *   of multi-threaded attach/detach sequences vs calling attach/detach during
 *   one time process init/destroy.
 *
 *  Application Locking:
 *  -a single process may access all of the FPGAs via the dev_index(es) without
 *   locking.
 *  -a single thread may access a single FPGA via the dev_index without locking.
 *  -multi-threaded access to the same FPGA must be done with locking within
 *   the application.
 */

/**
 * Type definition for a descriptor/handle used to specify a BAR. Initialize
 * with PCI_BAR_HANDLE_INIT.
 */
typedef int pci_bar_handle_t;
#define PCI_BAR_HANDLE_INIT (-1)

/**
 * Initialize the pci library.
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_init(void);

/**
 * Attach to an FPGA memory space.
 *
 * @param[in]  slot_id  logical slot index
 * @param[in]  pf_id    physical function id, e.g. FPGA_APP_PF
 * @param[in]  bar_id   base address register, e.g. APP_PF_BAR4
 * @param[in]  flags    set various options (flags defined below)
 * @param[out] handle   used to identify fpga attachment for future library
 *                      calls
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_attach(int slot_id, int pf_id, int bar_id, uint32_t flags,
    pci_bar_handle_t *handle);

/**
 * Flags used to specify options for fpga_pci_attach.
 */
enum {
    BURST_CAPABLE = 0x1,
    FPGA_ATTACH_RESERVED = 0xfffffffe,
};

/**
 * Detach from an FPGA memory space.
 *
 * @param[in]  handle  the value provided by fpga_pci_attach corresponding to
 *                     the memory space to detach
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_detach(pci_bar_handle_t handle);

/**
 * Write a value to a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to write
 * @param[in]  value   value to write to the register
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_poke(pci_bar_handle_t handle, uint64_t offset, uint32_t value);

/**
 * Write a value to a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to write
 * @param[in]  value   64-bit value to write to the register
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_poke64(pci_bar_handle_t handle, uint64_t offset, uint64_t value);

/**
 * Write a burst to a burst capable memory bar.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for  to write
 * @param[in]  datap   pointer to the data to be written
 * @param[in]  dword_len  the length of data to write in burst, in 4-byte DWORDs
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_write_burst(pci_bar_handle_t handle, uint64_t offset,
    uint32_t* datap, uint64_t dword_len);

/**
 * Read a value from a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to read
 * @param[out] value   value read from the register (32-bit)
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_peek(pci_bar_handle_t handle, uint64_t offset, uint32_t *value);

/**
 * Read a value from a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to read
 * @param[out] value   64-bit value read from the register
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_peek64(pci_bar_handle_t handle, uint64_t offset, uint64_t *value);

/**
 * Use a logical slot id to populate a slot spec
 *
 * @param[in]  slot_id  The logical slot id of the FPGA of interest
 * @param[in]  pf_id    physical function id (e.g. FPGA_APP_PF)
 * @param[in]  bar_id   base address register id (e.g. APP_PF_BAR0)
 * @param[out] spec     Pointer to fpga_slot spec to populate
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_get_slot_spec(int slot_id, struct fpga_slot_spec *spec);

/**
 * Populate slot specs for all FPGAs on the system. It is recommended to use
 * FPGA_SLOT_MAX as the size of the spec_array;
 *
 * @param[out]  spec_array  array to populate
 * @param[in]   size        allocated size of the provided array
 */
int fpga_pci_get_all_slot_specs(struct fpga_slot_spec spec_array[], int size);

/**
 * Get resource map information for a single slot and physical function. This
 * information is provided in the slot_spec, but occasionally only the resource
 * map is needed.
 *
 * @param[in]   slot_id  The logical slot id of the FPGA of interest
 * @param[in]   pf_id    physical function id (e.g. FPGA_APP_PF)
 * @param[out]  map      resource map to populate
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_get_resource_map(int slot_id, int pf_id,
    struct fpga_pci_resource_map *map);

/**
 * Rescan the slot application physical functions.
 * -performs both a pci device remove and a PCI rescan to refresh the device
 *  vendor and device IDs within the OS.
 *
 * @param[in]   slot_id  The logical slot id of the FPGA of interest
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_rescan_slot_app_pfs(int slot_id);

/**
 * Get a bounds checked pointer to memory in the mapped region for this handle.
 *
 * @param[in]   handle    handle provided by fpga_pci_attach
 * @param[in]   offset    offset into the mmap'ed region
 * @param[in]   dword_len the length of data to write in burst, in 4-byte DWORDs
 *                        (used for bounds checking)
 * @param[out]  ptr       pointer to memory
 *
 * @return 0 on success, non-zero on error (bounds errors in particular)
 */
int fpga_pci_get_address(pci_bar_handle_t handle, uint64_t offset,
	uint64_t dword_len, void **ptr);

/**
 * Initialze a segment of memory to an initial value. This has the best
 * performance when the BAR is attached with write combining enabled.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset to write
 * @param[in]  value   value to write into memory
 * @param[in]  dword_len  the length of data to write in burst, in 4-byte DWORDs
 *
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_memset(pci_bar_handle_t handle, uint64_t offset, uint32_t value,
	uint64_t dword_len);

#ifdef __cplusplus
}
#endif
