// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <fpga_pci_sv.h>

/**
 * Initialize the pci library.
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_init(void)
{
  return 0;
}

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
    pci_bar_handle_t *handle)
{
  return 0;
}
/**
 * Detach from an FPGA memory space.
 *
 * @param[in]  handle  the value provided by fpga_pci_attach corresponding to
 *                     the memory space to detach
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_detach(pci_bar_handle_t handle)
{
  return 0;
}

/**
 * Write a value to a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to write
 * @param[in]  value   value to write to the register
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_poke(pci_bar_handle_t handle, uint64_t offset, uint32_t value)
{

  sv_fpga_pci_poke(handle, offset, value);

  return 0;
}

/**
 * Read a value from a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to read
 * @param[out] value   value read from the register (32-bit)
 * @returns 0 on success, non-zero on error
 */
extern int sv_fpga_pci_poke(pci_bar_handle_t handle, uint64_t offset, uint32_t value);

/**
 * Read a value from a register.
 *
 * @param[in]  handle  handle provided by fpga_pci_attach
 * @param[in]  offset  memory location offset for register to read
 * @param[out] value   value read from the register (32-bit)
 * @returns 0 on success, non-zero on error
 */
int fpga_pci_peek(pci_bar_handle_t handle, uint64_t offset, uint32_t *value)
{

  sv_fpga_pci_peek(handle, offset, value);

  return 0;
}
