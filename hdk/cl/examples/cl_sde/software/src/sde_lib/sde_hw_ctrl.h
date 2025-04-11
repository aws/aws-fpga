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
 * The sde_hw_ctrl library contains a structure and functions for managing access to the hardware registers on
 * the FPGA card.
 */

#pragma once

#include <fpga_pci.h>
#include <sde_enums.h>

struct sde_hw_ctrl{
  int slot_id;
  pci_bar_handle_t bar0_handle;
  pci_bar_handle_t bar4_handle;
  pci_bar_handle_t bar4_wc_handle;

  bool initialized;
};

int sde_hw_init(struct sde_hw_ctrl* ctrl, int slot_id);
int sde_hw_close(struct sde_hw_ctrl* ctrl);

int sde_hw_reset(struct sde_hw_ctrl* ctrl);

int sde_hw_cfg_loopback_mode(struct sde_hw_ctrl* ctrl, bool enable);
int sde_hw_cfg_atg_mode(struct sde_hw_ctrl* ctrl, bool enable, uint32_t data, uint32_t pkt_size);

int sde_hw_cfg_c2h(struct sde_hw_ctrl* ctrl, uint64_t c2h_status_pa, uint64_t c2h_md_ring_pa, uint32_t c2h_md_ring_size);
int sde_hw_cfg_h2c(struct sde_hw_ctrl* ctrl, uint64_t h2c_status_pa);

int sde_hw_post_descriptor(struct sde_hw_ctrl* ctrl, uint64_t descriptor_va, size_t num_desc, enum SDE_SUBSYSTEM subsytem);
