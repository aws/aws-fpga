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

#include <sde_hw_ctrl.h>
#include <utils/log.h>
#include <sde_hw_regs.h>

int sde_hw_init(struct sde_hw_ctrl* ctrl, int slot_id) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");

  ctrl->slot_id = slot_id;
  ctrl->initialized = false;

  ctrl->bar0_handle = PCI_BAR_HANDLE_INIT;
  ret = fpga_pci_attach(ctrl->slot_id, FPGA_APP_PF, APP_PF_BAR0, 0, &ctrl->bar0_handle);

  ret |= fpga_pci_attach(ctrl->slot_id, FPGA_APP_PF, APP_PF_BAR4, 0, &ctrl->bar4_handle);

  ret |= fpga_pci_attach(ctrl->slot_id, FPGA_APP_PF, APP_PF_BAR4, BURST_CAPABLE, &ctrl->bar4_wc_handle);

  if (ret == FPGA_ERR_OK) {
    ctrl->initialized = true;
  }

err:
  return ret;
}

int sde_hw_close(struct sde_hw_ctrl* ctrl) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");

  if (ctrl->initialized) {
    ret = fpga_pci_detach(ctrl->bar0_handle);
    ret |= fpga_pci_detach(ctrl->bar4_handle);
    ret |= fpga_pci_detach(ctrl->bar4_wc_handle);
    ctrl->initialized = false;
  }

  if (ret != FPGA_ERR_OK) {
    log_error("Error during fpga_sde_close");
  }

err:
  return ret;
}

static int poke_and_verify(pci_bar_handle_t handle, uint64_t offset, uint32_t value, uint32_t expected_value, uint32_t mask) {
  int ret = 0;

  ret = fpga_pci_poke(handle, offset, value);
  fail_on(ret, err, "Unable to write register offset 0x%lx", offset);

  uint32_t data;
  ret = fpga_pci_peek(handle, offset, &data);
  fail_on(ret, err, "Unable to read from the SDE BAR0");

  fail_on_with_code((data & mask) != (expected_value & mask), err, ret, SDE_UNEXPECTED_REGISTER_VALUE, "poke_and_verify: expected 0x%x, got 0x%x, mask 0x%x", expected_value, data, mask);
err:
  return ret;
}

int sde_hw_reset (struct sde_hw_ctrl* ctrl) {
  uint32_t gpcr_data;
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  pci_bar_handle_t bar0_handle = ctrl->bar0_handle;

  ret = fpga_pci_peek(bar0_handle, SDE_GENERAL_PURPOSE_CFG_REG, &gpcr_data);
  fail_on(ret, err, "Unable to read from the GENERAL_PURPOSE_CFG_REG");

  SDE_SET_BITFIELD(GPCR_SDE_RESET, 1, &gpcr_data);
  ret = poke_and_verify(bar0_handle, SDE_GENERAL_PURPOSE_CFG_REG, gpcr_data, GPCR_SDE_RESET_MASK, GPCR_SDE_RESET_MASK);
  fail_on(ret, err, "Reset SDE bit not set");

  SDE_SET_BITFIELD(GPCR_SDE_RESET, 0, &gpcr_data);
  ret = poke_and_verify(bar0_handle, SDE_GENERAL_PURPOSE_CFG_REG, gpcr_data, 0, GPCR_SDE_RESET_MASK);
  fail_on(ret, err, "Reset SDE bit not cleared");

err:
  return ret;
}

int sde_hw_cfg_loopback_mode(struct sde_hw_ctrl* ctrl, bool enable) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  pci_bar_handle_t bar0_handle = ctrl->bar0_handle;

  uint32_t rx_control_value = 0;
  SDE_SET_BITFIELD(RCR_LOOPBACK_EN, enable, &rx_control_value);
  SDE_SET_BITFIELD(RCR_BACKPRESSURE_EN, enable, &rx_control_value);
  ret = poke_and_verify(bar0_handle, SDE_RX_CONTROL_REG, rx_control_value, rx_control_value, RCR_LOOPBACK_EN_MASK);
  fail_on(ret, err, "Unable to write and read RX_CONTROL_REG");

err:
  return ret;
}

int sde_hw_cfg_atg_mode(struct sde_hw_ctrl* ctrl, bool enable, uint32_t data, uint32_t pkt_size) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  pci_bar_handle_t bar0_handle = ctrl->bar0_handle;

  ret = poke_and_verify(bar0_handle, SDE_ATG0_DATA_REG, data, data, 0xffffffff);
  fail_on(ret, err, "Unable to write and read ATG0_DATA_REG");

  ret = poke_and_verify(bar0_handle, SDE_ATG1_DATA_REG, data, data, 0xffffffff);
  fail_on(ret, err, "Unable to write and read ATG1_DATA_REG");

  // atg_cfg_pkt_size is the pkt_size divided by 64, or right shifted by 6.
  uint32_t atg_cfg_pkt_size = pkt_size >> 6;
  ret = poke_and_verify(bar0_handle, SDE_ATG0_SIZE_REG, atg_cfg_pkt_size, atg_cfg_pkt_size, 0xffffffff);
  fail_on(ret, err, "Unable to write and read ATG0_SIZE_REG");

  ret = poke_and_verify(bar0_handle, SDE_ATG1_SIZE_REG, atg_cfg_pkt_size, atg_cfg_pkt_size, 0xffffffff);
  fail_on(ret, err, "Unable to write and read ATG1_SIZE_REG");

  ret = poke_and_verify(bar0_handle, SDE_ATG_TX_CTRL_REG, enable, enable, 0x7fffffff);
  fail_on(ret, err, "Unable to write and read ATG_TX_CTRL_REG");

err:
  return ret;
}

int sde_hw_cfg_c2h(struct sde_hw_ctrl* ctrl, uint64_t c2h_status_pa, uint64_t c2h_md_ring_pa, uint32_t c2h_md_ring_size) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  pci_bar_handle_t bar4_handle = ctrl->bar4_handle;

  uint32_t mask = 0xffffffff;

  uint32_t writes_to_coalesc = 8;
  uint32_t wb_cfg_value = C2H_WBCR_DESC_CDT_WB_EN_MASK | C2H_WBCR_DESC_CDT_WC_EN_MASK | C2H_WBCR_DESC_CNT_WC_EN_MASK | C2H_WBCR_PKT_CNT_WC_EN_MASK | C2H_WBCR_MD_WR_PTR_WC_EN_MASK;
  SDE_SET_BITFIELD(C2H_WBCR_WC_CNT_MINUS1, (writes_to_coalesc - 1), &wb_cfg_value);
  ret = poke_and_verify(bar4_handle, SDE_C2H_WRITEBACK_CFG_REG, wb_cfg_value, wb_cfg_value, mask);
  fail_on(ret, err, "Unable to write and read C2H_WRITEBACK_CFG_REG");

  uint32_t c2h_status_pa_lo = (uint32_t) (c2h_status_pa & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_C2H_STATUS_CNTRS_BADDR_LO_REG, c2h_status_pa_lo, c2h_status_pa_lo, mask);
  fail_on(ret, err, "Unable to write and read C2H_STATUS_CNTRS_BADDR_LO_REG");

  uint32_t c2h_status_pa_hi = (uint32_t) ((c2h_status_pa >> 32) & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_C2H_STATUS_CNTRS_BADDR_HI_REG, c2h_status_pa_hi, c2h_status_pa_hi, mask);
  fail_on(ret, err, "Unable to write and read C2H_STATUS_CNTRS_BADDR_HI_REG");

  uint32_t wc_to_tick_count = 0x40000;
  uint32_t tick_to_wc_count = 0xf;
  uint32_t coal_tmo_cnt_value = 0;
  SDE_SET_BITFIELD(C2H_WCTC_TICK_TO_WC_CNT, tick_to_wc_count, &coal_tmo_cnt_value);
  SDE_SET_BITFIELD(C2H_WCTC_WC_TO_TICK_CNT, wc_to_tick_count, &coal_tmo_cnt_value);
  ret = poke_and_verify(bar4_handle, SDE_C2H_WRITEBACK_COAL_TMO_CNT_REG, coal_tmo_cnt_value, coal_tmo_cnt_value, mask);
  fail_on(ret, err, "Unable to write and read C2H_WRITEBACK_COAL_TMO_CNT_REG");

  // Clear by writing 0
  ret = poke_and_verify(bar4_handle, SDE_C2H_DESCRIPTOR_CREDIT_CONSUMED_COUNTER_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear C2H_DESCRIPTOR_CREDIT_CONSUMED_COUNTER_REG");

  uint32_t c2h_descriptor_ram_depth = 0x40;
  ret = poke_and_verify(bar4_handle, SDE_C2H_DESCRIPTOR_CREDIT_LIMIT_COUNTER_REG, 0, c2h_descriptor_ram_depth, mask);
  fail_on(ret, err, "Unable to clear C2H_DESCRIPTOR_CREDIT_LIMIT_COUNTER_REG");

  ret = poke_and_verify(bar4_handle, SDE_C2H_COMPLETED_DESCRIPTOR_COUNTER_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear C2H_COMPLETED_DESCRIPTOR_COUNTER_REG");

  ret = poke_and_verify(bar4_handle, SDE_C2H_PACKET_COUNT_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear C2H_PACKET_COUNT_REG");

  uint32_t c2h_md_ring_pa_lo = (uint32_t) (c2h_md_ring_pa & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_C2H_MD_RING_BADDR_LO_REG, c2h_md_ring_pa_lo, c2h_md_ring_pa_lo, mask);
  fail_on(ret, err, "Unable to write and read C2H_MD_RING_BADDR_LO_REG");

  uint32_t c2h_md_ring_pa_hi = (uint32_t) ((c2h_md_ring_pa >> 32) & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_C2H_MD_RING_BADDR_HI_REG, c2h_md_ring_pa_hi, c2h_md_ring_pa_hi, mask);
  fail_on(ret, err, "Unable to write and read C2H_MD_RING_BADDR_HI_REG");

  ret = poke_and_verify(bar4_handle, SDE_C2H_MD_RING_SZ_REG, c2h_md_ring_size, c2h_md_ring_size, mask);
  fail_on(ret, err, "Unable to write and read C2H_MD_RING_SZ_REG");

  ret = poke_and_verify(bar4_handle, SDE_C2H_MD_RING_RD_PTR_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to write and read C2H_MD_RING_RD_PTR_REG");

  ret = poke_and_verify(bar4_handle, SDE_C2H_MD_RING_WR_PTR_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to write and read C2H_MD_RING_WR_PTR_REG");

err:
  return ret;
}

int sde_hw_cfg_h2c(struct sde_hw_ctrl* ctrl, uint64_t h2c_status_pa) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  pci_bar_handle_t bar4_handle = ctrl->bar4_handle;

  uint32_t mask = 0xffffffff;

  uint32_t writes_to_coalesc = 8;
  uint32_t h2c_wb_cfg_csr_value = H2C_WBCR_DESC_CDT_WB_EN_MASK | H2C_WBCR_DESC_CDT_WC_EN_MASK | H2C_WBCR_DESC_CNT_WC_EN_MASK | H2C_WBCR_PKT_CNT_WC_EN_MASK;
  SDE_SET_BITFIELD(H2C_WBCR_WC_CNT_MINUS1, (writes_to_coalesc - 1), &h2c_wb_cfg_csr_value);
  ret = poke_and_verify(bar4_handle, SDE_H2C_WRITEBACK_CFG_REG, h2c_wb_cfg_csr_value, h2c_wb_cfg_csr_value, mask);
  fail_on(ret, err, "Unable to write and read H2C_WRITEBACK_CFG_REG");

  uint32_t h2c_status_pa_lo = (uint32_t) (h2c_status_pa & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_H2C_STATUS_CNTRS_BADDR_LO_REG, h2c_status_pa_lo, h2c_status_pa_lo, mask);
  fail_on(ret, err, "Unable to write and read H2C_STATUS_CNTRS_BADDR_LO_REG");

  uint32_t h2c_status_pa_hi = (uint32_t) ((h2c_status_pa >> 32) & (uint64_t) 0xffffffff);
  ret = poke_and_verify(bar4_handle, SDE_H2C_STATUS_CNTRS_BADDR_HI_REG, h2c_status_pa_hi, h2c_status_pa_hi, mask);
  fail_on(ret, err, "Unable to write and read H2C_STATUS_CNTRS_BADDR_HI_REG");

  uint32_t wc_to_tick_count = 0x40000;
  uint32_t tick_to_wc_count = 0xf;
  uint32_t coal_tmo_cnt_value = 0;
  SDE_SET_BITFIELD(H2C_WCTC_WC_TO_TICK_CNT, wc_to_tick_count, &coal_tmo_cnt_value);
  SDE_SET_BITFIELD(H2C_WCTC_WC_TO_CNT, tick_to_wc_count, &coal_tmo_cnt_value);
  ret = poke_and_verify(bar4_handle, SDE_H2C_WRITEBACK_COAL_TMO_CNT_REG, coal_tmo_cnt_value, coal_tmo_cnt_value, mask);
  fail_on(ret, err, "Unable to write and read H2C_WRITEBACK_COAL_TMO_CNT_REG");

  // Clear by writing 0
  ret = poke_and_verify(bar4_handle, SDE_H2C_DESCRIPTOR_CREDIT_CONSUMED_COUNTER_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear H2C_DESCRIPTOR_CREDIT_CONSUMED_COUNTER_REG");

  uint32_t h2c_descriptor_ram_depth = 0x40;
  ret = poke_and_verify(bar4_handle, SDE_H2C_DESCRIPTOR_CREDIT_LIMIT_COUNTER_REG, 0, h2c_descriptor_ram_depth, mask);
  fail_on(ret, err, "Unable to clear H2C_DESCRIPTOR_CREDIT_LIMIT_COUNTER_REG");

  ret = poke_and_verify(bar4_handle, SDE_H2C_COMPLETED_DESCRIPTOR_COUNTER_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear H2C_COMPLETED_DESCRIPTOR_COUNTER_REG");

  ret = poke_and_verify(bar4_handle, SDE_H2C_PACKET_COUNT_REG, 0, 0, mask);
  fail_on(ret, err, "Unable to clear H2C_PACKET_COUNT_REG");

err:
  return ret;
}

int sde_hw_post_descriptor(struct sde_hw_ctrl* ctrl, uint64_t descriptor_va, size_t num_desc, enum SDE_SUBSYSTEM subsystem) {
  int ret = 0;

  fail_on_with_code(ctrl == NULL, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "ctrl is NULL");
  fail_on_with_code(!ctrl->initialized, err, ret, FPGA_ERR_SOFTWARE_PROBLEM, "SDE not initialized");

  size_t desc_element_size = (subsystem == SDE_SUBSYSTEM_C2H) ? sizeof(struct c2h_desc) : sizeof(struct h2c_desc);
  uint64_t descriptor_offset = (subsystem == SDE_SUBSYSTEM_C2H) ? SDE_C2H_DESC_RAM_MAP_OFFSET : SDE_H2C_DESC_RAM_MAP_OFFSET;

  pci_bar_handle_t bar4_handle = ctrl->bar4_handle;

  for (size_t desc_idx = 0; desc_idx < num_desc; ++desc_idx) {
    for (size_t dw_idx = 0; dw_idx < desc_element_size >> 2; ++dw_idx) {
      uint32_t* descriptor = (uint32_t*)(descriptor_va + desc_idx * desc_element_size + dw_idx * sizeof(uint32_t));
      ret = fpga_pci_poke(bar4_handle, descriptor_offset, *descriptor);
      fail_on(ret, err, "Unable to write descriptor");
    }
  }

err:
  return ret;
}
