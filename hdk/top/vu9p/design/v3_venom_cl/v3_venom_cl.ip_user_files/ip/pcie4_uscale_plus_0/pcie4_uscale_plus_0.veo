// (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
// DO NOT MODIFY THIS FILE.

// IP VLNV: xilinx.com:ip:pcie4_uscale_plus:1.1
// IP Revision: 2

// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG
pcie4_uscale_plus_0 your_instance_name (
  .pci_exp_txn(pci_exp_txn),                                                                      // output wire [15 : 0] pci_exp_txn
  .pci_exp_txp(pci_exp_txp),                                                                      // output wire [15 : 0] pci_exp_txp
  .pci_exp_rxn(pci_exp_rxn),                                                                      // input wire [15 : 0] pci_exp_rxn
  .pci_exp_rxp(pci_exp_rxp),                                                                      // input wire [15 : 0] pci_exp_rxp
  .user_clk(user_clk),                                                                            // output wire user_clk
  .user_reset(user_reset),                                                                        // output wire user_reset
  .user_lnk_up(user_lnk_up),                                                                      // output wire user_lnk_up
  .s_axis_rq_tdata(s_axis_rq_tdata),                                                              // input wire [511 : 0] s_axis_rq_tdata
  .s_axis_rq_tkeep(s_axis_rq_tkeep),                                                              // input wire [15 : 0] s_axis_rq_tkeep
  .s_axis_rq_tlast(s_axis_rq_tlast),                                                              // input wire s_axis_rq_tlast
  .s_axis_rq_tready(s_axis_rq_tready),                                                            // output wire [3 : 0] s_axis_rq_tready
  .s_axis_rq_tuser(s_axis_rq_tuser),                                                              // input wire [136 : 0] s_axis_rq_tuser
  .s_axis_rq_tvalid(s_axis_rq_tvalid),                                                            // input wire s_axis_rq_tvalid
  .m_axis_rc_tdata(m_axis_rc_tdata),                                                              // output wire [511 : 0] m_axis_rc_tdata
  .m_axis_rc_tkeep(m_axis_rc_tkeep),                                                              // output wire [15 : 0] m_axis_rc_tkeep
  .m_axis_rc_tlast(m_axis_rc_tlast),                                                              // output wire m_axis_rc_tlast
  .m_axis_rc_tready(m_axis_rc_tready),                                                            // input wire m_axis_rc_tready
  .m_axis_rc_tuser(m_axis_rc_tuser),                                                              // output wire [160 : 0] m_axis_rc_tuser
  .m_axis_rc_tvalid(m_axis_rc_tvalid),                                                            // output wire m_axis_rc_tvalid
  .m_axis_cq_tdata(m_axis_cq_tdata),                                                              // output wire [511 : 0] m_axis_cq_tdata
  .m_axis_cq_tkeep(m_axis_cq_tkeep),                                                              // output wire [15 : 0] m_axis_cq_tkeep
  .m_axis_cq_tlast(m_axis_cq_tlast),                                                              // output wire m_axis_cq_tlast
  .m_axis_cq_tready(m_axis_cq_tready),                                                            // input wire m_axis_cq_tready
  .m_axis_cq_tuser(m_axis_cq_tuser),                                                              // output wire [182 : 0] m_axis_cq_tuser
  .m_axis_cq_tvalid(m_axis_cq_tvalid),                                                            // output wire m_axis_cq_tvalid
  .s_axis_cc_tdata(s_axis_cc_tdata),                                                              // input wire [511 : 0] s_axis_cc_tdata
  .s_axis_cc_tkeep(s_axis_cc_tkeep),                                                              // input wire [15 : 0] s_axis_cc_tkeep
  .s_axis_cc_tlast(s_axis_cc_tlast),                                                              // input wire s_axis_cc_tlast
  .s_axis_cc_tready(s_axis_cc_tready),                                                            // output wire [3 : 0] s_axis_cc_tready
  .s_axis_cc_tuser(s_axis_cc_tuser),                                                              // input wire [80 : 0] s_axis_cc_tuser
  .s_axis_cc_tvalid(s_axis_cc_tvalid),                                                            // input wire s_axis_cc_tvalid
  .pcie_rq_seq_num0(pcie_rq_seq_num0),                                                            // output wire [5 : 0] pcie_rq_seq_num0
  .pcie_rq_seq_num_vld0(pcie_rq_seq_num_vld0),                                                    // output wire pcie_rq_seq_num_vld0
  .pcie_rq_seq_num1(pcie_rq_seq_num1),                                                            // output wire [5 : 0] pcie_rq_seq_num1
  .pcie_rq_seq_num_vld1(pcie_rq_seq_num_vld1),                                                    // output wire pcie_rq_seq_num_vld1
  .pcie_rq_tag0(pcie_rq_tag0),                                                                    // output wire [7 : 0] pcie_rq_tag0
  .pcie_rq_tag1(pcie_rq_tag1),                                                                    // output wire [7 : 0] pcie_rq_tag1
  .pcie_rq_tag_av(pcie_rq_tag_av),                                                                // output wire [3 : 0] pcie_rq_tag_av
  .pcie_rq_tag_vld0(pcie_rq_tag_vld0),                                                            // output wire pcie_rq_tag_vld0
  .pcie_rq_tag_vld1(pcie_rq_tag_vld1),                                                            // output wire pcie_rq_tag_vld1
  .pcie_tfc_nph_av(pcie_tfc_nph_av),                                                              // output wire [3 : 0] pcie_tfc_nph_av
  .pcie_tfc_npd_av(pcie_tfc_npd_av),                                                              // output wire [3 : 0] pcie_tfc_npd_av
  .pcie_cq_np_req(pcie_cq_np_req),                                                                // input wire [1 : 0] pcie_cq_np_req
  .pcie_cq_np_req_count(pcie_cq_np_req_count),                                                    // output wire [5 : 0] pcie_cq_np_req_count
  .cfg_phy_link_down(cfg_phy_link_down),                                                          // output wire cfg_phy_link_down
  .cfg_phy_link_status(cfg_phy_link_status),                                                      // output wire [1 : 0] cfg_phy_link_status
  .cfg_negotiated_width(cfg_negotiated_width),                                                    // output wire [2 : 0] cfg_negotiated_width
  .cfg_current_speed(cfg_current_speed),                                                          // output wire [1 : 0] cfg_current_speed
  .cfg_max_payload(cfg_max_payload),                                                              // output wire [1 : 0] cfg_max_payload
  .cfg_max_read_req(cfg_max_read_req),                                                            // output wire [2 : 0] cfg_max_read_req
  .cfg_function_status(cfg_function_status),                                                      // output wire [15 : 0] cfg_function_status
  .cfg_function_power_state(cfg_function_power_state),                                            // output wire [11 : 0] cfg_function_power_state
  .cfg_vf_status(cfg_vf_status),                                                                  // output wire [503 : 0] cfg_vf_status
  .cfg_vf_power_state(cfg_vf_power_state),                                                        // output wire [755 : 0] cfg_vf_power_state
  .cfg_link_power_state(cfg_link_power_state),                                                    // output wire [1 : 0] cfg_link_power_state
  .cfg_mgmt_addr(cfg_mgmt_addr),                                                                  // input wire [9 : 0] cfg_mgmt_addr
  .cfg_mgmt_function_number(cfg_mgmt_function_number),                                            // input wire [7 : 0] cfg_mgmt_function_number
  .cfg_mgmt_write(cfg_mgmt_write),                                                                // input wire cfg_mgmt_write
  .cfg_mgmt_write_data(cfg_mgmt_write_data),                                                      // input wire [31 : 0] cfg_mgmt_write_data
  .cfg_mgmt_byte_enable(cfg_mgmt_byte_enable),                                                    // input wire [3 : 0] cfg_mgmt_byte_enable
  .cfg_mgmt_read(cfg_mgmt_read),                                                                  // input wire cfg_mgmt_read
  .cfg_mgmt_read_data(cfg_mgmt_read_data),                                                        // output wire [31 : 0] cfg_mgmt_read_data
  .cfg_mgmt_read_write_done(cfg_mgmt_read_write_done),                                            // output wire cfg_mgmt_read_write_done
  .cfg_mgmt_debug_access(cfg_mgmt_debug_access),                                                  // input wire cfg_mgmt_debug_access
  .cfg_err_cor_out(cfg_err_cor_out),                                                              // output wire cfg_err_cor_out
  .cfg_err_nonfatal_out(cfg_err_nonfatal_out),                                                    // output wire cfg_err_nonfatal_out
  .cfg_err_fatal_out(cfg_err_fatal_out),                                                          // output wire cfg_err_fatal_out
  .cfg_local_error_valid(cfg_local_error_valid),                                                  // output wire cfg_local_error_valid
  .cfg_local_error_out(cfg_local_error_out),                                                      // output wire [4 : 0] cfg_local_error_out
  .cfg_ltssm_state(cfg_ltssm_state),                                                              // output wire [5 : 0] cfg_ltssm_state
  .cfg_rx_pm_state(cfg_rx_pm_state),                                                              // output wire [1 : 0] cfg_rx_pm_state
  .cfg_tx_pm_state(cfg_tx_pm_state),                                                              // output wire [1 : 0] cfg_tx_pm_state
  .cfg_rcb_status(cfg_rcb_status),                                                                // output wire [3 : 0] cfg_rcb_status
  .cfg_obff_enable(cfg_obff_enable),                                                              // output wire [1 : 0] cfg_obff_enable
  .cfg_pl_status_change(cfg_pl_status_change),                                                    // output wire cfg_pl_status_change
  .cfg_tph_requester_enable(cfg_tph_requester_enable),                                            // output wire [3 : 0] cfg_tph_requester_enable
  .cfg_tph_st_mode(cfg_tph_st_mode),                                                              // output wire [11 : 0] cfg_tph_st_mode
  .cfg_vf_tph_requester_enable(cfg_vf_tph_requester_enable),                                      // output wire [251 : 0] cfg_vf_tph_requester_enable
  .cfg_vf_tph_st_mode(cfg_vf_tph_st_mode),                                                        // output wire [755 : 0] cfg_vf_tph_st_mode
  .cfg_msg_received(cfg_msg_received),                                                            // output wire cfg_msg_received
  .cfg_msg_received_data(cfg_msg_received_data),                                                  // output wire [7 : 0] cfg_msg_received_data
  .cfg_msg_received_type(cfg_msg_received_type),                                                  // output wire [4 : 0] cfg_msg_received_type
  .cfg_msg_transmit(cfg_msg_transmit),                                                            // input wire cfg_msg_transmit
  .cfg_msg_transmit_type(cfg_msg_transmit_type),                                                  // input wire [2 : 0] cfg_msg_transmit_type
  .cfg_msg_transmit_data(cfg_msg_transmit_data),                                                  // input wire [31 : 0] cfg_msg_transmit_data
  .cfg_msg_transmit_done(cfg_msg_transmit_done),                                                  // output wire cfg_msg_transmit_done
  .cfg_fc_ph(cfg_fc_ph),                                                                          // output wire [7 : 0] cfg_fc_ph
  .cfg_fc_pd(cfg_fc_pd),                                                                          // output wire [11 : 0] cfg_fc_pd
  .cfg_fc_nph(cfg_fc_nph),                                                                        // output wire [7 : 0] cfg_fc_nph
  .cfg_fc_npd(cfg_fc_npd),                                                                        // output wire [11 : 0] cfg_fc_npd
  .cfg_fc_cplh(cfg_fc_cplh),                                                                      // output wire [7 : 0] cfg_fc_cplh
  .cfg_fc_cpld(cfg_fc_cpld),                                                                      // output wire [11 : 0] cfg_fc_cpld
  .cfg_fc_sel(cfg_fc_sel),                                                                        // input wire [2 : 0] cfg_fc_sel
  .cfg_dsn(cfg_dsn),                                                                              // input wire [63 : 0] cfg_dsn
  .cfg_bus_number(cfg_bus_number),                                                                // output wire [7 : 0] cfg_bus_number
  .cfg_power_state_change_ack(cfg_power_state_change_ack),                                        // input wire cfg_power_state_change_ack
  .cfg_power_state_change_interrupt(cfg_power_state_change_interrupt),                            // output wire cfg_power_state_change_interrupt
  .cfg_err_cor_in(cfg_err_cor_in),                                                                // input wire cfg_err_cor_in
  .cfg_err_uncor_in(cfg_err_uncor_in),                                                            // input wire cfg_err_uncor_in
  .cfg_flr_in_process(cfg_flr_in_process),                                                        // output wire [3 : 0] cfg_flr_in_process
  .cfg_flr_done(cfg_flr_done),                                                                    // input wire [3 : 0] cfg_flr_done
  .cfg_vf_flr_in_process(cfg_vf_flr_in_process),                                                  // output wire [251 : 0] cfg_vf_flr_in_process
  .cfg_vf_flr_func_num(cfg_vf_flr_func_num),                                                      // input wire [7 : 0] cfg_vf_flr_func_num
  .cfg_vf_flr_done(cfg_vf_flr_done),                                                              // input wire [0 : 0] cfg_vf_flr_done
  .cfg_link_training_enable(cfg_link_training_enable),                                            // input wire cfg_link_training_enable
  .cfg_ext_read_received(cfg_ext_read_received),                                                  // output wire cfg_ext_read_received
  .cfg_ext_write_received(cfg_ext_write_received),                                                // output wire cfg_ext_write_received
  .cfg_ext_register_number(cfg_ext_register_number),                                              // output wire [9 : 0] cfg_ext_register_number
  .cfg_ext_function_number(cfg_ext_function_number),                                              // output wire [7 : 0] cfg_ext_function_number
  .cfg_ext_write_data(cfg_ext_write_data),                                                        // output wire [31 : 0] cfg_ext_write_data
  .cfg_ext_write_byte_enable(cfg_ext_write_byte_enable),                                          // output wire [3 : 0] cfg_ext_write_byte_enable
  .cfg_ext_read_data(cfg_ext_read_data),                                                          // input wire [31 : 0] cfg_ext_read_data
  .cfg_ext_read_data_valid(cfg_ext_read_data_valid),                                              // input wire cfg_ext_read_data_valid
  .cfg_interrupt_int(cfg_interrupt_int),                                                          // input wire [3 : 0] cfg_interrupt_int
  .cfg_interrupt_pending(cfg_interrupt_pending),                                                  // input wire [3 : 0] cfg_interrupt_pending
  .cfg_interrupt_sent(cfg_interrupt_sent),                                                        // output wire cfg_interrupt_sent
  .cfg_interrupt_msi_enable(cfg_interrupt_msi_enable),                                            // output wire [3 : 0] cfg_interrupt_msi_enable
  .cfg_interrupt_msi_mmenable(cfg_interrupt_msi_mmenable),                                        // output wire [11 : 0] cfg_interrupt_msi_mmenable
  .cfg_interrupt_msi_mask_update(cfg_interrupt_msi_mask_update),                                  // output wire cfg_interrupt_msi_mask_update
  .cfg_interrupt_msi_data(cfg_interrupt_msi_data),                                                // output wire [31 : 0] cfg_interrupt_msi_data
  .cfg_interrupt_msi_select(cfg_interrupt_msi_select),                                            // input wire [1 : 0] cfg_interrupt_msi_select
  .cfg_interrupt_msi_int(cfg_interrupt_msi_int),                                                  // input wire [31 : 0] cfg_interrupt_msi_int
  .cfg_interrupt_msi_pending_status(cfg_interrupt_msi_pending_status),                            // input wire [31 : 0] cfg_interrupt_msi_pending_status
  .cfg_interrupt_msi_pending_status_data_enable(cfg_interrupt_msi_pending_status_data_enable),    // input wire cfg_interrupt_msi_pending_status_data_enable
  .cfg_interrupt_msi_pending_status_function_num(cfg_interrupt_msi_pending_status_function_num),  // input wire [1 : 0] cfg_interrupt_msi_pending_status_function_num
  .cfg_interrupt_msi_sent(cfg_interrupt_msi_sent),                                                // output wire cfg_interrupt_msi_sent
  .cfg_interrupt_msi_fail(cfg_interrupt_msi_fail),                                                // output wire cfg_interrupt_msi_fail
  .cfg_interrupt_msi_attr(cfg_interrupt_msi_attr),                                                // input wire [2 : 0] cfg_interrupt_msi_attr
  .cfg_interrupt_msi_tph_present(cfg_interrupt_msi_tph_present),                                  // input wire cfg_interrupt_msi_tph_present
  .cfg_interrupt_msi_tph_type(cfg_interrupt_msi_tph_type),                                        // input wire [1 : 0] cfg_interrupt_msi_tph_type
  .cfg_interrupt_msi_tph_st_tag(cfg_interrupt_msi_tph_st_tag),                                    // input wire [7 : 0] cfg_interrupt_msi_tph_st_tag
  .cfg_interrupt_msi_function_number(cfg_interrupt_msi_function_number),                          // input wire [7 : 0] cfg_interrupt_msi_function_number
  .cfg_interrupt_msix_enable(cfg_interrupt_msix_enable),                                          // output wire [3 : 0] cfg_interrupt_msix_enable
  .cfg_interrupt_msix_mask(cfg_interrupt_msix_mask),                                              // output wire [3 : 0] cfg_interrupt_msix_mask
  .cfg_interrupt_msix_vf_enable(cfg_interrupt_msix_vf_enable),                                    // output wire [251 : 0] cfg_interrupt_msix_vf_enable
  .cfg_interrupt_msix_vf_mask(cfg_interrupt_msix_vf_mask),                                        // output wire [251 : 0] cfg_interrupt_msix_vf_mask
  .cfg_pm_aspm_l1_entry_reject(cfg_pm_aspm_l1_entry_reject),                                      // input wire cfg_pm_aspm_l1_entry_reject
  .cfg_pm_aspm_tx_l0s_entry_disable(cfg_pm_aspm_tx_l0s_entry_disable),                            // input wire cfg_pm_aspm_tx_l0s_entry_disable
  .cfg_interrupt_msix_data(cfg_interrupt_msix_data),                                              // input wire [31 : 0] cfg_interrupt_msix_data
  .cfg_interrupt_msix_address(cfg_interrupt_msix_address),                                        // input wire [63 : 0] cfg_interrupt_msix_address
  .cfg_interrupt_msix_int(cfg_interrupt_msix_int),                                                // input wire cfg_interrupt_msix_int
  .cfg_interrupt_msix_vec_pending(cfg_interrupt_msix_vec_pending),                                // input wire [1 : 0] cfg_interrupt_msix_vec_pending
  .cfg_interrupt_msix_vec_pending_status(cfg_interrupt_msix_vec_pending_status),                  // output wire [0 : 0] cfg_interrupt_msix_vec_pending_status
  .cfg_hot_reset_out(cfg_hot_reset_out),                                                          // output wire cfg_hot_reset_out
  .cfg_config_space_enable(cfg_config_space_enable),                                              // input wire cfg_config_space_enable
  .cfg_req_pm_transition_l23_ready(cfg_req_pm_transition_l23_ready),                              // input wire cfg_req_pm_transition_l23_ready
  .cfg_hot_reset_in(cfg_hot_reset_in),                                                            // input wire cfg_hot_reset_in
  .cfg_ds_port_number(cfg_ds_port_number),                                                        // input wire [7 : 0] cfg_ds_port_number
  .cfg_ds_bus_number(cfg_ds_bus_number),                                                          // input wire [7 : 0] cfg_ds_bus_number
  .cfg_ds_device_number(cfg_ds_device_number),                                                    // input wire [4 : 0] cfg_ds_device_number
  .sys_clk(sys_clk),                                                                              // input wire sys_clk
  .sys_clk_gt(sys_clk_gt),                                                                        // input wire sys_clk_gt
  .sys_reset(sys_reset),                                                                          // input wire sys_reset
  .common_commands_in(common_commands_in),                                                        // input wire [25 : 0] common_commands_in
  .pipe_rx_0_sigs(pipe_rx_0_sigs),                                                                // input wire [83 : 0] pipe_rx_0_sigs
  .pipe_rx_1_sigs(pipe_rx_1_sigs),                                                                // input wire [83 : 0] pipe_rx_1_sigs
  .pipe_rx_2_sigs(pipe_rx_2_sigs),                                                                // input wire [83 : 0] pipe_rx_2_sigs
  .pipe_rx_3_sigs(pipe_rx_3_sigs),                                                                // input wire [83 : 0] pipe_rx_3_sigs
  .pipe_rx_4_sigs(pipe_rx_4_sigs),                                                                // input wire [83 : 0] pipe_rx_4_sigs
  .pipe_rx_5_sigs(pipe_rx_5_sigs),                                                                // input wire [83 : 0] pipe_rx_5_sigs
  .pipe_rx_6_sigs(pipe_rx_6_sigs),                                                                // input wire [83 : 0] pipe_rx_6_sigs
  .pipe_rx_7_sigs(pipe_rx_7_sigs),                                                                // input wire [83 : 0] pipe_rx_7_sigs
  .pipe_rx_8_sigs(pipe_rx_8_sigs),                                                                // input wire [83 : 0] pipe_rx_8_sigs
  .pipe_rx_9_sigs(pipe_rx_9_sigs),                                                                // input wire [83 : 0] pipe_rx_9_sigs
  .pipe_rx_10_sigs(pipe_rx_10_sigs),                                                              // input wire [83 : 0] pipe_rx_10_sigs
  .pipe_rx_11_sigs(pipe_rx_11_sigs),                                                              // input wire [83 : 0] pipe_rx_11_sigs
  .pipe_rx_12_sigs(pipe_rx_12_sigs),                                                              // input wire [83 : 0] pipe_rx_12_sigs
  .pipe_rx_13_sigs(pipe_rx_13_sigs),                                                              // input wire [83 : 0] pipe_rx_13_sigs
  .pipe_rx_14_sigs(pipe_rx_14_sigs),                                                              // input wire [83 : 0] pipe_rx_14_sigs
  .pipe_rx_15_sigs(pipe_rx_15_sigs),                                                              // input wire [83 : 0] pipe_rx_15_sigs
  .common_commands_out(common_commands_out),                                                      // output wire [25 : 0] common_commands_out
  .pipe_tx_0_sigs(pipe_tx_0_sigs),                                                                // output wire [83 : 0] pipe_tx_0_sigs
  .pipe_tx_1_sigs(pipe_tx_1_sigs),                                                                // output wire [83 : 0] pipe_tx_1_sigs
  .pipe_tx_2_sigs(pipe_tx_2_sigs),                                                                // output wire [83 : 0] pipe_tx_2_sigs
  .pipe_tx_3_sigs(pipe_tx_3_sigs),                                                                // output wire [83 : 0] pipe_tx_3_sigs
  .pipe_tx_4_sigs(pipe_tx_4_sigs),                                                                // output wire [83 : 0] pipe_tx_4_sigs
  .pipe_tx_5_sigs(pipe_tx_5_sigs),                                                                // output wire [83 : 0] pipe_tx_5_sigs
  .pipe_tx_6_sigs(pipe_tx_6_sigs),                                                                // output wire [83 : 0] pipe_tx_6_sigs
  .pipe_tx_7_sigs(pipe_tx_7_sigs),                                                                // output wire [83 : 0] pipe_tx_7_sigs
  .pipe_tx_8_sigs(pipe_tx_8_sigs),                                                                // output wire [83 : 0] pipe_tx_8_sigs
  .pipe_tx_9_sigs(pipe_tx_9_sigs),                                                                // output wire [83 : 0] pipe_tx_9_sigs
  .pipe_tx_10_sigs(pipe_tx_10_sigs),                                                              // output wire [83 : 0] pipe_tx_10_sigs
  .pipe_tx_11_sigs(pipe_tx_11_sigs),                                                              // output wire [83 : 0] pipe_tx_11_sigs
  .pipe_tx_12_sigs(pipe_tx_12_sigs),                                                              // output wire [83 : 0] pipe_tx_12_sigs
  .pipe_tx_13_sigs(pipe_tx_13_sigs),                                                              // output wire [83 : 0] pipe_tx_13_sigs
  .pipe_tx_14_sigs(pipe_tx_14_sigs),                                                              // output wire [83 : 0] pipe_tx_14_sigs
  .pipe_tx_15_sigs(pipe_tx_15_sigs)                                                              // output wire [83 : 0] pipe_tx_15_sigs
);
// INST_TAG_END ------ End INSTANTIATION Template ---------

// You must compile the wrapper file pcie4_uscale_plus_0.v when simulating
// the core, pcie4_uscale_plus_0. When compiling the wrapper file, be sure to
// reference the Verilog simulation library.

