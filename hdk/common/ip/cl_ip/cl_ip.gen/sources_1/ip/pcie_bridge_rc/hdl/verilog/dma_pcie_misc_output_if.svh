`ifndef IF_PCIE_DMA_MISC_OUTPUT_SV
`define IF_PCIE_DMA_MISC_OUTPUT_SV

interface dma_pcie_misc_output_if();
logic  [2:0]       cfg_fc_sel;
logic  [1:0]       pcie_cq_np_req;
logic  [18:0]      cfg_mgmt_addr;
logic              cfg_mgmt_write;
logic  [31:0]      cfg_mgmt_write_data;
logic  [3:0]       cfg_mgmt_byte_enable;
logic              cfg_mgmt_read;
logic  [7:0]       cfg_mgmt_function_number;
logic              cfg_mgmt_type1_cfg_reg_access;
logic  [7:0]       cfg_ds_port_number;
logic  [7:0]       cfg_ds_bus_number;
logic  [4:0]       cfg_ds_device_number;
logic  [2:0]       cfg_ds_function_number;
logic  [2:0]       cfg_per_func_status_control;
logic  [6:0]       cfg_per_function_number;
logic              cfg_per_function_output_request;
logic              cfg_per_function_logic_request;
logic              cfg_msg_transmit;
logic  [2:0]       cfg_msg_transmit_type;
logic  [31:0]      cfg_msg_transmit_data;
//logic  [15:0]      cfg_subsys_id;
//logic  [15:0]      cfg_subsys_vend_id;
//logic  [15:0]      cfg_vend_id;
logic  [63:0]      cfg_dsn;
logic              cfg_err_cor_in;
logic              cfg_err_uncor_in;
logic              cfg_link_training_enable;
logic  [31:0]      cfg_ext_read_data;
logic              cfg_ext_read_data_valid;
logic  [3:0]       cfg_flr_done;
logic              cfg_vf_flr_done;
logic  [7:0]       cfg_vf_flr_func_num;
logic              cfg_config_space_enable;
logic              cfg_hot_reset_in;
logic  [31:0]      cfg_interrupt_msi_int;
logic  [31:0]      cfg_interrupt_msi_pending_status;
logic              cfg_interrupt_msi_pending_status_data_enable;
logic  [3:0]       cfg_interrupt_msi_pending_status_function_num;
logic  [2:0]       cfg_interrupt_msi_attr;
logic              cfg_interrupt_msi_tph_present;
logic  [1:0]       cfg_interrupt_msi_tph_type;
logic  [8:0]       cfg_interrupt_msi_tph_st_tag;
logic  [3:0]       cfg_interrupt_msi_function_number;
logic              cfg_interrupt_msix_int;
logic  [31:0]      cfg_interrupt_msix_data;
logic  [255:0]     cfg_interrupt_msix_address;
logic  [3:0]       cfg_interrupt_int;
logic  [3:0]       cfg_interrupt_pending;

modport m (
output      cfg_fc_sel,
output      pcie_cq_np_req,
output      cfg_mgmt_addr,
output      cfg_mgmt_write,
output      cfg_mgmt_write_data,
output      cfg_mgmt_byte_enable,
output      cfg_mgmt_read,
output      cfg_mgmt_function_number,
output      cfg_mgmt_type1_cfg_reg_access,
output      cfg_ds_port_number,
output      cfg_ds_bus_number,
output      cfg_ds_device_number,
output      cfg_ds_function_number,
output      cfg_per_function_output_request,
output      cfg_per_function_logic_request,
output      cfg_per_func_status_control,
output      cfg_per_function_number,
output      cfg_msg_transmit,
output      cfg_msg_transmit_type,
output      cfg_msg_transmit_data,
//output      cfg_rev_id,
//output      cfg_subsys_id,
//output      cfg_subsys_vend_id,
//output      cfg_vend_id,
output      cfg_dsn,
output      cfg_err_cor_in,
output      cfg_err_uncor_in,
output      cfg_link_training_enable,
output      cfg_ext_read_data,
output      cfg_ext_read_data_valid,
output      cfg_flr_done,
output      cfg_vf_flr_done,
output      cfg_vf_flr_func_num,
output      cfg_config_space_enable,
output      cfg_hot_reset_in,
output      cfg_interrupt_msi_int,
output      cfg_interrupt_msi_pending_status,
output      cfg_interrupt_msi_pending_status_data_enable,
output      cfg_interrupt_msi_pending_status_function_num,
output      cfg_interrupt_msi_attr,
output      cfg_interrupt_msi_tph_present,
output      cfg_interrupt_msi_tph_type,
output      cfg_interrupt_msi_tph_st_tag,
output      cfg_interrupt_msi_function_number,
output      cfg_interrupt_msix_int,
output      cfg_interrupt_msix_data,
output      cfg_interrupt_msix_address,
output      cfg_interrupt_int,
output      cfg_interrupt_pending
);

modport s (
input      cfg_fc_sel,
input      pcie_cq_np_req,
input      cfg_mgmt_addr,
input      cfg_mgmt_write,
input      cfg_mgmt_write_data,
input      cfg_mgmt_byte_enable,
input      cfg_mgmt_read,
input      cfg_mgmt_function_number,
input      cfg_mgmt_type1_cfg_reg_access,
input      cfg_ds_port_number,
input      cfg_ds_bus_number,
input      cfg_ds_device_number,
input      cfg_ds_function_number,
input      cfg_per_func_status_control,
input      cfg_per_function_number,
input      cfg_per_function_output_request,
input      cfg_per_function_logic_request,
input      cfg_msg_transmit,
input      cfg_msg_transmit_type,
input      cfg_msg_transmit_data,
//input      cfg_rev_id,
//input      cfg_subsys_id,
//input      cfg_subsys_vend_id,
//input      cfg_vend_id,
input      cfg_dsn,
input      cfg_err_cor_in,
input      cfg_err_uncor_in,
input      cfg_link_training_enable,
input      cfg_ext_read_data,
input      cfg_ext_read_data_valid,
input      cfg_flr_done,
input      cfg_vf_flr_done,
input      cfg_vf_flr_func_num,
input      cfg_config_space_enable,
input      cfg_hot_reset_in,
input      cfg_interrupt_msi_int,
input      cfg_interrupt_msi_pending_status,
input      cfg_interrupt_msi_pending_status_data_enable,
input      cfg_interrupt_msi_pending_status_function_num,
input      cfg_interrupt_msi_attr,
input      cfg_interrupt_msi_tph_present,
input      cfg_interrupt_msi_tph_type,
input      cfg_interrupt_msi_tph_st_tag,
input      cfg_interrupt_msi_function_number,
input      cfg_interrupt_msix_int,
input      cfg_interrupt_msix_data,
input      cfg_interrupt_msix_address,
input      cfg_interrupt_int,
input      cfg_interrupt_pending
);
endinterface : dma_pcie_misc_output_if
`endif
