# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.


set HDK_SHELL_DIR $::env(HDK_COMMON_DIR)
set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)

set IS_DEFINE [get_property verilog_define [get_filesets sim_1]]

	if {$IS_DEFINE == ""} {
		set_property verilog_define "CL_NAME=cl_top TEST_NAME=test_cl" [get_filesets sim_1]
	}

add_files -fileset sim_1 [ list \
 ${HDK_SHELL_DESIGN_DIR}/ip/axi_register_slice/sim/axi_register_slice.v\
 ${HDK_SHELL_DIR}/verif/models/ddr4_model/ddr4_sdram_model_wrapper.sv\
 ${HDK_SHELL_DIR}/verif/models/sh_bfm/axi_bfm_defines.svh\
 ${HDK_SHELL_DIR}/verif/tb/sv/tb_type_defines_pkg.sv\
 ${HDK_SHELL_DIR}/verif/models/sh_bfm/sh_bfm.sv\
 ${HDK_SHELL_DIR}/verif/include/sh_dpi_tasks.svh\
 ${HDK_SHELL_DIR}/verif/models/sh_bfm/axil_bfm.sv\
 ${HDK_SHELL_DIR}/verif/models/fpga/fpga.sv\
 ${HDK_SHELL_DIR}/verif/models/fpga/card.sv\
 $::aws::make_faas::_nsvars::script_dir/../../verif/tb.sv\
]


add_files -fileset sim_1 [ list \
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_bi_delay.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_db_delay_model.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_dimm.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_dir_detect.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rank.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rcd_model.sv\
 ${HDK_SHELL_DIR}/verif/models/ddr4_rdimm_wrapper/ddr4_rdimm_wrapper.sv\
]


set_property top tb [get_filesets sim_1]
set_property top_lib xil_defaultlib [get_filesets sim_1]
