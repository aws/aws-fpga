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

-define CL_NAME=cl_sde
-define NO_SDE_DEBUG_ILA
-define DISABLE_VJTAG_DEBUG

-include $CL_DIR/verif/tests
-f $HDK_COMMON_DIR/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

-include $CL_DIR/design
$CL_DIR/design/cl_id_defines.vh
$CL_DIR/design/sde_pkg.sv
$CL_DIR/design/cl_pkt_tst.sv
$CL_DIR/design/ila_axi4_wrapper.sv
$CL_DIR/design/axi_prot_chk.sv
$CL_DIR/design/cl_tst.sv
$CL_DIR/design/cl_sde_srm.sv
$CL_DIR/design/sde_c2h_axis.sv
$CL_DIR/design/sde_c2h_buf.sv
$CL_DIR/design/sde_c2h_cfg.sv
$CL_DIR/design/sde_c2h_data.sv
$CL_DIR/design/sde_c2h.sv
$CL_DIR/design/sde_h2c_axis.sv
$CL_DIR/design/sde_h2c_buf.sv
$CL_DIR/design/sde_h2c_cfg.sv
$CL_DIR/design/sde_h2c_data.sv
$CL_DIR/design/sde_h2c.sv
$CL_DIR/design/sde_pm.sv
$CL_DIR/design/sde_ps_acc.sv
$CL_DIR/design/sde_ps.sv
$CL_DIR/design/sde_wb.sv
$CL_DIR/design/sde_desc.sv
$CL_DIR/design/sde.sv
$CL_DIR/design/cl_sde.sv
