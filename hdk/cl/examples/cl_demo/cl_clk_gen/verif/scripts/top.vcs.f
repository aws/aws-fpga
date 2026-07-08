# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


+define+CL_NAME=cl_clk_gen
+define+NO_CL_CLK_GEN_ILA
+define+DISABLE_VJTAG_DEBUG

+incdir+$CL_DIR/verif/tests
-f $HDK_COMMON_DIR/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}

+incdir+$CL_DIR/design
$CL_DIR/design/cl_id_defines.vh
$CL_DIR/design/cl_clk_gen_defines.vh
$CL_DIR/design/cl_axil_adder.sv
$CL_DIR/design/cl_clk_gen.sv
