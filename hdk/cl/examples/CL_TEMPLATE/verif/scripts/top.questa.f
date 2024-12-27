# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


+define+CL_NAME=CL_TEMPLATE
+define+DISABLE_VJTAG_DEBUG

# NOTE: Modifying the auto-generate block will break it
# Disable by defining `export DONT_GENERATE_FILE_LIST=1` before running `make`

##############################
#### BEGIN AUTO-GENERATE #####

+incdir+$CL_DIR/design/

$CL_DIR/design/CL_TEMPLATE.sv
$CL_DIR/design/cl_id_defines.vh

##### END AUTO-GENERATE ######
##############################

+incdir+$CL_DIR/verif/tests
-f $HDK_COMMON_DIR/verif/tb/filelists/tb.${SIMULATOR}.f
${TEST_NAME}
