# Amazon FPGA Hardware Development Kit
#
# Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


# Common CL Synthesis Tcl Script Footer


###############################################################################
print "Writing post-synth design checkpoint"
###############################################################################
write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_synth.dcp

# Check if the tool loaded calibration_ddr.elf file into DDR Controller BRAMs
#   NOTE: If BRAM Contents are not populated then the DDR will not calibrate on HW
#   TODO: Remove this once we discover why DDR is not calibrated by default
source ${HDK_SHELL_DIR}/build/scripts/check_ddr_bram.tcl

close_project

# Set param back to default value
#   NOTE: set in synth_cl_header.tcl
set_param sta.enableAutoGenClkNamePersistence 1
