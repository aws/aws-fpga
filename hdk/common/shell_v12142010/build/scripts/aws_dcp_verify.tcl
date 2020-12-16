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

# ################################################
# Emulate AWS Bitstream Generation
# ################################################
puts "AWS FPGA: Emulate AWS bitstream generation"

# Make temp dir for bitstream
file mkdir $CL_DIR/build/${timestamp}_aws_verify_temp_dir

# Verify the Developer DCP is compatible with SH_BB. 
pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp

open_checkpoint $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp

write_bitstream -force -bin_file $CL_DIR/build/${timestamp}_aws_verify_temp_dir/${timestamp}.SH_CL_final.bit

# Clean-up temp dir for bitstream
file delete -force $CL_DIR/build/${timestamp}_aws_verify_temp_dir

close_design


