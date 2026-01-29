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

# FireSim Note: This script copies source files to the post-encryption directory
# WITHOUT actually encrypting them. This allows FireSim to keep timing reports
# and checkpoint names readable while maintaining compatibility with AWS build flow
# that expects files in the src_post_encryption directory.

# Define required variables from environment and script context
set CL_DIR $::env(CL_DIR)
set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)
set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)

# Set directory paths
set src_post_enc_dir $CL_DIR/build/src_post_encryption
set design_dir $CL_DIR/design

# Create the target directory if it doesn't exist
file mkdir $src_post_enc_dir

# Remove any previously copied files that may no longer be used
if {[llength [glob -nocomplain -dir ${src_post_enc_dir} *]] != 0} {
  eval file delete -force [glob ${src_post_enc_dir}/*]
}

# Copy shell interface files
foreach f [glob -directory ${HDK_SHELL_DESIGN_DIR}/interfaces *.inc] {
  file copy -force $f ${src_post_enc_dir}/
}

# Copy all design source files (Verilog, SystemVerilog, headers)
foreach f [glob -directory ${design_dir} *.{v,sv,vh,svh,inc}] {
  file copy -force $f ${src_post_enc_dir}/
}

# Make files writable
exec chmod +w {*}[glob ${src_post_enc_dir}/*]

# FireSim Note: Original AWS flow would encrypt files here using:
# encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_keyfile.txt -lang verilog [glob -nocomplain -- ${src_post_enc_dir}/*.{v,sv,vh,inc}]
# encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_vhdl_keyfile.txt -lang vhdl -quiet [ glob -nocomplain -- ${src_post_enc_dir}/*.vhd? ]
#
# We skip encryption to keep names readable in timing reports and checkpoints.
# The files are already copied to where the build flow expects them.

puts "AWS FPGA: Copied source files to ${src_post_enc_dir} (encryption skipped for FireSim)"
