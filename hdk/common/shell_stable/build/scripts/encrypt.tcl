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


# Remove any previously encrypted files, that may no longer be used
if {[llength [glob -nocomplain -dir ${src_post_enc_dir} *]] != 0} {
  eval file delete -force [glob ${src_post_enc_dir}/*]
}

foreach f [glob -directory ${HDK_SHELL_DESIGN_DIR}/interfaces *.inc] {
  file copy -force $f ${src_post_enc_dir}/
}

foreach f [glob -directory ${design_dir} *.{v,sv,vh,svh,inc}] {
  file copy -force $f ${src_post_enc_dir}/
}

exec chmod +w {*}[glob ${src_post_enc_dir}/*]

# encrypt .v/.sv/.vh/inc as verilog files
encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_keyfile.txt -lang verilog [glob -nocomplain -- ${src_post_enc_dir}/*.{v,sv,vh,inc}]

# encrypt *vhdl files
encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_vhdl_keyfile.txt -lang vhdl -quiet [ glob -nocomplain -- ${src_post_enc_dir}/*.vhd? ]
