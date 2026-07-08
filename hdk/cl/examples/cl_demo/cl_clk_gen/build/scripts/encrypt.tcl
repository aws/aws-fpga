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

# Remove any previously encrypted files, that may no longer be used
if {[llength [glob -nocomplain -dir $src_post_enc_dir *]] != 0} {
  eval file delete -force [glob $src_post_enc_dir/*]
}

#---- Developer would replace this section with design files ----
set UNUSED_TEMPLATES_DIR $HDK_SHELL_DESIGN_DIR/interfaces

file copy -force $UNUSED_TEMPLATES_DIR/unused_flr_template.inc        $src_post_enc_dir
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_template.inc        $src_post_enc_dir
file copy -force $UNUSED_TEMPLATES_DIR/unused_apppf_irq_template.inc  $src_post_enc_dir
file copy -force $UNUSED_TEMPLATES_DIR/unused_dma_pcis_template.inc   $src_post_enc_dir
file copy -force $UNUSED_TEMPLATES_DIR/unused_pcim_template.inc       $src_post_enc_dir

file copy -force $CL_DIR/design/cl_id_defines.vh                      $src_post_enc_dir
file copy -force $CL_DIR/design/cl_clk_gen_defines.vh                $src_post_enc_dir
file copy -force $CL_DIR/design/cl_axil_adder.sv                      $src_post_enc_dir
file copy -force $CL_DIR/design/cl_clk_gen.sv                        $src_post_enc_dir

#---- End of section replaced by Developer ---

# Make sure files have write permissions for the encryption
exec chmod +w {*}[glob ${src_post_enc_dir}/*]

# Optional encryption
if {$ENCRYPT} {
  print "Encryption enabled. Encrypting HDL files and DCPs."
  encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_keyfile.txt      -lang verilog -quiet [glob -nocomplain -- ${src_post_enc_dir}/*.{v,sv,vh,inc}]
  encrypt -k ${HDK_SHELL_DIR}/build/scripts/vivado_vhdl_keyfile.txt -lang vhdl    -quiet [glob -nocomplain -- ${src_post_enc_dir}/*.vhd?]
} else {
  print "Encryption disabled."
}
