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

# TODO:
# Add check if CL_DIR and HDK_SHELL_DIR directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
set HDK_SHELL_DESIGN_DIR $::env(HDK_SHELL_DESIGN_DIR)
set CL_DIR $::env(CL_DIR)

set TARGET_DIR $CL_DIR/build/src_post_encryption
set UNUSED_TEMPLATES_DIR $HDK_SHELL_DESIGN_DIR/interfaces


# Remove any previously encrypted files, that may no longer be used
exec rm -f $TARGET_DIR/*

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.

file copy -force $CL_DIR/../common/design/cl_common_defines.vh       $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_flr_template.inc       $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_a_b_d_template.inc $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_ddr_c_template.inc     $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_cl_sda_template.inc    $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_sh_bar1_template.inc   $TARGET_DIR
file copy -force $UNUSED_TEMPLATES_DIR/unused_apppf_irq_template.inc $TARGET_DIR

file copy -force $CL_DIR/lib/bram_1w1r.sv    $TARGET_DIR
file copy -force $CL_DIR/lib/flop_fifo_in.sv $TARGET_DIR
file copy -force $CL_DIR/lib/ft_fifo.v       $TARGET_DIR
file copy -force $CL_DIR/lib/ft_fifo_p.v     $TARGET_DIR
file copy -force $CL_DIR/lib/rr_arb.sv       $TARGET_DIR
file copy -force $CL_DIR/lib/axis_flop_fifo.sv $TARGET_DIR
file copy -force $CL_DIR/lib/ram_fifo_ft.sv    $TARGET_DIR

file copy -force $CL_DIR/design/ila_axi4_wrapper.sv $TARGET_DIR

file copy -force $CL_DIR/design/sde_pkg.sv      $TARGET_DIR
file copy -force $CL_DIR/design/sde.sv          $TARGET_DIR
file copy -force $CL_DIR/design/sde_c2h.sv      $TARGET_DIR
file copy -force $CL_DIR/design/sde_c2h_axis.sv $TARGET_DIR
file copy -force $CL_DIR/design/sde_c2h_buf.sv  $TARGET_DIR
file copy -force $CL_DIR/design/sde_c2h_cfg.sv  $TARGET_DIR
file copy -force $CL_DIR/design/sde_c2h_data.sv $TARGET_DIR
file copy -force $CL_DIR/design/sde_h2c.sv      $TARGET_DIR
file copy -force $CL_DIR/design/sde_h2c_axis.sv $TARGET_DIR
file copy -force $CL_DIR/design/sde_h2c_buf.sv  $TARGET_DIR
file copy -force $CL_DIR/design/sde_h2c_cfg.sv  $TARGET_DIR
file copy -force $CL_DIR/design/sde_h2c_data.sv $TARGET_DIR
file copy -force $CL_DIR/design/sde_wb.sv       $TARGET_DIR
file copy -force $CL_DIR/design/sde_desc.sv     $TARGET_DIR
file copy -force $CL_DIR/design/sde_pm.sv       $TARGET_DIR
file copy -force $CL_DIR/design/sde_ps_acc.sv   $TARGET_DIR
file copy -force $CL_DIR/design/sde_ps.sv       $TARGET_DIR

file copy -force $CL_DIR/design/cl_id_defines.vh   $TARGET_DIR
file copy -force $CL_DIR/design/cl_pkt_tst.sv $TARGET_DIR
file copy -force $CL_DIR/design/cl_tst.sv     $TARGET_DIR
file copy -force $CL_DIR/design/cl_sde_srm.sv      $TARGET_DIR
file copy -force $CL_DIR/design/cl_sde.sv          $TARGET_DIR
file copy -force $CL_DIR/design/axi_prot_chk.sv    $TARGET_DIR

#---- End of section replaced by Developr ---



# Make sure files have write permissions for the encryption

exec chmod +w {*}[glob $TARGET_DIR/*]

# encrypt .v/.sv/.vh/inc as verilog files
#encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_keyfile.txt -lang verilog  [glob -nocomplain -- $TARGET_DIR/*.{v,sv}] [glob -nocomplain -- $TARGET_DIR/*.vh] [glob -nocomplain -- $TARGET_DIR/*.inc]

# encrypt *vhdl files
#encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_vhdl_keyfile.txt -lang vhdl -quiet [ glob -nocomplain -- $TARGET_DIR/*.vhd? ]

