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


# TODO:
# Add check if CL_DIR and HDK_SHELL_DIR directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

set TARGET_DIR $scripts_dir/../src_post_encryption
set UNUSED_TEMPLATES_DIR $HDK_SHELL_DESIGN_DIR/interfaces


# Remove any previously encrypted files, that may no longer be used
if {[llength [glob -nocomplain -dir $TARGET_DIR *]] != 0} {
  eval file delete -force [glob $TARGET_DIR/*]
}

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/cl_axi_ctl.sv                      $TARGET_DIR
file copy -force $CL_DIR/design/cl_kernel_ctl.sv                   $TARGET_DIR
file copy -force $CL_DIR/design/cl_kernel_regs.sv                  $TARGET_DIR
file copy -force $CL_DIR/design/cl_kernel_req.sv                   $TARGET_DIR
file copy -force $CL_DIR/design/cl_clk_freq.sv                     $TARGET_DIR
file copy -force $CL_DIR/design/cl_hbm_perf_kernel.sv              $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_hbm_axi4.sv                 $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_hbm_wrapper.sv              $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_ocl_dec.sv                  $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_pcis_dec.sv                 $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_perf_defines.vh             $TARGET_DIR
file copy -force $CL_DIR/design/cl_id_defines.vh                   $TARGET_DIR
file copy -force $CL_DIR/design/cl_mem_perf.sv                     $TARGET_DIR

# RTL source from CL_DRAM_HBM_DMA
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_tst.sv               $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_int_tst.sv           $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/mem_scrb.sv             $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_tst_scrb.sv          $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/axil_slave.sv           $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_int_slv.sv           $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_pcim_mstr.sv         $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_vio.sv               $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_ila.sv               $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_sda_slv.sv           $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_dram_dma_axi_mstr.sv $TARGET_DIR
file copy -force $CL_DIR/../cl_dram_hbm_dma/design/cl_dram_dma_pkg.sv      $TARGET_DIR

#---- End of section replaced by Developr ---



# Make sure files have write permissions for the encryption

exec chmod +w {*}[glob $TARGET_DIR/*]

set TOOL_VERSION $::env(VIVADO_TOOL_VERSION)
set vivado_version [string range [version -short] 0 5]
puts "AWS FPGA: VIVADO_TOOL_VERSION $TOOL_VERSION"
puts "vivado_version $vivado_version"

#NOTE: Uncomment below to encrypt source files
# encrypt .v/.sv/.vh/inc as verilog files
encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_keyfile.txt -lang verilog  [glob -nocomplain -- $TARGET_DIR/*.{v,sv,vh,inc}]

# encrypt *vhdl files
encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_vhdl_keyfile.txt -lang vhdl -quiet [ glob -nocomplain -- $TARGET_DIR/*.vhd? ]
