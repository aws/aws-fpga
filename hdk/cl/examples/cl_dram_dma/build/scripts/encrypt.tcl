## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## encrypt.tcl: Encrypt source code files
## =============================================================================

# TODO:
# Add check if CL_DIR and HDK_SHELL_DIR directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
set CL_DIR $::env(CL_DIR)

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/cl_dram_dma_defines.vh $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_dram_dma.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_tst.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_int_tst.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/mem_scrb.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_tst_scrb.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axil_slave.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/src_register_slice/src_register_slice.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/dest_register_slice/dest_register_slice.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_crossbar_0.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_register_slice_v2_1_vl_rfs.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_crossbar_v2_1_vl_rfs.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_data_fifo_v2_1_vl_rfs.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_infrastructure_v1_1_0.vh $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/axi_infrastructure_v1_1_vl_rfs.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/generic_baseblocks_v2_1_vl_rfs.v $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/axi_crossbar_0/fifo_generator_v13_1_rfs.v $CL_DIR/build/src_post_encryption


encrypt -k $HDK_SHELL_DIR/build/scripts/vivado_keyfile.txt -lang verilog \
$CL_DIR/build/src_post_encryption/cl_dram_dma_defines.vh \
$CL_DIR/build/src_post_encryption/cl_dram_dma.sv \
$CL_DIR/build/src_post_encryption/cl_tst.sv  \
$CL_DIR/build/src_post_encryption/mem_scrb.sv  \
$CL_DIR/build/src_post_encryption/cl_tst_scrb.sv  \
$CL_DIR/build/src_post_encryption/cl_int_tst.sv \
$CL_DIR/build/src_post_encryption/axil_slave.sv \
$CL_DIR/build/src_post_encryption/src_register_slice.v \
$CL_DIR/build/src_post_encryption/dest_register_slice.v \
$CL_DIR/build/src_post_encryption/axi_crossbar_0.v \
$CL_DIR/build/src_post_encryption/axi_register_slice_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_crossbar_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_data_fifo_v2_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/axi_infrastructure_v1_1_0.vh \
$CL_DIR/build/src_post_encryption/axi_infrastructure_v1_1_vl_rfs.v \
$CL_DIR/build/src_post_encryption/generic_baseblocks_v2_1_vl_rfs.v 
#$CL_DIR/build/src_post_encryption/fifo_generator_v13_1_rfs.v

#---- End of section replaced by Developr ---
