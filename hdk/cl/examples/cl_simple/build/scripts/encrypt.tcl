## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## encrypt.tcl: Encrypt source code files
## =============================================================================

# TODO:
# Add check if CL_DIR and AWS_HDK_COMMON directories exist
# Add check if /build and /build/src_port_encryption directories exist
# Add check if the vivado_keyfile exist

##Convenience to set the root of the RTL directory
#set RTL_ORIGIN ../../../rtl

#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/cl_simple_defines.vh $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_simple.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_tst.sv .$CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_int_tst.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/mem_scrb.sv $CL_DIR/build/src_post_encryption
file copy -force $CL_DIR/design/cl_tst_scrb.sv $CL_DIR/build/src_post_encryption

encrypt -k $HDK_COMMON_DIR/vivado_keyfile.txt -lang verilog \
$CL_DIR/build/src_post_encryption/cl_simple_defines.vh \
$CL_DIR/build/src_post_encryption/cl_simple.sv \
$CL_DIR/build/src_post_encryption/cl_tst.sv  \
$CL_DIR/build/src_post_encryption/mem_scrb.sv  \
$CL_DIR/build/src_post_encryption/cl_tst_scrb.sv  \
$CL_DIR/build/src_post_encryption/cl_int_tst.sv  

#---- End of section replaced by Developr ---