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


#---- Developr would replace this section with design files ----

## Change file names and paths below to reflect your CL area.  DO NOT include AWS RTL files.
file copy -force $CL_DIR/design/PUT_YOUR_FILE_NAME_HERE $CL_DIR/build/src_post_encryption


encrypt -k $HDK_COMMON_DIR/build/scripts/vivado_keyfile.txt -lang verilog \
$CL_DIR/build/src_post_encryption/PUT_YOUR_FIRST_FILE_NAME_HERE \
$CL_DIR/build/src_post_encryption/PUT_YOUR_LAST_FILE_NAME_HERE
