## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## encrypt.tcl: Encrypt source code files
## =============================================================================

##Convenience to set the root of the RTL directory
#set RTL_ORIGIN ../../../rtl

#---- User would replae this section with design files ----

## Change file names and paths below to reflect your user area.  DO NOT include AWS RTL files.
file copy -force $RTL_ORIGIN/cl/cl_simple_defines.vh ../src_post_encryption
file copy -force $RTL_ORIGIN/cl/cl_simple.sv ../src_post_encryption
file copy -force $RTL_ORIGIN/cl/cl_tst.sv ../src_post_encryption
file copy -force $RTL_ORIGIN/cl/cl_int_tst.sv ../src_post_encryption
file copy -force $RTL_ORIGIN/cl/mem_scrb.sv ../src_post_encryption
file copy -force $RTL_ORIGIN/cl/cl_tst_scrb.sv ../src_post_encryption

encrypt -k keyfile.txt -lang verilog \
../src_post_encryption/cl_simple_defines.vh \
../src_post_encryption/cl_simple.sv \
../src_post_encryption/cl_tst.sv  \
../src_post_encryption/mem_scrb.sv  \
../src_post_encryption/cl_tst_scrb.sv  \
../src_post_encryption/cl_int_tst.sv  

#---- End of section replaced by User ---
