## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+libext+.v
+libext+.sv

$XILINX_VIVADO/data/verilog/src/glbl.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/ddr.questa.f

${HDK_COMMON_DIR}/verif/models/sh_bfm/sh_bfm.sv
${HDK_COMMON_DIR}/verif/tb/sv/tb.sv


