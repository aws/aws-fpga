## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+libext+.v
+libext+.sv

-y $XILINX_VIVADO/data/verilog/src/unisims
+incdir+$XILINX_VIVADO/data/verilog/src
+incdir+${HDK_COMMON_DIR}/verif/models/sh_bfm

$XILINX_VIVADO/data/verilog/src/glbl.v
-v $XILINX_VIVADO/data/verilog/src/unisim_retarget_comp.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/ddr.vcs.f

${HDK_COMMON_DIR}/verif/models/sh_bfm/axi_bfm_defines.svh

${HDK_COMMON_DIR}/verif/models/sh_bfm/axil_bfm.sv
${HDK_COMMON_DIR}/verif/models/sh_bfm/sh_bfm.sv
${HDK_COMMON_DIR}/verif/tb/sv/tb.sv


