## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+libext+.v
+libext+.sv
-sysv_ext +.vh
-vlogext verilog

$XILINX_VIVADO/data/verilog/src/glbl.v

-y $XILINX_VIVADO/data/verilog/src/unisims

+incdir+$XILINX_VIVADO/data/verilog/src
+incdir+${HDK_COMMON_DIR}/verif/models/sh_bfm
+incdir+${HDK_COMMON_DIR}/verif/models/fpga

-v $XILINX_VIVADO/data/verilog/src/unisim_retarget_comp.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/ddr.ies.f

${HDK_COMMON_DIR}/verif/models/xilinx_axi_pc/axi_protocol_checker_v1_1_vl_rfs.v

${HDK_COMMON_DIR}/verif/models/sh_bfm/axi_bfm_defines.svh
${HDK_COMMON_DIR}/verif/tb/sv/tb_type_defines_pkg.sv

${HDK_COMMON_DIR}/verif/models/sh_bfm/axil_bfm.sv
${HDK_COMMON_DIR}/verif/models/sh_bfm/sh_bfm.sv
${HDK_COMMON_DIR}/verif/models/fpga/fpga.sv
${HDK_COMMON_DIR}/verif/models/fpga/card.sv
${HDK_COMMON_DIR}/verif/tb/sv/tb.sv


