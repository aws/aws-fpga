## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

+libext+.v
+libext+.sv

$XILINX_VIVADO/data/verilog/src/glbl.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/ddr.questa.f

${HDK_COMMON_DIR}/verif/models/xilinx_axi_pc/axi_protocol_checker_v1_1_vl_rfs.v

${HDK_COMMON_DIR}/verif/models/sh_bfm/axi_bfm_defines.svh
${HDK_COMMON_DIR}/verif/tb/sv/tb_type_defines_pkg.sv

${HDK_COMMON_DIR}/verif/models/sh_bfm/sh_bfm.sv
${HDK_COMMON_DIR}/verif/models/sh_bfm/axil_bfm.sv
${HDK_COMMON_DIR}/verif/models/fpga/fpga.sv
${HDK_COMMON_DIR}/verif/models/fpga/card.sv
${HDK_COMMON_DIR}/verif/tb/sv/tb.sv


