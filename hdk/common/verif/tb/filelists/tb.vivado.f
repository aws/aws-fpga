## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-sourcelibext .v
-sourcelibext .sv

# -sourcelibdir /proj/awsip_scratch/f1/winefred/hdk_delivery/hdk_0p6a_vu9p/v3_venom_cl/v3_venom_cl.srcs/sources_1/imports/rtl/cl
# -sourcelibdir /proj/awsip_scratch/f1/winefred/hdk_delivery/hdk_0p6a_vu9p/v3_venom_cl/v3_venom_cl.srcs/sources_1/imports/rtl/mgt
# -sourcelibdir /proj/awsip_scratch/f1/winefred/hdk_delivery/hdk_0p6a_vu9p/v3_venom_cl/v3_venom_cl.srcs/sources_1/imports/rtl/sh
# -sourcelibdir /proj/awsip_scratch/f1/winefred/hdk_delivery/hdk_0p6a_vu9p/v3_venom_cl/v3_venom_cl.srcs/sources_1/imports/rtl/lib

$XILINX_VIVADO/data/verilog/src/glbl.v

-f ${HDK_COMMON_DIR}/verif/tb/filelists/ddr.vivado.f

${HDK_COMMON_DIR}/verif/models/sh_bfm/sh_bfm.sv
${HDK_COMMON_DIR}verif/tb/sv/tb.sv


