## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

-y $XILINX_VIVADO/data/verilog/src/unisims
+incdir+$XILINX_VIVADO/data/verilog/src
$XILINX_VIVADO/data/verilog/src/glbl.v

-v $XILINX_VIVADO/data/secureip/gthe3_channel/gthe3_channel_001.vp
-v $XILINX_VIVADO/data/secureip/gthe3_channel/gthe3_channel_002.vp
-v $XILINX_VIVADO/data/secureip/gthe3_common/gthe3_common_001.vp
$XILINX_VIVADO/data/secureip/gthe3_common/gthe3_common_002.vp
-v $XILINX_VIVADO/data/secureip/pcie_3_1/pcie_3_1_001.vp
$XILINX_VIVADO/data/secureip/pcie_3_1/pcie_3_1_002.vp
-v $XILINX_VIVADO/data/secureip/gtye3_common/gtye3_common_001.vp
$XILINX_VIVADO/data/secureip/gtye3_common/gtye3_common_002.vp
-v $XILINX_VIVADO/data/secureip/gtye3_channel/gtye3_channel_001.vp
-v $XILINX_VIVADO/data/secureip/gtye3_channel/gtye3_channel_002.vp

$XILINX_VIVADO/data/ip/xpm/xpm_cdc/hdl/xpm_cdc.sv
