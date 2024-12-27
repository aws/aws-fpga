# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.
# =============================================================================


# CL pin constraints


###############################################################################
# DDR4 DIMM
###############################################################################
set_property PACKAGE_PIN F35          [get_ports CLK_DIMM_DP]
set_property IOSTANDARD  DIFF_SSTL12  [get_ports {CLK_DIMM_D*}]
set_property ODT         RTT_48       [get_ports {CLK_DIMM_D*}]

set_property PACKAGE_PIN G37          [get_ports RST_DIMM_N]
set_property IOSTANDARD  LVCMOS12     [get_ports RST_DIMM_N]
set_property DRIVE       8            [get_ports RST_DIMM_N]

set_property PACKAGE_PIN D34          [get_ports {M_CLK_DP[0]}]
set_property PACKAGE_PIN C34          [get_ports {M_CLK_DN[0]}]
set_property PACKAGE_PIN C37          [get_ports {M_CLK_DP[1]}]
set_property PACKAGE_PIN B38          [get_ports {M_CLK_DN[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_CLK_DP[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_CLK_DN[1]}]

set_property PACKAGE_PIN H35          [get_ports {M_CKE[0]}]
set_property PACKAGE_PIN G38          [get_ports {M_CKE[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_CKE[*]}]

set_property PACKAGE_PIN H38          [get_ports {M_CS_N[0]}]
set_property PACKAGE_PIN H34          [get_ports {M_CS_N[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_CS_N[*]}]

set_property PACKAGE_PIN F39          [get_ports {M_ODT[0]}]
set_property PACKAGE_PIN G35          [get_ports {M_ODT[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_ODT[*]}]

set_property PACKAGE_PIN F38          [get_ports M_PAR]
set_property IOSTANDARD  SSTL12_DCI   [get_ports M_PAR]

set_property PACKAGE_PIN G36          [get_ports M_ACT_N]
set_property IOSTANDARD  SSTL12_DCI   [get_ports M_ACT_N]

set_property PACKAGE_PIN C35          [get_ports {M_MA[0]}]
set_property PACKAGE_PIN B36          [get_ports {M_MA[1]}]
set_property PACKAGE_PIN B37          [get_ports {M_MA[2]}]
set_property PACKAGE_PIN A38          [get_ports {M_MA[3]}]
set_property PACKAGE_PIN B35          [get_ports {M_MA[4]}]
set_property PACKAGE_PIN A36          [get_ports {M_MA[5]}]
set_property PACKAGE_PIN A34          [get_ports {M_MA[6]}]
set_property PACKAGE_PIN A35          [get_ports {M_MA[7]}]
set_property PACKAGE_PIN E37          [get_ports {M_MA[8]}]
set_property PACKAGE_PIN E38          [get_ports {M_MA[9]}]
set_property PACKAGE_PIN D35          [get_ports {M_MA[10]}]
set_property PACKAGE_PIN D36          [get_ports {M_MA[11]}]
set_property PACKAGE_PIN E39          [get_ports {M_MA[12]}]
set_property PACKAGE_PIN D39          [get_ports {M_MA[13]}]
set_property PACKAGE_PIN F34          [get_ports {M_MA[14]}]
set_property PACKAGE_PIN E34          [get_ports {M_MA[15]}]
set_property PACKAGE_PIN E36          [get_ports {M_MA[16]}]
set_property PACKAGE_PIN C39          [get_ports {M_MA[17]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_MA[*]}]

set_property PACKAGE_PIN D37          [get_ports {M_BA[0]}]
set_property PACKAGE_PIN J39          [get_ports {M_BA[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_BA[*]}]

set_property PACKAGE_PIN H39          [get_ports {M_BG[0]}]
set_property PACKAGE_PIN H37          [get_ports {M_BG[1]}]
set_property IOSTANDARD  SSTL12_DCI   [get_ports {M_BG[*]}]

set_property PACKAGE_PIN J30          [get_ports {M_DQ[0]}]
set_property PACKAGE_PIN J31          [get_ports {M_DQ[1]}]
set_property PACKAGE_PIN K29          [get_ports {M_DQ[2]}]
set_property PACKAGE_PIN J29          [get_ports {M_DQ[3]}]
set_property PACKAGE_PIN L29          [get_ports {M_DQ[4]}]
set_property PACKAGE_PIN L30          [get_ports {M_DQ[5]}]
set_property PACKAGE_PIN L31          [get_ports {M_DQ[6]}]
set_property PACKAGE_PIN K31          [get_ports {M_DQ[7]}]
set_property PACKAGE_PIN H29          [get_ports {M_DQ[8]}]
set_property PACKAGE_PIN H30          [get_ports {M_DQ[9]}]
set_property PACKAGE_PIN H32          [get_ports {M_DQ[10]}]
set_property PACKAGE_PIN G32          [get_ports {M_DQ[11]}]
set_property PACKAGE_PIN G31          [get_ports {M_DQ[12]}]
set_property PACKAGE_PIN F31          [get_ports {M_DQ[13]}]
set_property PACKAGE_PIN F30          [get_ports {M_DQ[14]}]
set_property PACKAGE_PIN G30          [get_ports {M_DQ[15]}]
set_property PACKAGE_PIN L34          [get_ports {M_DQ[16]}]
set_property PACKAGE_PIN K34          [get_ports {M_DQ[17]}]
set_property PACKAGE_PIN K37          [get_ports {M_DQ[18]}]
set_property PACKAGE_PIN J37          [get_ports {M_DQ[19]}]
set_property PACKAGE_PIN L39          [get_ports {M_DQ[20]}]
set_property PACKAGE_PIN K39          [get_ports {M_DQ[21]}]
set_property PACKAGE_PIN K36          [get_ports {M_DQ[22]}]
set_property PACKAGE_PIN J36          [get_ports {M_DQ[23]}]
set_property PACKAGE_PIN A29          [get_ports {M_DQ[24]}]
set_property PACKAGE_PIN A30          [get_ports {M_DQ[25]}]
set_property PACKAGE_PIN B28          [get_ports {M_DQ[26]}]
set_property PACKAGE_PIN A28          [get_ports {M_DQ[27]}]
set_property PACKAGE_PIN C28          [get_ports {M_DQ[28]}]
set_property PACKAGE_PIN C29          [get_ports {M_DQ[29]}]
set_property PACKAGE_PIN B32          [get_ports {M_DQ[30]}]
set_property PACKAGE_PIN A33          [get_ports {M_DQ[31]}]
set_property PACKAGE_PIN G41          [get_ports {M_DQ[32]}]
set_property PACKAGE_PIN G42          [get_ports {M_DQ[33]}]
set_property PACKAGE_PIN G43          [get_ports {M_DQ[34]}]
set_property PACKAGE_PIN H43          [get_ports {M_DQ[35]}]
set_property PACKAGE_PIN J40          [get_ports {M_DQ[36]}]
set_property PACKAGE_PIN J41          [get_ports {M_DQ[37]}]
set_property PACKAGE_PIN H42          [get_ports {M_DQ[38]}]
set_property PACKAGE_PIN J42          [get_ports {M_DQ[39]}]
set_property PACKAGE_PIN A39          [get_ports {M_DQ[40]}]
set_property PACKAGE_PIN A40          [get_ports {M_DQ[41]}]
set_property PACKAGE_PIN B41          [get_ports {M_DQ[42]}]
set_property PACKAGE_PIN B42          [get_ports {M_DQ[43]}]
set_property PACKAGE_PIN D40          [get_ports {M_DQ[44]}]
set_property PACKAGE_PIN C40          [get_ports {M_DQ[45]}]
set_property PACKAGE_PIN D41          [get_ports {M_DQ[46]}]
set_property PACKAGE_PIN E41          [get_ports {M_DQ[47]}]
set_property PACKAGE_PIN A43          [get_ports {M_DQ[48]}]
set_property PACKAGE_PIN A44          [get_ports {M_DQ[49]}]
set_property PACKAGE_PIN C44          [get_ports {M_DQ[50]}]
set_property PACKAGE_PIN B45          [get_ports {M_DQ[51]}]
set_property PACKAGE_PIN D42          [get_ports {M_DQ[52]}]
set_property PACKAGE_PIN C43          [get_ports {M_DQ[53]}]
set_property PACKAGE_PIN C45          [get_ports {M_DQ[54]}]
set_property PACKAGE_PIN B46          [get_ports {M_DQ[55]}]
set_property PACKAGE_PIN D45          [get_ports {M_DQ[56]}]
set_property PACKAGE_PIN D44          [get_ports {M_DQ[57]}]
set_property PACKAGE_PIN E44          [get_ports {M_DQ[58]}]
set_property PACKAGE_PIN F44          [get_ports {M_DQ[59]}]
set_property PACKAGE_PIN G45          [get_ports {M_DQ[60]}]
set_property PACKAGE_PIN H45          [get_ports {M_DQ[61]}]
set_property PACKAGE_PIN F45          [get_ports {M_DQ[62]}]
set_property PACKAGE_PIN F46          [get_ports {M_DQ[63]}]
set_property IOSTANDARD  POD12_DCI    [get_ports {M_DQ[*]}]

set_property PACKAGE_PIN E28          [get_ports {M_ECC[0]}]
set_property PACKAGE_PIN D29          [get_ports {M_ECC[1]}]
set_property PACKAGE_PIN D32          [get_ports {M_ECC[2]}]
set_property PACKAGE_PIN C32          [get_ports {M_ECC[3]}]
set_property PACKAGE_PIN F29          [get_ports {M_ECC[4]}]
set_property PACKAGE_PIN E29          [get_ports {M_ECC[5]}]
set_property PACKAGE_PIN F33          [get_ports {M_ECC[6]}]
set_property PACKAGE_PIN E33          [get_ports {M_ECC[7]}]
set_property IOSTANDARD  POD12_DCI    [get_ports {M_ECC[*]}]

set_property PACKAGE_PIN J32          [get_ports {M_DQS_DN[0]}]
set_property PACKAGE_PIN K32          [get_ports {M_DQS_DP[0]}]
set_property PACKAGE_PIN L33          [get_ports {M_DQS_DP[1]}]
set_property PACKAGE_PIN K33          [get_ports {M_DQS_DN[1]}]
set_property PACKAGE_PIN G33          [get_ports {M_DQS_DN[2]}]
set_property PACKAGE_PIN H33          [get_ports {M_DQS_DP[2]}]
set_property PACKAGE_PIN G28          [get_ports {M_DQS_DP[3]}]
set_property PACKAGE_PIN F28          [get_ports {M_DQS_DN[3]}]
set_property PACKAGE_PIN K38          [get_ports {M_DQS_DN[4]}]
set_property PACKAGE_PIN L38          [get_ports {M_DQS_DP[4]}]
set_property PACKAGE_PIN L35          [get_ports {M_DQS_DP[5]}]
set_property PACKAGE_PIN L36          [get_ports {M_DQS_DN[5]}]
set_property PACKAGE_PIN A31          [get_ports {M_DQS_DN[6]}]
set_property PACKAGE_PIN B30          [get_ports {M_DQS_DP[6]}]
set_property PACKAGE_PIN C30          [get_ports {M_DQS_DP[7]}]
set_property PACKAGE_PIN B31          [get_ports {M_DQS_DN[7]}]
set_property PACKAGE_PIN H40          [get_ports {M_DQS_DP[8]}]
set_property PACKAGE_PIN G40          [get_ports {M_DQS_DN[8]}]
set_property PACKAGE_PIN K41          [get_ports {M_DQS_DP[9]}]
set_property PACKAGE_PIN K42          [get_ports {M_DQS_DN[9]}]
set_property PACKAGE_PIN B40          [get_ports {M_DQS_DP[10]}]
set_property PACKAGE_PIN A41          [get_ports {M_DQS_DN[10]}]
set_property PACKAGE_PIN F40          [get_ports {M_DQS_DP[11]}]
set_property PACKAGE_PIN F41          [get_ports {M_DQS_DN[11]}]
set_property PACKAGE_PIN A45          [get_ports {M_DQS_DP[12]}]
set_property PACKAGE_PIN A46          [get_ports {M_DQS_DN[12]}]
set_property PACKAGE_PIN E42          [get_ports {M_DQS_DP[13]}]
set_property PACKAGE_PIN E43          [get_ports {M_DQS_DN[13]}]
set_property PACKAGE_PIN E46          [get_ports {M_DQS_DP[14]}]
set_property PACKAGE_PIN D46          [get_ports {M_DQS_DN[14]}]
set_property PACKAGE_PIN J44          [get_ports {M_DQS_DP[15]}]
set_property PACKAGE_PIN H44          [get_ports {M_DQS_DN[15]}]
set_property PACKAGE_PIN D31          [get_ports {M_DQS_DN[16]}]
set_property PACKAGE_PIN D30          [get_ports {M_DQS_DP[16]}]
set_property PACKAGE_PIN E31          [get_ports {M_DQS_DP[17]}]
set_property PACKAGE_PIN E32          [get_ports {M_DQS_DN[17]}]
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports {M_DQS_DP[*]}]
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports {M_DQS_DN[*]}]

###############################################################################
# C2C PCIe endpoint
###############################################################################
set_property PACKAGE_PIN AL40         [get_ports PCIE_EP_REF_CLK_P]
set_property IOSTANDARD  LVDS         [get_ports PCIE_EP_REF_CLK_P]

set_property PACKAGE_PIN BN27         [get_ports PCIE_EP_PERSTN]
set_property IOSTANDARD  LVCMOS18     [get_ports PCIE_EP_PERSTN]

set_property PACKAGE_PIN AL44         [get_ports {PCIE_EP_TXP[0]}]
set_property PACKAGE_PIN AM46         [get_ports {PCIE_EP_TXP[1]}]
set_property PACKAGE_PIN AN44         [get_ports {PCIE_EP_TXP[2]}]
set_property PACKAGE_PIN AP46         [get_ports {PCIE_EP_TXP[3]}]
set_property PACKAGE_PIN AR44         [get_ports {PCIE_EP_TXP[4]}]
set_property PACKAGE_PIN AR48         [get_ports {PCIE_EP_TXP[5]}]
set_property PACKAGE_PIN AT46         [get_ports {PCIE_EP_TXP[6]}]
set_property PACKAGE_PIN AU48         [get_ports {PCIE_EP_TXP[7]}]

###############################################################################
# C2C PCIe root port
###############################################################################
set_property PACKAGE_PIN AR15         [get_ports PCIE_RP_REF_CLK_P]
set_property IOSTANDARD  LVDS         [get_ports PCIE_RP_REF_CLK_P]

set_property PACKAGE_PIN BG23         [get_ports PCIE_RP_PERSTN]
set_property IOSTANDARD  LVCMOS18     [get_ports PCIE_RP_PERSTN]

set_property PACKAGE_PIN AV4          [get_ports {PCIE_RP_RXP[0]}]
set_property PACKAGE_PIN AW6          [get_ports {PCIE_RP_RXP[1]}]
set_property PACKAGE_PIN AW2          [get_ports {PCIE_RP_RXP[2]}]
set_property PACKAGE_PIN AY4          [get_ports {PCIE_RP_RXP[3]}]
set_property PACKAGE_PIN BA6          [get_ports {PCIE_RP_RXP[4]}]
set_property PACKAGE_PIN BA2          [get_ports {PCIE_RP_RXP[5]}]
set_property PACKAGE_PIN BB4          [get_ports {PCIE_RP_RXP[6]}]
set_property PACKAGE_PIN BC2          [get_ports {PCIE_RP_RXP[7]}]
