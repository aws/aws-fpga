##-----------------------------------------------------------------------------
##
## (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
##
## This file contains confidential and proprietary information
## of AMD, Inc. and is protected under U.S. and
## international copyright and other intellectual property
## laws.
##
## DISCLAIMER
## This disclaimer is not a license and does not grant any
## rights to the materials distributed herewith. Except as
## otherwise provided in a valid license issued to you by
## AMD, and to the maximum extent permitted by applicable
## law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
## WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
## AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
## BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
## INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
## (2) AMD shall not be liable (whether in contract or tort,
## including negligence, or under any other theory of
## liability) for any loss or damage of any kind or nature
## related to, arising under or in connection with these
## materials, including for any direct, or any indirect,
## special, incidental, or consequential loss or damage
## (including loss of data, profits, goodwill, or any type of
## loss or damage suffered as a result of any action brought
## by a third party) even if such damage or loss was
## reasonably foreseeable or AMD had been advised of the
## possibility of the same.
##
## CRITICAL APPLICATIONS
## AMD products are not designed or intended to be fail-
## safe, or for use in any application requiring fail-safe
## performance, such as life-support or safety devices or
## systems, Class III medical devices, nuclear facilities,
## applications related to the deployment of airbags, or any
## other applications that could lead to death, personal
## injury, or severe property or environmental damage
## (individually and collectively, "Critical
## Applications"). Customer assumes the sole risk and
## liability of any use of AMD products in Critical
## Applications, subject only to applicable laws and
## regulations governing limitations on product liability.
##
## THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
## PART OF THIS FILE AT ALL TIMES.
##
##-----------------------------------------------------------------------------
##
## Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
## File       : ip_pcie4c_uscale_plus_impl_x0y1.xdc
## Version    : 1.0 
##-----------------------------------------------------------------------------
#
set_false_path -from [get_pins sys_reset]
#
###############################################################################
# TIMING Exceptions - MCP
###############################################################################
#
#
# Multi Cycle Paths
set PCIE4INST pcie_bridge_ep_pcie4c_ip_pcie_4_0_pipe_inst/pcie_4_c_e4_inst
set USERPINS  [get_pins "$PCIE4INST/CFG* $PCIE4INST/CONF* $PCIE4INST/PCIECQNPREQ* $PCIE4INST/PCIERQTAG* $PCIE4INST/PCIETFC* $PCIE4INST/USERSPARE*"]
#
set USERINPINS [get_pins $USERPINS -filter DIRECTION==IN]
set_multicycle_path -setup 2 -end   -through $USERINPINS
set_multicycle_path -hold  1 -end   -through $USERINPINS
#
set USEROUTPINS [get_pins $USERPINS -filter DIRECTION==OUT]
set_multicycle_path -setup 2 -start -through $USEROUTPINS
set_multicycle_path -hold  1 -start -through $USEROUTPINS
#
set USERPINS1  [get_pins "$PCIE4INST/CFGPHYLINKDOWN "]
set USERINPINS1 [get_pins $USERPINS1 -filter DIRECTION==IN]
set_multicycle_path -setup 4 -end   -through $USERINPINS1
set_multicycle_path -hold  3 -end   -through $USERINPINS1
set USEROUTPINS1 [get_pins $USERPINS1 -filter DIRECTION==OUT]
set_multicycle_path -setup 4 -start -through $USEROUTPINS1
set_multicycle_path -hold  3 -start -through $USEROUTPINS1
#
# Multi Cycle Paths
set PCIE4INSTPS pcie_bridge_ep_pcie4c_ip_pcie_4_0_pipe_inst/pcie_4_c_e4_inst
set USERPINSPS  [get_pins "$PCIE4INSTPS/PCIERQSEQ*"]
#
set USERINPINSPS [get_pins $USERPINSPS -filter DIRECTION==IN]
set_multicycle_path -setup 2 -end   -through $USERINPINSPS
set_multicycle_path -hold  1 -end   -through $USERINPINSPS
#
set USEROUTPINSPS [get_pins $USERPINSPS -filter DIRECTION==OUT]
set_multicycle_path -setup 2 -start -through $USEROUTPINSPS
set_multicycle_path -hold  1 -start -through $USEROUTPINSPS
