
##-----------------------------------------------------------------------------
##
## (c) Copyright 2020-2024 Advanced Micro Devices, Inc. All rights reserved.
##
## This file contains confidential and proprietary information
## of AMD and is protected under U.S. and
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
## Project    : The Xilinx PCI Express DMA 
## File       : pcie_bridge_rc_pcie4_uscaleplus_ip.xdc
## Version    : 4.1
##-----------------------------------------------------------------------------
#
# SXX
# false
# false
###############################################################################
# User Time Names / User Time Groups / Time Specs
###############################################################################

###############################################################################
# User Physical Constraints
###############################################################################


###############################################################################
# Pinout and Related I/O Constraints
###############################################################################
#
# Transceiver instance placement.  This constraint selects the
# transceivers to be used, which also dictates the pinout for the
# transmit and receive differential pairs.  Please refer to the
# Virtex-7 GT Transceiver User Guide (UG) for more information.
#
###############################################################################

###############################################################################
#
# PCI Express Block placement. This constraint selects the PCI Express
# Block to be used.
#
###############################################################################

###############################################################################
#
# Buffer (BRAM) Placement Constraints
#
###############################################################################

###############################################################################
# Timing Constraints
###############################################################################
#
#
###############################################################################
# Physical Constraints
###############################################################################
#
#create_clock -period 10 [get_ports sys_clk]
#create_clock -period 10 [get_ports sys_clk_gt]
#

###############################################################################
# End
##############################################################################
#create_waiver -internal -scope -id "TIMING-1" -user "xdma" -tag "1019576" -desc " TIMING-1 wavied" 
#create_waiver -internal -scope -id "TIMING-3" -user "xdma" -tag "1019576" -desc " TIMING-3 wavied" 
#create_waiver -internal -scope -id "TIMING-6" -user "xdma" -tag "1019576" -desc " TIMING-6 wavied" 
#create_waiver -internal -scope -id "TIMING-7" -user "xdma" -tag "1019576" -desc " TIMING-7 wavied"
#create_waiver -internal -scope -id "TIMING-18" -user "xdma" -tag "1019576" -desc " TIMING-18 wavied"
#create_waiver -internal -scope -id "LUTAR-1" -user "xdma" -tag "1019576" -desc " LUTAR-1 wavied"

#---------------------- Adding REQP waivers for IP level constraints --------------------------------#


create_waiver -type DRC -id {REQP-1839} -tags "1166691" -user "xdma" -internal -scope -desc "DRC expects synchronous pins to be provided to BRAM inputs. Since synchronization is present one stage before, it is safe to ignore" -objects [list [get_cells -hierarchical -filter {NAME =~ {*inst/debug_wrapper_U/*WIDE_PRIM36_NO_ECC.ram}}] [get_cells -hierarchical -filter {NAME =~ {*ram_top/*_DAT*_FIFO/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}] [get_cells -hierarchical -filter {NAME =~ {*ram_top/*_WRITE_FIFO/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}]]

create_waiver -type DRC -id {REQP-1840} -tags "1166691" -user "xdma" -internal -scope -desc "DRC expects synchronous pins to be provided to BRAM inputs. Since synchronization is present one stage before, it is safe to ignore" -objects [get_cells -hierarchical -filter {NAME =~ {*inst/debug_wrapper_U/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}] 

create_waiver -type DRC -id {REQP-1857} -tags "1166691" -user "xdma" -internal -scope -desc "Suggestion to change mode from WRITE_FIRST to NO_CHANGE, safe to waive off based on usecase" -objects [get_cells -hierarchical -filter {NAME =~ {*/inst/debug_wrapper_U/*.WIDE_PRIM18.ram}}]

create_waiver -type DRC -id {REQP-1858} -tags "1166691" -user "xdma" -internal -scope -desc "Suggestion to change mode from WRITE_FIRST to NO_CHANGE, safe to waive off based on usecase" -objects [list [get_cells -hierarchical -filter {NAME =~ {*/inst/debug_wrapper_U/*.WIDE_PRIM36_NO_ECC.ram}}] [get_cells -hierarchical -filter {NAME =~ {*/inst/pcie4c_ip_i/*.ramb36e2_inst}}]]


create_waiver -type DRC -id {REQP-1839} -tags "1166691" -user "xdma" -internal -scope -desc "DRC expects synchronous pins to be provided to BRAM inputs. Since synchronization is present one stage before, it is safe to ignore" -objects [list [get_cells -hierarchical -filter {NAME =~ {*ram_top/*_PCIE_DSC_CPLD_RAM/the_bram_reg_*} && PRIMITIVE_TYPE =~ {*BRAM*}}] [get_cells -hierarchical -filter {NAME =~ {*ram_top/MASTER_READ_BRAM/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}] [get_cells -hierarchical -filter {NAME =~ {*ram_top/mas_bridge_ram_write_512.MASTER*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}] [get_cells -hierarchical -filter {NAME =~ {*ram_top/*_DAT*_FIFO/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}]]

create_waiver -type DRC -id {REQP-1840} -tags "1166691" -user "xdma" -internal -scope -desc "DRC expects synchronous pins to be provided to BRAM inputs. Since synchronization is present one stage before, it is safe to ignore" -objects [get_cells -hierarchical -filter {NAME =~ {*ram_top/*_DAT*_FIFO/*.mem_reg*} && PRIMITIVE_TYPE =~ {*BRAM*}}]
