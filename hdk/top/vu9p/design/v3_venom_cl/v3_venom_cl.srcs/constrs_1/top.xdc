#######################################################################
# Copyright 2016 Amazon.com, Inc. or its affiliates.
# All Rights Reserved Worldwide.
# Amazon Confidential information
# Restricted NDA Material
#######################################################################


set_property BITSTREAM.CONFIG.CONFIGRATE 90 [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR YES [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.USR_ACCESS TIMESTAMP [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE YES [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property CONFIG_MODE SPIx4 [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]

set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN ENABLE [current_design]


create_pblock pblock_CL
add_cells_to_pblock [get_pblocks pblock_CL] [get_cells -quiet [list CL]]
#Really Big SH - For Develop# resize_pblock [get_pblocks pblock_CL] -add {CLOCKREGION_X0Y0:CLOCKREGION_X3Y14}
resize_pblock [get_pblocks pblock_CL] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y4 CLOCKREGION_X0Y5:CLOCKREGION_X3Y9 CLOCKREGION_X0Y10:CLOCKREGION_X5Y14}

#Let the tool Choose# set_property PARTPIN_SPREADING 2 [get_pblocks pblock_CL]
#Let the tool Choose# set_property PARTPIN_SPREADING 1 [get_pblocks pblock_CL] # default is 5 (higher the number denser the packing)

set_property HD.RECONFIGURABLE 1 [get_cells CL]

create_pblock pblock_SH
add_cells_to_pblock [get_pblocks pblock_SH] [get_cells -quiet -hierarchical [list SH]] 
#Really Big SH - For Develop# resize_pblock [get_pblocks pblock_SH] -add {CLOCKREGION_X4Y0:CLOCKREGION_X5Y14}
resize_pblock [get_pblocks pblock_SH] -add {CLOCKREGION_X4Y5:CLOCKREGION_X5Y9}

#Let the tool choose# set_property HD.PARTPIN_RANGE {SLICE_X101Y390:SLICE_X103Y539} [get_pins -of_objects [get_cells CL]]

## Child Pblocks if required - These have to be removed before giving the dcp to the customer - How to do that??
#### Child Pblocks if required - These have to be removed before giving the dcp to the customer - How to do that??
create_pblock -parent [get_pblocks pblock_CL] pblock_CL_top
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[0].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_0*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/genblk1.ddr_inst[0]*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[0].*}]
resize_pblock [get_pblocks pblock_CL_top] -add {CLOCKREGION_X0Y10:CLOCKREGION_X5Y14}

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_bot
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[2].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/genblk1.ddr_inst[2]*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[2].*}]
resize_pblock [get_pblocks pblock_CL_bot] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y4}

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_mid
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_pci_tst[0].CL_TST_PCI}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/PCI_AXL_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/PCI_AXI4_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[1].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/genblk1.ddr_inst[1]*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_TST_DDR_3}]
resize_pblock [get_pblocks pblock_CL_mid] -add {CLOCKREGION_X0Y5:CLOCKREGION_X3Y9}

##############################################
##########      Configuration       ##########
##############################################
set_property IOSTANDARD LVCMOS12 [get_ports FPGA_STATUS_LED]
set_property PACKAGE_PIN BD11 [get_ports FPGA_STATUS_LED]

set_property PACKAGE_PIN AR26 [get_ports RST_FPGA_LS_N]
set_property IOSTANDARD LVCMOS12 [get_ports RST_FPGA_LS_N]
set_property PULLUP true [get_ports RST_FPGA_LS_N]

#PCI Clocks
set_property PACKAGE_PIN AT10 [get_ports CLK_100M_PCIE0_DN]
set_property PACKAGE_PIN AT11 [get_ports CLK_100M_PCIE0_DP]

set_property IOSTANDARD LVCMOS15 [get_ports I2C_FPGA_QSFP28_R_SCL]
set_property IOSTANDARD LVCMOS15 [get_ports I2C_FPGA_QSFP28_R_SDA]
set_property IOSTANDARD LVCMOS15 [get_ports I2C_FPGA_MEM_R_SCL]
set_property IOSTANDARD LVCMOS15 [get_ports I2C_FPGA_MEM_R_SDA]

set_property PACKAGE_PIN AY22 [get_ports I2C_FPGA_QSFP28_R_SCL]
set_property PACKAGE_PIN BA22 [get_ports I2C_FPGA_QSFP28_R_SDA]
set_property PACKAGE_PIN BA24 [get_ports I2C_FPGA_MEM_R_SCL]
set_property PACKAGE_PIN BB24 [get_ports I2C_FPGA_MEM_R_SDA]

set_property DRIVE 4 [get_ports I2C_FPGA_MEM_R_SDA]

#SPI From uC
set_property IOSTANDARD LVCMOS15 [get_ports SPI_UCTRL_SCK]
set_property IOSTANDARD LVCMOS15 [get_ports SPI_UCTRL_MISO]
set_property IOSTANDARD LVCMOS15 [get_ports SPI_UCTRL_MOSI]
set_property IOSTANDARD LVCMOS15 [get_ports SPI_UCTRL_CS_N]
set_property IOSTANDARD LVCMOS15 [get_ports FPGA_UCTRL_GPIO0]

set_property PACKAGE_PIN BB22 [get_ports SPI_UCTRL_SCK]
set_property PACKAGE_PIN BC22 [get_ports SPI_UCTRL_MISO]
set_property PACKAGE_PIN BB21 [get_ports SPI_UCTRL_MOSI]
set_property PACKAGE_PIN BC21 [get_ports SPI_UCTRL_CS_N]
set_property PACKAGE_PIN BD24 [get_ports FPGA_UCTRL_GPIO0]

create_clock -period 40.000 -name clk_spi_sck -waveform {0.000 20.000} [get_ports SPI_UCTRL_SCK]

set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets SPI_CLK_BUFG/O]

set_input_delay -clock clk_spi_sck 5.000 [get_ports SPI_UCTRL_MOSI]
set_output_delay -clock clk_spi_sck 5.000 [get_ports SPI_UCTRL_MISO]


#Xtra clock
set_property PACKAGE_PIN BA9 [get_ports CLK_125MHZ_P]
set_property PACKAGE_PIN BA8 [get_ports CLK_125MHZ_N]
set_property IOSTANDARD LVDS [get_ports CLK_125MHZ_P]
set_property IOSTANDARD LVDS [get_ports CLK_125MHZ_N]

#set_property PACKAGE_PIN AV22 [get_ports QSFP28_P0_MODPRS_N]
#set_property IOSTANDARD LVCMOS15 [get_ports QSFP28_P0_MODPRS_N]
#set_property PULLUP true [get_ports QSFP28_P0_MODPRS_N]

create_clock -period 8.000 -name clk_xtra -waveform {0.000 4.000} [get_ports CLK_125MHZ_P]

#SYSMON I2C
set_property IOSTANDARD LVCMOS12 [get_ports SYSMON_SCL]
set_property IOSTANDARD LVCMOS12 [get_ports SYSMON_SDA]

set_property PACKAGE_PIN AM27 [get_ports SYSMON_SCL]
set_property PACKAGE_PIN AN27 [get_ports SYSMON_SDA]

set_property DRIVE 8 [get_ports SYSMON_SCL]
set_property DRIVE 8 [get_ports SYSMON_SDA]

set_property IOSTANDARD LVCMOS15 [get_ports QSFP28_P0_MODSEL_N]
set_property IOSTANDARD LVCMOS15 [get_ports QSFP28_P1_MODSEL_N]
set_property IOSTANDARD LVCMOS15 [get_ports QSFP28_P2_MODSEL_N]
set_property IOSTANDARD LVCMOS15 [get_ports QSFP28_P3_MODSEL_N]

set_property PACKAGE_PIN BC23 [get_ports QSFP28_P0_MODSEL_N]
set_property PACKAGE_PIN BF22 [get_ports QSFP28_P1_MODSEL_N]
set_property PACKAGE_PIN AW24 [get_ports QSFP28_P2_MODSEL_N]
set_property PACKAGE_PIN AW23 [get_ports QSFP28_P3_MODSEL_N]

# Real DDR resets

set_property PACKAGE_PIN AN28 [get_ports sh_RST_DIMM_A_N]
set_property PACKAGE_PIN AL25 [get_ports sh_RST_DIMM_B_N]
set_property PACKAGE_PIN AM25 [get_ports sh_RST_DIMM_D_N]
set_property PACKAGE_PIN AU25 [get_ports RST_DIMM_C_N]

set_property IOSTANDARD LVCMOS12 [get_ports sh_RST_DIMM_A_N]
set_property IOSTANDARD LVCMOS12 [get_ports sh_RST_DIMM_B_N]
set_property IOSTANDARD LVCMOS12 [get_ports sh_RST_DIMM_D_N]
set_property IOSTANDARD LVCMOS12 [get_ports RST_DIMM_C_N]

set_property DRIVE 8 [get_ports sh_RST_DIMM_A_N]
set_property DRIVE 8 [get_ports sh_RST_DIMM_B_N]
set_property DRIVE 8 [get_ports sh_RST_DIMM_D_N]
set_property DRIVE 8 [get_ports RST_DIMM_C_N]

####################################################################################
# Clocks
####################################################################################

create_clock -period 10.000 -name refclk_100 [get_ports CLK_100M_PCIE0_DP]

set_false_path -through [get_pins {SH/pci_inst[0].PCIE_CORE_0/user_reset}]

set_false_path -from [get_cells SH/MGT_TOP/cfg_scratch_reg*]

set_false_path -from [get_clocks refclk_100] -to [get_clocks -of_objects [get_nets clk_out]]

set_false_path -from [get_clocks -of_objects [get_nets clk_out]] -to [get_clocks refclk_100]

set_false_path -from [get_clocks refclk_100] -to [get_clocks -of_objects [get_nets clk_out]]

set_false_path -from [get_clocks -of_objects [get_nets clk_out]] -to [get_clocks refclk_100]

set_false_path -from [get_clocks pci_user_clk*] -to [get_clocks clk_out_mmcm*]

set_false_path -from [get_clocks clk_out] -to [get_clocks clk_out_mmcm*]
set_false_path -from [get_clocks clk_out_mmcm*] -to [get_clocks clk_out]

set_false_path -from [get_clocks clk_out_mmcm*] -to [get_clocks clk_out]
set_false_path -from [get_clocks clk_out] -to [get_clocks clk_out_mmcm*]

set_false_path -from [get_clocks clk_out] -to [get_clocks clk_spi_sck]
set_false_path -from [get_clocks clk_spi_sck] -to [get_clocks clk_out]

set_false_path -from [get_clocks clk_out] -to [get_clocks clk_xtra]
set_false_path -from [get_clocks clk_xtra] -to [get_clocks clk_out]
set_false_path -from [get_cells pin_toggle_reg]

set_false_path -from [get_clocks clk_xtra] -to [get_clocks clk_spi_sck]
set_false_path -from [get_clocks clk_spi_sck] -to [get_clocks clk_xtra]

set_false_path -from [get_clocks clk_out] -to [get_clocks dev01_refclk]
set_false_path -from [get_clocks dev01_refclk] -to [get_clocks clk_out]
set_false_path -from [get_clocks clk_out] -to [get_clocks dev01_refclk]
set_false_path -from [get_clocks dev01_refclk] -to [get_clocks clk_out]

set_false_path -from [get_clocks clk_out] -to [get_clocks dev23_refclk]
set_false_path -from [get_clocks dev23_refclk] -to [get_clocks clk_out]
set_false_path -from [get_clocks clk_out] -to [get_clocks dev23_refclk]
set_false_path -from [get_clocks dev23_refclk] -to [get_clocks clk_out]

# refclk_100 vs user_clk
set_clock_groups -name async5 -asynchronous -group [get_clocks refclk_100] -group [get_clocks -of_objects [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]]
set_clock_groups -name async6 -asynchronous -group [get_clocks -of_objects [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]] -group [get_clocks refclk_100]
# refclk_100 vs pclk
set_clock_groups -name async1 -asynchronous -group [get_clocks refclk_100] -group [get_clocks -of_objects [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_pclk/O]]
set_clock_groups -name async2 -asynchronous -group [get_clocks -of_objects [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_pclk/O]] -group [get_clocks refclk_100]
# refclk_100 vs TXOUTCLK
set_clock_groups -name async18 -asynchronous -group [get_clocks refclk_100] -group [get_clocks -of_objects [get_pins -hierarchical -filter {NAME =~ *gen_channel_container[*].*gen_gtye4_channel_inst[*].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]]
set_clock_groups -name async19 -asynchronous -group [get_clocks -of_objects [get_pins -hierarchical -filter {NAME =~ *gen_channel_container[*].*gen_gtye4_channel_inst[*].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]] -group [get_clocks refclk_100]
#

#########################
## PCIe PBLOCK contraint
#########################
## Add/Edit Pblock slice constraints for 512b soft logic to improve timing
#create_pblock soft_512b; add_cells_to_pblock [get_pblocks soft_512b] [get_cells {SH/pci_inst[0].PCIE_CORE_0/inst/pcie_4_0_pipe_inst/pcie_4_0_init_ctrl_inst SH/pci_inst[0].PCIE_CORE_0/inst/pcie_4_0_pipe_inst/pcie4_0_512b_intfc_mod}]
## Keep This Logic Left/Right Side Of The PCIe Block (Whichever is near to the FPGA Boundary)
#resize_pblock [get_pblocks soft_512b] -add {SLICE_X157Y300:SLICE_X168Y370}
#set_property EXCLUDE_PLACEMENT 1 [get_pblocks soft_512b]

set_false_path -from [get_clocks -of_objects [get_nets SH/buf_pci_clk]] -to [get_clocks -of_objects [get_nets SH/clk]]
set_false_path -from [get_clocks -of_objects [get_nets SH/clk]] -to [get_clocks -of_objects [get_nets SH/buf_pci_clk]]

set_false_path -from [get_ports RST_FPGA_LS_N]

#Problematic constraint# set_clock_groups -asynchronous -group [get_clocks -of_objects [get_pins {SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/gt_wizard.gtwizard_top_i/pcie4_uscale_plus_0_gt_i/inst/gen_gtwizard_gtye4_top.pcie4_uscale_plus_0_gt_gtwizard_gtye4_inst/gen_gtwizard_gtye4.gen_channel_container[32].gen_enabled_channel.gtye4_channel_wrapper_inst/channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[3].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]] -group [get_clocks -of_objects [get_pins {SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O}]]

#################################################
## FIXME -- For now false path from reset
#################################################
set_false_path -from [get_cells SH/sync_rst_n_reg*]

#set_clock_uncertainty -setup 0.200 [get_clocks -of [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]]
#set_clock_uncertainty -hold 0.050 [get_clocks -of [get_pins SH/pci_inst[0].PCIE_CORE_0/inst/gt_top_i/diablo_gt.diablo_gt_phy_wrapper/phy_clk_i/bufg_gt_userclk/O]]

