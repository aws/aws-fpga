# This contains the CL specific constraints for Top level PNR

create_pblock pblock_CL_top
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/gen_ddr_tst[0].*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_0*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_inst[0].*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_stat[0].*}]
resize_pblock [get_pblocks pblock_CL_top] -add {CLOCKREGION_X0Y10:CLOCKREGION_X5Y14}
set_property PARENT pblock_CL [get_pblocks pblock_CL_top]

create_pblock pblock_CL_mid
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/gen_ddr_tst[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_inst[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_stat[1].*}]
#resize_pblock [get_pblocks pblock_CL_mid] -add {CLOCKREGION_X0Y5:CLOCKREGION_X3Y9}
resize_pblock [get_pblocks pblock_CL_mid] -add {SLICE_X88Y300:SLICE_X107Y599}
resize_pblock [get_pblocks pblock_CL_mid] -add {DSP48E2_X11Y120:DSP48E2_X13Y239}
resize_pblock [get_pblocks pblock_CL_mid] -add {LAGUNA_X12Y240:LAGUNA_X15Y479}
resize_pblock [get_pblocks pblock_CL_mid] -add {RAMB18_X7Y120:RAMB18_X7Y239}
resize_pblock [get_pblocks pblock_CL_mid] -add {RAMB36_X7Y60:RAMB36_X7Y119}
resize_pblock [get_pblocks pblock_CL_mid] -add {URAM288_X2Y80:URAM288_X2Y159}
resize_pblock [get_pblocks pblock_CL_mid] -add {CLOCKREGION_X0Y5:CLOCKREGION_X2Y9}
set_property SNAPPING_MODE ON [get_pblocks pblock_CL_mid]
set_property PARENT pblock_CL [get_pblocks pblock_CL_mid]

create_pblock pblock_CL_bot
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/gen_ddr_tst[2].*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_cores.DDR4_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_inst[2].*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet -hierarchical -filter {NAME =~ WRAPPER_INST/CL/SH_DDR/ddr_stat[2].*}]
#resize_pblock [get_pblocks pblock_CL_bot] -add {CLOCKREGION_X0Y0:CLOCKREGION_X3Y4}
resize_pblock [get_pblocks pblock_CL_bot] -add {SLICE_X88Y0:SLICE_X107Y299}
resize_pblock [get_pblocks pblock_CL_bot] -add {DSP48E2_X11Y0:DSP48E2_X13Y119}
resize_pblock [get_pblocks pblock_CL_bot] -add {LAGUNA_X12Y0:LAGUNA_X15Y239}
resize_pblock [get_pblocks pblock_CL_bot] -add {RAMB18_X7Y0:RAMB18_X7Y119}
resize_pblock [get_pblocks pblock_CL_bot] -add {RAMB36_X7Y0:RAMB36_X7Y59}
resize_pblock [get_pblocks pblock_CL_bot] -add {URAM288_X2Y0:URAM288_X2Y79}
resize_pblock [get_pblocks pblock_CL_bot] -add {CLOCKREGION_X0Y0:CLOCKREGION_X2Y4}
set_property SNAPPING_MODE ON [get_pblocks pblock_CL_bot]
set_property PARENT pblock_CL [get_pblocks pblock_CL_bot]

# False paths to FireSim reset synchronizers
set_false_path -from [get_clocks clk_main_a0] \
               -to   [get_cells {WRAPPER_INST/CL/pre_sync_rst_n_extra1_reg* \
                                 WRAPPER_INST/CL/pre_sync_rst_n_firesim_reg* \
                                 WRAPPER_INST/CL/rst_firesim_n_sync_reg* \
                                 WRAPPER_INST/CL/rst_extra1_n_sync_reg* }]


set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets WRAPPER_INST/SH/kernel_clks_i/clkwiz_sys_clk/inst/CLK_CORE_DRP_I/clk_inst/clk_out2]

# FireSim added CDC + width adapters
# SH DDR (Channel C)
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet WRAPPER_INST/CL/clock_convert_dramslim_0]
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet WRAPPER_INST/CL/dwidth_adapt_64bits_512bits_0]

# CL DDR A
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet WRAPPER_INST/CL/clock_convert_dramslim_1]
add_cells_to_pblock [get_pblocks pblock_CL_top] [get_cells -quiet WRAPPER_INST/CL/dwidth_adapt_64bits_512bits_1]

# CL DDR B
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet WRAPPER_INST/CL/clock_convert_dramslim_2]
add_cells_to_pblock [get_pblocks pblock_CL_mid] [get_cells -quiet WRAPPER_INST/CL/dwidth_adapt_64bits_512bits_2]

# CL DDR D
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet WRAPPER_INST/CL/clock_convert_dramslim_3]
add_cells_to_pblock [get_pblocks pblock_CL_bot] [get_cells -quiet WRAPPER_INST/CL/dwidth_adapt_64bits_512bits_3]

# Give the main simulator clock a better name
create_generated_clock -name host_clock [get_pins WRAPPER_INST/CL/firesim_clocking/inst/mmcme4_adv_inst/CLKOUT0]
