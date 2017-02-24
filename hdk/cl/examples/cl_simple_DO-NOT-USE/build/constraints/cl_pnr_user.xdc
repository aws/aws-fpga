# This contains the CL specific constraints for Top level PNR

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_top
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[0].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_0*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[0]*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[0].*}]
resize_pblock [get_pblocks pblock_CL_top] -add {CLOCKREGION_X0Y10:CLOCKREGION_X5Y14}

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_bot
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[2].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[2]*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[2].*}]
resize_pblock [get_pblocks pblock_CL_bot] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y4}


create_pblock -parent [get_pblocks pblock_CL] pblock_CL_mid
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_pci_tst[0].CL_TST_PCI}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/PCI_AXL_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/PCI_AXI4_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/gen_ddr_tst[1].CL_TST_DDR*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[1]*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_TST_DDR_3}]
resize_pblock [get_pblocks pblock_CL_mid] -add {CLOCKREGION_X0Y5:CLOCKREGION_X3Y9}
