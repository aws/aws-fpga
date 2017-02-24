# This contains the CL specific constraints for Top level PNR

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_top
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/CL_TST_DDR0*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR0_TST_AXI4_REG_SLC_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/gen_ddr_tst[0].*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_0*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[0].*}]
add_cells_to_pblock [get_pblocks pblock_CL_top] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[0].*}]
resize_pblock [get_pblocks pblock_CL_top] -add {CLOCKREGION_X0Y10:CLOCKREGION_X5Y14}

create_pblock -parent [get_pblocks pblock_CL] pblock_CL_bot
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/CL_TST_DDR2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR2_TST_AXI4_REG_SLC_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/gen_ddr_tst[2].*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[2].*}]
add_cells_to_pblock [get_pblocks pblock_CL_bot] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[2].*}]
resize_pblock [get_pblocks pblock_CL_bot] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y4}


create_pblock -parent [get_pblocks pblock_CL] pblock_CL_mid
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_PCIM_MSTR/CL_TST_PCI}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/PCI_AXL_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_PCIM_MSTR/PCI_AXI4_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/CL_TST_DDR1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR0_TST_AXI4_REG_SLC_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR1_TST_AXI4_REG_SLC_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR2_TST_AXI4_REG_SLC_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR1_TST_AXI4_REG_SLC_2*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/gen_ddr_tst[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_cores.DDR4_1*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_inst[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/SH_DDR/ddr_stat[1].*}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/CL_TST_DDR_3}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR_TST_3_AXI4_REG_SLC}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/DDR_TST_3_AXI4_REG_SLC_1}]
add_cells_to_pblock [get_pblocks pblock_CL_mid] -cells [get_cells -quiet -hierarchical -filter {NAME =~ CL/CL_DMA_PCIS_SLV/AXI_CROSSBAR}]
resize_pblock [get_pblocks pblock_CL_mid] -add {CLOCKREGION_X0Y5:CLOCKREGION_X2Y9}

#From Jeff's email on 02/14 - Sundeep Amirineni
create_pblock ddr1_right
add_cells_to_pblock [get_pblocks ddr1_right] [get_cells -quiet [list CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_infrastructure CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/GND \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/VCC CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/en_vtc_in_reg CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/rst_r1_reg \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_ddr_cal_riu CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_ddr_mc CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_ddr_ui \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_en_vtc_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_fab_rst_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_addr_strobe_lvl_sync \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_addr_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_read_data_sync \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_ready_lvl_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_write_data_sync \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_io_write_strobe_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_mig_ddr4_phy CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_bisc_complete_sync \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_fixdly_rdy_low CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_fixdly_rdy_upp \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_phy_rdy_low CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_phy_rdy_upp CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_phy2clb_phy_ready_sync]]
resize_pblock [get_pblocks ddr1_right] -add {CLOCKREGION_X2Y5:CLOCKREGION_X2Y9}
set_property SNAPPING_MODE ON [get_pblocks ddr1_right]
create_pblock ddr1_left
add_cells_to_pblock [get_pblocks ddr1_left] [get_cells -quiet [list CL/SH_DDR/ddr_cores.DDR4_1/inst/GND CL/SH_DDR/ddr_cores.DDR4_1/inst/VCC CL/SH_DDR/ddr_cores.DDR4_1/inst/axi_ctrl_top_0 \
CL/SH_DDR/ddr_cores.DDR4_1/inst/c0_ddr4_init_calib_complete_r_reg CL/SH_DDR/ddr_cores.DDR4_1/inst/div_clk_rst_r1_reg CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_ddr_cal_top \
CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr4_mem_intfc/u_riu2clb_valid_sync CL/SH_DDR/ddr_cores.DDR4_1/inst/u_ddr_axi]]
resize_pblock [get_pblocks ddr1_left] -add {CLOCKREGION_X1Y5:CLOCKREGION_X1Y9}
set_property SNAPPING_MODE ON [get_pblocks ddr1_left]

