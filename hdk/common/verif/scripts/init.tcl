create_project -force tmp_ddr ./tmp -part xcvu9p-flgb2104-2-i-es1
add_files -norecurse $::env(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip/ddr4_core/ddr4_core.xci
export_ip_user_files -of_objects  [get_files  $::env(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip/ddr4_core/ddr4_core.xci] -force -quiet
open_example_project -force -dir ./tmp/tmp_ddr_ex [get_ips  ddr4_core]

#Only for PCIe
# add_files -norecurse $::env(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip/pcie4_uscale_plus_0/pcie4_uscale_plus_0.xci
# upgrade_ip [get_ips pcie4_uscale_plus_0]
# export_ip_user_files -of_objects  [get_files   $::env(HDK_DIR)/top/vu9p/design/v3_venom_cl/v3_venom_cl.srcs/sources_1/ip/pcie4_uscale_plus_0/pcie4_uscale_plus_0.xci] -force -quiet
# open_example_project -force -dir ./tmp/tmp_pci_ex [get_ips pcie4_uscale_plus_0]

exit

