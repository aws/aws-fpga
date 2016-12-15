set_msg_config -severity INFO -suppress
set_msg_config -severity STATUS -suppress
set_msg_config -severity WARNING -suppress
set_msg_config -string {exportsim} -suppress
set_msg_config -string {IP_Flow} -suppress

create_project -force tmp_ddr ./tmp -part xcvu9p-flgb2104-2-i-es1
add_files -norecurse $::env(HDK_COMMON_DIR)/shell_latest/design/ip/ddr4_core/ddr4_core.xci
export_ip_user_files -of_objects  [get_files  $::env(HDK_COMMON_DIR)/shell_latest/design/ip/ddr4_core/ddr4_core.xci] -force -quiet
open_example_project -force -dir ./tmp/tmp_ddr_ex [get_ips  ddr4_core]


exit

