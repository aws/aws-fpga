# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

set_msg_config -severity INFO -suppress
set_msg_config -severity STATUS -suppress
set_msg_config -severity WARNING -suppress
set_msg_config -string {exportsim} -suppress
set_msg_config -string {IP_Flow} -suppress

create_project -force tmp_ddr ./tmp -part xcvu9p-flgb2104-2-i 
add_files -norecurse $::env(HDK_COMMON_DIR)/shell_stable/design/ip/ddr4_core/ddr4_core.xci
export_ip_user_files -of_objects  [get_files  $::env(HDK_COMMON_DIR)/shell_stable/design/ip/ddr4_core/ddr4_core.xci] -force -quiet
open_example_project -force -dir ./tmp/tmp_ddr_ex [get_ips  ddr4_core]


exit

