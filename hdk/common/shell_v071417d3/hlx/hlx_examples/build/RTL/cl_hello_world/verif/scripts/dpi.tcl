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

set HDK_COMMON_DIR $::env(HDK_COMMON_DIR)
set AWS_FPGA_REPO_DIR $::env(AWS_FPGA_REPO_DIR)

set SIMULATOR [get_property target_simulator [current_project]]

if {$SIMULATOR == "VCS"} {
	set mypath [exec which vlogan]
	if {$mypath == ""} {
	    puts "Should exit!"
	    return 1
	}
	set string_len [string length $mypath]
	set directory [string range $mypath 0 [expr {$string_len - 8}]]	
	set include_dir "${directory}/../include"
	
} elseif {$SIMULATOR == "IES"} {
	set mypath [exec which ncsim]
	if {$mypath == ""} {
	    puts "Should exit!"
	    return 1
	}
	set string_len [string length $mypath]
	set directory [string range $mypath 0 [expr {$string_len - 7}]]	
	set include_dir "${directory}/../../tools.lnx86/include"
} else {
	set mypath [exec which vsim]
	if {$mypath == ""} {
	    puts "Should exit!"
	    return 1
	}
	set string_len [string length $mypath]
	set directory [string range $mypath 0 [expr {$string_len - 6}]]	
	set include_dir "${directory}/../include"
}

#exec gcc  ${HDK_COMMON_DIR}/software/src/test_null.c ${AWS_FPGA_REPO_DIR}/sdk/userspace/utils/sh_dpi_tasks.c -fpic -shared -o ./libdpi.so -I${AWS_FPGA_REPO_DIR}/sdk/userspace/include -I${AWS_FPGA_REPO_DIR}/sdk/userspace/utils -I${HDK_COMMON_DIR}/software/include

exec gcc -I${include_dir} ${AWS_FPGA_REPO_DIR}/hdk/cl/examples/cl_hello_world/software/verif_rtl/src/test_hello_world.c -fpic -shared -o ./libdpi.so -I${AWS_FPGA_REPO_DIR}/hdk/cl/examples/cl_hello_world/software/verif_rtl/include -I${AWS_FPGA_REPO_DIR}/sdk/userspace/include -I${AWS_FPGA_REPO_DIR}/sdk/userspace/utils -I${HDK_COMMON_DIR}/software/include





