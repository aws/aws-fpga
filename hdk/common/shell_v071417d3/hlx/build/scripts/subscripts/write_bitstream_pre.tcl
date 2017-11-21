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

#add in rest of script

if {[info exist FAAS_CL_DIR] eq 0} {
	if {[info exist ::env(FAAS_CL_DIR)]} {
		set FAAS_CL_DIR $::env(FAAS_CL_DIR)
	} else {
		::tclapp::xilinx::faasutils::make_faas -force -bypass_drcs -partial
#		send_msg_id "write_bitstream_pre 0-1" ERROR "FAAS_CL_DIR environment varaiable not set, please run the proc 'aws::make_ipi_faas_setup' at the Vivado TCL command prompt"
	}
}

send_msg_id {make_faas 0-1870} ERROR "Bitstream Generation Not Supported for AWS flow, creatint TAR file instead. \n\nSUCCESS!  TAR file generated at $FAAS_CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar"

#close design


