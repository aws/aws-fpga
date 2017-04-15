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


clean:
	cd $(SIM_DIR) && rm -rf .Xil
	cd $(SIM_DIR) && rm -rf xsim.dir
	cd $(SIM_DIR) && rm -rf *.log
	cd $(SIM_DIR) && rm -rf *.jou
	cd $(SIM_DIR) && rm -rf *.pb
	cd $(SIM_DIR) && rm -rf *.dat
	cd $(SIM_DIR) && rm -rf *.wdb

