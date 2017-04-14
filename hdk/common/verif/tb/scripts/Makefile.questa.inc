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
	cd $(SIM_ROOT)/.. && rm -rf modelsim.ini
	cd $(SIM_ROOT)/.. && rm -rf *.log
	cd $(SIM_ROOT)/.. && rm -rf *.jou
	cd $(SIM_ROOT)/.. && rm -rf .cxl.questasim.version
	cd $(SIM_ROOT)/.. && rm -rf compile_simlib.log
	cd $(SIM_ROOT)/.. && rm -rf vivado.log
	cd $(SIM_DIR) && rm -rf work
	cd $(SIM_DIR) && rm -rf transcript

