# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

# Device type for AWS EC2 F2 instances
# Part: Xilinx UltraScale+ VU47P FPGA

# Define as both a variable and a procedure for compatibility
set DEVICE_TYPE "xcvu47p-fsvh2892-2-e"

proc DEVICE_TYPE {} {
    return "xcvu47p-fsvh2892-2-e"
}

