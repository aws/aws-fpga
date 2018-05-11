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

# kernel_global Application
COMMON_REPO:=../../xilinx

include $(COMMON_REPO)/utility/boards.mk
include $(COMMON_REPO)/libs/xcl/xcl.mk
include $(COMMON_REPO)/libs/opencl/opencl.mk

# kernel_global Host Application
kernel_global_SRCS=./src/kernel_global_bandwidth.cpp $(xcl_SRCS)
kernel_global_HDRS=$(xcl_HDRS)
kernel_global_CXXFLAGS=$(xcl_CXXFLAGS) $(opencl_CXXFLAGS)
kernel_global_LDFLAGS=$(opencl_LDFLAGS)

EXES=kernel_global

krnl_kernel_global_SRCS=./src/kernel.cl
krnl_kernel_global_CLFLAGS=--max_memory_ports bandwidth

krnl_kernel_global_LDCLFLAGS+= --sp bandwidth_1.m_axi_gmem0:bank0 --sp bandwidth_1.m_axi_gmem1:bank1 --sp bandwidth_1.m_axi_gmem2:bank2	

XOS=krnl_kernel_global

krnl_kernel_global_XOS=krnl_kernel_global

XCLBINS=krnl_kernel_global

# check
check_EXE=kernel_global
check_XCLBINS=krnl_kernel_global

CHECKS=check

include $(COMMON_REPO)/utility/rules.mk
