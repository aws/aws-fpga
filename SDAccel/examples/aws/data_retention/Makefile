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

# vaddvmul Application

COMMON_REPO:=../../xilinx
include $(COMMON_REPO)/utility/boards.mk
include $(COMMON_REPO)/libs/opencl/opencl.mk
include $(COMMON_REPO)/libs/xcl2/xcl2.mk

# data_retention Host Application
data_retention_SRCS=./src/vmul_vadd_x4.cpp $(xcl2_SRCS)
data_retention_HDRS=$(xcl2_HDRS)
data_retention_EXE=data_retention
data_retention_CXXFLAGS=-I./src/ $(opencl_CXXFLAGS) $(xcl2_CXXFLAGS)
data_retention_LDFLAGS=$(opencl_LDFLAGS)

EXES=data_retention

# vmul Kernel
krnl_vmulx4_SRCS=./src/vmulx4.cl
krnl_vmulx4_LDCLFLAGS=--nk vmul0:4:vmul_0.vmul_1.vmul_2.vmul_3 --sp vmul_0.m_axi_gmem:bank0 --sp vmul_1.m_axi_gmem:bank1 --sp vmul_2.m_axi_gmem:bank2 --sp vmul_3.m_axi_gmem:bank3


# vadd Kernel
krnl_vaddx4_SRCS=./src/vaddx4.cl
krnl_vaddx4_LDCLFLAGS=--nk vadd0:4:vadd_0.vadd_1.vadd_2.vadd_3 --sp vadd_0.m_axi_gmem:bank0 --sp vadd_1.m_axi_gmem:bank1 --sp vadd_2.m_axi_gmem:bank2 --sp vadd_3.m_axi_gmem:bank3

XOS=krnl_vmulx4 krnl_vaddx4

# vmul Kernel
krnl_vmulx4_XOS=krnl_vmulx4

# vadd Kernel
krnl_vaddx4_XOS=krnl_vaddx4

XCLBINS=krnl_vmulx4 krnl_vaddx4


# check
check_EXE=data_retention
check_XCLBINS=krnl_vmulx4 krnl_vaddx4

CHECKS=check

include $(COMMON_REPO)/utility/rules.mk
