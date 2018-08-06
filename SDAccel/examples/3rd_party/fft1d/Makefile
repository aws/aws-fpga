## Copyright 2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
##
## Licensed under the Amazon Software License (the "License"). You may not use
## this file except in compliance with the License. A copy of the License is
## located at
##
##    http://aws.amazon.com/asl/
##
## or in the "license" file accompanying this file. This file is distributed on
## an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
## implied. See the License for the specific language governing permissions and
## limitations under the License.


COMMON_REPO := $(SDACCEL_DIR)/examples/xilinx

include $(COMMON_REPO)/utility/boards.mk
include $(COMMON_REPO)/libs/xcl2/xcl2.mk
include $(COMMON_REPO)/libs/opencl/opencl.mk
include $(COMMON_REPO)/libs/oclHelper/oclHelper.mk

# Host Application
main_SRCS=$(wildcard host/src/*.cpp ../common/src/AOCLUtils/*.cpp) $(xcl2_SRCS) $(oclHelper_SRCS)
main_HDRS=$(xcl2_HDRS)
main_CXXFLAGS=$(xcl2_CXXFLAGS) $(opencl_CXXFLAGS)  -Ihost/inc -I../common/inc/ $(oclHelper_CXXFLAGS)
main_LDFLAGS=$(opencl_LDFLAGS) -lrt

EXES=main

# Kernel                                                                                                                                                                                              
fft1d_SRCS=./device/fft1d.cl
#fft1d_CLFLAGS= -optimizequick
#Specifying Fifo depth for Dataflow                                                                                                                                                                  
##fft1d_CLFLAGS+=--xp "param:compiler.xclDataflowFifoDepth=32"

XOS=fft1d

# xclbin                                                                                                                                                                                              
fft1d_XOS=fft1d

XCLBINS=fft1d

# check                                                                                                                                                                                               
check_EXE=main
check_XCLBINS=fft1d

CHECKS=check

CXXFLAGS += -g

#CXX := g++

include $(COMMON_REPO)/utility/rules.mk

