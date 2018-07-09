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
include $(COMMON_REPO)/libs/xcl/xcl.mk
include $(COMMON_REPO)/libs/opencl/opencl.mk

main_SRCS=$(wildcard host/src/*.cpp ../common/src/AOCLUtils/*.cpp) $(xcl_SRCS)
main_HDRS=$(xcl_HDRS)

main_CXXFLAGS=$(xcl_CXXFLAGS) $(opencl_CXXFLAGS)  -Ihost/inc/ -I../common/inc/
main_LDFLAGS=$(opencl_LDFLAGS) -lrt

EXES=main

# Kernel                                                                                                                                                                                              
matrix_mult_SRCS=./device/matrix_mult.cl
matrix_mult_CLFLAGS= -k matrix_mult -Ihost/inc/
#Specifyinng Fifo depth for Dataflow                                                                                                                                                                  
matrix_mult_CLFLAGS+=--xp "param:compiler.xclDataflowFifoDepth=32"

XOS=matrix_mult

# xclbin                                                                                                                                                                                              
matrix_mult_XOS=matrix_mult

XCLBINS=matrix_mult

# check                                                                                                                                                                                               
check_EXE=main
check_XCLBINS=matrix_mult

CHECKS=check

# Compilation flags
ifeq ($(DEBUG),1)
CXXFLAGS += -g
else
CXXFLAGS += -O2
endif

# Compiler
#CXX := g++

include $(COMMON_REPO)/utility/rules.mk
