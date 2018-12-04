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

main_CXXFLAGS=$(xcl_CXXFLAGS) $(opencl_CXXFLAGS)  -I../common/inc/
main_LDFLAGS=$(opencl_LDFLAGS) -lrt

EXES=main

# Kernel                                                                                                                                                                                              
vector_add_SRCS=./device/vector_add.cl
vector_add_CLFLAGS= -k vector_add
#Specifying Fifo depth for Dataflow                                                                                                                                                                  
vector_add_CLFLAGS+=--xp "param:compiler.xclDataflowFifoDepth=32"

XOS=vector_add

# xclbin                                                                                                                                                                                              
vector_add_XOS=vector_add

XCLBINS=vector_add

# check                                                                                                                                                                                               
check_EXE=main
check_XCLBINS=vector_add

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
