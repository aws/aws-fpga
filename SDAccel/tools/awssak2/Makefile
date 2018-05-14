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

EXENAME := xbsak

CXX_EXT := cpp
CL_EXT := cl

AR := ar
CXX := g++

CXXFLAGS := -Wall -Werror -std=c++11

ROOT = $(SDACCEL_DIR)
HAL_INC := -I$(SDACCEL_DIR)/userspace/src2 -I$(SDACCEL_DIR)/userspace/include -I$(SDK_DIR)/userspace/include -I$(SDK_DIR)/linux_kernel_drivers

CXXFLAGS += $(HAL_INC)

ifeq ($(ec2),1)
AWS_HAL_LIBNAME := $(ROOT)/userspace/src2/libxrt-aws.a
else
AWS_HAL_LIBNAME := $(ROOT)/userspace/src2/libxrtbm-aws.a
CXXFLAGS += -DINTERNAL_RELEASE
endif

ifeq ($(debug),1)
	CXXFLAGS += -g -D_DEBUG
else
	CXXFLAGS += -O2 -DNDEBUG
endif

SRCS := $(wildcard *.$(CXX_EXT))
OBJS := $(patsubst %.$(CXX_EXT), %.o, $(SRCS))

-include $(OBJS:.o=.d)

AWS_FPGA_MGMTLIB := fpga_mgmt
AWS_FPGA_MGMTLIB_DIR := $(SDK_DIR)/userspace/lib

ifeq ($(ec2),1)
LDFLAGS += -L$(AWS_FPGA_MGMTLIB_DIR)
LDLIBS += -l$(AWS_FPGA_MGMTLIB)
endif

all : $(EXENAME)

%.o: %.$(CXX_EXT)
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c $< -o $@
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c -MM $< -o $(patsubst %.o, %.d, $@)

$(EXENAME): $(OBJS) $(AWS_HAL_LIBNAME)
	$(CXX) -o $@ $(OBJS) $(AWS_HAL_LIBNAME) $(LDFLAGS) $(LDLIBS) -lrt

clean:
	rm -rf *.o *.d $(EXENAME)

.PHONY: all

.DEFAULT_GOAL := all
