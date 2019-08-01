# Amazon FPGA Hardware Development Kit
#
# Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


# AWS Bare-metal HAL Driver Makefile
# set ec2=1 to compile for F1 instance

CXX := g++
CXX_EXT := cpp
AR := ar
ARFLAGS := rcv

ifeq ($(ec2),1)
    CXXFLAGS := -Werror -std=c++11
    STLIB = libxrt-aws.a
    SHLIB = libxrt-aws.so
else
# For bare metal testing, i.e. in non EC2 environment
    CXXFLAGS := -Werror -std=c++11 -DINTERNAL_TESTING
    STLIB = libxrtbm-aws.a
    SHLIB = libxrtbm-aws.so
endif

LIBS := $(STLIB) $(SHLIB)

XCLHAL_VER = -DXCLHAL_MAJOR_VER=2 -DXCLHAL_MINOR_VER=1

# Include XCLHAL includes, AWS fpga_pci/mgmt and AWS kernel drivers
SHIM_INC := -I../include -I$(SDK_DIR)/userspace/include -I$(SDK_DIR)/linux_kernel_drivers

CXXFLAGS += $(CXXFLAGS) $(XCLHAL_VER) $(SHIM_INC) -fpic -fvisibility=hidden -lrt -Wall

ifeq ($(debug),1)
	CXXFLAGS += -g -DDEBUG
else
	CXXFLAGS += -O2 -DNDEBUG
endif

SRCS := $(wildcard *.$(CXX_EXT))
OBJS := $(patsubst %.$(CXX_EXT), %.o, $(SRCS))

-include $(OBJS:.o=.d)

# the name that will be included as libXXXXX.so
AWS_FPGA_MGMTLIB := fpga_mgmt
AWS_FPGA_MGMTLIB_DIR := $(SDK_DIR)/userspace/lib

ifeq ($(ec2),1)
LDFLAGS += -L$(AWS_FPGA_MGMTLIB_DIR)
LDLIBS += -l$(AWS_FPGA_MGMTLIB)
endif

all: $(LIBS)

clean:
	rm -rf *.o *.d lib*drv.*

%.o: %.$(CXX_EXT)
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c $< -o $@
	$(CXX) $(CXXFLAGS) $(MYCFLAGS) $(MYCXXFLAGS) -c -MM $< -o $(patsubst %.o, %.d, $@)

$(STLIB) : $(OBJS)
	$(AR) $(ARFLAGS) -o $@ $(OBJS)

$(SHLIB) : $(OBJS)
	$(CXX) -shared -o $@ $(OBJS) $(LDFLAGS) $(LDLIBS)

.PHONY: all clean

.DEFAULT_GOAL := all
