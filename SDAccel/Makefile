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

# AWS HAL Driver Makefile
# set ec2=1 to compile for F1 instance

ifndef SDK_DIR
$(error Environment variable SDK_DIR not set)
else
$(info SDK_DIR = $(SDK_DIR))
endif

ifndef SDACCEL_DIR
$(error Environment variable SDACCEL_DIR not set)
else
$(info SDACCEL_DIR = $(SDACCEL_DIR))
endif

ifndef XILINX_SDX
$(error Environment variable XILINX_SDX not set)
else
$(info XILINX_SDX = $(XILINX_SDX))
endif


MODULE :=
ifeq ($(RELEASE_VER),2017.4)
  DSA := $(DSA)
  SRC_DIR = src2
  XRT_HAL_LIB = libxrt-aws.so
  EXE = awssak2
  MODULE = xocl
  GLIBCPP_PATH = lib/lnx64.o/Default
else
  $(error Environment variable RELEASE_VER not recognized: $(RELEASE_VER))
endif

OPENCLLIB := 
OPENCLFILE =  $(SDACCEL_DIR)/aws_platform/$(DSA)/sw/lib/x86_64/libxilinxopencl.so

ifeq ($(OPENCLFILE),)
  OPENCLLIB := ${XILINX_SDX}/runtime/lib/x86_64/libxilinxopencl.so
else
  OPENCLLIB := $(OPENCLFILE)
endif

all:
	make -C ${SDACCEL_DIR}/userspace/$(SRC_DIR) debug=$(debug) ec2=$(ec2)
	make -C ${SDACCEL_DIR}/tools/$(EXE) debug=$(debug) ec2=$(ec2)
	make -C ${SDK_DIR}/linux_kernel_drivers/$(MODULE)

clean:
	make -C ${SDACCEL_DIR}/userspace/$(SRC_DIR) clean debug=$(debug) ec2=$(ec2)
	make -C ${SDACCEL_DIR}/tools/$(EXE) clean debug=$(debug) ec2=$(ec2)
	make -C ${SDK_DIR}/linux_kernel_drivers/$(MODULE) clean

install:
	@echo "INSTALL_ROOT=$(INSTALL_ROOT)"
	@echo "DSA=$(DSA)"
	make -C ${SDK_DIR}/linux_kernel_drivers/$(MODULE) install
	install -d $(INSTALL_ROOT)/runtime/platforms/$(DSA)/driver
	install -d $(INSTALL_ROOT)/runtime/bin
	install -d $(INSTALL_ROOT)/runtime/lib/x86_64
	install -m 755 ${SDACCEL_DIR}/userspace/$(SRC_DIR)/$(XRT_HAL_LIB) $(INSTALL_ROOT)/runtime/platforms/$(DSA)/driver
	install -m 755 ${SDACCEL_DIR}/tools/$(EXE)/xbsak $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbincat $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbinsplit $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${OPENCLLIB} $(INSTALL_ROOT)/runtime/lib/x86_64
	install -m 755 ${XILINX_SDX}/$(GLIBCPP_PATH)/libstdc++.so* $(INSTALL_ROOT)/runtime/lib/x86_64
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_ROOT)/setup.sh for bash"
	@echo "export XILINX_OPENCL=$(INSTALL_ROOT)" > $(INSTALL_ROOT)/setup.sh
	@echo "export LD_LIBRARY_PATH=\$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_ROOT)/setup.sh
	@echo "export PATH=\$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_ROOT)/setup.sh
	@echo "unset XILINX_SDACCEL" >> $(INSTALL_ROOT)/setup.sh
	@echo "unset XILINX_SDX" >> $(INSTALL_ROOT)/setup.sh
	@echo "unset XCL_EMULATION_MODE" >> $(INSTALL_ROOT)/setup.sh
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_ROOT)/setup.csh for (t)csh"
	@echo "setenv XILINX_OPENCL $(INSTALL_ROOT)" > $(INSTALL_ROOT)/setup.csh
	@echo "if ( ! \$$?LD_LIBRARY_PATH ) then" >> $(INSTALL_ROOT)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64" >> $(INSTALL_ROOT)/setup.csh
	@echo "else" >> $(INSTALL_ROOT)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_ROOT)/setup.csh
	@echo "endif" >> $(INSTALL_ROOT)/setup.csh
	@echo "if ( ! \$$?PATH ) then" >> $(INSTALL_ROOT)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin" >> $(INSTALL_ROOT)/setup.csh
	@echo "else" >> $(INSTALL_ROOT)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_ROOT)/setup.csh
	@echo "endif" >> $(INSTALL_ROOT)/setup.csh
	@echo "unsetenv XILINX_SDACCEL" >> $(INSTALL_ROOT)/setup.csh
	@echo "unsetenv XILINX_SDX" >> $(INSTALL_ROOT)/setup.csh
	@echo "unsetenv XCL_EMULATION_MODE" >> $(INSTALL_ROOT)/setup.csh
	@echo "XILINX_OPENCL="$(INSTALL_ROOT)

.PHONY: all clean

.DEFAULT_GOAL := all
