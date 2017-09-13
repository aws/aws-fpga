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

INSTALL_ROOT = /opt/Xilinx/SDx/2017.1
DSA = xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0

all:
	make -C ${SDACCEL_DIR}/userspace/src debug=$(debug) ec2=$(ec2)
	make -C ${SDACCEL_DIR}/tools/awssak debug=$(debug) ec2=$(ec2)
	make -C ${SDK_DIR}/linux_kernel_drivers/xdma

clean:
	make -C ${SDACCEL_DIR}/userspace/src clean debug=$(debug) ec2=$(ec2)
	make -C ${SDACCEL_DIR}/tools/awssak clean debug=$(debug) ec2=$(ec2)
	make -C ${SDK_DIR}/linux_kernel_drivers/xdma clean

install:
	make -C ${SDK_DIR}/linux_kernel_drivers/xdma install
	install -d $(INSTALL_ROOT)/runtime/platforms/$(DSA)/driver
	install -d $(INSTALL_ROOT)/runtime/bin
	install -d $(INSTALL_ROOT)/runtime/lib/x86_64
	install -m 755 ${SDACCEL_DIR}/userspace/src/libawsxcldrv.so $(INSTALL_ROOT)/runtime/platforms/$(DSA)/driver
	install -m 755 ${SDACCEL_DIR}/tools/awssak/xbsak $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbincat $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbinsplit $(INSTALL_ROOT)/runtime/bin
	install -m 755 ${XILINX_SDX}/lib/lnx64.o/libxilinxopencl.so $(INSTALL_ROOT)/runtime/lib/x86_64
	install -m 755 ${XILINX_SDX}/lib/lnx64.o/libstdc++.so* $(INSTALL_ROOT)/runtime/lib/x86_64
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
