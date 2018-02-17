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

INSTALL_ROOT = /opt/Xilinx/SDx/2017.1.rte
INSTALL_1DDR = /opt/Xilinx/SDx/2017.1.rte.1ddr
INSTALL_4DDR = /opt/Xilinx/SDx/2017.1.rte.4ddr
INSTALL_4DDR_DEBUG = /opt/Xilinx/SDx/2017.1.rte.4ddr_debug

DSA = xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0
OPENCLFILE =  ${SDACCEL_DIR}/aws_platform/libxilinxopencl.so

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
	install -d $(INSTALL_1DDR)/runtime/platforms/xilinx_aws-vu9p-f1_1ddr-xpr-2pr_4_0/driver
	install -d $(INSTALL_1DDR)/runtime/bin
	install -d $(INSTALL_1DDR)/runtime/lib/x86_64
	install -m 755 ${SDACCEL_DIR}/userspace/src/libawsxcldrv.so $(INSTALL_1DDR)/runtime/platforms/xilinx_aws-vu9p-f1_1ddr-xpr-2pr_4_0/driver
	install -m 755 ${SDACCEL_DIR}/tools/awssak/xbsak $(INSTALL_1DDR)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbincat $(INSTALL_1DDR)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbinsplit $(INSTALL_1DDR)/runtime/bin
	#install -m 755 ${XILINX_SDX}/lib/lnx64.o/libxilinxopencl.so $(INSTALL_1DDR)/runtime/lib/x86_64
	install -m 755 ${OPENCLFILE} $(INSTALL_1DDR)/runtime/lib/x86_64
	install -m 755 ${XILINX_SDX}/lib/lnx64.o/libstdc++.so* $(INSTALL_1DDR)/runtime/lib/x86_64
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_1DDR)/setup.sh for bash"
	@echo "export XILINX_OPENCL=$(INSTALL_1DDR)" > $(INSTALL_1DDR)/setup.sh
	@echo "export LD_LIBRARY_PATH=\$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_1DDR)/setup.sh
	@echo "export PATH=\$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_1DDR)/setup.sh
	@echo "unset XILINX_SDACCEL" >> $(INSTALL_1DDR)/setup.sh
	@echo "unset XILINX_SDX" >> $(INSTALL_1DDR)/setup.sh
	@echo "unset XCL_EMULATION_MODE" >> $(INSTALL_1DDR)/setup.sh
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_1DDR)/setup.csh for (t)csh"
	@echo "setenv XILINX_OPENCL $(INSTALL_1DDR)" > $(INSTALL_1DDR)/setup.csh
	@echo "if ( ! \$$?LD_LIBRARY_PATH ) then" >> $(INSTALL_1DDR)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64" >> $(INSTALL_1DDR)/setup.csh
	@echo "else" >> $(INSTALL_1DDR)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_1DDR)/setup.csh
	@echo "endif" >> $(INSTALL_1DDR)/setup.csh
	@echo "if ( ! \$$?PATH ) then" >> $(INSTALL_1DDR)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin" >> $(INSTALL_1DDR)/setup.csh
	@echo "else" >> $(INSTALL_1DDR)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_1DDR)/setup.csh
	@echo "endif" >> $(INSTALL_1DDR)/setup.csh
	@echo "unsetenv XILINX_SDACCEL" >> $(INSTALL_1DDR)/setup.csh
	@echo "unsetenv XILINX_SDX" >> $(INSTALL_1DDR)/setup.csh
	@echo "unsetenv XCL_EMULATION_MODE" >> $(INSTALL_1DDR)/setup.csh
	@echo "XILINX_OPENCL="$(INSTALL_1DDR)
	
	install -d $(INSTALL_4DDR)/runtime/platforms/xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0/driver
	install -d $(INSTALL_4DDR)/runtime/bin
	install -d $(INSTALL_4DDR)/runtime/lib/x86_64
	install -m 755 ${SDACCEL_DIR}/userspace/src/libawsxcldrv.so $(INSTALL_4DDR)/runtime/platforms/xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0/driver
	install -m 755 ${SDACCEL_DIR}/tools/awssak/xbsak $(INSTALL_4DDR)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbincat $(INSTALL_4DDR)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbinsplit $(INSTALL_4DDR)/runtime/bin
	#install -m 755 ${XILINX_SDX}/lib/lnx64.o/libxilinxopencl.so $(INSTALL_4DDR)/runtime/lib/x86_64
	install -m 755 ${OPENCLFILE} $(INSTALL_4DDR)/runtime/lib/x86_64
	install -m 755 ${XILINX_SDX}/lib/lnx64.o/libstdc++.so* $(INSTALL_4DDR)/runtime/lib/x86_64
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_4DDR)/setup.sh for bash"
	@echo "export XILINX_OPENCL=$(INSTALL_4DDR)" > $(INSTALL_4DDR)/setup.sh
	@echo "export LD_LIBRARY_PATH=\$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_4DDR)/setup.sh
	@echo "export PATH=\$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_4DDR)/setup.sh
	@echo "unset XILINX_SDACCEL" >> $(INSTALL_4DDR)/setup.sh
	@echo "unset XILINX_SDX" >> $(INSTALL_4DDR)/setup.sh
	@echo "unset XCL_EMULATION_MODE" >> $(INSTALL_4DDR)/setup.sh
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_4DDR)/setup.csh for (t)csh"
	@echo "setenv XILINX_OPENCL $(INSTALL_4DDR)" > $(INSTALL_4DDR)/setup.csh
	@echo "if ( ! \$$?LD_LIBRARY_PATH ) then" >> $(INSTALL_4DDR)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64" >> $(INSTALL_4DDR)/setup.csh
	@echo "else" >> $(INSTALL_4DDR)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_4DDR)/setup.csh
	@echo "endif" >> $(INSTALL_4DDR)/setup.csh
	@echo "if ( ! \$$?PATH ) then" >> $(INSTALL_4DDR)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin" >> $(INSTALL_4DDR)/setup.csh
	@echo "else" >> $(INSTALL_4DDR)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_4DDR)/setup.csh
	@echo "endif" >> $(INSTALL_4DDR)/setup.csh
	@echo "unsetenv XILINX_SDACCEL" >> $(INSTALL_4DDR)/setup.csh
	@echo "unsetenv XILINX_SDX" >> $(INSTALL_4DDR)/setup.csh
	@echo "unsetenv XCL_EMULATION_MODE" >> $(INSTALL_4DDR)/setup.csh
	@echo "XILINX_OPENCL="$(INSTALL_4DDR)
	
	install -d $(INSTALL_4DDR_DEBUG)/runtime/platforms/xilinx_aws-vu9p-f1_4ddr-xpr-2pr-debug_4_0/driver
	install -d $(INSTALL_4DDR_DEBUG)/runtime/bin
	install -d $(INSTALL_4DDR_DEBUG)/runtime/lib/x86_64
	install -m 755 ${SDACCEL_DIR}/userspace/src/libawsxcldrv.so $(INSTALL_4DDR_DEBUG)/runtime/platforms/xilinx_aws-vu9p-f1_4ddr-xpr-2pr-debug_4_0/driver
	install -m 755 ${SDACCEL_DIR}/tools/awssak/xbsak $(INSTALL_4DDR_DEBUG)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbincat $(INSTALL_4DDR_DEBUG)/runtime/bin
	install -m 755 ${XILINX_SDX}/runtime/bin/xclbinsplit $(INSTALL_4DDR_DEBUG)/runtime/bin
	#install -m 755 ${XILINX_SDX}/lib/lnx64.o/libxilinxopencl.so $(INSTALL_4DDR_DEBUG)/runtime/lib/x86_64
	install -m 755 ${OPENCLFILE} $(INSTALL_4DDR_DEBUG)/runtime/lib/x86_64
	install -m 755 ${XILINX_SDX}/lib/lnx64.o/libstdc++.so* $(INSTALL_4DDR_DEBUG)/runtime/lib/x86_64
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_4DDR_DEBUG)/setup.sh for bash"
	@echo "export XILINX_OPENCL=$(INSTALL_4DDR_DEBUG)" > $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "export LD_LIBRARY_PATH=\$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "export PATH=\$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "unset XILINX_SDACCEL" >> $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "unset XILINX_SDX" >> $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "unset XCL_EMULATION_MODE" >> $(INSTALL_4DDR_DEBUG)/setup.sh
	@echo "Generating SDAccel F1 runtime environment setup script, $(INSTALL_4DDR_DEBUG)/setup.csh for (t)csh"
	@echo "setenv XILINX_OPENCL $(INSTALL_4DDR_DEBUG)" > $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "if ( ! \$$?LD_LIBRARY_PATH ) then" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "else" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "    setenv LD_LIBRARY_PATH \$$XILINX_OPENCL/runtime/lib/x86_64:\$$LD_LIBRARY_PATH" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "endif" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "if ( ! \$$?PATH ) then" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "else" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "    setenv PATH \$$XILINX_OPENCL/runtime/bin:\$$PATH" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "endif" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "unsetenv XILINX_SDACCEL" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "unsetenv XILINX_SDX" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "unsetenv XCL_EMULATION_MODE" >> $(INSTALL_4DDR_DEBUG)/setup.csh
	@echo "XILINX_OPENCL="$(INSTALL_4DDR_DEBUG)

.PHONY: all clean

.DEFAULT_GOAL := all
