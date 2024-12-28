# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


clean:
	@ -rm -rf $(SIM_ROOT)/*.done
	@ -rm -rf $(SIM_ROOT)/xsim.dir
	@ -rm -rf $(SIM_ROOT)/work
	@ -rm -rf $(SIM_ROOT)/*.log
	@ -rm -rf $(SIM_ROOT)/*.pb
	@ -rm -rf $(SIM_ROOT)/tests
	@ -rm -rf $(SIM_DIR)/.Xil
	@ -rm -rf $(SIM_DIR)/xsim.dir
	@ -rm -rf $(SIM_DIR)/*.jou
	@ -rm -rf $(SIM_DIR)/*.pb
	@ -rm -rf $(SIM_DIR)/*.dat
	@ -rm -rf $(SIM_DIR)/*.wdb


XSIM_PLUSARGS_DIRTY = $(subst +define+,--define ,$(PLUSARGS))
XSIM_PLUSARGS = $(subst +, --define ,$(XSIM_PLUSARGS_DIRTY))

XSIM_DEFINES_DIRTY = $(subst +define+,--define ,$(DEFAULT_DEFINES))
XSIM_DEFINES = $(subst +, --define ,$(XSIM_DEFINES_DIRTY))

XSIM_C_INCLUDE_ARGS = $(foreach inc_dir,$(C_INCLUDE_DIRS),--gcc_compile_options "-I$(inc_dir)")

copy_xsim_ini:
ifeq ("$(wildcard $(COMPLIB_DIR)/xsim.ini)","")
	mkdir -p $(COMPLIB_DIR)
	cp $(XILINX_VIVADO)/data/xsim/xsim.ini $(COMPLIB_DIR)
endif

compile: copy_xsim_ini $(COMPILE_CL_IP_DIR) generate_sim_file_list
	cd ${SIM_DIR} && ln -s -f $(COMPLIB_DIR)/xsim.ini
	cd $(SIM_DIR) && xsc $(C_FILES) $(XSIM_C_INCLUDE_ARGS) --gcc_compile_options "-DVIVADO_SIM" --gcc_compile_options "-DSV_TEST" --gcc_compile_options "-DDMA_TEST"
	cd $(SIM_DIR) && xvlog --sv -m64 --define DMA_TEST $(XSIM_PLUSARGS) $(XSIM_DEFINES) --work xil_defaultlib --incr --relax -f $(SCRIPTS_DIR)/top.$(SIMULATOR).f
	cd $(SIM_DIR) && xelab -m64 $(XSIM_PLUSARGS) $(XSIM_DEFINES) --timescale 1ps/1ps --debug typical --relax --mt 8 $(LIBLISTS_ARGS) -sv_lib dpi --snapshot tb xil_defaultlib.tb xil_defaultlib.glbl xil_defaultlib.$(TEST)

run:
ifeq ($(TEST),test_null)
   ifneq ($(C_TEST),test_null)
	cd $(SIM_DIR) && xsim -log $(C_TEST).log -tclbatch $(SCRIPTS_DIR)/waves.tcl tb
   else
	cd $(SIM_DIR) && xsim -log $(TEST).log -tclbatch $(SCRIPTS_DIR)/waves.tcl tb
   endif
else
	cd $(SIM_DIR) && xsim -log $(TEST).log -tclbatch $(SCRIPTS_DIR)/waves.tcl tb
endif
