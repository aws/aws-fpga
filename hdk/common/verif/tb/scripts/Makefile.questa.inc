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


clean:
	cd $(SIM_ROOT)/.. && rm -rf modelsim.ini
	cd $(SIM_ROOT)/.. && rm -rf *.log
	cd $(SIM_ROOT)/.. && rm -rf *.jou
	cd $(SIM_ROOT)/.. && rm -rf .cxl.questasim.version
	cd $(SIM_ROOT)/.. && rm -rf compile_simlib.log
	cd $(SIM_ROOT)/.. && rm -rf vivado.log
	cd $(SIM_DIR) && rm -rf work
	cd $(SIM_DIR) && rm -rf transcript

QUESTA_C_INCLUDE_ARGS = $(foreach inc_dir,$(C_INCLUDE_DIRS),-ccflags "-I$(inc_dir)")

compile: $(COMPILE_CL_IP_DIR) generate_sim_file_list
	cd ${SIM_DIR} && ln -s -f $(COMPLIB_DIR)/modelsim.ini
	cd $(SIM_DIR) && vlog $(C_FILES) $(QUESTA_C_INCLUDE_ARGS) -ccflags "-DSV_TEST" -ccflags "-DSCOPE" -ccflags "-DQUESTA_SIM" -ccflags "-DINT_MAIN"
	cd $(SIM_DIR) && vlog +define+QUESTA_SIM +define+DMA_TEST $(DEFAULT_DEFINES) -mfcu -sv -64 -timescale 1ps/1ps -93 -L $(COMPLIB_DIR)/unisims_ver -L $(COMPLIB_DIR)/unimacro_ver -L $(COMPLIB_DIR)/secureip -f $(SCRIPTS_DIR)/top.$(SIMULATOR).f

run:
ifeq ($(TEST),test_null)
   ifneq ($(C_TEST),test_null)
	cd $(SIM_DIR) &&  vsim -c tb $(C_TEST) glbl -voptargs="+acc" -64 -t ps -sv_seed random $(LIBLISTS_ARGS) $(PLUSARGS) -l $(TEST).log -do "run -all; quit -f" | $(FILTER_OUT_HBM_META_INJECTIONS) | $(FILTER_OUT_EMPTY_LINES)
   else
	cd $(SIM_DIR) &&  vsim -c tb $(TEST) glbl -voptargs="+acc" -64 -t ps -sv_seed random $(LIBLISTS_ARGS) $(PLUSARGS) -l $(TEST).log -do "run -all; quit -f" | $(FILTER_OUT_HBM_META_INJECTIONS) | $(FILTER_OUT_EMPTY_LINES)
   endif
else
	cd $(SIM_DIR) &&  vsim -c tb $(TEST) glbl -voptargs="+acc" -64 -t ps -sv_seed random $(LIBLISTS_ARGS) $(PLUSARGS) -l $(TEST).log -do "run -all; quit -f" | $(FILTER_OUT_HBM_META_INJECTIONS) | $(FILTER_OUT_EMPTY_LINES)
endif
