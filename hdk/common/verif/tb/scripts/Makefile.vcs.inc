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
	@ -rm -rf $(SIM_ROOT)/*.jou
	@ -rm -rf $(SIM_ROOT)/.cxl.vcs_mx.version
	@ -rm -rf $(SIM_ROOT)/compile_simlib.log
	@ -rm -rf $(SIM_ROOT)/synopsys_sim.setup
	@ -rm -rf $(SIM_ROOT)/vivado.log
	@ -rm -rf $(SIM_ROOT)/AN.DB
	@ -rm -rf $(SIM_ROOT)/csrc
	@ -rm -rf $(SIM_ROOT)/simv*
	@ -rm -rf $(SIM_ROOT)/ucli.key
	@ -rm -rf $(SIM_ROOT)/vc_hdrs.h
	@ -rm -rf $(SIM_ROOT)/*.log
	@ -rm -rf $(SIM_ROOT)/*.done
	@ -rm -rf $(SIM_DIR)


VCS_C_INCLUDE_ARGS = $(foreach inc_dir,$(C_INCLUDE_DIRS),-CFLAGS "-I$(inc_dir)")

compile: $(COMPILE_CL_IP_DIR) generate_sim_file_list
	cd ${SIM_DIR} && ln -s -f $(COMPLIB_DIR)/synopsys_sim.setup
	cd $(SIM_DIR) && vlogan -ntb_opts tb_timescale=1ps/1ps -timescale=1ps/1ps -sverilog +systemverilogext+.sv +libext+.sv +libext+.v +libext+.svh -full64 -lca -v2005 +v2k -l compile.vlogan.log -debug_acc+all -debug_region+cell+encrypt -f $(SCRIPTS_DIR)/top.$(SIMULATOR).f +define+VCS +define+DMA_TEST $(DEFAULT_DEFINES) +lint=TFIPC-L
	cd $(SIM_DIR) && vcs tb $(TEST) $(C_FILES) +error+9999 glbl -debug_region=cell+encrypt +warn=noFCDCI,noFCICIO +note=noFCICIO -Mupdate=0 $(VCS_C_INCLUDE_ARGS) -std=gnu99 -CFLAGS "-DSV_TEST" -CFLAGS "-DSCOPE" -debug_acc+all -debug_region+cell+encrypt -M +lint=TFIPC-L -debug_pp glbl -ntb_opts tb_timescale=1ps/1ps -timescale=1ps/1ps -sverilog -full64 +memcbk -licqueue -lca -v2005 -l compile.vcs.log +plusarg_save +timeout=1ms -ignore initializer_driver_checks

run:
ifeq ($(TEST),test_null)
   ifneq ($(C_TEST),test_null)
	cd $(SIM_DIR) && ./simv -l $(C_TEST).log $(PLUSARGS) +ntb_random_seed_automatic +vpdfile+$(TEST).vpd | $(FILTER_OUT_HBM_META_INJECTIONS)
   else
	cd $(SIM_DIR) && ./simv -l $(TEST).log $(PLUSARGS) +ntb_random_seed_automatic +vpdfile+$(TEST).vpd | $(FILTER_OUT_HBM_META_INJECTIONS)
   endif
else
	cd $(SIM_DIR) && ./simv -l $(TEST).log $(PLUSARGS) +ntb_random_seed_automatic +vpdfile+$(TEST).vpd | $(FILTER_OUT_HBM_META_INJECTIONS)
endif
