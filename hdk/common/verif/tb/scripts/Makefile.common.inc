#-------------------------------------------------------------------------------
# Amazon FPGA Hardware Development Kit
#
# Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#-------------------------------------------------------------------------------

all: change_simulated_dimm_size make_sim_dir compile run

define \n


endef

define \t

endef

help: ## Display this help
	$(info )
	$(info $(\n)Targets:)
	$(info $(\t)make clean               - Removes all simulator specific files)
	$(info $(\t)make regenerate_sim_libs - Regenerates the simulation libraries located at $(HDK_COMMON_DIR)/verif/ip_simulation_libraries)
	$(info $(\t)make recompile_cl_ips    - Recompile the CL IP source files after generating the simulation libraries)
	$(info )
	$(info $(\n)Supported simulators:)
	$(info $(\t)XSIM (default) - Set this to use the Xilinx Vivado XSIM simulator)
	$(info $(\t)VCS            - Set this to use the Synopsys VCS simulator)
	$(info $(\t)QUESTA         - Set this to use the Modelsim Questa simulator)
	$(info )
	$(info SH_DDR Configuration: "make <TEST TARGET> USE_64GB_DDR_DIMM=1")
	$(info $(\t)USE_32GB_DDR_DIMM (DEFAULT) - Set this to use a 32GB DDR DIMM for simulations)
	$(info $(\t)USE_64GB_DDR_DIMM           - Set this to use a 64GB DDR DIMM for simulations)
	$(info $(\t)USE_AP_32GB_DDR_DIMM        - Set this to use a 32GB DDR DIMM with user-controlled Auto Precharge for simulations)
	$(info $(\t)USE_AP_64GB_DDR_DIMM        - Set this to use a 64GB DDR DIMM with user-controlled Auto Precharge for simulations)
	$(info $(\n))

VCS    ?= 0 ## Set 'VCS=1' ## Enable VCS simulations
QUESTA ?= 0
IES    ?= 0

ifeq ($(filter $(strip $(QUESTA)), 0 1),)
   $(error Variable QUESTA is set to the value other than 0 or 1 -> QUESTA=$(QUESTA). Exiting...)
endif
ifeq ($(filter $(strip $(VCS)), 0 1),)
   $(error Variable VCS is set to the value other than 0 or 1 -> VCS=$(VCS). Exiting...)
endif
ifeq ($(filter $(strip $(IES)), 0 1),)
   $(error Variable IES is set to the value other than 0 or 1 -> IES=$(IES). Exiting...)
endif

ifneq ($(filter $(strip $(QUESTA))$(strip $(VCS))$(strip $(IES)), 000),)
   define  = --define $(strip $(1))
   plusarg = --testplusarg "$(strip $(1))"
   export SIMULATOR = xsim
else
   ifeq ($(filter $(strip $(QUESTA))$(strip $(VCS))$(strip $(IES)), 100 010 001),)
      $(info Shall not enable QUESTA=$(strip $(QUESTA)) VCS=$(strip $(VCS)) IES=$(strip $(IES)) altogether!)
      $(error Choose only one of them! Exiting...)
   endif
   define  = +define+$(strip $(1))
   plusarg = +$(strip $(1))
   ifeq ($(strip $(QUESTA)), 1)
      export SIMULATOR = questa
   endif
   ifeq ($(strip $(VCS)), 1)
      export SIMULATOR = vcs
   endif
   ifeq ($(strip $(IES)), 1)
      export SIMULATOR = ies
   endif
endif

DEFAULT_DEFINES ?=
DEFAULT_DEFINES += +define+AWS_SIM
PLUSARGS ?=
PLUSARGS += +plusarg_save +timeout=1ms

DDR4_RDIMM_WRAPPER = $(HDK_COMMON_DIR)/verif/models/ddr4_rdimm_wrapper/ddr4_rdimm_wrapper.sv
DIMM_REPLACEMENT = "NONE"

ifeq ($(USE_64GB_DDR_DIMM), 1)
   DEFAULT_DEFINES += $(call define, USE_64GB_DDR_DIMM=1)
   DIMM_REPLACEMENT = sed -i s/_8G/_16G/g $(DDR4_RDIMM_WRAPPER)
else
   ifeq ($(USE_AP_64GB_DDR_DIMM), 1)
      DEFAULT_DEFINES += $(call define, USE_AP_64GB_DDR_DIMM=1)
      DIMM_REPLACEMENT = sed -i s/_8G/_16G/g $(DDR4_RDIMM_WRAPPER)
   else
      ifeq ($(USE_AP_32GB_DDR_DIMM), 1)
         DEFAULT_DEFINES += $(call define, USE_AP_32GB_DDR_DIMM=1)
         DIMM_REPLACEMENT = sed -i s/_16G/_8G/g $(DDR4_RDIMM_WRAPPER)
      else
         DEFAULT_DEFINES += $(call define, USE_32GB_DDR_DIMM=1)
         DIMM_REPLACEMENT = sed -i s/_16G/_8G/g $(DDR4_RDIMM_WRAPPER)
      endif
   endif
endif

change_simulated_dimm_size:
	$(DIMM_REPLACEMENT)
	echo "Updating simulated DIMM configuration: $(DIMM_REPLACEMENT)"


# Simulation variables and directory name changes
ifeq ($(C_TEST),test_null)
   # The AXI memory model offers error correction checking
   ifeq ($(AXI_MEMORY_MODEL), 1)
      DEFAULT_DEFINES += $(call define, FAST_SIM_MODE)
      DEFAULT_DEFINES += $(call define, NO_DDR)

      ifeq ($(ECC_DIRECT), 1)
         DEFAULT_DEFINES += $(call define, ECC_DIRECT_EN=1)
         DEFAULT_DEFINES += $(call define, RND_ECC_EN=0)
         DEFAULT_DEFINES += $(call define, RND_ECC_WEIGHT=0)
         DEFAULT_DEFINES += $(call define, ECC_ADDR_HI=$(ECC_ADDR_HI))
         DEFAULT_DEFINES += $(call define, ECC_ADDR_LO=$(ECC_ADDR_LO))
	 SIM_DIR_EXTENSION = _sv_fast_ecc_direct
      else

         DEFAULT_DEFINES += $(call define, ECC_DIRECT_EN=0)
         DEFAULT_DEFINES += $(call define, RND_ECC_WEIGHT=$(RND_ECC_WEIGHT))

         ifeq ($(ECC_RAND), 1)
            DEFAULT_DEFINES += $(call define, RND_ECC_EN=1)
	    SIM_DIR_EXTENSION = _sv_fast_ecc_rnd
         else
            DEFAULT_DEFINES += $(call define, RND_ECC_EN=0)
	    SIM_DIR_EXTENSION = _sv_fast
         endif

         DEFAULT_DEFINES += $(call define, ECC_ADDR_HI=0)
         DEFAULT_DEFINES += $(call define, ECC_ADDR_LO=0)
      endif
   else

      SIM_DIR_EXTENSION = _sv
   endif

   export SIM_DIR = $(SIM_ROOT)/$(TEST)$(SIM_DIR_EXTENSION)
else
   SIM_DIR_EXTENSION = _c
   export SIM_DIR = $(SIM_ROOT)/$(C_TEST)$(SIM_DIR_EXTENSION)
endif

COMMON_LIBLISTS =\
   unisims_ver\
   unisim\
   unifast_ver\
   unifast\
   unimacro_ver\
   unimacro\
   secureip\
   xpm\
   xil_defaultlib\
   axi_dwidth_converter_v2_1_31\
   axi_protocol_converter_v2_1_31\
   axi_protocol_checker_v2_0_17\
   hbm2e_pl_v1_0_1\
   noc_hbm_v1_0_0\
   hbm_v1_0_16\
   axi_register_slice_v2_1_31\
   axi_infrastructure_v1_1_0\
   axi_crossbar_v2_1_32\
   axi_clock_converter_v2_1_30\
   fifo_generator_v13_2_10\
   axi_data_fifo_v2_1_30\
   generic_baseblocks_v2_1_2\
   lut_buffer_v2_0_1\
   xsdbm_v3_0_2\
   xdma_v4_1_29\
   xlconstant_v1_1_9\
   smartconnect_v1_0

LIBLISTS_ARGS = $(shell echo " $(strip $(COMMON_LIBLISTS))" | sed 's|\ | -L |g')

FILTER_OUT_EMPTY_LINES = grep -v "^\# $$" | sed '/^$$/d'
FILTER_OUT_HBM_META_INJECTIONS = grep -v "\*\*\*Meta" | sed '/^$$/d'


#
#- GENERATE SIMULATION LIBRARIES
#

export IP_SIM_DIR = $(HDK_COMMON_DIR)/verif/ip_simulation_libraries
ifndef COMPLIB_DIR
   export COMPLIB_DIR = $(IP_SIM_DIR)/$(strip $(SIMULATOR))_complib
endif

ifndef COMPILE_CL_IP_DIR
   export COMPILE_CL_IP_DIR = $(IP_SIM_DIR)/$(strip $(SIMULATOR))_compiled_cl_ips
endif

# DO NOT REMOVE: This is used to space out prints
define n
endef


export COMPLIB_IN_PROGRESS = $(IP_SIM_DIR)/$(strip $(SIMULATOR))_complib_dir_in_progress
check_complib_in_progress:
ifneq ("$(wildcard $(COMPLIB_IN_PROGRESS))","")
	$(error "$n ERROR: Simulation library compilation is in progress $n")
else
	mkdir -p $(COMPLIB_DIR) && touch $(COMPLIB_IN_PROGRESS)
endif


export CL_IP_IN_PROGRESS = $(IP_SIM_DIR)/$(strip $(SIMULATOR))_compile_cl_ips_dir_in_progress
check_cl_ip_in_progress:
ifneq ("$(wildcard $(CL_IP_IN_PROGRESS))","")
	$(error "$n ERROR: CL IP compilation is in progress $n")
else
	mkdir -p $(COMPILE_CL_IP_DIR) && touch $(CL_IP_IN_PROGRESS)
endif


regenerate_sim_libs: check_complib_in_progress
	rm -rf $(COMPLIB_DIR)
	rm -f $(COMPLIB_IN_PROGRESS)
	$(MAKE) $(COMPLIB_DIR)
	$(MAKE) recompile_cl_ips


recompile_cl_ips: check_cl_ip_in_progress
	rm -rf $(COMPILE_CL_IP_DIR)
	rm -f $(CL_IP_IN_PROGRESS)
	$(MAKE) $(COMPILE_CL_IP_DIR)


$(COMPLIB_DIR): check_complib_in_progress
ifeq ("$(SIMULATOR)","xsim")
	$(info "$n WARNING: XSIM does not require simulation library compilation $n")
else
ifeq ("$(wildcard $(COMPLIB_DIR))","")
	mkdir -p $(SIM_ROOT)
	cd $(SIM_ROOT) && echo "compile_simlib -language all -dir $(COMPLIB_DIR) -simulator $(SIMULATOR) -no_systemc_compile -library all -family  all" > create_libs.tcl
	cd $(SIM_ROOT) && vivado -mode batch -source create_libs.tcl
	cd $(SIM_ROOT) && rm -rf create_libs.tcl
endif
endif
	rm -f $(COMPLIB_IN_PROGRESS)


$(COMPILE_CL_IP_DIR): check_cl_ip_in_progress $(COMPLIB_DIR)
ifeq ("$(SIMULATOR)","xsim")
	$(MAKE) copy_xsim_ini
endif
ifeq ("$(wildcard $(COMPILE_CL_IP_DIR)/done)","")
	$(HDK_COMMON_DIR)/verif/scripts/compile_cl_ips.py --simulator $(SIMULATOR) --complib_dir $(COMPLIB_DIR) --compile_cl_ip_dir $(COMPILE_CL_IP_DIR) --in_progress_file $(CL_IP_IN_PROGRESS);
endif
	rm -f $(CL_IP_IN_PROGRESS)


#
include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(strip $(SIMULATOR)).inc
#


#
#- AUTO GENERATE SIM FILE LIST
#
generate_sim_file_list:
ifndef DONT_GENERATE_FILE_LIST
	$(HDK_COMMON_DIR)/verif/scripts/generate_sim_file_list.py --cl_dir $(CL_DIR) --simulator $(SIMULATOR)
endif


$(HDK_COMMON_DIR)/verif/models/fpga/fpga_ports.vh:
	#
	#- CREATE CL_PORTS ----------
	#
	@ perl $(HDK_COMMON_DIR)/verif/scripts/cl_ports_gen.pl


$(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh: $(HDK_SHELL_DESIGN_DIR)/interfaces/cl_ports.vh $(HDK_COMMON_DIR)/verif/models/fpga/fpga_ports.vh
	#
	#- CREATE CL_PORTS ----------
	#
	@ perl $(HDK_COMMON_DIR)/verif/scripts/cl_ports_gen.pl

make_sim_dir: $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh
	#
	#- CREATE SIM_ROOT ----------
	#
	@ if [ ! -d $(SIM_DIR) ]; then \
      mkdir -p $(SIM_DIR);\
      cp $(HDK_COMMON_DIR)/verif/include/xpm_internal_config* $(SIM_DIR) 2>/dev/null; \
      touch $(SIM_DIR)/bd_2e02_lmb_bram_I_0.mem $(SIM_DIR)/bd_2e02_second_lmb_bram_I_0.mem; \
   fi

#
# Command wrapper API source
#
SIMSCR = source $(HDK_COMMON_DIR)/verif/tb/scripts/simapi.sh

#
# Regression Sub-Targets
#

# Get name of target for all tests that are not commented out
DEFAULT_REGRESSION_TEST_LIST_COLLECTION=$(shell grep -h TEST ${CL_DIR}/verif/scripts/Makefile.tests | grep -v '^.*\#.*TEST' | sed 's/:.*//g' | xargs)


REGRESSION_RESULTS_LOG = $(PWD)/$(SIMULATOR)_regression_results$(SIM_DIR_EXTENSION).log
run_regression:
	for test_name in $(REGRESSION_TEST_LIST) ; do \
		$(MAKE) $$test_name AXI_MEMORY_MODEL=$(AXI_MEMORY_MODEL) ECC_DIRECT=$(ECC_DIRECT) ECC_RAND=$(ECC_RAND) ECC_ADDR_HI=$(ECC_ADDR_HI) ECC_ADDR_LO=$(ECC_ADDR_LO) RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) XSIM=$(XSIM) VCS=$(VCS) QUESTA=$(QUESTA) ; \
	done


log_regression_results:
	$(HDK_COMMON_DIR)/verif/scripts/log_regression_results.py --simulator $(SIMULATOR) --cl_dir $(CL_DIR) --regression_results_log $(REGRESSION_RESULTS_LOG) --sim_dir_extension "$(SIM_DIR_EXTENSION)"

print_regression_results:
	echo "" ; \
	echo "*** SEE RESULTS IN '$(REGRESSION_RESULTS_LOG)'" ; \
	cat $(REGRESSION_RESULTS_LOG) ; \

check_xsim:
ifeq ("$(SIMULATOR)","xsim")
   $(info "$n **** WARNING CHECK_XSIM This test is not supported for XSIM simulator **** $n")
endif
