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

ifeq ($(QUESTA), 1)
  export SIMULATOR = questa
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/questa/questa_complib
  include Makefile.questa
    ifeq ($(AXI_MEMORY_MODEL), 1)
    ifeq ($(ECC_DIRECT), 1)
      DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=1 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=0 +define+ECC_ADDR_HI=$(ECC_ADDR_HI) +define+ECC_ADDR_LO=$(ECC_ADDR_LO)
    else 
      ifeq ($(ECC_RAND), 1)
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=1 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      else
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      endif
    endif
  else
    ifeq ($(DDR_BKDR), 1)
      PLUSARGS =+HDKDIR=$(HDK_DIR)
    endif
    export DEFAULT_DEFINES =
  endif
else
ifeq ($(VCS), 1)
  export SIMULATOR = vcs
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/vcs/vcs_complib
  include Makefile.vcs
  ifeq ($(AXI_MEMORY_MODEL), 1)
    ifeq ($(ECC_DIRECT), 1)
      DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=1 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=0 +define+ECC_ADDR_HI=$(ECC_ADDR_HI) +define+ECC_ADDR_LO=$(ECC_ADDR_LO)
    else 
      ifeq ($(ECC_RAND), 1)
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=1 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      else
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      endif
    endif
  else
    ifeq ($(DDR_BKDR), 1)
      PLUSARGS =+HDKDIR=$(HDK_DIR)
    endif
    export DEFAULT_DEFINES =
  endif
else
ifeq ($(IES), 1)
  export SIMULATOR = ies
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/ies/ies_complib
  include Makefile.ies
  ifeq ($(AXI_MEMORY_MODEL), 1)
    ifeq ($(ECC_DIRECT), 1)
      DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=1 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=0 +define+ECC_ADDR_HI=$(ECC_ADDR_HI) +define+ECC_ADDR_LO=$(ECC_ADDR_LO)
    else 
      ifeq ($(ECC_RAND), 1)
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=1 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      else
        DEFAULT_DEFINES = +define+AXI_MEMORY_MODEL +define+NO_DDR +define+ECC_DIRECT_EN=0 +define+RND_ECC_EN=0 +define+RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) +define+ECC_ADDR_HI=0 +define+ECC_ADDR_LO=0
      endif
    endif
  else
    ifeq ($(DDR_BKDR), 1)
      PLUSARGS =+HDKDIR=$(HDK_DIR)
    endif
    export DEFAULT_DEFINES =
  endif
else
  export SIMULATOR = vivado
  include Makefile.vivado
  ifeq ($(AXI_MEMORY_MODEL), 1)
    ifeq ($(ECC_DIRECT), 1)
      DEFAULT_DEFINES = --define AXI_MEMORY_MODEL --define NO_DDR --define ECC_DIRECT_EN=1 --define RND_ECC_EN=0 --define RND_ECC_WEIGHT=0 --define ECC_ADDR_HI=$(ECC_ADDR_HI) --define ECC_ADDR_LO=$(ECC_ADDR_LO)
    else 
      ifeq ($(ECC_RAND), 1)
        DEFAULT_DEFINES = --define AXI_MEMORY_MODEL --define NO_DDR --define ECC_DIRECT_EN=0 --define RND_ECC_EN=1 --define RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) --define ECC_ADDR_HI=0 --define ECC_ADDR_LO=0
      else
        DEFAULT_DEFINES = --define AXI_MEMORY_MODEL --define NO_DDR --define ECC_DIRECT_EN=0 --define RND_ECC_EN=0 --define RND_ECC_WEIGHT=$(RND_ECC_WEIGHT) --define ECC_ADDR_HI=0 --define ECC_ADDR_LO=0
      endif
    endif
  else
    ifeq ($(DDR_BKDR), 1)
      PLUSARGS = --testplusarg "HDKDIR=$(HDK_DIR)"
    endif
    export DEFAULT_DEFINES =
  endif
endif
endif
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc

regression: $(SV_TEST_LIST) $(C_TEST_LIST) 

$(SV_TEST_LIST):
	make TEST=$(@F)

$(C_TEST_LIST):
	make C_TEST=$(*F)

$(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh: $(HDK_SHELL_DESIGN_DIR)/interfaces/cl_ports.vh
	sed -e 's/input/input_temp/g; s/output/input logic/g; s/input_temp/output logic/g' < $(HDK_SHELL_DESIGN_DIR)/interfaces/cl_ports.vh > $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh;
	sed -e 's/input logic logic/input logic /g; s/output logic logic/output logic /g' < $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh > $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh;
	rm -f $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh;

make_sim_dir: $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh
	mkdir -p $(SIM_ROOT)
