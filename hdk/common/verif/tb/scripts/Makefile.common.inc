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
else
ifeq ($(VCS), 1)
  export SIMULATOR = vcs
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/vcs/vcs_complib
  include Makefile.vcs
else
ifeq ($(IES), 1)
  export SIMULATOR = ies
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/ies/ies_complib
  include Makefile.ies
else
  export SIMULATOR = vivado
  include Makefile.vivado
endif
endif
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc


regression: $(SV_TEST_LIST) $(C_TEST_LIST) 

$(SV_TEST_LIST):
	make TEST=$(@F)

$(C_TEST_LIST):
	make C_TEST=$(*F)

make_sim_dir:
	sed -e 's/input/input_temp/g; s/output/input logic/g; s/input_temp/output logic/g' < $(HDK_SHELL_DESIGN_DIR)/interfaces/cl_ports.vh > $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh;
	sed -e 's/input logic logic/input logic /g; s/output logic logic/output logic /g' < $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh > $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_sh_bfm.vh;
	rm -f $(HDK_COMMON_DIR)/verif/models/sh_bfm/cl_ports_t.vh;
	mkdir -p $(SIM_ROOT)