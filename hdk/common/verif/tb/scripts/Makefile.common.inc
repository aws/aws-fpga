# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

ifeq ($(QUESTA), 1)
  export SIMULATOR = questa
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/questa_complib
  include Makefile.questa
else
ifeq ($(VCS), 1)
  export SIMULATOR = vcs
  export COMPLIB_DIR = $(CL_ROOT)/verif/sim/vcs_complib
  include Makefile.vcs
else
  export SIMULATOR = vivado
  include Makefile.vivado
endif
endif

include $(HDK_COMMON_DIR)/verif/tb/scripts/Makefile.$(SIMULATOR).inc

regression: $(SV_TEST_LIST) $(C_TEST_LIST) 

$(SV_TEST_LIST):
	make TEST=$(@F)

$(C_TEST_LIST):
	make C_TEST=$(*F)

make_sim_dir:
	mkdir -p $(SIM_ROOT)