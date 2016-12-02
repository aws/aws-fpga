## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

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

