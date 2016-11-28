## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================


include Makefile.inc

ifeq ($(VCS), 1)
include Makefile.vcs
else
ifeq ($(IES), 1)
include Makefile.ies
else
include Makefile.questa
endif
endif

ifeq ($(REGRESS), 1)
export FILES_DIR=$(COMPILE_DIR)/$(COMPILE_SUBDIR)
else
export FILES_DIR=$(RUN_DIR)/$(RUN_SUBDIR)/$(TEST_DIR)
endif

UVM_TESTNAME ?= uvm_null_test

DEFINES ?= # Blank if not specified on command line
ifeq ($(REGRESS), 1)
PLUSARGS ?= # Blank if not specified on command line
override PLUSARGS += +NO_WAVES
else
PLUSARGS ?= # Blank if not specified on command line
endif
DEFAULT_DEFINES ?= +define+PIPE_SIM +define+NO_ICAP +define+SIM +define+SYNC_SIM_META +define+SYNC_SIM_META_PROB=20 +define+NO_SYS_MGT
COMPILE_SUBDIR ?= #Blank if not specified on command line
FILES ?= $(SCRIPTS_DIR)/filelist.f

override PLUSARGS += +UVM_TESTNAME=$(UVM_TESTNAME)

SIMV_EXISTS=$(shell [ -e $(COMPILE_DIR)/$(COMPILE_SUBDIR)/simv ] && echo 1 || echo 0 )
LOG_EXTENSION ?= clean.log
LOG_EXISTS=$(shell [ -e $(RUN_DIR)/$(RUN_SUBDIR)/$(TEST_DIR)/$(TESTNAME).$(LOG_EXTENSION) ] && echo 1 || echo 0 )
FAIL_EXISTS=$(shell grep 'TEST FAIL' $(RUN_DIR)/$(RUN_SUBDIR)/$(TEST_DIR)/$(TESTNAME).$(LOG_EXTENSION) | wc -l)
ERROR_EXISTS=$(shell grep 'ERROR' $(RUN_DIR)/$(RUN_SUBDIR)/$(TEST_DIR)/$(TESTNAME).$(LOG_EXTENSION) | wc -l)
PASS_EXISTS=$(shell grep 'TEST PASS' $(RUN_DIR)/$(RUN_SUBDIR)/$(TEST_DIR)/$(TESTNAME).$(LOG_EXTENSION) | wc -l)

REGRESS ?= 0
RESULTS_FILE ?= results.log

cl_pcie: TESTNAME = pcie_test
cl_pcie: RUN_SUBDIR ?= cl
cl_pcie: TEST_DIR = pcie_test
cl_pcie: run check

cl_ddr0: TESTNAME = ddr_test
cl_ddr0: RUN_SUBDIR ?= cl
cl_ddr0: TEST_DIR = ddr0_test
cl_ddr0: override PLUSARGS += +TEST_DDR=0
cl_ddr0: run check

cl_ddr1: TESTNAME = ddr_test
cl_ddr1: RUN_SUBDIR ?= cl
cl_ddr1: TEST_DIR = ddr1_test
cl_ddr1: override PLUSARGS += +TEST_DDR=1
cl_ddr1: run check

cl_ddr2: TESTNAME = ddr_test
cl_ddr2: RUN_SUBDIR ?= cl
cl_ddr2: TEST_DIR = ddr2_test
cl_ddr2: override PLUSARGS += +TEST_DDR=2
cl_ddr2: run check

cl_ddr3: TESTNAME = ddr_test
cl_ddr3: RUN_SUBDIR ?= cl
cl_ddr3: TEST_DIR = ddr3_test
cl_ddr3: override PLUSARGS += +TEST_DDR=3
cl_ddr3: run check

