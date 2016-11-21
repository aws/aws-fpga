## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## Amazon Confidential information
## Restricted NDA Material
## =============================================================================

export XILINX_VIVADO ?= /path/to/Xilinx/Vivado/2016.3
export DESIGN_DIR = $(PWD)/../..
export IMPORT_DESIGN_DIR = $(PWD)/../../v3_venom_cl/v3_venom_cl.srcs/sources_1/imports/rtl
export IP_DESIGN_DIR = $(PWD)/../../v3_venom_cl/v3_venom_cl.srcs/sources_1/ip
export TB_DIR  = $(PWD)/..
export RUN_DIR = $(PWD)/../cl_test
export MODELS_DIR = $(PWD)/../../models
export SCRIPTS_DIR = $(TB_DIR)/scripts
export QUESTA_COMPLIB_DIR = $(DESIGN_DIR)/questa_complib
export DESIGN_NAME = v3_venom_cl