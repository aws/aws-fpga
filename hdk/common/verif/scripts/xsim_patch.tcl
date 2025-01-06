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
#
# Disable Data Bus Inversion for cl_hbm 
# This is ONLY needed for XSIM simulation with HBM, not needed for other simulators
#
# Source this file if different cl_hbm configuration is desired and regenerate ip simualtion models 
# the new xpm_internal_config* files will replace those in verif/include/xsim_hbm
#
set_property CONFIG.USER_MC0_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC1_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC2_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC3_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC4_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC5_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC6_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC7_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC8_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC9_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC10_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC11_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC12_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC13_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC14_WRITE_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC15_WRITE_DBI_EN false [get_ips cl_hbm]

set_property CONFIG.USER_MC0_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC1_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC2_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC3_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC4_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC5_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC6_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC7_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC8_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC9_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC10_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC11_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC12_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC13_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC14_READ_DBI_EN false [get_ips cl_hbm]
set_property CONFIG.USER_MC15_READ_DBI_EN false [get_ips cl_hbm]
