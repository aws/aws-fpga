# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


###############################################################################
# This contains the CL specific timing constraints for CL
###############################################################################

#################################################################################
### Main Clock
#################################################################################
# Alias of Shell interface clock
set clk_main_a0 [get_clocks -of_objects [get_ports clk_main_a0]]
