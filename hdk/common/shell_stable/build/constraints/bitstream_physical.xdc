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


# Bitstream generation constraints


###############################################################################
# TODO
###############################################################################
set_property CONFIG_MODE                       SPIx4    [current_design]
set_property CONFIG_VOLTAGE                    1.8      [current_design]
set_property BITSTREAM.GENERAL.COMPRESS        TRUE     [current_design]
##set_property BITSTREAM.CONFIG.OVERTEMPSHUTDOWN ENABLE   [current_design]
set_property BITSTREAM.CONFIG.USR_ACCESS       00000000 [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE       85.0     [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR   YES      [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE    YES      [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH     4        [current_design]
