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


# Level 1 CL region floorplan


###############################################################################
# Parent Pblock
###############################################################################
########################################
# Pblock
########################################
create_pblock pblock_CL

# Complete CRs in SLR2
resize_pblock pblock_CL -add {CLOCKREGION_X0Y8:CLOCKREGION_X7Y11}

# Complete CRs in SLR1
resize_pblock pblock_CL -add {CLOCKREGION_X0Y4:CLOCKREGION_X3Y7}
resize_pblock pblock_CL -add {CLOCKREGION_X5Y1:CLOCKREGION_X5Y7}

# Complete CRs in SLR0
resize_pblock pblock_CL -add {CLOCKREGION_X0Y0:CLOCKREGION_X3Y3}
resize_pblock pblock_CL -add {CLOCKREGION_X4Y0:CLOCKREGION_X7Y0}
resize_pblock pblock_CL -add {CLOCKREGION_X4Y3:CLOCKREGION_X4Y3}
resize_pblock pblock_CL -add {CLOCKREGION_X6Y1:CLOCKREGION_X6Y1}

# Partial CRs in SLR2 & SLR1
resize_pblock pblock_CL -add {SLICE_X176Y240:SLICE_X188Y719 \
                              DSP48E2_X25Y90:DSP48E2_X26Y281 \
                              LAGUNA_X24Y120:LAGUNA_X25Y599 \
                              RAMB18_X11Y96:RAMB18_X11Y287 \
                              RAMB36_X11Y48:RAMB36_X11Y143 \
                              URAM288_X4Y64:URAM288_X4Y191}

# Partial CRs in SLR1
resize_pblock pblock_CL -add {SLICE_X120Y240:SLICE_X145Y479 \
                              DSP48E2_X16Y90:DSP48E2_X19Y185 \
                              LAGUNA_X16Y120:LAGUNA_X19Y359 \
                              RAMB18_X8Y96:RAMB18_X9Y191 \
                              RAMB36_X8Y48:RAMB36_X9Y95 \
                              URAM288_X2Y64:URAM288_X2Y127}

#Remove CLB for SLR1 I/O shim
resize_pblock pblock_CL -remove SLICE_X120Y300:SLICE_X121Y359

# Added the 3 CR (Used to be for IO_SHIM)
resize_pblock pblock_CL -add {CLOCKREGION_X4Y6:CLOCKREGION_X4Y7}
resize_pblock pblock_CL -add {CLOCKREGION_X4Y4:CLOCKREGION_X4Y4}

# Partial CRs in SLR0
resize_pblock pblock_CL -add {SLICE_X176Y120:SLICE_X190Y239 \
                              DSP48E2_X25Y42:DSP48E2_X26Y89 \
                              LAGUNA_X24Y0:LAGUNA_X25Y119 \
                              RAMB18_X11Y48:RAMB18_X11Y95 \
                              RAMB36_X11Y24:RAMB36_X11Y47 \
                              URAM288_X4Y32:URAM288_X4Y63}

resize_pblock pblock_CL -add {SLICE_X120Y120:SLICE_X145Y179 \
                              DSP48E2_X16Y42:DSP48E2_X19Y65 \
                              RAMB18_X8Y48:RAMB18_X9Y71 \
                              RAMB36_X8Y24:RAMB36_X9Y35 \
                              URAM288_X2Y32:URAM288_X2Y47}

resize_pblock pblock_CL -add {SLICE_X118Y60:SLICE_X145Y119 \
                              DSP48E2_X16Y18:DSP48E2_X19Y41 \
                              RAMB18_X8Y24:RAMB18_X9Y47 \
                              RAMB36_X8Y12:RAMB36_X9Y23 \
                              URAM288_X2Y16:URAM288_X2Y31}

resize_pblock pblock_CL -add {SLICE_X206Y60:SLICE_X219Y119 \
                              DSP48E2_X30Y18:DSP48E2_X30Y41 \
                              RAMB18_X12Y24:RAMB18_X12Y47 \
                              RAMB36_X12Y12:RAMB36_X12Y23}

resize_pblock pblock_CL -add {SLICE_X221Y60:SLICE_X232Y119 \
                              DSP48E2_X31Y18:DSP48E2_X31Y41 \
                              RAMB18_X13Y24:RAMB18_X13Y47 \
                              RAMB36_X13Y12:RAMB36_X13Y23 \
                              BUFG_GT_X1Y24:BUFG_GT_X1Y47 \
                              BUFG_GT_SYNC_X1Y15:BUFG_GT_SYNC_X1Y29 \
                              GTYE4_COMMON_X1Y1:GTYE4_COMMON_X1Y1 \
                              GTYE4_CHANNEL_X1Y4:GTYE4_CHANNEL_X1Y7}

########################################
# Parameters and Adjustment
########################################
set_property SNAPPING_MODE ON [get_pblocks pblock_CL]
set_property IS_SOFT       0  [get_pblocks pblock_CL]

resize_pblock pblock_CL -remove {SLICE_X117Y60:SLICE_X117Y119}

#Remove space for unoptimized design
resize_pblock pblock_CL -remove {SLICE_X178Y240:SLICE_X190Y479 \
                                 DSP48E2_X25Y90:DSP48E2_X26Y185 \
                                 LAGUNA_X24Y120:LAGUNA_X25Y359 \
                                 RAMB18_X11Y96:RAMB18_X11Y191 \
                                 RAMB36_X11Y48:RAMB36_X11Y95 \
                                 URAM288_X4Y64:URAM288_X4Y127}
resize_pblock pblock_CL -remove {SLICE_X176Y120:SLICE_X190Y239 \
                                 DSP48E2_X25Y42:DSP48E2_X26Y89 \
                                 LAGUNA_X24Y0:LAGUNA_X25Y119 \
                                 RAMB18_X11Y48:RAMB18_X11Y95 \
                                 RAMB36_X11Y24:RAMB36_X11Y47 \
                                 URAM288_X4Y32:URAM288_X4Y63}
resize_pblock pblock_CL -remove {SLICE_X176Y240:SLICE_X177Y479}

########################################
# Module Mapping
########################################
add_cells_to_pblock pblock_CL [get_cells [list WRAPPER/CL]]
