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


# Common CL Implementation Tcl Script


# AWS shell DCP location
set AWS_DCP_DIR "${HDK_SHELL_DIR}/build/checkpoints/from_aws/"


###############################################################################
print "Start linking customer design ${CL}"
###############################################################################
add_files ${AWS_DCP_DIR}/cl_bb_routed.${SHELL_MODE}.dcp
add_files ${checkpoints_dir}/${CL}.${TAG}.post_synth.dcp

set_property SCOPED_TO_CELLS {WRAPPER/CL} \
             [get_files ${checkpoints_dir}/${CL}.${TAG}.post_synth.dcp]

link_design -mode default \
            -reconfig_partitions {WRAPPER/CL} \
            -top top

print "Writing post-link design checkpoint"
write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_link.dcp

#######################################
#
# MMCM Clock recipe constraints
#
#######################################
source $HDK_SHELL_DIR/build/scripts/aws_clock_properties.tcl

#######################################
# Floorplan Constraints
#######################################
# Dynamic region floorplan (CL)
read_xdc ${HDK_SHELL_DIR}/build/constraints/${SHELL_MODE}_level_1_fp_cl.xdc

# User defined floorplan (use SLR0/SLR1/SLR2 from main floorplan)
read_xdc ${constraints_dir}/${SHELL_MODE}_cl_pnr_user.xdc

# Optional, MIG placement training
source ${HDK_SHELL_DIR}/build/scripts/ddr_io_train.tcl

# # MMCM cascade placement constraint
# read_xdc ${HDK_SHELL_DESIGN_DIR}/../build/constraints/mmcm_cascade.xdc


###############################################################################
print "Start optimizing customer design ${CL}"
###############################################################################
opt_design

print "Writing post-opt design checkpoint and report"
write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_opt.dcp

report_timing -delay_type max \
              -path_type full_clock_expanded \
              -max_paths 10 \
              -nworst 1 \
              -input_pins \
              -slice_pins \
              -sort_by group \
              -significant_digits 3 \
              -file ${reports_dir}/${CL}.${TAG}.post_opt_timing.rpt


###############################################################################
print "Start placing customer design ${CL}"
###############################################################################
# open_checkpoint ${checkpoints_dir}/${CL}.${TAG}.post_opt.dcp

place_design -directive $PLACE_DIRECT -no_bufg_opt

print "Writing post-place design checkpoint and report"

write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_place.dcp

report_timing -delay_type max \
              -path_type full_clock_expanded \
              -max_paths 10 \
              -nworst 1 \
              -input_pins \
              -slice_pins \
              -sort_by group \
              -significant_digits 3 \
              -file $reports_dir/${CL}.${TAG}.post_place_timing.rpt


###############################################################################
print "Start physical-optimizing customer design ${CL}"
###############################################################################
phys_opt_design -directive $PHY_OPT_DIRECT

print "Writing post-phy_opt design checkpoint and report"

write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_phys_opt.dcp

report_timing -delay_type max \
              -path_type full_clock_expanded \
              -max_paths 10 \
              -nworst 1 \
              -input_pins \
              -slice_pins \
              -sort_by group \
              -significant_digits 3 \
              -file $reports_dir/${CL}.${TAG}.post_phy_opt_timing.rpt


###############################################################################
print "Start routing customer design ${CL}"
###############################################################################
route_design -directive $ROUTE_DIRECT -tns_cleanup

print "Writing post-route design checkpoint and report"

set failPath [check_timing_path]
if {$failPath>0} {
    write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_route.VIOLATED.dcp
} else {
    write_checkpoint -force ${checkpoints_dir}/${CL}.${TAG}.post_route.dcp
}

report_timing -delay_type max \
              -path_type full_clock_expanded \
              -max_paths 10 \
              -nworst 1 \
              -input_pins \
              -slice_pins \
              -sort_by group \
              -significant_digits 3 \
              -file ${reports_dir}/${CL}.${TAG}.post_route_timing.rpt

write_debug_probes -no_partial_ltxfile -force ${checkpoints_dir}/${TAG}.debug_probes.ltx


###############################################################################
print "Finished building design checkpoints for customer design ${CL}"
###############################################################################

close_design
