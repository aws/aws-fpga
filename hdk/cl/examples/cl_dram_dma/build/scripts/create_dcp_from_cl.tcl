#//---------------------------------------------------------------------------------------
#// Amazon FGPA Hardware Development Kit
#//
#// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#//
#// Licensed under the Amazon Software License (the "License"). You may not use
#// this file except in compliance with the License. A copy of the License is
#// located at
#//
#//    http://aws.amazon.com/asl/
#//
#// or in the "license" file accompanying this file. This file is distributed on
#// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
#// implied. See the License for the specific language governing permissions and
#// limitations under the License.
#//---------------------------------------------------------------------------------------

package require tar

#################################################
## Command-line Arguments
#################################################
set timestamp     [lindex $argv 0]
set strategy      [lindex $argv 1]
set hdk_version   [lindex $argv 2]
set shell_version [lindex $argv 3]

#################################################
## Generate CL_routed.dcp (Done by User)
#################################################
puts "AWS FPGA Scripts";
puts "Creating Design Checkpoint from Custom Logic source code";
puts "HDK Version:        $hdk_version";
puts "Shell Version:      $shell_version";
puts "Vivado Script Name: $argv0";

#checking if CL_DIR env variable exists
if { [info exists ::env(CL_DIR)] } {
        set CL_DIR $::env(CL_DIR)
        puts "Using CL directory $CL_DIR";
} else {
        puts "Error: CL_DIR environment variable not defined ! ";
        puts "Use export CL_DIR=Your_Design_Root_Directory"
        exit 2
}

#checking if HDK_SHELL_DIR env variable exists
if { [info exists ::env(HDK_SHELL_DIR)] } {
        set HDK_SHELL_DIR $::env(HDK_SHELL_DIR)
        puts "Using Shell directory $HDK_SHELL_DIR";
} else {
        puts "Error: HDK_SHELL_DIR environment variable not defined ! ";
        puts "Run the hdk_setup.sh script from the root directory of aws-fpga";
        exit 2
}

puts "All reports and intermediate results will be time stamped with $timestamp";

set_msg_config -severity INFO -suppress
set_msg_config -severity STATUS -suppress
set_msg_config -severity WARNING -suppress
set_msg_config -id {Chipscope 16-3} -suppress
set_msg_config -string {AXI_QUAD_SPI} -suppress

puts "AWS FPGA: Calling the encrypt.tcl";

source encrypt.tcl

#This sets the Device Type
source $HDK_SHELL_DIR/build/scripts/device_type.tcl

create_project -in_memory -part [DEVICE_TYPE] -force

set_param chipscope.enablePRFlow true

#############################
## Read design files
#############################

#---- User would replace this section -----

#Convenience to set the root of the RTL directory
set ENC_SRC_DIR $CL_DIR/build/src_post_encryption

puts "AWS FPGA: Reading developer's Custom Logic files post encryption";

read_verilog -sv [ glob $ENC_SRC_DIR/*.vh ]

#Global defines (this is specific to the CL design).  This file is encrypted by encrypt.tcl
set_property file_type {Verilog Header} [get_files $ENC_SRC_DIR/cl_dram_dma_defines.vh ]
set_property is_global_include true [get_files $ENC_SRC_DIR/cl_dram_dma_defines.vh ]

#User design files (these are the files that were encrypted by encrypt.tcl)
read_verilog -sv [ glob $ENC_SRC_DIR/*.?v ]

#---- End of section replaced by User ----
puts "AWS FPGA: Reading AWS Shell design";

#Read AWS Design files
read_verilog [ list \
  $HDK_SHELL_DIR/design/lib/flop_fifo.sv \
  $HDK_SHELL_DIR/design/lib/flop_fifo_in.sv \
  $HDK_SHELL_DIR/design/lib/bram_2rw.sv \
  $HDK_SHELL_DIR/design/lib/flop_ccf.sv \
  $HDK_SHELL_DIR/design/lib/ccf_ctl.v \
  $HDK_SHELL_DIR/design/lib/sync.v \
  $HDK_SHELL_DIR/design/lib/axi4_ccf.sv \
  $HDK_SHELL_DIR/design/lib/axi4_flop_fifo.sv \
  $HDK_SHELL_DIR/design/lib/lib_pipe.sv \
  $HDK_SHELL_DIR/design/lib/mgt_acc_axl.sv  \
  $HDK_SHELL_DIR/design/lib/mgt_gen_axl.sv  \
  $HDK_SHELL_DIR/design/interfaces/sh_ddr.sv \
  $HDK_SHELL_DIR/design/interfaces/cl_ports.vh 
]

puts "AWS FPGA: Reading IP blocks";
#Read DDR IP
read_ip [ list \
  $HDK_SHELL_DIR/design/ip/ddr4_core/ddr4_core.xci 
]

#Read IP for axi register slices
read_ip [ list \
  $HDK_SHELL_DIR/design/ip/src_register_slice/src_register_slice.xci \
  $HDK_SHELL_DIR/design/ip/axi_clock_converter_0/axi_clock_converter_0.xci \
  $HDK_SHELL_DIR/design/ip/dest_register_slice/dest_register_slice.xci 
]

#Read IP for virtual jtag / ILA/VIO
read_ip [ list \
  $HDK_SHELL_DIR/design/ip/cl_debug_bridge/cl_debug_bridge.xci \
  $HDK_SHELL_DIR/design/ip/ila_1/ila_1.xci \
  $HDK_SHELL_DIR/design/ip/ila_vio_counter/ila_vio_counter.xci \
  $HDK_SHELL_DIR/design/ip/vio_0/vio_0.xci
]
read_bd [ list \
$HDK_SHELL_DIR/design/ip/cl_axi_interconnect/cl_axi_interconnect.bd
]

puts "AWS FPGA: Reading AWS constraints";

#Read all the constraints
#
#  cl_synth_aws.xdc  - AWS provided constraints.          ***DO NOT MODIFY***
#  cl_clocks_aws.xdc - AWS provided clock constraint.     ***DO NOT MODIFY***
#  cl_ddr.xdc        - AWS provided DDR pin constraints.  ***DO NOT MODIFY***
read_xdc [ list \
   $HDK_SHELL_DIR/build/constraints/cl_clocks_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc \
   $CL_DIR/build/constraints/cl_synth_user.xdc
]

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]

########################
# CL Synthesis
########################
puts "AWS FPGA: Start design synthesis";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers -flatten_hierarchy rebuilt
    }
    "TIMING" {
        puts "TIMING strategy."
        synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context -no_lc -shreg_min_size 5 -fsm_extraction one_hot -resource_sharing off 
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context -directive AlternateRoutability -no_lc -shreg_min_size 10 -control_set_opt_threshold 16
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        synth_design -top cl_dram_dma -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context  -keep_equivalent_registers
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

## Prohibit the top two URAM sites of each URAM quad.
## These two sites cannot be used within PR designs.
#set uramSites [get_sites -filter { SITE_TYPE == "URAM288" } ]
#foreach uramSite $uramSites {
#  # Get the URAM location within a quad
#  set quadLoc [expr  [string range $uramSite [expr [string first Y $uramSite] + 1] end] % 4]
#  # The top-two sites have usage restrictions
#  if {$quadLoc == 2 || $quadLoc == 3} {
#    # Prohibit the appropriate site
#    set_property PROHIBIT true $uramSite
#    puts "Setting Placement Prohibit on $uramSite"
#  }
#}

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp
close_project

########################
# CL Optimize
########################
puts "AWS FPGA: Optimizing design";

# Implementation

#Read in the Shell checkpoint and do the CL implementation
puts "AWS FPGA: Implementation step -Combining Shell and CL design checkpoints";

open_checkpoint $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
read_checkpoint -strict -cell CL $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp

#Read the constraints, note *DO NOT* read cl_clocks_aws (clocks originating from AWS shell)
read_xdc [ list \
$HDK_SHELL_DIR/build/constraints/cl_pnr_aws.xdc \
$CL_DIR/build/constraints/cl_pnr_user.xdc \
$HDK_SHELL_DIR/build/constraints/cl_ddr.xdc
]

puts "AWS FPGA: Optimize design during implementation";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        opt_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        opt_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        opt_design -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        opt_design -bufg_opt -control_set_merge -hier_fanout_limit 512 -muxf_remap -propconst -retarget -sweep
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        opt_design -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

# Prohibit the top two URAM sites of each URAM quad.
# These two sites cannot be used within PR designs.
set uramSites [get_sites -filter { SITE_TYPE == "URAM288" } ]
foreach uramSite $uramSites {
  # Get the URAM location within a quad
  set quadLoc [expr  [string range $uramSite [expr [string first Y $uramSite] + 1] end] % 4]
  # The top-two sites have usage restrictions
  if {$quadLoc == 2 || $quadLoc == 3} {
    # Prohibit the appropriate site
    set_property PROHIBIT true $uramSite
    puts "Setting Placement Prohibit on $uramSite"
  }
}

########################
# CL Place
########################
puts "AWS FPGA: Place design stage";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        place_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        place_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        place_design -directive ExtraNetDelay_high
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        place_design -directive AltSpreadLogic_medium
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        place_design -directive ExtraNetDelay_high
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.SH_CL.post_place.dcp

###########################
# CL Physical Optimization
###########################
puts "AWS FPGA: Physical optimization stage";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        phys_opt_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        phys_opt_design -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        phys_opt_design -directive Explore
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        phys_opt_design -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

########################
# CL Route
########################
puts "AWS FPGA: Route design stage";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
        route_design
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        route_design -directive Explore
    }
    "TIMING" {
        puts "TIMING strategy."
        route_design -directive Explore -tns_cleanup
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        route_design -directive Explore
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        route_design -directive Explore
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

#################################
# CL Final Physical Optimization
#################################
puts "AWS FPGA: Post-route Physical optimization stage ";

switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
    }
    "TIMING" {
        puts "TIMING strategy."
        phys_opt_design  -directive Explore
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        phys_opt_design  -directive Explore
        puts "AWS FPGA: Locking design ";
        lock_design -level routing
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

#This is what will deliver to AWS
write_checkpoint -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
close_project

# ################################################
# Verify PR Build
# ################################################
switch $strategy {
    "BASIC" {
        puts "BASIC strategy."
    }
    "EXPLORE" {
        puts "EXPLORE strategy."
        puts "AWS FPGA: Verify compatibility of generated checkpoint with SH checkpoint"
        pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
    }
    "TIMING" {
        puts "TIMING strategy."
        puts "AWS FPGA: Verify compatibility of generated checkpoint with SH checkpoint"
        pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
    }
    "CONGESTION" {
        puts "CONGESTION strategy."
        puts "AWS FPGA: Verify compatibility of generated checkpoint with SH checkpoint"
        pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
    }
    "DEFAULT" {
        puts "DEFAULT strategy."
        puts "AWS FPGA: Verify compatibility of generated checkpoint with SH checkpoint"
        pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp
    }
    default {
        puts "$strategy is NOT a valid strategy."
    }
}

# ################################################
# Emulate AWS Bitstream Generation
# ################################################
puts "AWS FPGA: Emulate AWS bitstream generation"

# Make temp dir for bitstream
file mkdir $CL_DIR/build/${timestamp}_aws_verify_temp_dir

# Verify the Developer DCP is compatible with SH_BB. 
pr_verify -full_check $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp $HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp

open_checkpoint $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp
report_timing_summary -file $CL_DIR/build/reports/${timestamp}.SH_CL_final_timing_summary.rpt

set_param bitstream.enablePR 4123
write_bitstream -force -bin_file $CL_DIR/build/${timestamp}_aws_verify_temp_dir/${timestamp}.SH_CL_final.bit

# Clean-up temp dir for bitstream
file delete -force $CL_DIR/build/${timestamp}_aws_verify_temp_dir

### --------------------------------------------

# Create a zipped tar file, that would be used for createFpgaImage EC2 API
puts "Compress files for sending back to AWS"

# clean up vivado.log file
exec perl $HDK_SHELL_DIR/build/scripts/clean_log.pl ${timestamp}

# Create manifest file
set manifest_file [open "$CL_DIR/build/checkpoints/to_aws/${timestamp}.manifest.txt" w]
set hash [lindex [split [exec sha256sum $CL_DIR/build/checkpoints/to_aws/${timestamp}.SH_CL_routed.dcp] ] 0]

puts $manifest_file "MANIFEST_FORMAT_VERSION=1\n"
puts $manifest_file "DCP_HASH=$hash\n"
puts $manifest_file "SHELL_VERSION=$shell_version\n"
puts $manifest_file "FILE_NAME=${timestamp}.SH_CL_routed.dcp\n"
puts $manifest_file "HDK_VERSION=$hdk_version\n"
puts $manifest_file "DATE=$timestamp\n"

close $manifest_file

# Delete old tar file with same name
if { [file exists $CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar] } {
        puts "Deleting old tar file with same name.";
        file delete -force $CL_DIR/build/checkpoints/to_aws/${timestamp}.Developer_CL.tar
}

# Tar checkpoint to aws
cd $CL_DIR/build/checkpoints
tar::create to_aws/${timestamp}.Developer_CL.tar [glob to_aws/${timestamp}*]

close_design


