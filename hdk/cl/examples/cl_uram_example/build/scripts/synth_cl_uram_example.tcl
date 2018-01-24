# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#Param needed to avoid clock name collisions
set_param sta.enableAutoGenClkNamePersistence 0
set CL_MODULE $CL_MODULE

create_project -in_memory -part [DEVICE_TYPE] -force

########################################
## Generate clocks based on Recipe 
########################################

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Calling aws_gen_clk_constraints.tcl to generate clock constraints from developer's specified recipe.";

source $HDK_SHELL_DIR/build/scripts/aws_gen_clk_constraints.tcl

#############################
## Read design files
#############################

#Convenience to set the root of the RTL directory
set ENC_SRC_DIR $CL_DIR/build/src_post_encryption

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Reading developer's Custom Logic files post encryption.";

#---- User would replace this section -----

# Reading the .sv and .v files, as proper designs would not require
# reading .v, .vh, nor .inc files

read_verilog -sv [glob $ENC_SRC_DIR/*.?v]
read_vhdl $ENC_SRC_DIR/ctrl_uram.vhd

# Create BD
create_bd_design "bd_uram"
update_compile_order -fileset sources_1

# Create uram
create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.3 blk_mem_gen_0
create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.3 blk_mem_gen_1
set depth_uram 819200
set_property -dict [list CONFIG.Memory_Type {Simple_Dual_Port_RAM} CONFIG.PRIM_type_to_Implement {URAM} CONFIG.Write_Depth_A $depth_uram CONFIG.Operating_Mode_A {READ_FIRST} CONFIG.Register_PortB_Output_of_Memory_Primitives {false} CONFIG.use_bram_block {Stand_Alone} CONFIG.Enable_32bit_Address {false} CONFIG.Use_Byte_Write_Enable {false} CONFIG.Byte_Size {9} CONFIG.Assume_Synchronous_Clk {true} CONFIG.Enable_A {Use_ENA_Pin} CONFIG.Operating_Mode_B {READ_FIRST} CONFIG.Enable_B {Use_ENB_Pin} CONFIG.Register_PortA_Output_of_Memory_Primitives {false} CONFIG.Use_REGCEB_Pin {false} CONFIG.Use_RSTA_Pin {false} CONFIG.Port_B_Clock {100} CONFIG.Port_B_Enable_Rate {100}] [get_bd_cells blk_mem_gen_0]
set_property -dict [list CONFIG.Memory_Type {Simple_Dual_Port_RAM} CONFIG.PRIM_type_to_Implement {URAM} CONFIG.Write_Depth_A $depth_uram CONFIG.Operating_Mode_A {READ_FIRST} CONFIG.Register_PortB_Output_of_Memory_Primitives {false} CONFIG.use_bram_block {Stand_Alone} CONFIG.Enable_32bit_Address {false} CONFIG.Use_Byte_Write_Enable {false} CONFIG.Byte_Size {9} CONFIG.Assume_Synchronous_Clk {true} CONFIG.Enable_A {Use_ENA_Pin} CONFIG.Operating_Mode_B {READ_FIRST} CONFIG.Enable_B {Use_ENB_Pin} CONFIG.Register_PortA_Output_of_Memory_Primitives {false} CONFIG.Use_REGCEB_Pin {false} CONFIG.Use_RSTA_Pin {false} CONFIG.Port_B_Clock {100} CONFIG.Port_B_Enable_Rate {100}] [get_bd_cells blk_mem_gen_1]

# Make external
make_bd_pins_external  [get_bd_cells blk_mem_gen_0] [get_bd_cells blk_mem_gen_1]
make_bd_intf_pins_external  [get_bd_cells blk_mem_gen_0] [get_bd_cells blk_mem_gen_1]
set_property name URAM_PORTA [get_bd_intf_ports BRAM_PORTA]
set_property name URAM_PORTB [get_bd_intf_ports BRAM_PORTB]
set_property name URAM_PORTA_1 [get_bd_intf_ports BRAM_PORTA_1]
set_property name URAM_PORTB_1 [get_bd_intf_ports BRAM_PORTB_1]

#Validate design
validate_bd_design

# Generate Output Products
generate_target all [get_files ./.srcs/sources_1/bd/bd_uram/bd_uram.bd]

# Save BD
save_bd_design

#---- End of section replaced by User ----

puts "AWS FPGA: Reading AWS Shell design";

#Read AWS Design files
read_verilog -sv [ list \
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sync.v\
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/flop_ccf.sv\
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/ccf_ctl.v\
  $HDK_SHELL_DESIGN_DIR/sh_ddr/synth/sh_ddr.sv \
  $HDK_SHELL_DESIGN_DIR/interfaces/cl_ports.vh
]

puts "AWS FPGA: Reading IP blocks";

#Read IP for axi register slices
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/ip/src_register_slice/src_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/dest_register_slice/dest_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice/axi_register_slice.xci \
  $HDK_SHELL_DESIGN_DIR/ip/axi_register_slice_light/axi_register_slice_light.xci
]

#Read IP for virtual jtag / ILA/VIO
read_ip [ list \
  $HDK_SHELL_DESIGN_DIR/ip/ila_0/ila_0.xci\
  $HDK_SHELL_DESIGN_DIR/ip/cl_debug_bridge/cl_debug_bridge.xci \
  $HDK_SHELL_DESIGN_DIR/ip/ila_vio_counter/ila_vio_counter.xci \
  $HDK_SHELL_DESIGN_DIR/ip/vio_0/vio_0.xci
]

# Additional IP's that might be needed if using the DDR
#read_bd [ list \
# $HDK_SHELL_DESIGN_DIR/ip/ddr4_core/ddr4_core.xci \
# $HDK_SHELL_DESIGN_DIR/ip/cl_axi_interconnect/cl_axi_interconnect.bd
#]

puts "AWS FPGA: Reading AWS constraints";

#Read all the constraints
#
#  cl_clocks_aws.xdc  - AWS auto-generated clock constraint.   ***DO NOT MODIFY***
#  cl_ddr.xdc         - AWS provided DDR pin constraints.      ***DO NOT MODIFY***
#  cl_synth_user.xdc  - Developer synthesis constraints.
read_xdc [ list \
   $CL_DIR/build/constraints/cl_clocks_aws.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_ddr.xdc \
   $HDK_SHELL_DIR/build/constraints/cl_synth_aws.xdc \
   $CL_DIR/build/constraints/cl_synth_user.xdc
]

#Do not propagate local clock constraints for clocks generated in the SH
set_property USED_IN {synthesis implementation OUT_OF_CONTEXT} [get_files cl_clocks_aws.xdc]
set_property PROCESSING_ORDER EARLY  [get_files cl_clocks_aws.xdc]

########################
# CL Synthesis
########################
puts "AWS FPGA: ([clock format [clock seconds] -format %T]) Start design synthesis.";

update_compile_order -fileset sources_1
puts "\nRunning synth_design for $CL_MODULE $CL_DIR/build/scripts \[[clock format [clock seconds] -format {%a %b %d %H:%M:%S %Y}]\]"
eval [concat synth_design -top $CL_MODULE -verilog_define XSDB_SLV_DIS -part [DEVICE_TYPE] -mode out_of_context $synth_options -directive $synth_directive]

set failval [catch {exec grep "FAIL" failfast.csv}]
if { $failval==0 } {
	puts "AWS FPGA: FATAL ERROR--Resource utilization error; check failfast.csv for details"
	exit 1
}

puts "AWS FPGA: ([clock format [clock seconds] -format %T]) writing post synth checkpoint.";
write_checkpoint -force $CL_DIR/build/checkpoints/${timestamp}.CL.post_synth.dcp

close_project
#Set param back to default value
set_param sta.enableAutoGenClkNamePersistence 1
