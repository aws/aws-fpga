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

################################################################
# This is a generated script based on design: cl
#
# Though there are limitations about the generated script,
# the main purpose of this utility is to make learning
# IP Integrator Tcl commands easier.
################################################################

namespace eval _tcl {
proc get_script_folder {} {
   set script_path [file normalize [info script]]
   set script_folder [file dirname $script_path]
   return $script_folder
}
}
variable script_folder
set script_folder [_tcl::get_script_folder]

################################################################
# Check if script is running in correct Vivado version.
################################################################
set scripts_vivado_version 2017.1
set current_vivado_version [version -short]

if { [string first $scripts_vivado_version $current_vivado_version] == -1 } {
   puts ""
   catch {common::send_msg_id "BD_TCL-109" "ERROR" "This script was generated using Vivado <$scripts_vivado_version> and is being run in <$current_vivado_version> of Vivado. Please run the script in Vivado <$scripts_vivado_version> then open the design in Vivado <$current_vivado_version>. Upgrade the design by running \"Tools => Report => Report IP Status...\", then run write_bd_tcl to create an updated script."}

   return 1
}

################################################################
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source cl_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./myproj/project_1.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { $list_projs eq "" } {
   create_project project_1 myproj -part xcvu9p-flgb2104-2-i
   set_property BOARD_PART xilinx.com:f1_cl:part0:1.0 [current_project]
}


# CHANGE DESIGN NAME HERE
set design_name cl

# If you do not already have an existing IP Integrator design open,
# you can create a design using the following command:
#    create_bd_design $design_name

# Creating design if needed
set errMsg ""
set nRet 0

set cur_design [current_bd_design -quiet]
set list_cells [get_bd_cells -quiet]

if { ${design_name} eq "" } {
   # USE CASES:
   #    1) Design_name not set

   set errMsg "Please set the variable <design_name> to a non-empty value."
   set nRet 1

} elseif { ${cur_design} ne "" && ${list_cells} eq "" } {
   # USE CASES:
   #    2): Current design opened AND is empty AND names same.
   #    3): Current design opened AND is empty AND names diff; design_name NOT in project.
   #    4): Current design opened AND is empty AND names diff; design_name exists in project.

   if { $cur_design ne $design_name } {
      common::send_msg_id "BD_TCL-001" "INFO" "Changing value of <design_name> from <$design_name> to <$cur_design> since current design is empty."
      set design_name [get_property NAME $cur_design]
   }
   common::send_msg_id "BD_TCL-002" "INFO" "Constructing design in IPI design <$cur_design>..."

} elseif { ${cur_design} ne "" && $list_cells ne "" && $cur_design eq $design_name } {
   # USE CASES:
   #    5) Current design opened AND has components AND same names.

   set errMsg "Design <$design_name> already exists in your project, please set the variable <design_name> to another value."
   set nRet 1
} elseif { [get_files -quiet ${design_name}.bd] ne "" } {
   # USE CASES: 
   #    6) Current opened design, has components, but diff names, design_name exists in project.
   #    7) No opened design, design_name exists in project.

   set errMsg "Design <$design_name> already exists in your project, please set the variable <design_name> to another value."
   set nRet 2

} else {
   # USE CASES:
   #    8) No opened design, design_name not in project.
   #    9) Current opened design, has components, but diff names, design_name not in project.

   common::send_msg_id "BD_TCL-003" "INFO" "Currently there is no design <$design_name> in project, so creating one..."

   create_bd_design $design_name

   common::send_msg_id "BD_TCL-004" "INFO" "Making design <$design_name> as current_bd_design."
   current_bd_design $design_name

}

common::send_msg_id "BD_TCL-005" "INFO" "Currently the variable <design_name> is equal to \"$design_name\"."

if { $nRet != 0 } {
   catch {common::send_msg_id "BD_TCL-114" "ERROR" $errMsg}
   return $nRet
}

##################################################################
# DESIGN PROCs
##################################################################



# Procedure to create entire design; Provide argument to make
# procedure reusable. If parentCell is "", will use root.
proc create_root_design { parentCell } {

  variable script_folder

  if { $parentCell eq "" } {
     set parentCell [get_bd_cells /]
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_msg_id "BD_TCL-100" "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_msg_id "BD_TCL-101" "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj


  # Create interface ports
  set S_SH [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aws_f1_sh1_rtl:1.0 S_SH ]

  # Create ports

  # Create instance: aws_0, and set properties
  set aws_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:aws:1.0 aws_0 ]
  set_property -dict [ list \
CONFIG.AUX_PRESENT {1} \
CONFIG.BAR1_PRESENT {1} \
CONFIG.CLOCK_A0_FREQ {250000000} \
CONFIG.CLOCK_A1_FREQ {125000000} \
CONFIG.CLOCK_A2_FREQ {375000000} \
CONFIG.CLOCK_A3_FREQ {500000000} \
CONFIG.CLOCK_A_RECIPE {1} \
CONFIG.NUM_A_CLOCKS {1} \
CONFIG.VENDOR_ID {0x0001} \
 ] $aws_0

  # Create instance: aws_0_axi_periph, and set properties
  set aws_0_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect:2.1 aws_0_axi_periph ]
  set_property -dict [ list \
CONFIG.NUM_MI {1} \
 ] $aws_0_axi_periph

  # Create instance: axi_gpio_0, and set properties
  set axi_gpio_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_gpio:2.0 axi_gpio_0 ]
  set_property -dict [ list \
CONFIG.C_ALL_INPUTS {1} \
CONFIG.C_ALL_OUTPUTS_2 {1} \
CONFIG.C_GPIO2_WIDTH {16} \
CONFIG.C_GPIO_WIDTH {16} \
CONFIG.C_IS_DUAL {1} \
 ] $axi_gpio_0

  # Create interface connections
  connect_bd_intf_net -intf_net S_SH_1 [get_bd_intf_ports S_SH] [get_bd_intf_pins aws_0/S_SH]
  connect_bd_intf_net -intf_net aws_0_M_AXI_BAR1 [get_bd_intf_pins aws_0/M_AXI_BAR1] [get_bd_intf_pins aws_0_axi_periph/S00_AXI]
  connect_bd_intf_net -intf_net aws_0_axi_periph_M00_AXI [get_bd_intf_pins aws_0_axi_periph/M00_AXI] [get_bd_intf_pins axi_gpio_0/S_AXI]

  # Create port connections
  connect_bd_net -net aws_0_clk_main_a0_out [get_bd_pins aws_0/clk_main_a0_out] [get_bd_pins aws_0_axi_periph/ACLK] [get_bd_pins aws_0_axi_periph/M00_ACLK] [get_bd_pins aws_0_axi_periph/S00_ACLK] [get_bd_pins axi_gpio_0/s_axi_aclk]
  connect_bd_net -net aws_0_rst_main_n_out1 [get_bd_pins aws_0/rst_main_n_out] [get_bd_pins aws_0_axi_periph/ARESETN] [get_bd_pins aws_0_axi_periph/M00_ARESETN] [get_bd_pins aws_0_axi_periph/S00_ARESETN] [get_bd_pins axi_gpio_0/s_axi_aresetn]
  connect_bd_net -net aws_0_status_vdip [get_bd_pins aws_0/status_vdip] [get_bd_pins axi_gpio_0/gpio_io_i]
  connect_bd_net -net axi_gpio_0_gpio2_io_o [get_bd_pins aws_0/status_vled] [get_bd_pins axi_gpio_0/gpio2_io_o]

  # Create address segments
  create_bd_addr_seg -range 0x00001000 -offset 0x00000000 [get_bd_addr_spaces aws_0/M_AXI_BAR1] [get_bd_addr_segs axi_gpio_0/S_AXI/Reg] SEG_axi_gpio_0_Reg


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


