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
# START
################################################################

# To test this script, run the following commands from Vivado Tcl console:
# source cl_script.tcl


# The design that will be created by this Tcl script contains the following 
# module references:
# hello_world

# Please add the sources of those modules before sourcing this Tcl script.

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

  # Create instance: f1_inst, and set properties
  set f1_inst [ create_bd_cell -type ip -vlnv xilinx.com:ip:aws f1_inst ]
  set_property -dict [ list \
    CONFIG.AUX_PRESENT {1} \
    CONFIG.OCL_PRESENT {1} \
  ] $f1_inst

  # Create instance: f1_inst_axi_periph, and set properties
  set f1_inst_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect f1_inst_axi_periph ]
  set_property -dict [ list \
    CONFIG.NUM_MI {1} \
  ] $f1_inst_axi_periph

  # Create instance: hello_world_0, and set properties
  set block_name hello_world
  set block_cell_name hello_world_0
  if { [catch {set hello_world_0 [create_bd_cell -type module -reference $block_name $block_cell_name] } errmsg] } {
     catch {common::send_msg_id "BD_TCL-105" "ERROR" "Unable to add referenced block <$block_name>. Please add the files for ${block_name}'s definition into the project."}
     return 1
   } elseif { $hello_world_0 eq "" } {
     catch {common::send_msg_id "BD_TCL-106" "ERROR" "Unable to referenced block <$block_name>. Please add the files for ${block_name}'s definition into the project."}
     return 1
   }
  
  set_property -dict [ list \
    CONFIG.NUM_READ_OUTSTANDING {1} \
    CONFIG.NUM_WRITE_OUTSTANDING {1} \
  ] [get_bd_intf_pins /hello_world_0/s_axi]


  # Create instance: system_ila_0, and set properties
  set system_ila_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:system_ila system_ila_0 ]
  
  set_property -dict [ list \
    CONFIG.C_MON_TYPE {INTERFACE} \
    CONFIG.C_NUM_MONITOR_SLOTS {1} \
    CONFIG.C_SLOT_0_APC_EN {0} \
    CONFIG.C_SLOT_0_AXI_AR_SEL_DATA {1} \
    CONFIG.C_SLOT_0_AXI_AR_SEL_TRIG {1} \
    CONFIG.C_SLOT_0_AXI_AW_SEL_DATA {1} \
    CONFIG.C_SLOT_0_AXI_AW_SEL_TRIG {1} \
    CONFIG.C_SLOT_0_AXI_B_SEL_DATA {1} \
    CONFIG.C_SLOT_0_AXI_B_SEL_TRIG {1} \
    CONFIG.C_SLOT_0_AXI_R_SEL_DATA {1} \
    CONFIG.C_SLOT_0_AXI_R_SEL_TRIG {1} \
    CONFIG.C_SLOT_0_AXI_W_SEL_DATA {1} \
    CONFIG.C_SLOT_0_AXI_W_SEL_TRIG {1} \
    CONFIG.C_SLOT_0_INTF_TYPE {xilinx.com:interface:aximm_rtl:1.0} \
  ] $system_ila_0

  # Create interface connections
  connect_bd_intf_net -intf_net f1_inst_M_AXI_OCL [get_bd_intf_pins f1_inst/M_AXI_OCL] [get_bd_intf_pins f1_inst_axi_periph/S00_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets f1_inst_M_AXI_OCL] [get_bd_intf_pins f1_inst/M_AXI_OCL] [get_bd_intf_pins system_ila_0/SLOT_0_AXI]
  set_property -dict [ list \
    HDL_ATTRIBUTE.DEBUG {true} \
  ] [get_bd_intf_nets f1_inst_M_AXI_OCL]
  connect_bd_intf_net -intf_net f1_inst_S_SH [get_bd_intf_ports S_SH] [get_bd_intf_pins f1_inst/S_SH]
  connect_bd_intf_net -intf_net f1_inst_axi_periph_M00_AXI [get_bd_intf_pins f1_inst_axi_periph/M00_AXI] [get_bd_intf_pins hello_world_0/s_axi]

  # Create port connections
  connect_bd_net -net f1_inst_clk_main_a0_out [get_bd_pins f1_inst/clk_main_a0_out] [get_bd_pins f1_inst_axi_periph/ACLK] [get_bd_pins f1_inst_axi_periph/M00_ACLK] [get_bd_pins f1_inst_axi_periph/S00_ACLK] [get_bd_pins hello_world_0/s_axi_aclk] [get_bd_pins system_ila_0/clk]
  connect_bd_net -net f1_inst_rst_main_n_out [get_bd_pins f1_inst/rst_main_n_out] [get_bd_pins f1_inst_axi_periph/ARESETN] [get_bd_pins f1_inst_axi_periph/M00_ARESETN] [get_bd_pins f1_inst_axi_periph/S00_ARESETN] [get_bd_pins hello_world_0/s_axi_aresetn] [get_bd_pins system_ila_0/resetn]
  connect_bd_net -net f1_inst_status_vdip [get_bd_pins f1_inst/status_vdip] [get_bd_pins hello_world_0/vdip]
  connect_bd_net -net hello_world_0_vled [get_bd_pins f1_inst/status_vled] [get_bd_pins hello_world_0/vled]

  # Create address segments
  create_bd_addr_seg -range 0x02000000 -offset 0x00000000 [get_bd_addr_spaces f1_inst/M_AXI_OCL] [get_bd_addr_segs hello_world_0/s_axi/reg0] SEG_hello_world_0_reg0


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


