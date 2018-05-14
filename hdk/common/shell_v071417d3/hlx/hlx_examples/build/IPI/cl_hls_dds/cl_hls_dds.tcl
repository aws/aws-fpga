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

  # Create instance: axi_gpio_0, and set properties
  set axi_gpio_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_gpio axi_gpio_0 ]
  set_property -dict [ list \
    CONFIG.C_ALL_INPUTS {1} \
    CONFIG.C_GPIO_WIDTH {1} \
  ] $axi_gpio_0

  # Create instance: axi_smc, and set properties
  set axi_smc [ create_bd_cell -type ip -vlnv xilinx.com:ip:smartconnect axi_smc ]
  set_property -dict [ list \
    CONFIG.NUM_SI {3} \
  ] $axi_smc

  # Create instance: dds_0, and set properties
  set dds_0 [ create_bd_cell -type ip -vlnv xilinx.com:hls:dds dds_0 ]
  set_property -dict [ list \
    CONFIG.C_M_AXI_DDS_OUTPUT1_DATA_WIDTH {512} \
    CONFIG.C_M_AXI_DDS_OUTPUT1_TARGET_ADDR {0x82000000} \
    CONFIG.C_M_AXI_DDS_OUTPUT_DATA_WIDTH {512} \
    CONFIG.C_M_AXI_DDS_OUTPUT_TARGET_ADDR {0x81000000} \
  ] $dds_0

  set_property -dict [ list \
    CONFIG.NUM_READ_OUTSTANDING {1} \
    CONFIG.NUM_WRITE_OUTSTANDING {1} \
  ] [get_bd_intf_pins /dds_0/s_axi_PROG_BUS]

  # Create instance: f1_inst, and set properties
  set f1_inst [ create_bd_cell -type ip -vlnv xilinx.com:ip:aws f1_inst ]
  set_property -dict [ list \
    CONFIG.BAR1_PRESENT {1} \
    CONFIG.CLOCK_A0_FREQ {250000000} \
    CONFIG.CLOCK_A1_FREQ {125000000} \
    CONFIG.CLOCK_A2_FREQ {375000000} \
    CONFIG.CLOCK_A3_FREQ {500000000} \
    CONFIG.CLOCK_A_RECIPE {1} \
    CONFIG.DDR_C_PRESENT {1} \
    CONFIG.NUM_A_CLOCKS {2} \
    CONFIG.PCIS_PRESENT {1} \
  ] $f1_inst

  # Create instance: f1_inst_axi_periph, and set properties
  set f1_inst_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect f1_inst_axi_periph ]
  set_property -dict [ list \
    CONFIG.NUM_MI {2} \
  ] $f1_inst_axi_periph

  # Create instance: rst_f1_inst_125M, and set properties
  set rst_f1_inst_125M [ create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset rst_f1_inst_125M ]

  # Create interface connections
  connect_bd_intf_net -intf_net axi_smc_M00_AXI [get_bd_intf_pins axi_smc/M00_AXI] [get_bd_intf_pins f1_inst/S_AXI_DDRC]
  connect_bd_intf_net -intf_net dds_0_m_axi_DDS_OUTPUT [get_bd_intf_pins axi_smc/S00_AXI] [get_bd_intf_pins dds_0/m_axi_DDS_OUTPUT]
  connect_bd_intf_net -intf_net dds_0_m_axi_DDS_OUTPUT1 [get_bd_intf_pins axi_smc/S01_AXI] [get_bd_intf_pins dds_0/m_axi_DDS_OUTPUT1]
  connect_bd_intf_net -intf_net f1_inst_M_AXI_BAR1 [get_bd_intf_pins f1_inst/M_AXI_BAR1] [get_bd_intf_pins f1_inst_axi_periph/S00_AXI]
  connect_bd_intf_net -intf_net f1_inst_M_AXI_PCIS [get_bd_intf_pins axi_smc/S02_AXI] [get_bd_intf_pins f1_inst/M_AXI_PCIS]
  connect_bd_intf_net -intf_net f1_inst_S_SH [get_bd_intf_ports S_SH] [get_bd_intf_pins f1_inst/S_SH]
  connect_bd_intf_net -intf_net f1_inst_axi_periph_M00_AXI [get_bd_intf_pins dds_0/s_axi_PROG_BUS] [get_bd_intf_pins f1_inst_axi_periph/M00_AXI]
  connect_bd_intf_net -intf_net f1_inst_axi_periph_M01_AXI [get_bd_intf_pins axi_gpio_0/S_AXI] [get_bd_intf_pins f1_inst_axi_periph/M01_AXI]

  # Create port connections
  connect_bd_net -net f1_inst_clk_extra_a1_out [get_bd_pins axi_gpio_0/s_axi_aclk] [get_bd_pins f1_inst/clk_extra_a1_out] [get_bd_pins f1_inst_axi_periph/M01_ACLK] [get_bd_pins rst_f1_inst_125M/slowest_sync_clk]
  connect_bd_net -net f1_inst_clk_main_a0_out [get_bd_pins axi_smc/aclk] [get_bd_pins dds_0/ap_clk] [get_bd_pins f1_inst/clk_main_a0_out] [get_bd_pins f1_inst_axi_periph/ACLK] [get_bd_pins f1_inst_axi_periph/M00_ACLK] [get_bd_pins f1_inst_axi_periph/S00_ACLK]
  connect_bd_net -net f1_inst_ddrc_is_ready [get_bd_pins axi_gpio_0/gpio_io_i] [get_bd_pins f1_inst/ddrc_is_ready]
  connect_bd_net -net f1_inst_rst_main_n_out [get_bd_pins axi_smc/aresetn] [get_bd_pins dds_0/ap_rst_n] [get_bd_pins f1_inst/rst_main_n_out] [get_bd_pins f1_inst_axi_periph/ARESETN] [get_bd_pins f1_inst_axi_periph/M00_ARESETN] [get_bd_pins f1_inst_axi_periph/S00_ARESETN] [get_bd_pins rst_f1_inst_125M/ext_reset_in]
  connect_bd_net -net rst_f1_inst_125M_peripheral_aresetn [get_bd_pins axi_gpio_0/s_axi_aresetn] [get_bd_pins f1_inst_axi_periph/M01_ARESETN] [get_bd_pins rst_f1_inst_125M/peripheral_aresetn]

  # Create address segments
  create_bd_addr_seg -range 0x80000000 -offset 0x80000000 [get_bd_addr_spaces dds_0/Data_m_axi_DDS_OUTPUT] [get_bd_addr_segs f1_inst/S_AXI_DDRC/Mem_DDRC] SEG_f1_inst_Mem_DDRC
  create_bd_addr_seg -range 0x80000000 -offset 0x80000000 [get_bd_addr_spaces dds_0/Data_m_axi_DDS_OUTPUT1] [get_bd_addr_segs f1_inst/S_AXI_DDRC/Mem_DDRC] SEG_f1_inst_Mem_DDRC
  create_bd_addr_seg -range 0x00001000 -offset 0x00010000 [get_bd_addr_spaces f1_inst/M_AXI_BAR1] [get_bd_addr_segs axi_gpio_0/S_AXI/Reg] SEG_axi_gpio_0_Reg
  create_bd_addr_seg -range 0x00010000 -offset 0x00000000 [get_bd_addr_spaces f1_inst/M_AXI_BAR1] [get_bd_addr_segs dds_0/s_axi_PROG_BUS/Reg] SEG_dds_0_Reg
  create_bd_addr_seg -range 0x000100000000 -offset 0x00000000 [get_bd_addr_spaces f1_inst/M_AXI_PCIS] [get_bd_addr_segs f1_inst/S_AXI_DDRC/Mem_DDRC] SEG_f1_inst_Mem_DDRC


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


