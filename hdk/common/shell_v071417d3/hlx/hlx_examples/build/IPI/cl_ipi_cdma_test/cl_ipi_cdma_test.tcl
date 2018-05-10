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
  set aws_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:aws aws_0 ]
  set_property -dict [ list \
    CONFIG.AUX_PRESENT {1} \
    CONFIG.BAR1_PRESENT {1} \
    CONFIG.DDR_A_PRESENT {1} \
    CONFIG.DDR_B_PRESENT {1} \
    CONFIG.DDR_C_PRESENT {1} \
    CONFIG.DDR_D_PRESENT {1} \
    CONFIG.NUM_STAGES_SCALAR {3} \
    CONFIG.OCL_PRESENT {1} \
    CONFIG.PCIS_PRESENT {1} \
    CONFIG.SDA_PRESENT {1} \
  ] $aws_0

  # Create instance: aws_0_axi_periph, and set properties
  set aws_0_axi_periph [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect aws_0_axi_periph ]
  set_property -dict [ list \
    CONFIG.NUM_MI {1} \
    CONFIG.S00_HAS_REGSLICE {4} \
  ] $aws_0_axi_periph

  # Create instance: aws_0_axi_periph_1, and set properties
  set aws_0_axi_periph_1 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect aws_0_axi_periph_1 ]
  set_property -dict [ list \
    CONFIG.NUM_MI {1} \
    CONFIG.S00_HAS_REGSLICE {4} \
  ] $aws_0_axi_periph_1

  # Create instance: aws_0_axi_periph_2, and set properties
  set aws_0_axi_periph_2 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect aws_0_axi_periph_2 ]
  set_property -dict [ list \
    CONFIG.NUM_MI {1} \
    CONFIG.S00_HAS_REGSLICE {4} \
  ] $aws_0_axi_periph_2

  # Create instance: axi_cdma_0, and set properties
  set axi_cdma_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_cdma axi_cdma_0 ]
  set_property -dict [ list           \
    CONFIG.C_ADDR_WIDTH {64}          \
    CONFIG.C_INCLUDE_SG {0}           \
    CONFIG.C_M_AXI_DATA_WIDTH {512}   \
    CONFIG.C_M_AXI_MAX_BURST_LEN {64} \
  ] $axi_cdma_0

  # Create instance: axi_gpio_0, and set properties
  set axi_gpio_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_gpio axi_gpio_0 ]
  set_property -dict [ list \
    CONFIG.C_ALL_INPUTS {1} \
    CONFIG.C_GPIO_WIDTH {4} \
  ] $axi_gpio_0

  # Create instance: axi_gpio_1, and set properties
  set axi_gpio_1 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_gpio axi_gpio_1 ]
  set_property -dict [ list  \
    CONFIG.C_ALL_OUTPUTS {1} \
    CONFIG.C_GPIO_WIDTH {16} \
  ] $axi_gpio_1

  # Create instance: axi_mem_intercon, and set properties
  set axi_mem_intercon [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect axi_mem_intercon ]
  set_property -dict [ list     \
    CONFIG.M00_HAS_REGSLICE {4} \
    CONFIG.M01_HAS_REGSLICE {4} \
    CONFIG.M02_HAS_REGSLICE {4} \
    CONFIG.M03_HAS_REGSLICE {4} \
    CONFIG.NUM_MI {4}           \
    CONFIG.NUM_SI {2}           \
    CONFIG.S00_HAS_REGSLICE {4} \
    CONFIG.S01_HAS_REGSLICE {4} \
  ] $axi_mem_intercon

  # Create instance: system_ila_0, and set properties
  set system_ila_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:system_ila system_ila_0 ]

  # Create instance: xlconcat_0, and set properties
  set xlconcat_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:xlconcat xlconcat_0 ]
  set_property -dict [ list \
    CONFIG.NUM_PORTS {4} \
  ] $xlconcat_0

  # Create interface connections
  connect_bd_intf_net -intf_net S01_AXI_1 [get_bd_intf_pins aws_0/M_AXI_PCIS] [get_bd_intf_pins axi_mem_intercon/S01_AXI]
  connect_bd_intf_net -intf_net S_SH_1 [get_bd_intf_ports S_SH] [get_bd_intf_pins aws_0/S_SH]
  connect_bd_intf_net -intf_net aws_0_M_AXI_BAR1 [get_bd_intf_pins aws_0/M_AXI_BAR1] [get_bd_intf_pins aws_0_axi_periph_2/S00_AXI]
  connect_bd_intf_net -intf_net aws_0_M_AXI_OCL [get_bd_intf_pins aws_0/M_AXI_OCL] [get_bd_intf_pins aws_0_axi_periph_1/S00_AXI]
  connect_bd_intf_net -intf_net aws_0_M_AXI_SDA [get_bd_intf_pins aws_0/M_AXI_SDA] [get_bd_intf_pins aws_0_axi_periph/S00_AXI]
  connect_bd_intf_net -intf_net aws_0_axi_periph_1_M00_AXI [get_bd_intf_pins aws_0_axi_periph_1/M00_AXI] [get_bd_intf_pins axi_gpio_1/S_AXI]
  connect_bd_intf_net -intf_net aws_0_axi_periph_2_M00_AXI [get_bd_intf_pins aws_0_axi_periph_2/M00_AXI] [get_bd_intf_pins axi_cdma_0/S_AXI_LITE]
  connect_bd_intf_net -intf_net aws_0_axi_periph_M00_AXI [get_bd_intf_pins aws_0_axi_periph/M00_AXI] [get_bd_intf_pins axi_gpio_0/S_AXI]
  connect_bd_intf_net -intf_net axi_cdma_0_M_AXI [get_bd_intf_pins axi_cdma_0/M_AXI] [get_bd_intf_pins axi_mem_intercon/S00_AXI]
  connect_bd_intf_net -intf_net [get_bd_intf_nets axi_cdma_0_M_AXI] [get_bd_intf_pins axi_cdma_0/M_AXI] [get_bd_intf_pins system_ila_0/SLOT_0_AXI]
  connect_bd_intf_net -intf_net axi_mem_intercon_M00_AXI [get_bd_intf_pins aws_0/S_AXI_DDRA] [get_bd_intf_pins axi_mem_intercon/M00_AXI]
  connect_bd_intf_net -intf_net axi_mem_intercon_M01_AXI [get_bd_intf_pins aws_0/S_AXI_DDRB] [get_bd_intf_pins axi_mem_intercon/M01_AXI]
  connect_bd_intf_net -intf_net axi_mem_intercon_M02_AXI [get_bd_intf_pins aws_0/S_AXI_DDRC] [get_bd_intf_pins axi_mem_intercon/M02_AXI]
  connect_bd_intf_net -intf_net axi_mem_intercon_M03_AXI [get_bd_intf_pins aws_0/S_AXI_DDRD] [get_bd_intf_pins axi_mem_intercon/M03_AXI]

  # Create port connections
  connect_bd_net -net aws_0_clk_main_a0_out [get_bd_pins aws_0/clk_main_a0_out] [get_bd_pins aws_0_axi_periph/ACLK] [get_bd_pins aws_0_axi_periph/M00_ACLK] [get_bd_pins aws_0_axi_periph/S00_ACLK] [get_bd_pins aws_0_axi_periph_1/ACLK] [get_bd_pins aws_0_axi_periph_1/M00_ACLK] [get_bd_pins aws_0_axi_periph_1/S00_ACLK] [get_bd_pins aws_0_axi_periph_2/ACLK] [get_bd_pins aws_0_axi_periph_2/M00_ACLK] [get_bd_pins aws_0_axi_periph_2/S00_ACLK] [get_bd_pins axi_cdma_0/m_axi_aclk] [get_bd_pins axi_cdma_0/s_axi_lite_aclk] [get_bd_pins axi_gpio_0/s_axi_aclk] [get_bd_pins axi_gpio_1/s_axi_aclk] [get_bd_pins axi_mem_intercon/ACLK] [get_bd_pins axi_mem_intercon/M00_ACLK] [get_bd_pins axi_mem_intercon/M01_ACLK] [get_bd_pins axi_mem_intercon/M02_ACLK] [get_bd_pins axi_mem_intercon/M03_ACLK] [get_bd_pins axi_mem_intercon/S00_ACLK] [get_bd_pins axi_mem_intercon/S01_ACLK] [get_bd_pins system_ila_0/clk]
  connect_bd_net -net aws_0_ddra_is_ready [get_bd_pins aws_0/ddra_is_ready] [get_bd_pins xlconcat_0/In0]
  connect_bd_net -net aws_0_ddrb_is_ready [get_bd_pins aws_0/ddrb_is_ready] [get_bd_pins xlconcat_0/In1]
  connect_bd_net -net aws_0_ddrc_is_ready [get_bd_pins aws_0/ddrc_is_ready] [get_bd_pins xlconcat_0/In3]
  connect_bd_net -net aws_0_ddrd_is_ready [get_bd_pins aws_0/ddrd_is_ready] [get_bd_pins xlconcat_0/In2]
  connect_bd_net -net aws_0_rst_main_n_out [get_bd_pins aws_0/rst_main_n_out] [get_bd_pins aws_0_axi_periph/ARESETN] [get_bd_pins aws_0_axi_periph/M00_ARESETN] [get_bd_pins aws_0_axi_periph/S00_ARESETN] [get_bd_pins aws_0_axi_periph_1/ARESETN] [get_bd_pins aws_0_axi_periph_1/M00_ARESETN] [get_bd_pins aws_0_axi_periph_1/S00_ARESETN] [get_bd_pins aws_0_axi_periph_2/ARESETN] [get_bd_pins aws_0_axi_periph_2/M00_ARESETN] [get_bd_pins aws_0_axi_periph_2/S00_ARESETN] [get_bd_pins axi_cdma_0/s_axi_lite_aresetn] [get_bd_pins axi_gpio_0/s_axi_aresetn] [get_bd_pins axi_gpio_1/s_axi_aresetn] [get_bd_pins axi_mem_intercon/ARESETN] [get_bd_pins axi_mem_intercon/M00_ARESETN] [get_bd_pins axi_mem_intercon/M01_ARESETN] [get_bd_pins axi_mem_intercon/M02_ARESETN] [get_bd_pins axi_mem_intercon/M03_ARESETN] [get_bd_pins axi_mem_intercon/S00_ARESETN] [get_bd_pins axi_mem_intercon/S01_ARESETN] [get_bd_pins system_ila_0/resetn]
  connect_bd_net -net axi_gpio_1_gpio_io_o [get_bd_pins aws_0/status_vled] [get_bd_pins axi_gpio_1/gpio_io_o]
  connect_bd_net -net xlconcat_0_dout [get_bd_pins axi_gpio_0/gpio_io_i] [get_bd_pins xlconcat_0/dout]

  # Create address segments
  create_bd_addr_seg -range 0x80000000 -offset 0x000C00000000 [get_bd_addr_spaces aws_0/M_AXI_PCIS] [get_bd_addr_segs aws_0/S_AXI_DDRA/Mem_DDRA] SEG_aws_0_Mem_DDRA
  create_bd_addr_seg -range 0x80000000 -offset 0x000D00000000 [get_bd_addr_spaces aws_0/M_AXI_PCIS] [get_bd_addr_segs aws_0/S_AXI_DDRB/Mem_DDRB] SEG_aws_0_Mem_DDRB
  create_bd_addr_seg -range 0x80000000 -offset 0x000E00000000 [get_bd_addr_spaces aws_0/M_AXI_PCIS] [get_bd_addr_segs aws_0/S_AXI_DDRC/Mem_DDRC] SEG_aws_0_Mem_DDRC
  create_bd_addr_seg -range 0x80000000 -offset 0x000F00000000 [get_bd_addr_spaces aws_0/M_AXI_PCIS] [get_bd_addr_segs aws_0/S_AXI_DDRD/Mem_DDRD] SEG_aws_0_Mem_DDRD
  create_bd_addr_seg -range 0x00010000 -offset 0x00000000 [get_bd_addr_spaces aws_0/M_AXI_BAR1] [get_bd_addr_segs axi_cdma_0/S_AXI_LITE/Reg] SEG_axi_cdma_0_Reg
  create_bd_addr_seg -range 0x00001000 -offset 0x00000000 [get_bd_addr_spaces aws_0/M_AXI_SDA] [get_bd_addr_segs axi_gpio_0/S_AXI/Reg] SEG_axi_gpio_0_Reg
  create_bd_addr_seg -range 0x00001000 -offset 0x00000000 [get_bd_addr_spaces aws_0/M_AXI_OCL] [get_bd_addr_segs axi_gpio_1/S_AXI/Reg] SEG_axi_gpio_1_Reg
  create_bd_addr_seg -range 0x80000000 -offset 0x000C00000000 [get_bd_addr_spaces axi_cdma_0/Data] [get_bd_addr_segs aws_0/S_AXI_DDRA/Mem_DDRA] SEG_aws_0_Mem_DDRA
  create_bd_addr_seg -range 0x80000000 -offset 0x000D00000000 [get_bd_addr_spaces axi_cdma_0/Data] [get_bd_addr_segs aws_0/S_AXI_DDRB/Mem_DDRB] SEG_aws_0_Mem_DDRB
  create_bd_addr_seg -range 0x80000000 -offset 0x000E00000000 [get_bd_addr_spaces axi_cdma_0/Data] [get_bd_addr_segs aws_0/S_AXI_DDRC/Mem_DDRC] SEG_aws_0_Mem_DDRC
  create_bd_addr_seg -range 0x80000000 -offset 0x000F00000000 [get_bd_addr_spaces axi_cdma_0/Data] [get_bd_addr_segs aws_0/S_AXI_DDRD/Mem_DDRD] SEG_aws_0_Mem_DDRD


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


