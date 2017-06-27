
################################################################
# This is a generated script based on design: cl_axi_interconnect
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
# source cl_axi_interconnect_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./myproj/project_1.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { $list_projs eq "" } {
   create_project project_1 myproj -part xcvu9p-flgb2104-2-i
}


# CHANGE DESIGN NAME HERE
set design_name cl_axi_interconnect

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
  set M00_AXI [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M00_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.NUM_READ_OUTSTANDING {16} \
CONFIG.NUM_WRITE_OUTSTANDING {16} \
CONFIG.PROTOCOL {AXI4} \
 ] $M00_AXI
  set M01_AXI [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M01_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.NUM_READ_OUTSTANDING {16} \
CONFIG.NUM_WRITE_OUTSTANDING {16} \
CONFIG.PROTOCOL {AXI4} \
 ] $M01_AXI
  set M02_AXI [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M02_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.NUM_READ_OUTSTANDING {16} \
CONFIG.NUM_WRITE_OUTSTANDING {16} \
CONFIG.PROTOCOL {AXI4} \
 ] $M02_AXI
  set M03_AXI [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:aximm_rtl:1.0 M03_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.NUM_READ_OUTSTANDING {16} \
CONFIG.NUM_WRITE_OUTSTANDING {16} \
CONFIG.PROTOCOL {AXI4} \
 ] $M03_AXI
  set S00_AXI [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S00_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.ARUSER_WIDTH {0} \
CONFIG.AWUSER_WIDTH {0} \
CONFIG.BUSER_WIDTH {0} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.HAS_BRESP {1} \
CONFIG.HAS_BURST {1} \
CONFIG.HAS_CACHE {1} \
CONFIG.HAS_LOCK {1} \
CONFIG.HAS_PROT {1} \
CONFIG.HAS_QOS {1} \
CONFIG.HAS_REGION {1} \
CONFIG.HAS_RRESP {1} \
CONFIG.HAS_WSTRB {1} \
CONFIG.ID_WIDTH {6} \
CONFIG.MAX_BURST_LENGTH {256} \
CONFIG.NUM_READ_OUTSTANDING {32} \
CONFIG.NUM_READ_THREADS {16} \
CONFIG.NUM_WRITE_OUTSTANDING {32} \
CONFIG.NUM_WRITE_THREADS {16} \
CONFIG.PROTOCOL {AXI4} \
CONFIG.READ_WRITE_MODE {READ_WRITE} \
CONFIG.RUSER_BITS_PER_BYTE {0} \
CONFIG.RUSER_WIDTH {0} \
CONFIG.SUPPORTS_NARROW_BURST {1} \
CONFIG.WUSER_BITS_PER_BYTE {0} \
CONFIG.WUSER_WIDTH {0} \
 ] $S00_AXI
  set S01_AXI [ create_bd_intf_port -mode Slave -vlnv xilinx.com:interface:aximm_rtl:1.0 S01_AXI ]
  set_property -dict [ list \
CONFIG.ADDR_WIDTH {64} \
CONFIG.ARUSER_WIDTH {0} \
CONFIG.AWUSER_WIDTH {0} \
CONFIG.BUSER_WIDTH {0} \
CONFIG.CLK_DOMAIN {cl_axi_interconnect_ACLK} \
CONFIG.DATA_WIDTH {512} \
CONFIG.FREQ_HZ {250000000} \
CONFIG.HAS_BRESP {1} \
CONFIG.HAS_BURST {1} \
CONFIG.HAS_CACHE {1} \
CONFIG.HAS_LOCK {1} \
CONFIG.HAS_PROT {1} \
CONFIG.HAS_QOS {1} \
CONFIG.HAS_REGION {1} \
CONFIG.HAS_RRESP {1} \
CONFIG.HAS_WSTRB {1} \
CONFIG.ID_WIDTH {6} \
CONFIG.MAX_BURST_LENGTH {256} \
CONFIG.NUM_READ_OUTSTANDING {32} \
CONFIG.NUM_READ_THREADS {16} \
CONFIG.NUM_WRITE_OUTSTANDING {32} \
CONFIG.NUM_WRITE_THREADS {16} \
CONFIG.PROTOCOL {AXI4} \
CONFIG.READ_WRITE_MODE {READ_WRITE} \
CONFIG.RUSER_BITS_PER_BYTE {0} \
CONFIG.RUSER_WIDTH {0} \
CONFIG.SUPPORTS_NARROW_BURST {1} \
CONFIG.WUSER_BITS_PER_BYTE {0} \
CONFIG.WUSER_WIDTH {0} \
 ] $S01_AXI

  # Create ports
  set ACLK [ create_bd_port -dir I -type clk ACLK ]
  set_property -dict [ list \
CONFIG.FREQ_HZ {250000000} \
 ] $ACLK
  set ARESETN [ create_bd_port -dir I -type rst ARESETN ]

  # Create instance: axi_interconnect_0, and set properties
  set axi_interconnect_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect:2.1 axi_interconnect_0 ]
  set_property -dict [ list \
CONFIG.ENABLE_ADVANCED_OPTIONS {1} \
CONFIG.M00_HAS_REGSLICE {4} \
CONFIG.M01_HAS_REGSLICE {4} \
CONFIG.M02_HAS_REGSLICE {4} \
CONFIG.M03_HAS_REGSLICE {4} \
CONFIG.NUM_MI {4} \
CONFIG.NUM_SI {2} \
CONFIG.S00_HAS_REGSLICE {4} \
CONFIG.S01_HAS_REGSLICE {4} \
CONFIG.XBAR_DATA_WIDTH {512} \
 ] $axi_interconnect_0

  # Create interface connections
  connect_bd_intf_net -intf_net S00_AXI_1 [get_bd_intf_ports S00_AXI] [get_bd_intf_pins axi_interconnect_0/S00_AXI]
  connect_bd_intf_net -intf_net S01_AXI_1 [get_bd_intf_ports S01_AXI] [get_bd_intf_pins axi_interconnect_0/S01_AXI]
  connect_bd_intf_net -intf_net axi_interconnect_0_M00_AXI [get_bd_intf_ports M00_AXI] [get_bd_intf_pins axi_interconnect_0/M00_AXI]
  connect_bd_intf_net -intf_net axi_interconnect_0_M01_AXI [get_bd_intf_ports M01_AXI] [get_bd_intf_pins axi_interconnect_0/M01_AXI]
  connect_bd_intf_net -intf_net axi_interconnect_0_M02_AXI [get_bd_intf_ports M02_AXI] [get_bd_intf_pins axi_interconnect_0/M02_AXI]
  connect_bd_intf_net -intf_net axi_interconnect_0_M03_AXI [get_bd_intf_ports M03_AXI] [get_bd_intf_pins axi_interconnect_0/M03_AXI]

  # Create port connections
  connect_bd_net -net ACLK_1 [get_bd_ports ACLK] [get_bd_pins axi_interconnect_0/ACLK] [get_bd_pins axi_interconnect_0/M00_ACLK] [get_bd_pins axi_interconnect_0/M01_ACLK] [get_bd_pins axi_interconnect_0/M02_ACLK] [get_bd_pins axi_interconnect_0/M03_ACLK] [get_bd_pins axi_interconnect_0/S00_ACLK] [get_bd_pins axi_interconnect_0/S01_ACLK]
  connect_bd_net -net ARESETN_1 [get_bd_ports ARESETN] [get_bd_pins axi_interconnect_0/ARESETN] [get_bd_pins axi_interconnect_0/M00_ARESETN] [get_bd_pins axi_interconnect_0/M01_ARESETN] [get_bd_pins axi_interconnect_0/M02_ARESETN] [get_bd_pins axi_interconnect_0/M03_ARESETN] [get_bd_pins axi_interconnect_0/S00_ARESETN] [get_bd_pins axi_interconnect_0/S01_ARESETN]

  # Create address segments
  create_bd_addr_seg -range 0x000400000000 -offset 0x00000000 [get_bd_addr_spaces S00_AXI] [get_bd_addr_segs M00_AXI/Reg] SEG_M00_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x00000000 [get_bd_addr_spaces S01_AXI] [get_bd_addr_segs M00_AXI/Reg] SEG_M00_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000400000000 [get_bd_addr_spaces S00_AXI] [get_bd_addr_segs M01_AXI/Reg] SEG_M01_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000400000000 [get_bd_addr_spaces S01_AXI] [get_bd_addr_segs M01_AXI/Reg] SEG_M01_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000800000000 [get_bd_addr_spaces S00_AXI] [get_bd_addr_segs M02_AXI/Reg] SEG_M02_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000800000000 [get_bd_addr_spaces S01_AXI] [get_bd_addr_segs M02_AXI/Reg] SEG_M02_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000C00000000 [get_bd_addr_spaces S00_AXI] [get_bd_addr_segs M03_AXI/Reg] SEG_M03_AXI_Reg
  create_bd_addr_seg -range 0x000400000000 -offset 0x000C00000000 [get_bd_addr_spaces S01_AXI] [get_bd_addr_segs M03_AXI/Reg] SEG_M03_AXI_Reg


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


