
################################################################
# This is a generated script based on design: bd_a493
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
set scripts_vivado_version 2016.4
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
# source bd_a493_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./myproj/project_1.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { $list_projs eq "" } {
   create_project project_1 myproj -part xcvu9p-flgb2104-2-i-es2
}


# CHANGE DESIGN NAME HERE
set design_name bd_a493

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

   create_bd_design -bdsource SBD $design_name

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

  # Create ports
  set bscanid [ create_bd_port -dir O -from 31 -to 0 bscanid ]
  set capture [ create_bd_port -dir I capture ]
  set clk [ create_bd_port -dir I -type clk clk ]
  set drck [ create_bd_port -dir I drck ]
  set reset [ create_bd_port -dir I reset ]
  set runtest [ create_bd_port -dir I runtest ]
  set sel [ create_bd_port -dir I sel ]
  set shift [ create_bd_port -dir I shift ]
  set tck [ create_bd_port -dir I tck ]
  set tdi [ create_bd_port -dir I tdi ]
  set tdo [ create_bd_port -dir O tdo ]
  set tms [ create_bd_port -dir I tms ]
  set update [ create_bd_port -dir I update ]

  # Create instance: lut_buffer, and set properties
  set lut_buffer [ create_bd_cell -type ip -vlnv xilinx.com:ip:lut_buffer:1.0 lut_buffer ]

  # Create instance: xsdbm, and set properties
  set xsdbm [ create_bd_cell -type ip -vlnv xilinx.com:ip:xsdbm:2.0 xsdbm ]
  set_property -dict [ list \
CONFIG.C_BUILD_REVISION {0} \
CONFIG.C_CLK_INPUT_FREQ_HZ {300000000} \
CONFIG.C_CORE_MAJOR_VER {1} \
CONFIG.C_CORE_MINOR_ALPHA_VER {97} \
CONFIG.C_CORE_MINOR_VER {0} \
CONFIG.C_CORE_TYPE {1} \
CONFIG.C_DCLK_HAS_RESET {0} \
CONFIG.C_ENABLE_CLK_DIVIDER {false} \
CONFIG.C_EN_INT_SIM {1} \
CONFIG.C_FIFO_STYLE {SUBCORE} \
CONFIG.C_MAJOR_VERSION {14} \
CONFIG.C_MINOR_VERSION {1} \
CONFIG.C_TWO_PRIM_MODE {false} \
CONFIG.C_USER_SCAN_CHAIN {1} \
CONFIG.C_USE_BUFR {0} \
CONFIG.C_USE_EXT_BSCAN {true} \
CONFIG.C_USE_STARTUP_CLK {false} \
CONFIG.C_XSDB_NUM_SLAVES {0} \
 ] $xsdbm

  # Create port connections
  connect_bd_net -net capture_1 [get_bd_ports capture] [get_bd_pins xsdbm/capture]
  connect_bd_net -net clk_1 [get_bd_ports clk] [get_bd_pins xsdbm/clk]
  connect_bd_net -net drck_1 [get_bd_ports drck] [get_bd_pins xsdbm/drck]
  connect_bd_net -net lut_buffer_bscanid_o [get_bd_ports bscanid] [get_bd_pins lut_buffer/bscanid_o]
  connect_bd_net -net lut_buffer_tdo_o [get_bd_ports tdo] [get_bd_pins lut_buffer/tdo_o]
  connect_bd_net -net reset_1 [get_bd_ports reset] [get_bd_pins xsdbm/reset]
  connect_bd_net -net runtest_1 [get_bd_ports runtest] [get_bd_pins xsdbm/runtest]
  connect_bd_net -net sel_1 [get_bd_ports sel] [get_bd_pins xsdbm/sel]
  connect_bd_net -net shift_1 [get_bd_ports shift] [get_bd_pins xsdbm/shift]
  connect_bd_net -net tck_1 [get_bd_ports tck] [get_bd_pins xsdbm/tck]
  connect_bd_net -net tdi_1 [get_bd_ports tdi] [get_bd_pins xsdbm/tdi]
  connect_bd_net -net tms_1 [get_bd_ports tms] [get_bd_pins xsdbm/tms]
  connect_bd_net -net update_1 [get_bd_ports update] [get_bd_pins xsdbm/update]
  connect_bd_net -net xsdbm_bscanid [get_bd_pins lut_buffer/bscanid_i] [get_bd_pins xsdbm/bscanid]
  connect_bd_net -net xsdbm_tdo [get_bd_pins lut_buffer/tdo_i] [get_bd_pins xsdbm/tdo]

  # Create address segments


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


