
################################################################
# This is a generated script based on design: bd_bf3f
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
# source bd_bf3f_script.tcl

# If there is no project opened, this script will create a
# project, but make sure you do not have an existing project
# <./myproj/project_1.xpr> in the current working folder.

set list_projs [get_projects -quiet]
if { $list_projs eq "" } {
   create_project project_1 myproj -part xcvu9p-flgb2104-2-i
}


# CHANGE DESIGN NAME HERE
set design_name bd_bf3f

# This script was generated for a remote BD. To create a non-remote design,
# change the variable <run_remote_bd_flow> to <0>.

set run_remote_bd_flow 1
if { $run_remote_bd_flow == 1 } {
  # Set the reference directory for source file relative paths (by default 
  # the value is script directory path)
  set origin_dir ./v4_venom_cl.srcs/sources_1/ip/ddr4_core/bd_0

  # Use origin directory path location variable, if specified in the tcl shell
  if { [info exists ::origin_dir_loc] } {
     set origin_dir $::origin_dir_loc
  }

  set str_bd_folder [file normalize ${origin_dir}]
  set str_bd_filepath ${str_bd_folder}/${design_name}/${design_name}.bd

  # Check if remote design exists on disk
  if { [file exists $str_bd_filepath ] == 1 } {
     catch {common::send_msg_id "BD_TCL-110" "ERROR" "The remote BD file path <$str_bd_filepath> already exists!"}
     common::send_msg_id "BD_TCL-008" "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0>."
     common::send_msg_id "BD_TCL-009" "INFO" "Also make sure there is no design <$design_name> existing in your current project."

     return 1
  }

  # Check if design exists in memory
  set list_existing_designs [get_bd_designs -quiet $design_name]
  if { $list_existing_designs ne "" } {
     catch {common::send_msg_id "BD_TCL-111" "ERROR" "The design <$design_name> already exists in this project! Will not create the remote BD <$design_name> at the folder <$str_bd_folder>."}

     common::send_msg_id "BD_TCL-010" "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0> or please set a different value to variable <design_name>."

     return 1
  }

  # Check if design exists on disk within project
  set list_existing_designs [get_files -quiet */${design_name}.bd]
  if { $list_existing_designs ne "" } {
     catch {common::send_msg_id "BD_TCL-112" "ERROR" "The design <$design_name> already exists in this project at location:
    $list_existing_designs"}
     catch {common::send_msg_id "BD_TCL-113" "ERROR" "Will not create the remote BD <$design_name> at the folder <$str_bd_folder>."}

     common::send_msg_id "BD_TCL-011" "INFO" "To create a non-remote BD, change the variable <run_remote_bd_flow> to <0> or please set a different value to variable <design_name>."

     return 1
  }

  # Now can create the remote BD
  # NOTE - usage of <-dir> will create <$str_bd_folder/$design_name/$design_name.bd>
  create_bd_design -dir -bdsource SBD $str_bd_folder $design_name
} else {

  # Create regular design
  if { [catch {create_bd_design -bdsource SBD $design_name} errmsg] } {
     common::send_msg_id "BD_TCL-012" "INFO" "Please set a different value to variable <design_name>."

     return 1
  }
}

current_bd_design $design_name

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
  set IO [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:mcsio_bus_rtl:1.0 IO ]
  set TRACE [ create_bd_intf_port -mode Master -vlnv xilinx.com:interface:mbtrace_rtl:2.0 TRACE ]

  # Create ports
  set Clk [ create_bd_port -dir I -type clk Clk ]
  set_property -dict [ list \
CONFIG.ASSOCIATED_ASYNC_RESET {Reset} \
CONFIG.FREQ_HZ {100000000} \
 ] $Clk
  set Reset [ create_bd_port -dir I -type rst Reset ]
  set_property -dict [ list \
CONFIG.POLARITY {ACTIVE_HIGH} \
 ] $Reset

  # Create instance: dlmb, and set properties
  set dlmb [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_v10:3.0 dlmb ]
  set_property -dict [ list \
CONFIG.C_LMB_NUM_SLAVES {3} \
 ] $dlmb

  # Create instance: dlmb_cntlr, and set properties
  set dlmb_cntlr [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_bram_if_cntlr:4.0 dlmb_cntlr ]
  set_property -dict [ list \
CONFIG.C_MASK {0x00000000C0010000} \
 ] $dlmb_cntlr

  # Create instance: ilmb, and set properties
  set ilmb [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_v10:3.0 ilmb ]
  set_property -dict [ list \
CONFIG.C_LMB_NUM_SLAVES {2} \
 ] $ilmb

  # Create instance: ilmb_cntlr, and set properties
  set ilmb_cntlr [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_bram_if_cntlr:4.0 ilmb_cntlr ]
  set_property -dict [ list \
CONFIG.C_MASK {0x0000000080010000} \
 ] $ilmb_cntlr

  # Create instance: iomodule_0, and set properties
  set iomodule_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:iomodule:3.1 iomodule_0 ]
  set_property -dict [ list \
CONFIG.C_INSTANCE {iomodule} \
CONFIG.C_INTC_ADDR_WIDTH {17} \
CONFIG.C_INTC_HAS_FAST {1} \
CONFIG.C_INTC_LEVEL_EDGE {0x0000} \
CONFIG.C_INTC_POSITIVE {0xFFFF} \
CONFIG.C_INTC_USE_IRQ_OUT {1} \
CONFIG.C_IO_MASK {0x00000000C0000000} \
CONFIG.C_MASK {0x00000000C0000000} \
CONFIG.C_USE_IO_BUS {1} \
 ] $iomodule_0

  # Create instance: lmb_bram_I, and set properties
  set lmb_bram_I [ create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.3 lmb_bram_I ]
  set_property -dict [ list \
CONFIG.Memory_Type {True_Dual_Port_RAM} \
 ] $lmb_bram_I

  # Create instance: microblaze_I, and set properties
  set microblaze_I [ create_bd_cell -type ip -vlnv xilinx.com:ip:microblaze:10.0 microblaze_I ]
  set_property -dict [ list \
CONFIG.C_ASYNC_WAKEUP {3} \
CONFIG.C_DEBUG_ENABLED {0} \
CONFIG.C_FAULT_TOLERANT {0} \
CONFIG.C_INSTANCE {mb_microblaze_0} \
CONFIG.C_NUMBER_OF_PC_BRK {1} \
CONFIG.C_PC_WIDTH {17} \
CONFIG.C_TRACE {1} \
CONFIG.C_USE_BARREL {1} \
CONFIG.C_USE_DIV {1} \
CONFIG.C_USE_EXT_BRK {0} \
CONFIG.C_USE_EXT_NM_BRK {0} \
CONFIG.C_USE_HW_MUL {1} \
CONFIG.C_USE_PCMP_INSTR {1} \
CONFIG.C_USE_REORDER_INSTR {0} \
 ] $microblaze_I

  # Create instance: rst_0, and set properties
  set rst_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 rst_0 ]

  # Create instance: second_dlmb_cntlr, and set properties
  set second_dlmb_cntlr [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_bram_if_cntlr:4.0 second_dlmb_cntlr ]
  set_property -dict [ list \
CONFIG.C_MASK {0x00000000C0010000} \
 ] $second_dlmb_cntlr

  # Create instance: second_ilmb_cntlr, and set properties
  set second_ilmb_cntlr [ create_bd_cell -type ip -vlnv xilinx.com:ip:lmb_bram_if_cntlr:4.0 second_ilmb_cntlr ]
  set_property -dict [ list \
CONFIG.C_MASK {0x0000000080010000} \
 ] $second_ilmb_cntlr

  # Create instance: second_lmb_bram_I, and set properties
  set second_lmb_bram_I [ create_bd_cell -type ip -vlnv xilinx.com:ip:blk_mem_gen:8.3 second_lmb_bram_I ]
  set_property -dict [ list \
CONFIG.Memory_Type {True_Dual_Port_RAM} \
 ] $second_lmb_bram_I

  # Create interface connections
  connect_bd_intf_net -intf_net dlmb [get_bd_intf_pins dlmb/LMB_M] [get_bd_intf_pins microblaze_I/DLMB]
  connect_bd_intf_net -intf_net dlmb_port [get_bd_intf_pins dlmb_cntlr/BRAM_PORT] [get_bd_intf_pins lmb_bram_I/BRAM_PORTA]
  connect_bd_intf_net -intf_net dlmb_port_2 [get_bd_intf_pins second_dlmb_cntlr/BRAM_PORT] [get_bd_intf_pins second_lmb_bram_I/BRAM_PORTA]
  connect_bd_intf_net -intf_net dlmb_sl_0 [get_bd_intf_pins dlmb/LMB_Sl_0] [get_bd_intf_pins dlmb_cntlr/SLMB]
  connect_bd_intf_net -intf_net dlmb_sl_1 [get_bd_intf_pins dlmb/LMB_Sl_1] [get_bd_intf_pins iomodule_0/SLMB]
  connect_bd_intf_net -intf_net dlmb_sl_2 [get_bd_intf_pins dlmb/LMB_Sl_2] [get_bd_intf_pins second_dlmb_cntlr/SLMB]
  connect_bd_intf_net -intf_net ilmb [get_bd_intf_pins ilmb/LMB_M] [get_bd_intf_pins microblaze_I/ILMB]
  connect_bd_intf_net -intf_net ilmb_port [get_bd_intf_pins ilmb_cntlr/BRAM_PORT] [get_bd_intf_pins lmb_bram_I/BRAM_PORTB]
  connect_bd_intf_net -intf_net ilmb_port_2 [get_bd_intf_pins second_ilmb_cntlr/BRAM_PORT] [get_bd_intf_pins second_lmb_bram_I/BRAM_PORTB]
  connect_bd_intf_net -intf_net ilmb_sl_0 [get_bd_intf_pins ilmb/LMB_Sl_0] [get_bd_intf_pins ilmb_cntlr/SLMB]
  connect_bd_intf_net -intf_net ilmb_sl_1 [get_bd_intf_pins ilmb/LMB_Sl_1] [get_bd_intf_pins second_ilmb_cntlr/SLMB]
  connect_bd_intf_net -intf_net iomodule_0_IO [get_bd_intf_ports IO] [get_bd_intf_pins iomodule_0/IO_BUS]
  connect_bd_intf_net -intf_net microblaze_I_Trace [get_bd_intf_ports TRACE] [get_bd_intf_pins microblaze_I/TRACE]

  # Create port connections
  connect_bd_net -net Clk2 [get_bd_ports Clk] [get_bd_pins dlmb/LMB_Clk] [get_bd_pins dlmb_cntlr/LMB_Clk] [get_bd_pins ilmb/LMB_Clk] [get_bd_pins ilmb_cntlr/LMB_Clk] [get_bd_pins iomodule_0/Clk] [get_bd_pins microblaze_I/Clk] [get_bd_pins rst_0/slowest_sync_clk] [get_bd_pins second_dlmb_cntlr/LMB_Clk] [get_bd_pins second_ilmb_cntlr/LMB_Clk]
  connect_bd_net -net IO_Rst [get_bd_pins iomodule_0/Rst] [get_bd_pins rst_0/peripheral_reset]
  connect_bd_net -net LMB_Rst2 [get_bd_pins dlmb/SYS_Rst] [get_bd_pins dlmb_cntlr/LMB_Rst] [get_bd_pins ilmb/SYS_Rst] [get_bd_pins ilmb_cntlr/LMB_Rst] [get_bd_pins rst_0/bus_struct_reset] [get_bd_pins second_dlmb_cntlr/LMB_Rst] [get_bd_pins second_ilmb_cntlr/LMB_Rst]
  connect_bd_net -net MB_Reset [get_bd_pins microblaze_I/Reset] [get_bd_pins rst_0/mb_reset]
  connect_bd_net -net Reset [get_bd_ports Reset] [get_bd_pins rst_0/ext_reset_in]

  # Create address segments
  create_bd_addr_seg -range 0x00010000 -offset 0x00000000 [get_bd_addr_spaces microblaze_I/Data] [get_bd_addr_segs dlmb_cntlr/SLMB/Mem] SEG_dlmb_cntlr_Mem
  create_bd_addr_seg -range 0x00010000 -offset 0x00000000 [get_bd_addr_spaces microblaze_I/Instruction] [get_bd_addr_segs ilmb_cntlr/SLMB/Mem] SEG_ilmb_cntlr_Mem
  create_bd_addr_seg -range 0x40000000 -offset 0xC0000000 [get_bd_addr_spaces microblaze_I/Data] [get_bd_addr_segs iomodule_0/SLMB/IO] SEG_iomodule_0_IO
  create_bd_addr_seg -range 0x00010000 -offset 0x80000000 [get_bd_addr_spaces microblaze_I/Data] [get_bd_addr_segs iomodule_0/SLMB/Reg] SEG_iomodule_0_Reg
  create_bd_addr_seg -range 0x00008000 -offset 0x00010000 [get_bd_addr_spaces microblaze_I/Data] [get_bd_addr_segs second_dlmb_cntlr/SLMB/Mem] SEG_second_dlmb_cntlr_Mem
  create_bd_addr_seg -range 0x00008000 -offset 0x00010000 [get_bd_addr_spaces microblaze_I/Instruction] [get_bd_addr_segs second_ilmb_cntlr/SLMB/Mem] SEG_second_ilmb_cntlr_Mem


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
}
# End of create_root_design()


##################################################################
# MAIN FLOW
##################################################################

create_root_design ""


