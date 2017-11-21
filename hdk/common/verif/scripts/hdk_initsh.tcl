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


# TCL equivalent for common/verif/scripts/init.sh - Enables use of F1 on Windows to develop (implement to .tar) and then use AMI to create AFI


proc hdk_initsh_tcl_proc { {models_dir {""}} } {

	if {[ info exist ::env(HDK_COMMON_DIR) ] eq 0} {
		err_msg "HDK_COMMON_DIR not set. Source hdk_setup.tcl first."
		return 2
	}

	if { [ info exist ::env(VIVADO_VER) ] eq 0} {
		err_msg "VIVADO_VER not set. Source hdk_setup.tcl first."
		return 2
	}


	if { $models_dir eq "" } {
		set models_dir $::env(HDK_COMMON_DIR)/verif/models
	}

	if {[ file exist $models_dir] eq 0} {
		file mkdir $models_dir
	}


#########################################################################################
# Prevent multiple users from building in the same directory.
#########################################################################################
	set lockfile_filename $models_dir/build.lock
	if { [file exist $lockfile_filename] } {
		err_msg "$lockfile_filename exists"
		err_msg "Another process is already building the models."
		return 2
	}
	set writeThisFile [open $lockfile_filename w]
	puts $writeThisFile 1
	close $writeThisFile

	set writeThisFile [open $models_dir/.vivado_version w]
	puts $writeThisFile $::env(VIVADO_VER)
	close $writeThisFile

#########################################################################################
# Create the command and run Vivado to generate DDR4 verification models
#########################################################################################
	set vivcmd "vivado -mode batch -source $::env(HDK_COMMON_DIR)/verif/scripts/init.tcl"
	if {[exec {*}${vivcmd}] eq 0} {
		file delete -force $lockfile_filename
		return 2
	}

#########################################################################################
# Copy generated files from $ddr4_imports_dir to $ddr4_model_dir & $ddr4_rdimm_model_dir
#########################################################################################

	set ddr4_imports_dir tmp/tmp_ddr_ex/ddr4_core_ex/imports
	set ddr4_model_dir $models_dir/ddr4_model
	set ddr4_rdimm_model_dir $models_dir/ddr4_rdimm_wrapper
	

	if {[file isdirectory $ddr4_model_dir] eq 0 } {
		file mkdir $ddr4_model_dir
	}
	if {[file isdirectory $ddr4_rdimm_model_dir] eq 0 } {
		file mkdir $ddr4_rdimm_model_dir
	}

	lappend copylist arch_defines.v
	lappend copylist arch_package.sv            
	lappend copylist ddr4_model.sv               
	lappend copylist ddr4_sdram_model_wrapper.sv 
	#lappend copylist dimm_interface.sv          
	#lappend copylist dimm_subtest.vh             
	#lappend copylist dimm.vh                    
	lappend copylist interface.sv                
	lappend copylist MemoryArray.sv             
	lappend copylist proj_package.sv            
	lappend copylist StateTableCore.sv          
	lappend copylist StateTable.sv              
	#lappend copylist subtest.vh                 
	lappend copylist timing_tasks.sv            
	foreach {copyfile} $copylist {
		info_msg "Copying $ddr4_imports_dir/$copyfile to $ddr4_model_dir/$copyfile"
		file copy -force $ddr4_imports_dir/$copyfile $ddr4_model_dir/$copyfile
	}

	unset copylist
	lappend copylist ddr4_bi_delay.sv           
	lappend copylist ddr4_db_delay_model.sv     
	lappend copylist ddr4_db_dly_dir.sv         
	lappend copylist ddr4_dimm.sv               
	lappend copylist ddr4_dir_detect.sv         
	lappend copylist ddr4_rank.sv               
	lappend copylist ddr4_rcd_model.sv          
	lappend copylist ddr4_rdimm_wrapper.sv      
	foreach {copyfile} $copylist {
		info_msg "Copying $ddr4_imports_dir/$copyfile to $ddr4_model_dir/$copyfile"
		file copy -force $ddr4_imports_dir/$copyfile $ddr4_rdimm_model_dir/$copyfile
	}


#########################################################################################
# Remove lock file & return
#########################################################################################
	file delete -force $lockfile_filename


	return 0
}

#########################################################################################
#########################################################################################
## Process the models (sourcing the proc)
#########################################################################################
#########################################################################################
set backdir [pwd]
cd $::env(ddr4_build_dir)
if {[hdk_initsh_tcl_proc $::env(models_dir)] eq 2} {
	err_msg "DDR4 model build failed."
	err_msg "  Build dir=$::env(ddr4_build_dir)"
#	cd $backdir
#	return 2
}
cd $backdir
info_msg "DDR4 model build passed."
file delete -force $::env(ddr4_build_dir)

info_msg "AWS HDK setup COMPLETE (unverified SH_CL_BB_routed.dcp)."	

