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

for {set currentArgNum 0} {$currentArgNum < $argc} {incr currentArgNum} {
   set currentArg [lindex $argv $currentArgNum]
   if {[expr $currentArgNum + 1] < $argc} {
      set currentArgValue [lindex $argv [expr $currentArgNum +1]]
   }
   switch -regexp -- $currentArg {
      "^-h$" -
      "^-help" { 
         puts "None"
      }
      "^-TOP" {
         set TOP $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }      
      "^-IP_REPO" {
         set IP_REPO $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }
      "^-SYNTH_DIR" {
         set SYNTH_DIR $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }
      "^-BD_PATH" {
         set BD_PATH $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }
      "^-XDC" {
         set XDC $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }
      "^-USR_XDC" {
         set USR_XDC $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }
      "^-AWS_XDC" {
         set AWS_XDC $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }      
      "^-LINK_DCP_PATH" {
         set LINK_DCP_PATH $currentArgValue
	 # skip this arg the next pass through
	 incr currentArgNum
      }        
      "^-" {
      puts "SAE_ERROR: Unknown option!"
         
      }
      default {
      }
   }
   if {$currentArgNum >= $argc} {
      puts "SAE_ERROR: missing option value"
      usage
      return 1   
   }
}

  puts "$XDC"
  create_project -in_memory -part xcvu9p-flgb2104-2-i
  set_property ip_output_repo $IP_REPO [current_project]
  set_property ip_cache_permissions {read write} [current_project]
  add_files -quiet ${SYNTH_DIR}/${TOP}.dcp
  set_msg_config -source 4 -id {BD 41-1661} -suppress
	if {${BD_PATH} == "NONE"} {
		#Do Nothing
	} else {
  		add_files ${BD_PATH}
  		set_property is_locked true [get_files ${BD_PATH}]
	}  

  read_xdc -mode out_of_context ${XDC}
  set_property processing_order EARLY [get_files ${XDC}]
  read_xdc ${USR_XDC}
  
	if {${AWS_XDC} == "NONE"} {
		#Do Nothing
	} else {
  		read_xdc ${AWS_XDC}	

	}    
  link_design -top ${TOP} -part xcvu9p-flgb2104-2-i -mode out_of_context
  write_checkpoint -force $LINK_DCP_PATH
  exit