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

proc get_sink_clk_SC {sc clk_src} {
  set l_sc_clks [get_bd_pins -of [get_bd_cells $sc] -filter {TYPE == clk}]

  set num_of_clks [llength $l_sc_clks]
  set sink_clk ""
  foreach sc_clk $l_sc_clks {
     set clk [ find_bd_objs -quiet -legacy_mode -relation connected_to $sc_clk]
     if { $clk == $clk_src } {
        return ""
     }
     if { [string equal $sink_clk ""] && [string equal $clk ""] } {
         set sink_clk $sc_clk
     }
  }
  if { $sink_clk != "" } {
      return $sink_clk
  }
  set new_number [expr $num_of_clks + 1]
  if { $new_number > 2 } {
    set num_mi [get_property CONFIG.NUM_MI -quiet [get_bd_cells $sc] ]
    set num_si [get_property CONFIG.NUM_SI -quiet [get_bd_cells $sc] ]
    if { $num_mi == 1 && $num_si == 1} {
      set_property -quiet CONFIG.NUM_SI {2} [get_bd_cells $sc]
    }
  }
  set_property -dict [list CONFIG.NUM_CLKS $new_number] [get_bd_cells $sc]


  set sink_clk_name aclk$num_of_clks
  return [get_bd_pins $sc/$sink_clk_name]
}
