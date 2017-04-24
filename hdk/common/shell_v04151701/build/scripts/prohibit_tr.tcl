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

if [string match "2017.1" [version -short]] {
   puts "Running LUT utilization analysis"
   set lutDemand [llength [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ CLB.LUT.* } ]]
   set lutCapacity [llength [get_bels -filter { TYPE =~  "SLICE*6LUT" && PROHIBIT == "FALSE" } -of_objects [get_sites -filter { SITE_TYPE =~ "SLICE*" && PROHIBIT == "FALSE"} ] ]
   ]
   set lutUtil [expr (100 * $lutDemand) / $lutCapacity]
   
   #prohibit sites if utilization is low
   if {$lutUtil < 80} { 
     puts "Low LUT utilization detected. Prohibit placement in low routable regions"
     resize_pblock [get_pblocks pblock_CL] -remove {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
     resize_pblock [get_pblocks pblock_CL_top] -remove {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
   
     create_pblock prohibit_placement
     resize_pblock [get_pblocks prohibit_placement] -add {CLOCKREGION_X5Y10:CLOCKREGION_X5Y14}
     set_property EXCLUDE_PLACEMENT ON [get_pblocks prohibit_placement]
   }
}
