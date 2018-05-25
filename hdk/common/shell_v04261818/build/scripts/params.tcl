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

##################################################
### Tcl Procs and Params - 2017.1_sdx
##################################################
####Set params to disable OREG_B* in URAM for synthesis and physical synthesis
if {$uram_option != 2} {
  set_param synth.elaboration.rodinMoreOptions {rt::set_parameter disableOregPackingUram true}
  set_param physynth.ultraRAMOptOutput false
}

####Enable support of clocking from one RP to another (SH-->CL)
set_param hd.supportClockNetCrossDiffReconfigurablePartitions 1 

