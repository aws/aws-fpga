# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


# Check if the tool loaded calibration_ddr.elf file into DDR Controller BRAMs
# NOTE: If BRAM Contents are not populated then the DDR will not calibrate on HW
print "Checking if MiG BRAM is initialized"

set ram_inst [get_cells -hierarchical -filter \
  {NAME=~*mcs0/inst/lmb_bram_I/U0/inst_blk_mem_gen/gnbram.gnative_mem_map_bmg.native_mem_map_blk_mem_gen/valid.cstr/ramloop[0].ram.r/prim_noinit.ram/DEVICE_8SERIES.WITH_BMM_INFO.TRUE_DP.SIMPLE_PRIM36.SERIES8_TDP_SP36_NO_ECC_ATTR.ram}
]

if {$ram_inst != ""} {
  set bram_value_0 "256'h0000000000000000000000000000000000000000000000000000000000000000"
  set bram_init_value [get_property INIT_2C $ram_inst]

  if {$bram_init_value == $bram_value_0} {
      print "CRITICAL WARNING: MiG BRAM is not populated with ELF file. This results in Calibration Failure!!"
  } else {
      print "MiG BRAM is initialized. INIT_2C = $bram_init_value"
  }

} else {
  print "Skip DDR calibration check"
}
