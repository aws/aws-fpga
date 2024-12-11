# file: vio_0.xdc
##//////////////////////////////////////////////////////////////////////////////
#/$Date: 2012/02/06 10:34:16 $
#/$RCSfile:  $
#/$Revision: 1.2 $
#//////////////////////////////////////////////////////////////////////////////
#/ (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
#/
#/ This file contains confidential and proprietary information
#/ of AMD and is protected under U.S. and international copyright
#/ and other intellectual property laws.
#/
#/ DISCLAIMER
#/ This disclaimer is not a license and does not grant any
#/ rights to the materials distributed herewith. Except as
#/ otherwise provided in a valid license issued to you by
#/ AMD, and to the maximum extent permitted by applicable
#/ law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
#/ WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
#/ AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
#/ BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
#/ INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
#/ (2) AMD shall not be liable (whether in contract or tort,
#/ including negligence, or under any other theory of
#/ liability) for any loss or damage of any kind or nature
#/ related to, arising under or in connection with these
#/ materials, including for any direct, or any indirect,
#/ special, incidental, or consequential loss or damage
#/ (including loss of data, profits, goodwill, or any type of
#/ loss or damage suffered as a result of any action brought
#/ by a third party) even if such damage or loss was
#/ reasonably foreseeable or AMD had been advised of the
#/ possibility of the same.
#/
#/ CRITICAL APPLICATIONS
#/ AMD products are not designed or intended to be fail-
#/ safe, or for use in any application requiring fail-safe
#/ performance, such as life-support or safety devices or
#/ systems, Class III medical devices, nuclear facilities,
#/ applications related to the deployment of airbags, or any
#/ other applications that could lead to death, personal
#/ injury, or severe property or environmental damage
#/ (individually and collectively, "Critical
#/ Applications"). Customer assumes the sole risk and
#/ liability of any use of AMD products in Critical
#/ Applications, subject only to applicable laws and
#/ regulations governing limitations on product liability.
#/
#/ THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
#/ PART OF THIS FILE AT ALL TIMES.
#Created by Constraints Editor
 
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*Hold_probe_in*" &&  IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*PROBE_IN_INST/probe_in_reg*" && IS_SEQUENTIAL} ]
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*PROBE_IN_INST/probe_in_reg*" &&  IS_SEQUENTIAL} ] -to [get_cells -hierarchical -filter { NAME =~  "*data_int_sync1*" && IS_SEQUENTIAL }  ]
create_waiver -type CDC -id CDC-4 -from [get_pins -filter {REF_PIN_NAME=~C} -of_objects [get_cells -hierarchical -filter {NAME =~ "*probe_in_reg_reg*"}]]  -to [get_pins -filter {REF_PIN_NAME=~D} -of_objects [get_cells -hierarchical -filter {NAME =~ "*data_int_sync1_reg*"}]]  -user "vio" -description {The path has combinational circuit. But from hardware prospective the design works perfectly and the signals crossing happen after a very long time from the source has the value.} -tags "1050886" -scope -internal
    create_waiver -type CDC -id CDC-1 -from [get_pins -filter {REF_PIN_NAME=~C} -of_objects [get_cells -hierarchical -filter { NAME =~  "*Hold_probe_in*" &&  IS_SEQUENTIAL } ]]  -to [get_pins -filter {REF_PIN_NAME=~CE} -of_objects [get_cells -hierarchical -filter { NAME =~  "*PROBE_IN_INST/probe_in_reg*" && IS_SEQUENTIAL} ]]  -user "vio" -description {The path has combinational circuit. But from hardware prospective the design works perfectly and the signals crossing happen after a very long time from the source has the value.} -tags "1050886" -scope -internal
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*committ_int*" && IS_SEQUENTIAL}] -to [get_cells -hierarchical -filter { NAME =~  "*Committ_1*" &&  IS_SEQUENTIAL} ]
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*clear_int*" && IS_SEQUENTIAL}] -to [get_cells -hierarchical -filter { NAME =~  "*Probe_out*" && IS_SEQUENTIAL}] 
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*clear_int*" && IS_SEQUENTIAL }] -to [get_cells -hierarchical -filter { NAME =~  "*PROBE_OUT_ALL_INST/G_PROBE_OUT[*].PROBE_OUT0_INST/data_int*" && IS_SEQUENTIAL}]
	set_false_path -from [get_cells -hierarchical -filter { NAME =~  "*data_int_*" && IS_SEQUENTIAL } ] -to [get_cells -hierarchical -filter { NAME =~  "*Probe_out_*" && IS_SEQUENTIAL} ]
