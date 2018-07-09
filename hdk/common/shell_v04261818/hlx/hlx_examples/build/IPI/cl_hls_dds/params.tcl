#© Copyright 2017 Xilinx, Inc. All rights reserved.

#This file contains confidential and proprietary information of Xilinx, Inc. and is protected under U.S. and
#international copyright and other intellectual property laws.

#DISCLAIMER
#This disclaimer is not a license and does not grant any rights to the materials distributed herewith.
#Except as otherwise provided in a valid license issued to you by Xilinx, and to the maximum extent
#permitted by applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
#FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS, IMPLIED, OR
#STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NONINFRINGEMENT,
#OR FITNESS FOR ANY PARTICULAR PURPOSE; and (2) Xilinx shall not be liable (whether
#in contract or tort, including negligence, or under any other theory of liability) for any loss or damage of
#any kind or nature related to, arising under or in connection with these materials, including for any
#direct, or any indirect, special, incidental, or consequential loss or damage (including loss of data,
#profits, goodwill, or any type of loss or damage suffered as a result of any action brought by a third
#party) even if such damage or loss was reasonably foreseeable or Xilinx had been advised of the
#possibility of the same.

#CRITICAL APPLICATIONS
#Xilinx products are not designed or intended to be fail-safe, or for use in any application requiring failsafe
#performance, such as life-support or safety devices or systems, Class III medical devices, nuclear
#facilities, applications related to the deployment of airbags, or any other applications that could lead to
#death, personal injury, or severe property or environmental damage (individually and collectively,
#"Critical Applications"). Customer assumes the sole risk and liability of any use of Xilinx products in
#Critical Applications, subject only to applicable laws and regulations governing limitations on product
#liability.

#THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE AT ALL TIMES.


if {[version -short] < "2017.1"} {
	puts "Vivado version [version -short] not supported, please use 2017.1 or later"
}

if {[version -short] ne "2017.1" && [version -short] ne "2017.2"} {
#	set_param bd.faas_ipname "xilinx.com:ip:aws:1.0"
	set_param bd.faas_board "f1_cl"
#	set_param bd.faas_interface "S_SH"
}

