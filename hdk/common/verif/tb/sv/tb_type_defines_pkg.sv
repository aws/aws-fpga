// Amazon FGPA Hardware Development Kit
// 
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// 
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
// 
//    http://aws.amazon.com/asl/
// 
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

package tb_type_defines_pkg;

//                      clk_main_a0	clk_extra_a1	clk_extra_a2	clk_extra_a3
// Profile 0 (Default)       125        62.5            187.5           250
// Profile 1	               250       125	            375             500
// Profile 2                  62.5      31.25           250             125
// Profile 3                  15.625     7.8125         125              62.5
// Profile 4                 225       112.5            337.5           450
// Profile 5                 200       100              300             400
								
//                      clk_extra_b0 clk_extra_b1		
// Profile 0 (Default)       250       125		
// Profile 1                 125        62.5		
				
//                      clk_extra_c0 clk_extra_c1		
// Profile 0 (Default)       300       400		
// Profile 1                 150       200		
 
  virtual class ClockProfile;     
     typedef enum integer {PROFILE_0=0, PROFILE_1=1, PROFILE_2=2, PROFILE_3=3, PROFILE_4=4, PROFILE_5=5} CLK_PROFILE;
  endclass // Clock_Profile

  virtual class DataSize;
     typedef enum integer {UINT8=0, UINT16=1, UINT32=2, UINT64=3} DATA_SIZE;
  endclass // DataSize
   
  virtual class AxiPort;
     typedef enum integer {PORT_PCIS=0, PORT_SDA=1, PORT_OCL=2, PORT_BAR1=3} AXI_PORT;
  endclass // AxiPort
   
endpackage
