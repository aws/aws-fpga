// Amazon FPGA Hardware Development Kit
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
// Recipe A0 (Default)       125        62.5            187.5           250
// Recipe A1	             250       125	            375             500
// Recipe A2                  15.625     15.625         125              62.5
								
//                      clk_extra_b0 clk_extra_b1		
// Recipe B0 (Default)       250       125		
// Recipe B1                 125        62.5		
				
//                      clk_extra_c0 clk_extra_c1		
// Recipe C0 (Default)       300       400		
// Recipe C1                 150       200		
 
  virtual class ClockRecipe;
     typedef enum integer {A0=0, A1=1, A2=2} A_RECIPE;
     typedef enum integer {B0=0, B1=1} B_RECIPE;
     typedef enum integer {C0=0, C1=1} C_RECIPE;
  endclass // ClockRecipe

  virtual class DataSize;
     typedef enum integer {UINT8=0, UINT16=1, UINT32=2, UINT64=3, UINT128=4, UINT256=5, UINT512=6} DATA_SIZE;
  endclass // DataSize
   
  virtual class AxiPort;
     typedef enum integer {PORT_DMA_PCIS=0, PORT_SDA=1, PORT_OCL=2, PORT_BAR1=3} AXI_PORT;
  endclass // AxiPort
   
endpackage
