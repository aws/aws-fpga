// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////
`timescale 1ps/1ps

module ddr_dly_dir_detect #(
  CA_MIRROR         = "OFF" ,
  CS_NUM            =2,
  RDIMM_SLOTS       =1,
  MC_ABITS          =1
)
(
  input                ddr_ck,
  input [MC_ABITS-1:0] ddr_a,
  input [CS_NUM-1:0]ddr_cs_n,
  input [1:0]          ddr_bg,   
  input [1:0]          ddr_ba,
  input                initDone,
  output reg              db_dly_dir 
) ;

  
   
reg [2:0]   ddr_MRS_NUM_local;
reg [17:0]  ddr_a_local;


//vpradee:DDR4 Checker Updates for RDIMM(DT 829026)


 bit rank_Odd_Check;

 always@(ddr_ck)
  begin
   if((CS_NUM > 2)  )
     rank_Odd_Check= ((!ddr_cs_n[1]) || (!ddr_cs_n[3]));
   else if((RDIMM_SLOTS == 1) && (CS_NUM==2))
      rank_Odd_Check= !ddr_cs_n[1] ;
   else  
      rank_Odd_Check= 0 ;
  end


  always@(ddr_a[16:14]) begin

    if((CA_MIRROR=="ON")  && (rank_Odd_Check))  
    begin //{1
	  if(ddr_bg[0] == 1'b0)
          //*******Side A ********************
          begin //{2
           ddr_MRS_NUM_local[0]= ddr_ba[1];
           ddr_MRS_NUM_local[1]= ddr_ba[0];
           ddr_MRS_NUM_local[2]= ddr_bg[1];
	         ddr_a_local[0]  = ddr_a[0];
	         ddr_a_local[1]  = ddr_a[1];
	         ddr_a_local[2]  = ddr_a[2];
	         ddr_a_local[3]  = ddr_a[4];
	         ddr_a_local[4]  = ddr_a[3];
	         ddr_a_local[5]  = ddr_a[6];
	         ddr_a_local[6]  = ddr_a[5];
	         ddr_a_local[7]  = ddr_a[8];
	         ddr_a_local[8]  = ddr_a[7];
	         ddr_a_local[9]  = ddr_a[9];
	         ddr_a_local[10] = ddr_a[10];
	         ddr_a_local[11] = ddr_a[13];
	         ddr_a_local[12] = ddr_a[12];
	         ddr_a_local[13] = ddr_a[11];
	         ddr_a_local[14] = ddr_a[14];
	         ddr_a_local[15] = ddr_a[15];
	         ddr_a_local[16] = ddr_a[16];
	         ddr_a_local[17] = ddr_a[17];
	      end //} 2
      else   
          //*****Side B*************************
         begin //{3
             ddr_MRS_NUM_local[0] = ~ddr_ba[1];
             ddr_MRS_NUM_local[1] = ~ddr_ba[0];
             ddr_MRS_NUM_local[2] = ~ddr_bg[1];
	           ddr_a_local[0]  = ddr_a[0];
	           ddr_a_local[1]  = ddr_a[1];
	           ddr_a_local[2]  = ddr_a[2];
	           ddr_a_local[3]  = ~ddr_a[4];
	           ddr_a_local[4]  = ~ddr_a[3];
	           ddr_a_local[5]  = ~ddr_a[6];
	           ddr_a_local[6]  = ~ddr_a[5];
	           ddr_a_local[7]  = ~ddr_a[8];
	           ddr_a_local[8]  = ~ddr_a[7];
	           ddr_a_local[9]  = ~ddr_a[9];
	           ddr_a_local[10] = ddr_a[10];
	           ddr_a_local[11] = ~ddr_a[13];
	           ddr_a_local[12] = ddr_a[12];
	           ddr_a_local[13] = ~ddr_a[11];
	           ddr_a_local[14] = ddr_a[14];
	           ddr_a_local[15] = ddr_a[15];
	           ddr_a_local[16] = ddr_a[16];
	           ddr_a_local[17] = ~ddr_a[17];
	  end //}3
	  end // }1 CA_MIRROR
     else
     begin //{4
        //################## Mirror Address OFF  #######################
        if(ddr_bg[1] == 1'b0)
          begin //{5
           //*******Side A ********************
            ddr_a_local   = ddr_a ;
            ddr_MRS_NUM_local  = {ddr_bg[0],ddr_ba} ;
	    end //}5
	    else   
          begin //{6
             //*****Side B*************************
              ddr_MRS_NUM_local[0] = ~ddr_ba[0];
              ddr_MRS_NUM_local[1] = ~ddr_ba[1];
              ddr_MRS_NUM_local[2] = ~ddr_bg[0];
	            ddr_a_local[0]  = ddr_a[0];
	            ddr_a_local[1]  = ddr_a[1];
	            ddr_a_local[2]  = ddr_a[2];
	            ddr_a_local[3]  = ~ddr_a[3];
	            ddr_a_local[4]  = ~ddr_a[4];
	            ddr_a_local[5]  = ~ddr_a[5];
	            ddr_a_local[6]  = ~ddr_a[6];
	            ddr_a_local[7]  = ~ddr_a[7];
	            ddr_a_local[8]  = ~ddr_a[8];
	            ddr_a_local[9]  = ~ddr_a[9];
	            ddr_a_local[10] = ddr_a[10];
	            ddr_a_local[11] = ~ddr_a[11];
	            ddr_a_local[12] = ddr_a[12];
	            ddr_a_local[13] = ~ddr_a[13];
	            ddr_a_local[14] = ddr_a[14];
	            ddr_a_local[15] = ddr_a[15];
	            ddr_a_local[16] = ddr_a[16];
	            ddr_a_local[17] = ~ddr_a[17];
	     end //}6
      end   //}1
  end 


// Below thread always strats when there is change in command
  always@(ddr_ck) begin
    // Check if Command is for MRS2
    if((initDone ==1) && (ddr_a[16:14] == 3'b000) && (ddr_MRS_NUM_local == 3'b001)) begin
      // Drive the write leveling enable signal to dir_en
      //`uvm_info("always_block",$psprintf("Received MRS1 command for Write Leveling."), UVM_LOW);
    //  dir_en = ddr_a_local[7];
      db_dly_dir      = ddr_a_local[7];
   end
  end
 endmodule  
