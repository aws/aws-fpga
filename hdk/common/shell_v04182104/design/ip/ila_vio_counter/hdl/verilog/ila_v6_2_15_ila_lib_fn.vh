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
/*******************************************************************************

 *Device: All
 *Purpose:
 *  Verilog functions required by ila_lib 
 * 
 *******************************************************************************/

 function integer size_of_data;
  input integer num_match_units;
  input [`GC_TRIG_WIDTH_VEC_ARRAY_W-1:0] match_width_string;
  input [`GC_TRIG_TYPEID_VEC_ARRAY_W-1:0] match_tpid_string;
  integer i;
  begin
    size_of_data = match_width_string[0+:16]+1;
    for (i=1; i<num_match_units; i=i+1)
    begin
      if (match_tpid_string[(16*(i))+:16] > match_tpid_string[(16*(i-1))+:16])
        size_of_data = size_of_data + match_width_string[(match_tpid_string[(i*`GC_TRIG_TYPEID_VEC_W)+:16]*16)+:16]+1;
    end
  end
  
endfunction

 function integer match_units_count;
  input integer num_probes;
  input [`GC_MU_CNT_VEC_ARRAY_W-1:0] match_cnt_string;
  integer i;
  begin
    match_units_count = match_cnt_string[0+:4]+1;
    for (i=1; i<num_probes; i=i+1)
    begin
      match_units_count = match_units_count + match_cnt_string[(4*i)+:4]+1;
    end
  end
endfunction

 function [255:0] match_tpid;
  // Cast as bit16. Replace with null_value if not qualified.
      input [15:0] arg_ddr;
      input [15:0] arg;
      input        qual;
      input [15:0] val;
      integer i;
      integer j;
      integer arg_temp;
    begin
      arg_temp = qual ? arg_ddr : arg;

      for (i=0; i<arg_temp; i=i+1)
      begin
        match_tpid[i*16+:16] = val[15:0];
      end
      for (j=arg_temp; j<16; j=j+1)
      begin
        match_tpid[j*16+:16] = 16'h0000;
      end
    end
  endfunction

 function integer match_units_count_en;
  input integer num_mu;
  input [1023:0] is_string;
  integer i;
  begin
    //match_units_count = match_cnt_string[0+:2]+1;
    match_units_count_en = 0;
    for (i=0; i<num_mu; i=i+1)
    begin
      if (is_string[i] == 1'b1) begin
        match_units_count_en = match_units_count_en + 1;
      end  
    end
  end 
endfunction

 function integer size_of_data_less;
  input integer num_match_units;
  input [`GC_TRIG_WIDTH_VEC_ARRAY_W-1:0] match_width_string;
  input [`GC_TRIG_TYPEID_VEC_ARRAY_W-1:0] match_tpid_string;
  input [1023:0] is_string;
  integer i;
  begin
    if (is_string[0] == 1'b1) begin
      size_of_data_less = match_width_string[0+:16]+1;
    end else begin
      size_of_data_less = 0 ;
    end
    for (i=1; i<num_match_units; i=i+1)
    begin
      if (is_string[i] == 1'b1) begin
        size_of_data_less = size_of_data_less + match_width_string[i*16+:16]+1;
      end  
    end
  end
endfunction

 function integer size_of_data_full;
  input integer num_match_units;
  input [`GC_TRIG_WIDTH_VEC_ARRAY_W-1:0] match_width_string;
  input [`GC_TRIG_TYPEID_VEC_ARRAY_W-1:0] match_tpid_string;
  input [1023:0] is_string;
  integer i;
  begin
      size_of_data_full = match_width_string[0+:16]+1;
    for (i=1; i<num_match_units; i=i+1)
    begin
        size_of_data_full = size_of_data_full + match_width_string[i*16+:16]+1;
    end
  end
endfunction

