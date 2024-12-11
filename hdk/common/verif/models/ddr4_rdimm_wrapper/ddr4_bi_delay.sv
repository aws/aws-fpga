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

module bi_delay_ddr4 #(DELAY_WIDTH = 16)
(
  inout uni_a,                   //uni_a is one of the unidirectional buses if we split a bidirectional bus--direction is from L-R
  inout uni_b,                   //uni_b is the other unidirectional bus from the same bidirectional bus--direction is from R-L
  input reset ,			 //reset port to reset the internal queues used to catch the activities on either of the bi directional bus.
  input [DELAY_WIDTH-1:0] delay,  //delay is the delay value during simulation.
  input read_drive,
  input write_drive
);
     
//reg read_drive  = 0; 	//read_drive and write_drive are the variables which will determine the direction of the bus.
 			  //read_drive gets the value 1 if the direction of the bus is from R-L
//reg write_drive  = 0;   //write_drive gets the value 1 if the direction of the bus is from L-R
reg delay_uni_a;        //this variable is just to assign the delayed value of uni_a which further gets assigned to uni_b
reg delay_uni_b;        //this variable is just to assign the delayed value of uni_b which further gets assigned to uni_a
//bit a_q[$];
//bit b_q[$];
reg read_drive_d;
reg write_drive_d;
           
time                   previous_edge_a; //time variable to catch the time stamp of previous edge of a port
bit [DELAY_WIDTH : 0 ] previous_delay_a; //previous value of delay applied on a port
time                   previous_edge_b; //time variable to catch the time stamp of previous edge of b port
bit [DELAY_WIDTH : 0 ] previous_delay_b; //previous value of delay applied on b port
	

//Capture the activity on uni_a and generate a internal signal delayed based on the delay value
always @ (uni_a) begin
  
  if(!reset) begin
    if ( previous_delay_a <= ((delay) + ($time - previous_edge_a)) )
      begin
        delay_uni_a <= #(delay) uni_a;   //whenever there is a change in uni_a, the value of uni_a is assigned to delay_uni_a with some delay
        previous_delay_a <= delay ;
        previous_edge_a <= $time;
      end
    else 
      begin
        delay_uni_a <= #(previous_delay_a) uni_a;        		 
        previous_edge_a <= $time;
      end
  end  
  else begin
  	delay_uni_a <= 1'b1;
  end
end 


//Capture the activity on uni_b and generte a internal signal delayed based on the delay value 
always @ (uni_b) begin
  if(!reset) begin
    if  ( previous_delay_b <= ((delay) + ($time - previous_edge_b)) ) 
      begin
        delay_uni_b <= #(delay ) uni_b;
        previous_delay_b <= delay ;
        previous_edge_b <= $time;
      end
    else
      begin
        delay_uni_b <= #(previous_delay_b) uni_b;        	  
        previous_edge_b <= $time;
      end
  end 
  else begin
  	delay_uni_b <= 1'b1;
  end

end


always @(read_drive)
  read_drive_d <= #(delay) read_drive;
	 
always @(write_drive)
  write_drive_d <= #(delay) write_drive;
	 
/*
//function to check if there is some activity happened on the b port
function bit check_queue_b();
  if ( b_q.size() > 0 )
    return b_q.pop_front();
  else
    return 0;
endfunction


//function to check if there is some activity happened on the a port
function bit check_queue_a();
  if ( a_q.size() > 0 )
    return a_q.pop_front();
  else
    return 0;
endfunction
*/

//***************************************************************************************************************
//whenever the read_drive is 1,the value of delay_uni_b is assigned to uni_a as a result of which uni_a gets the delayed value wrt uni_b
//when write_drive is 1, the value of delay_uni_a is assigned to uni_b because of which uni_b gets the delayed value wrt uni_a
//***************************************************************************************************************
assign  uni_a = (read_drive_d === 1'b1) ? delay_uni_b : 1'bz; 
assign  uni_b = (write_drive_d === 1'b1) ? delay_uni_a : 1'bz;

//*******
// Weak Pullups on  the uni_a  and uni_b
//*******
`ifndef FIX_2R_X16
buf (weak1, weak0) MC_side_pullup (uni_a, 1'b1);
buf (weak1, weak0) Mem_side_pullup (uni_b, 1'b1);
`endif
//generation of write drive and read drive signals...

//The logic will check if the delayed version of uni_a port is non 'Z' and there is no activity happened on uni_b port, then drive the uni_b port with the delayed version of uni_a port.(write path).
/*always @(delay_uni_a) begin
  if(!reset) begin
    if ( (delay_uni_a !== 1'bz) && (check_queue_a() != 1) )
      begin
        write_drive =  1'b1;
        b_q.push_back(1);
      end
    else
      write_drive =  1'b0;
  end  
end

    
//The logic will check if the delayed version of uni_b port is non 'Z' and there is no activity happened on uni_a port, then drive the uni_a port with the delayed version of uni_b port.( read path)
always @(delay_uni_b) begin
  if(!reset) begin
    if ( (delay_uni_b !== 1'bz) && (check_queue_b() != 1) )
      begin
        read_drive =  1'b1;
        a_q.push_back(1);
      end
    else
      read_drive =  1'b0;
  end  
end

//At reset clear all the pending status for both the bi-direction ports.
always@(negedge reset) begin
  read_drive = 1'b0;
  write_drive = 1'b0 ;
  if(a_q.size() > 0) begin
      a_q.delete();
  end
  if(b_q.size() > 0) begin
      b_q.delete();
  end
end*/

endmodule
