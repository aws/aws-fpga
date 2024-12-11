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

module ddr4_db_delay_model #(
			    parameter MC_DQ_WIDTH = 16, // Memory DQ bus width
			    parameter MC_DQS_BITS = 4, // Number of DQS bits
			    parameter NUM_PHYSICAL_PARTS = 4, // Number of SDRAMs in a Single Rank
		        parameter MEM_PART_WIDTH = "x4" ,// Single Device width
			    parameter tCK = 1
			    )
  (
   input 		     ddr4_reset_n,
   inout [MC_DQ_WIDTH-1:0]   ddr4_db_dq,
   inout [MC_DQS_BITS-1:0]   ddr4_db_dqs_t,
   inout [MC_DQS_BITS-1:0]   ddr4_db_dqs_c,
   inout [MC_DQ_WIDTH-1:0]   ddr4_dimm_dq,
   inout [MC_DQS_BITS-1:0]   ddr4_dimm_dqs_t,
   inout [MC_DQS_BITS-1:0]   ddr4_dimm_dqs_c
   );


  wire     [NUM_PHYSICAL_PARTS-1:0] DB_rd_drive ; // used for control signal of bi_delay_ddr4
  wire     [NUM_PHYSICAL_PARTS-1:0]  DB_wr_drive ; // used for control signal of bi_delay_ddr4

  wire     [NUM_PHYSICAL_PARTS-1:0] wrlvl_rd_drive ; // used for comp_dq_rd_drive
  wire     [NUM_PHYSICAL_PARTS-1:0] DB_dq_rd_drive ; // used for control signal of dq bi_delay_ddr4
  wire     [NUM_PHYSICAL_PARTS-1:0] DB_dq_wr_drive ; // used for control signal of dq bi_delay_ddr4





  genvar 		     mem_part; // used in for-loop (shows which is the current mem part)
  genvar 		     dqs_y; // used in for-loop (shows which is the current dqs bit)
  localparam DQ_PER_DQS = 4 ;//only when MEM_PART_WIDTH=="x4"
  int DB2SDRAMdelays_int[NUM_PHYSICAL_PARTS]; // each word store the delay for a single device



  
  //VP-------------------- To generate DB to SDRAM Delays ----------------------------------------------------- 
 


 // Mem part  instances and adding of DB delays
  generate

	    // add DB to SDRAM delays on dq and dqs 
	    for(dqs_y=0; dqs_y<MC_DQS_BITS; dqs_y=dqs_y+1)
	      begin: add_delay_to_dq_dqs_dm

		// Add DB to SDRAM delays delays to DQ (each bit dqs is used to drive DQ_PER_DQS bits of dq)
		for(genvar dq_per_dqs_k=0; dq_per_dqs_k<DQ_PER_DQS; dq_per_dqs_k=dq_per_dqs_k+1)
		  begin: add_DB2SDRAM_delay_for_each_dq_bit

                  //------------------- DB BFM MIG ----------------------------------------------------

		    // bi_delays_ddr4 module add delay only to a single bit.
		    bi_delay_ddr4  #(.DELAY_WIDTH (32))
		    bit_delay_dq_DB2SDRAM (
     					    //.uni_a       (), 
     					    .uni_a       (ddr4_db_dq[dqs_y*DQ_PER_DQS+dq_per_dqs_k]), 
     	     				    .uni_b       (ddr4_dimm_dq[dqs_y*DQ_PER_DQS+dq_per_dqs_k]),
  					    .reset       (~ddr4_reset_n),
					    .write_drive (DB_dq_wr_drive[dqs_y]),
					    .read_drive  (DB_dq_rd_drive[dqs_y]),
					    .delay       (tCK)
					    );



                   // add DB delays to dqs_t
	   	bi_delay_ddr4  #(.DELAY_WIDTH (32))
		bit_delay_dqs_t_DB2SDRAM (
     					   .uni_a       (ddr4_db_dqs_t[dqs_y]),
     	     				   .uni_b       (ddr4_dimm_dqs_t[dqs_y]),
  					   .reset       (~ddr4_reset_n),
					   .write_drive (DB_wr_drive[dqs_y]),
					   .read_drive  (DB_rd_drive[dqs_y]),
					   .delay       (tCK)
					   );
		
		// add DB delays to dqs_c
		bi_delay_ddr4  #(.DELAY_WIDTH (32))
		bit_delay_dqs_c_DB2SDRAM (
     					   .uni_a       (ddr4_db_dqs_c[dqs_y]),
     	     				   .uni_b       (ddr4_dimm_dqs_c[dqs_y]),
  					   .reset       (~ddr4_reset_n),
					   .write_drive (DB_wr_drive[dqs_y]),
					   .read_drive  (DB_rd_drive[dqs_y]),
					   .delay       (tCK)
					   );

    
        end // add_delay_to_dq_dqs_dm
      end// add_db_to_sdram_delays

endgenerate


// direction detect module (read,write drive signals are used for control signals to bi_delay_ddr4
  // The number of dir_detect instances are NUM_PHYSICAL_PARTS*MC_DQS_BITS.
  generate
	
	for(mem_part=0; mem_part<NUM_PHYSICAL_PARTS; mem_part=mem_part+1)
	  begin: rd_wr_drive_signals_for_each_mem_part
		dir_detect U_dir_detect (
					    .MC_DQS_t  (ddr4_db_dqs_t[mem_part]),
        				.MC_DQS_c  (ddr4_db_dqs_c[mem_part]),
	         			.Mem_DQS_t (ddr4_dimm_dqs_t[mem_part]),
		         		.Mem_DQS_c (ddr4_dimm_dqs_c[mem_part]),
			        	.rd_drive  (DB_rd_drive[mem_part]),
				        .wr_drive  (DB_wr_drive[mem_part])
					    );
		
	        assign DB_dq_rd_drive[mem_part] =  DB_rd_drive[mem_part];
	        assign DB_dq_wr_drive[mem_part] =  DB_wr_drive[mem_part];
	     end
  endgenerate

endmodule // ddr4_db_delay_model
