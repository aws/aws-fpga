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

//typedef enum bit {SIDE_B, SIDE_A} components_side_e;
import arch_package::*;
`timescale 1ps/1ps
module ddr4_dimm #(
		   parameter MC_DQ_WIDTH = 16, // Memory DQ bus width
		   parameter MC_DQS_BITS = 4, // Number of DQS bits
		   parameter MC_DM_WIDTH = 4, // Number of DM bits
		   parameter MC_CKE_NUM = 1, // Number of CKE outputs to memory
		   parameter MC_ODT_WIDTH = 1, // Number of ODT pins
		   parameter MC_ABITS = 18, // Number of Address bits
		   parameter MC_BANK_WIDTH = 2, // Memory Bank address bits
		   parameter MC_BANK_GROUP = 2, // Memory Bank Groups
           `ifdef THREE_DS 
		   parameter MC_LR_WIDTH = 1, 
           `endif
		   parameter MC_CS_NUM = 1, // Number of unique CS output to Memory
		   parameter MC_RANKS_NUM = 1, // Number of Ranks
		   parameter NUM_PHYSICAL_PARTS = 4, // Number of SDRAMs in a Single Rank
		   parameter CALIB_EN = "NO", // When is set to "YES" ,R2R and FBT delays will be added 
		   parameter MIN_TOTAL_R2R_DELAY = 150, // Parameter shows the min range of Rank to Rank delay 
		   parameter MAX_TOTAL_R2R_DELAY = 1000, // Parameter shows the max range of Rank to Rank delay 
		   parameter TOTAL_FBT_DELAY = 2700, // Total Fly-by-Topology delay
		   parameter MEM_PART_WIDTH = "x4", // Single Device width
		   parameter MC_CA_MIRROR = "OFF", // TBD - Address Mirroring ON or OFF
		   // Shows which SDRAMs are connected to side A(first half) and side B(second half) of RCD.
		   //parameter components_side_e [NUM_PHYSICAL_PARTS-1:0] SDRAM = { {(NUM_PHYSICAL_PARTS/2){SIDE_B}}, {(NUM_PHYSICAL_PARTS/2){SIDE_A}} }, // SDRAM
		   parameter DDR_SIM_MODEL = "MICRON", // "MICRON" or "DENALI" memory model
		   parameter DM_DBI = "", // Disables dm_dbi_n if set to NONE
		   parameter MC_REG_CTRL = "ON", // Implement "ON" or "OFF" the RCD in rdimm wrapper
		   parameter UTYPE_density CONFIGURED_DENSITY = _4G
      )
  (
   // side A of the RCD
   input 		     qa_act_n,
   input [MC_ABITS-1:0]      qa_addr,
   input [MC_BANK_WIDTH-1:0] qa_ba,
   input [MC_BANK_GROUP-1:0] qa_bg,
   input 		     qa_par,
   input [MC_CKE_NUM-1:0]    qa_cke,
   input [MC_ODT_WIDTH-1:0]  qa_odt,
   `ifdef THREE_DS 
   input [MC_LR_WIDTH-1:0]   qa_c,
   `endif
   input [MC_CS_NUM-1:0]     qa_cs_n,
   // side B of the RCD
   input 		     qb_act_n,
   input [MC_ABITS-1:0]      qb_addr,
   input [MC_BANK_WIDTH-1:0] qb_ba,
   input [MC_BANK_GROUP-1:0] qb_bg,
   input 		     qb_par,
   input [MC_CKE_NUM-1:0]    qb_cke,
   input [MC_ODT_WIDTH-1:0]  qb_odt,
   `ifdef THREE_DS 
   input [MC_LR_WIDTH-1:0]   qb_c,
   `endif
   input [MC_CS_NUM-1:0]     qb_cs_n,
   
   input [MC_CS_NUM*2-1:0]   ck, // ck[0]->ck_c, ck[1]->ck_t
   input 		     reset_n,

   inout [MC_DQS_BITS-1:0]   dm_dbi_n,
   inout [MC_DQ_WIDTH-1:0]   dq,
   inout [MC_DQS_BITS-1:0]   dqs_t,
   inout [MC_DQS_BITS-1:0]   dqs_c, 
  
   output reg		     alert_n
   );

  localparam DQ_PER_DQS = (MEM_PART_WIDTH=="x4") ? 4 : 8; // DQ_PER_DQS is =4 only when MEM_PART_WIDTH=="x4"
    
  genvar 		     rank_x; // used in for-loop (shows which is the current Rank)
  genvar 		     dqs_y; // used in for-loop (shows which is the current dqs bit)
  

  // To each rank is necessary to have one bit cke and one bit odt.
  // In case there are differrence between number of Ranks and number of cke and odt bits, additional mapping for these signals are necessary. 
  wire [MC_RANKS_NUM-1:0]    mapped_qa_cke; // single bit cke for each rank
  wire [MC_RANKS_NUM-1:0]    mapped_qa_odt; // single bit odt for each rank
  wire [MC_RANKS_NUM-1:0]    mapped_qb_cke; // single bit cke for each rank
  wire [MC_RANKS_NUM-1:0]    mapped_qb_odt; // single bit odt for each rank
  
  // These wires are used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  // When Address Mirroring is enabled some bits of the address bus are swapped.
  wire [MC_ABITS-1:0] 	     swapped_qa_addr;
  wire [MC_BANK_WIDTH-1:0]   swapped_qa_ba;
  wire [MC_BANK_GROUP-1:0]   swapped_qa_bg;
  wire [MC_ABITS-1:0] 	     swapped_qb_addr;
  wire [MC_BANK_WIDTH-1:0]   swapped_qb_ba;
  wire [MC_BANK_GROUP-1:0]   swapped_qb_bg;

 //******** These signals are connected to Ranks ********//
 // In case that CALIB_EN="YES" to these signals are added R2R delays  
  reg [MC_CS_NUM*2-1:0]      rank_ck;
  reg [MC_RANKS_NUM-1:0]     rank_reset_n;
  reg [MC_RANKS_NUM-1:0]     rank_alert_n;
    
  reg [MC_RANKS_NUM-1:0]     rank_qa_act_n;
  reg [MC_ABITS-1:0] 	     rank_qa_addr [MC_RANKS_NUM];
  reg [MC_BANK_WIDTH-1:0]    rank_qa_ba [MC_RANKS_NUM];
  reg [MC_BANK_GROUP-1:0]    rank_qa_bg [MC_RANKS_NUM];
  reg [MC_RANKS_NUM-1:0]     rank_qa_par;
  reg [MC_RANKS_NUM-1:0]     rank_qa_cke; // single bit cke for each rank
  reg [MC_RANKS_NUM-1:0]     rank_qa_odt; // single bit cke for each rank
   `ifdef THREE_DS 
  reg [MC_LR_WIDTH-1:0]      rank_qa_c [MC_RANKS_NUM];
   `endif
  reg [MC_CS_NUM-1:0] 	     rank_qa_cs_n;
  
  reg [MC_RANKS_NUM-1:0]     rank_qb_act_n;
  reg [MC_ABITS-1:0] 	     rank_qb_addr [MC_RANKS_NUM];
  reg [MC_BANK_WIDTH-1:0]    rank_qb_ba [MC_RANKS_NUM];
  reg [MC_BANK_GROUP-1:0]    rank_qb_bg [MC_RANKS_NUM];
  reg [MC_RANKS_NUM-1:0]     rank_qb_par;
  reg [MC_RANKS_NUM-1:0]     rank_qb_cke; // single bit cke for each rank
  reg [MC_RANKS_NUM-1:0]     rank_qb_odt; // single bit cke for each rank  
   `ifdef THREE_DS 
  reg [MC_LR_WIDTH-1:0]      rank_qb_c [MC_RANKS_NUM];
   `endif
  reg [MC_CS_NUM-1:0] 	     rank_qb_cs_n;
  
  reg [MC_ABITS-1:0] 	     odd_rank_qa_addr [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  reg [MC_BANK_WIDTH-1:0]    odd_rank_qa_ba [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  reg [MC_BANK_GROUP-1:0]    odd_rank_qa_bg [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  
  reg [MC_ABITS-1:0] 	     odd_rank_qb_addr [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  reg [MC_BANK_WIDTH-1:0]    odd_rank_qb_ba [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)
  reg [MC_BANK_GROUP-1:0]    odd_rank_qb_bg [MC_RANKS_NUM]; // used only for odd ranks when MC_CA_MIRROR="ON" (enabled)

  wire [MC_DQS_BITS-1:0]     rank_dm_dbi_n [MC_RANKS_NUM]; // dm_dbi_n - direction is from Mem to MC
  wire [MC_DQ_WIDTH-1:0]     rank_dq [MC_RANKS_NUM]; // dq - direction is from Mem to MC
  wire [MC_DQS_BITS-1:0]     rank_dqs_t [MC_RANKS_NUM]; // dqs_t - direction is from Mem to MC
  wire [MC_DQS_BITS-1:0]     rank_dqs_c [MC_RANKS_NUM]; // dqs_c - direction is from Mem to MC 
  //******************************************************//
  
  wire [MC_DQS_BITS-1:0]     r2r_rd_drive [MC_RANKS_NUM]; // used for control signal of bi_delay_ddr4
  wire [MC_DQS_BITS-1:0]     r2r_wr_drive [MC_RANKS_NUM]; // used for control signal of bi_delay_ddr4
  
  int 			     r2r_delays_int [MC_RANKS_NUM]; // store the delays for each Rank
  
  //******************** Mapping of CKE and ODT signals ******************************************//
  // Mapping of CKE to each Rank
  generate
    if (MC_REG_CTRL == "ON") // RCD support maximum of only two bits CKE
      begin: cke_limitation_with_rcd
	if( (MC_RANKS_NUM==4) && (MC_CKE_NUM==2) )
	  begin: quad_ranks_cke_two_bits
	    assign mapped_qa_cke = { {2{qa_cke[1]}}, {2{qa_cke[0]}} }; // qx_cke[0] is connected to Rank 0 and Rank 1
	    assign mapped_qb_cke = { {2{qb_cke[1]}}, {2{qb_cke[0]}} }; // qx_cke[1] is connected to Rank 2 and Rank 3
	  end
	else
	  begin: begin_else_block_cke
	    if( (MC_RANKS_NUM==2) && (MC_CKE_NUM==2) )
	      begin: dual_ranks_cke_two_bits		
		assign mapped_qa_cke = qa_cke; // qx_cke[0] is connected to Rank 0
		assign mapped_qb_cke = qb_cke; // qx_cke[1] is connected to Rank 1
	      end
	    else
	      begin: ranks_cke_one_bit // qx_cke[0] is connected to all Ranks			    
		assign mapped_qa_cke = {MC_RANKS_NUM{qa_cke}};
		assign mapped_qb_cke = {MC_RANKS_NUM{qb_cke}};
	      end
	  end // block: begin_else_block_cke
      end // block: cke_limitation_with_rcd
    else // !if (MC_REG_CTRL == "ON")
      begin: cke_without_rcd
	assign mapped_qa_cke = qa_cke;
	assign mapped_qb_cke = qb_cke;
      end // cke_without_rcd
  endgenerate
  
  // Mapping of ODT to each Rank
  generate
    if(MC_REG_CTRL == "ON") // RCD support maximum of only two bits ODT
      begin: odt_limitation_with_rcd
	if( (MC_RANKS_NUM==4) && (MC_ODT_WIDTH==2) )
	  begin: quad_ranks_odt_two_bits
	    assign mapped_qa_odt = { {2{qa_odt[1]}}, {2{qa_odt[0]}} }; // qx_odt[0] is connected to Rank 0 and Rank 1
	    assign mapped_qb_odt = { {2{qb_odt[1]}}, {2{qb_odt[0]}} }; // qx_odt[1] is connected to Rank 2 and Rank 3
	  end
	else
	  begin: begin_else_block_odt
	    if( (MC_RANKS_NUM==2) && (MC_ODT_WIDTH==2) )
	      begin: dual_ranks_odt_two_bits		
		assign mapped_qa_odt = qa_odt; // qx_odt[0] is connected to Rank 0
		assign mapped_qb_odt = qb_odt; // qx_odt[1] is connected to Rank 1
	      end
	    else
	      begin: ranks_odt_one_bit // qx_odt[0] is connected to all Ranks			    
		assign mapped_qa_odt = {MC_RANKS_NUM{qa_odt}};
		assign mapped_qb_odt = {MC_RANKS_NUM{qb_odt}};
	      end
	  end // block: begin_else_block_odt
      end // block: odt_limitation_with_rcd
    else // !if(MC_REG_CTRL == "ON")
      begin: odt_without_rcd
        assign mapped_qa_odt = qa_odt;
	assign mapped_qb_odt = qb_odt;
      end // odt_without_rcd
  endgenerate
  //******************** End of Mapping of CKE and ODT signals ***********************************//

  //******************** Address Mirroring enabled - Addr, BA and BG signals for odd Ranks *******//
  // Only if MC_CA_MIRROR="ON"(enabled) - Addr, BA swapping
  generate
    if(MC_CA_MIRROR=="ON")
      begin: swapped_wires
	assign swapped_qa_ba = {qa_ba[0], qa_ba[1]}; // BA0 and BA1 swapped
	assign swapped_qb_ba = {qb_ba[0], qb_ba[1]}; // BA0 and BA1 swapped

//	if((MC_ABITS-14)>0) // MC_ABITS>14
//	  begin: mc_abits_more_than_14_bits	
	    assign swapped_qa_addr = { qa_addr[MC_ABITS-1:14],
					qa_addr[11], qa_addr[12], qa_addr[13], // A11 and A13 swapped
					qa_addr[10:9],
					qa_addr[7], qa_addr[8], // A7 and A8 swapped
					qa_addr[5], qa_addr[6], // A5 and A6 swapped
					qa_addr[3], qa_addr[4], // A3 and A4 swapped
					qa_addr[2:0] };
	    
	    assign swapped_qb_addr = { qb_addr[MC_ABITS-1:14],
					qb_addr[11], qb_addr[12], qb_addr[13], // A11 and A13 swapped
					qb_addr[10:9],
					qb_addr[7], qb_addr[8], // A7 and A8 swapped
					qb_addr[5], qb_addr[6], // A5 and A6 swapped
					qb_addr[3], qb_addr[4], // A3 and A4 swapped
					qb_addr[2:0] };
//	  end // block: mc_abits_more_than_14_bits
//	else // *if((MC_ABITS-14)>0) // MC_ABITS=14
//	  begin: mc_abits_equal_to_14_bits // In case qx_addr[13:0]
//	    assign swapped_qa_addr = {qa_addr[11], qa_addr[12], qa_addr[13], // A11 and A13 swapped
//				       qa_addr[10:9],
//				       qa_addr[7], qa_addr[8], // A7 and A8 swapped
//				       qa_addr[5], qa_addr[6], // A5 and A6 swapped
//				       qa_addr[3], qa_addr[4], // A3 and A4 swapped
//				       qa_addr[2:0]};
//	    
//	    assign swapped_qb_addr = {qb_addr[11], qb_addr[12], qb_addr[13], // A11 and A13 swapped
//				       qb_addr[10:9],
//				       qb_addr[7], qb_addr[8], // A7 and A8 swapped
//				       qb_addr[5], qb_addr[6], // A5 and A6 swapped
//				       qb_addr[3], qb_addr[4], // A3 and A4 swapped
//				       qb_addr[2:0]};				    
//	  end // block: mc_abits_equal_to_14_bits
      end // block: swapped_wires
  endgenerate
  
  // Only if MC_CA_MIRROR="ON"(enabled) - BG is one bit for x16 Devices and cannot be swapped
  generate
    if(MC_CA_MIRROR=="ON")
      begin: swapped_bg_wires
	if(MEM_PART_WIDTH=="x16") // BG is one bit for x16 Devices - cannot swapping
	  begin: one_bit_bg_cannot_swapped
	    assign swapped_qa_bg = qa_bg;
	    assign swapped_qb_bg = qb_bg;
	  end
	else // MEM_PART_WIDTH == x4 or x8
	  begin: two_bits_bg_swapped
	    assign swapped_qa_bg = {qa_bg[0], qa_bg[1]}; // BG0 and BG1 swapped
	    assign swapped_qb_bg = {qb_bg[0], qb_bg[1]}; // BG0 and BG1 swapped
	  end
      end // block: swapped_bg_wires
  endgenerate
  //************* End of Address Mirroring enabled - Addr, BA and BG signals for odd Ranks *******//

  // direction detect module (read,write drive signals are used for control signals to bi_delay_ddr4
  // The number of dir_detect instances are MC_RANKS_NUM*MC_DQS_BITS.
  generate
    if(CALIB_EN=="YES" && MC_RANKS_NUM!=1) // Note: in case of only one Rank, R2R delays are not added.
      begin: rd_wr_drive_signals
	
	for(rank_x=0; rank_x<MC_RANKS_NUM; rank_x=rank_x+1)
	  begin: rd_wr_drive_signals_for_each_rank
	    
	    for(dqs_y=0; dqs_y<MC_DQS_BITS; dqs_y=dqs_y+1)
	      begin: instance_of_dir_detect
		
		dir_detect dir_detect_inst (
					    .MC_DQS_t  (dqs_t[dqs_y]),
        				    .MC_DQS_c  (dqs_c[dqs_y]),
	         			    .Mem_DQS_t (rank_dqs_t[rank_x][dqs_y]),
		         		    .Mem_DQS_c (rank_dqs_c[rank_x][dqs_y]),
			        	    .rd_drive  (r2r_rd_drive[rank_x][dqs_y]),
				            .wr_drive  (r2r_wr_drive[rank_x][dqs_y])
					    );
	      end // block: instance_of_dir_detect	    
	  end // block: rd_wr_drive_signals_for_each_rank	     
      end // block: rd_wr_drive_signals
  endgenerate

`ifndef XILINX_SIMULATOR 
  // Rank to Rank delay - create object DDR_R2R_DELAYS. Randomize R2R delays for each Rank and pass the values of the delay to local variable r2r_delays_int.
  generate
    if(CALIB_EN=="YES" && MC_RANKS_NUM!=1)
      begin: create_r2r_delays

	//dimm_rank2rank_delays #(.MIN_TOTAL_R2R_DELAY(MIN_TOTAL_R2R_DELAY),.MAX_TOTAL_R2R_DELAY(MAX_TOTAL_R2R_DELAY),.NUM_RANKS(MC_CS_NUM), .ENABLE(1) ) DDR_R2R_DELAYS;

	//initial
	//  begin: create_reset_r2r_delays
	//    DDR_R2R_DELAYS = new();
	//    DDR_R2R_DELAYS.reset_value();
	//  end

	for(rank_x=0; rank_x<MC_RANKS_NUM; rank_x=rank_x+1)
	  begin: randomization_of_r2r_delays

	    initial
	      begin
		assert(DDR_R2R_DELAYS.randomize()) // Randomize R2R delay for each Rank		
		  else
		   // `uvm_error("ddr4_dimm.sv", "Randomization of DDR_R2R_DELAYS FAILED")

		r2r_delays_int[rank_x] = DDR_R2R_DELAYS.delay; // Store the randomized R2R delays in r2r_delays_int
	      end
	  end // block: randomization_of_r2r_delays
      end // block: create_r2r_delays
  endgenerate
`endif
 
  // Rank instances and adding of R2R delays
  generate
    for(rank_x=0; rank_x<MC_RANKS_NUM; rank_x=rank_x+1)
      begin: rank_instances

	//************************* WITH/WITHOUT R2R delays ***********************//
	if(CALIB_EN=="YES" && MC_RANKS_NUM!=1) // add Rank to Rank delays only if Number of Ranks is more than 1
	  begin: add_r2r_delays
	    
	    // add R2R delays to DQ, DQS and DM
	    for(dqs_y=0; dqs_y<MC_DQS_BITS; dqs_y=dqs_y+1)
	      begin: add_r2r_delay_to_dq_dqs_dm

		// Add R2R delays to DQ (each bit dqs is used to drive DQ_PER_DQS bits of dq)
		for(genvar dq_per_dqs_k=0; dq_per_dqs_k<DQ_PER_DQS; dq_per_dqs_k=dq_per_dqs_k+1)
		  begin: add_r2r_delay_for_each_dq_bit

		    // bi_delays_ddr4 module add delay only to a single bit.
		    bi_delay_ddr4  #(.DELAY_WIDTH (32))
		    bit_delay_dq_rank2rank (
     					    .uni_a       (dq[dqs_y*DQ_PER_DQS+dq_per_dqs_k]),
     	     				    .uni_b       (rank_dq[rank_x][dqs_y*DQ_PER_DQS+dq_per_dqs_k]),
  					    .reset       (~reset_n),
					    .write_drive (r2r_wr_drive[rank_x][dqs_y]),
					    .read_drive  (r2r_rd_drive[rank_x][dqs_y]),
					    .delay       (r2r_delays_int[rank_x])
					    );
		  end // block: add_r2r_delay_for_each_dq_bit

		// add R2R delays to dqs_t
		bi_delay_ddr4  #(.DELAY_WIDTH (32))
		bit_delay_dqs_t_rank2rank (
     					   .uni_a       (dqs_t[dqs_y]),
     	     				   .uni_b       (rank_dqs_t[rank_x][dqs_y]),
  					   .reset       (~reset_n),
					   .write_drive (r2r_wr_drive[rank_x][dqs_y]),
					   .read_drive  (r2r_rd_drive[rank_x][dqs_y]),
					   .delay       (r2r_delays_int[rank_x])
					   );
		
		// add R2R delays to dqs_c
		bi_delay_ddr4  #(.DELAY_WIDTH (32))
		bit_delay_dqs_c_rank2rank (
     					   .uni_a       (dqs_c[dqs_y]),
     	     				   .uni_b       (rank_dqs_c[rank_x][dqs_y]),
  					   .reset       (~reset_n),
					   .write_drive (r2r_wr_drive[rank_x][dqs_y]),
					   .read_drive  (r2r_rd_drive[rank_x][dqs_y]),
					   .delay       (r2r_delays_int[rank_x])
					   );
		
		// add R2R delays to dm_dbi_n
		bi_delay_ddr4  #(.DELAY_WIDTH (32))
		bit_delay_dm_dbi_n_rank2rank (
     					      .uni_a       (dm_dbi_n[dqs_y]),
     	     				      .uni_b       (rank_dm_dbi_n[rank_x][dqs_y]),
  					      .reset       (~reset_n),
					      .write_drive (r2r_wr_drive[rank_x][dqs_y]),
					      .read_drive  (r2r_rd_drive[rank_x][dqs_y]),
					      .delay       (r2r_delays_int[rank_x])
					      );

	      end // block: add_r2r_delay_to_dq_dqs_dm

	    if(MC_REG_CTRL=="ON") // without R2R delay to ck signal in case that MC_REG_CTRL = "ON"
	      always@(*) rank_ck[rank_x*2+:2] <= ck[rank_x*2+:2];
	    else
	      always@(*) rank_ck[rank_x*2+:2] <= #(r2r_delays_int[rank_x]) ck[rank_x*2+:2]; // without RCD to ck signal is added R2R delay

	    always@(*) rank_reset_n[rank_x] <= #(r2r_delays_int[rank_x]) reset_n;
	    always@(*) alert_n              <= #(r2r_delays_int[rank_x]) rank_alert_n[rank_x];
	    
	    always@(*) rank_qa_act_n[rank_x] <= #(r2r_delays_int[rank_x]) qa_act_n;
	    always@(*) rank_qa_addr[rank_x]  <= #(r2r_delays_int[rank_x]) qa_addr;
	    always@(*) rank_qa_ba[rank_x]    <= #(r2r_delays_int[rank_x]) qa_ba;
	    always@(*) rank_qa_bg[rank_x]    <= #(r2r_delays_int[rank_x]) qa_bg;
	    always@(*) rank_qa_par[rank_x]   <= #(r2r_delays_int[rank_x]) qa_par;
	    always@(*) rank_qa_cke[rank_x]   <= #(r2r_delays_int[rank_x]) mapped_qa_cke[rank_x];
	    always@(*) rank_qa_odt[rank_x]   <= #(r2r_delays_int[rank_x]) mapped_qa_odt[rank_x];
   `ifdef THREE_DS 
	    always@(*) rank_qa_c[rank_x]     <= #(r2r_delays_int[rank_x]) qa_c;
   `endif
	    always@(*) rank_qa_cs_n[rank_x]  <= #(r2r_delays_int[rank_x]) qa_cs_n[rank_x];
	    
	    always@(*) rank_qb_act_n[rank_x] <= #(r2r_delays_int[rank_x]) qb_act_n;
	    always@(*) rank_qb_addr[rank_x]  <= #(r2r_delays_int[rank_x]) qb_addr;
	    always@(*) rank_qb_ba[rank_x]    <= #(r2r_delays_int[rank_x]) qb_ba;
	    always@(*) rank_qb_bg[rank_x]    <= #(r2r_delays_int[rank_x]) qb_bg;
	    always@(*) rank_qb_par[rank_x]   <= #(r2r_delays_int[rank_x]) qb_par;
	    always@(*) rank_qb_cke[rank_x]   <= #(r2r_delays_int[rank_x]) mapped_qb_cke[rank_x];
	    always@(*) rank_qb_odt[rank_x]   <= #(r2r_delays_int[rank_x]) mapped_qb_odt[rank_x];
   `ifdef THREE_DS 
	    always@(*) rank_qb_c[rank_x]     <= #(r2r_delays_int[rank_x]) qb_c;
   `endif
	    always@(*) rank_qb_cs_n[rank_x]  <= #(r2r_delays_int[rank_x]) qb_cs_n[rank_x];
	    
	    always@(*) odd_rank_qa_addr[rank_x] <= #(r2r_delays_int[rank_x]) swapped_qa_addr;
	    always@(*) odd_rank_qa_ba[rank_x]   <= #(r2r_delays_int[rank_x]) swapped_qa_ba;
	    always@(*) odd_rank_qa_bg[rank_x]   <= #(r2r_delays_int[rank_x]) swapped_qa_bg;
	    
	    always@(*) odd_rank_qb_addr[rank_x] <= #(r2r_delays_int[rank_x]) swapped_qb_addr;
	    always@(*) odd_rank_qb_ba[rank_x]   <= #(r2r_delays_int[rank_x]) swapped_qb_ba;
	    always@(*) odd_rank_qb_bg[rank_x]   <= #(r2r_delays_int[rank_x]) swapped_qb_bg;
	    
	  end // block: add_r2r_delays
	else // !if(CALIB_EN=="YES" && MC_RANKS_NUM!=1) // Without Rank to Rank delays
	  begin: without_r2r_delays
	    `ifdef XILINX_SIMULATOR
    	short bidiDQ[MC_DQ_WIDTH-1:0]    (dq[MC_DQ_WIDTH-1:0],       rank_dq[rank_x][MC_DQ_WIDTH-1:0]); // Left side - Right side (MC - Mem)
	    short bidiDQS_t[MC_DQS_BITS-1:0] (dqs_t[MC_DQS_BITS-1:0],    rank_dqs_t[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
	    short bidiDQS_c[MC_DQS_BITS-1:0] (dqs_c[MC_DQS_BITS-1:0],    rank_dqs_c[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
	    short bidiDM_n[MC_DQS_BITS-1:0]  (dm_dbi_n[MC_DQS_BITS-1:0], rank_dm_dbi_n[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
        `else
	    tran bidiDQ[MC_DQ_WIDTH-1:0]    (dq[MC_DQ_WIDTH-1:0],       rank_dq[rank_x][MC_DQ_WIDTH-1:0]); // Left side - Right side (MC - Mem)
	    tran bidiDQS_t[MC_DQS_BITS-1:0] (dqs_t[MC_DQS_BITS-1:0],    rank_dqs_t[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
	    tran bidiDQS_c[MC_DQS_BITS-1:0] (dqs_c[MC_DQS_BITS-1:0],    rank_dqs_c[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
	    tran bidiDM_n[MC_DQS_BITS-1:0]  (dm_dbi_n[MC_DQS_BITS-1:0], rank_dm_dbi_n[rank_x][MC_DQS_BITS-1:0]); // Left side - Right side (MC - Mem)
        `endif

	    always@(*) rank_ck[rank_x*2+:2] <= ck[rank_x*2+:2];
	    always@(*) rank_reset_n[rank_x] <= reset_n;
	    always@(*) alert_n              <= rank_alert_n[rank_x];
	    
	    always@(*) rank_qa_act_n[rank_x] <= qa_act_n;
	    always@(*) rank_qa_addr[rank_x]  <= qa_addr;
	    always@(*) rank_qa_ba[rank_x]    <= qa_ba;
	    always@(*) rank_qa_bg[rank_x]    <= qa_bg;
	    always@(*) rank_qa_par[rank_x]   <= qa_par;
	    always@(*) rank_qa_cke[rank_x]   <= mapped_qa_cke[rank_x];
	    always@(*) rank_qa_odt[rank_x]   <= mapped_qa_odt[rank_x];
   `ifdef THREE_DS 
	    always@(*) rank_qa_c[rank_x]     <= qa_c;
   `endif
	    always@(*) rank_qa_cs_n[rank_x]  <= qa_cs_n[rank_x];
	    
	    always@(*) rank_qb_act_n[rank_x] <= qb_act_n;
	    always@(*) rank_qb_addr[rank_x]  <= qb_addr;
	    always@(*) rank_qb_ba[rank_x]    <= qb_ba;
	    always@(*) rank_qb_bg[rank_x]    <= qb_bg;
	    always@(*) rank_qb_par[rank_x]   <= qb_par;
	    always@(*) rank_qb_cke[rank_x]   <= mapped_qb_cke[rank_x];
	    always@(*) rank_qb_odt[rank_x]   <= mapped_qb_odt[rank_x];
   `ifdef THREE_DS 
	    always@(*) rank_qb_c[rank_x]     <= qb_c;
   `endif
	    always@(*) rank_qb_cs_n[rank_x]  <= qb_cs_n[rank_x];
	    
	    always@(*) odd_rank_qa_addr[rank_x] <= swapped_qa_addr;
	    always@(*) odd_rank_qa_ba[rank_x]   <= swapped_qa_ba;
	    always@(*) odd_rank_qa_bg[rank_x]   <= swapped_qa_bg;
	    
	    always@(*) odd_rank_qb_addr[rank_x] <= swapped_qb_addr;
	    always@(*) odd_rank_qb_ba[rank_x]   <= swapped_qb_ba;
	    always@(*) odd_rank_qb_bg[rank_x]   <= swapped_qb_bg;

	  end // block: without_r2r_delays
	//************************* End of WITH/WITHOUT R2R delays ***********************//

	// Rank instances 
	if( (MC_CA_MIRROR=="ON") && (rank_x%2==1) ) // MC_CA_MIRROR is enabled and the current rank is ODD
	  begin: mc_ca_mirroring_odd_rank
	    // Integration of ddr4_rank.v
	    // ODD Rank instance - in that case to the Rank  are connected odd_rank_* signals
	    ddr4_rank #(
			.MC_DQ_WIDTH (MC_DQ_WIDTH),
			.MC_DQS_BITS (MC_DQS_BITS),
			.MC_DM_WIDTH (MC_DM_WIDTH),
			.MC_ABITS (MC_ABITS),
			.MC_BANK_WIDTH (MC_BANK_WIDTH),
			.MC_BANK_GROUP (MC_BANK_GROUP),
   `ifdef THREE_DS 
			.MC_LR_WIDTH (MC_LR_WIDTH),
   `endif
			.NUM_PHYSICAL_PARTS (NUM_PHYSICAL_PARTS),
			.CALIB_EN (CALIB_EN),
			.TOTAL_FBT_DELAY (TOTAL_FBT_DELAY),
			.MEM_PART_WIDTH (MEM_PART_WIDTH),
		//	.SDRAM (SDRAM),
			.DDR_SIM_MODEL(DDR_SIM_MODEL),
			.DM_DBI(DM_DBI),
      .CONFIGURED_DENSITY (CONFIGURED_DENSITY)
			)
	    u_ddr4_rank (
			 .qa_act_n (rank_qa_act_n[rank_x]), // input
			 .qa_addr (odd_rank_qa_addr[rank_x][MC_ABITS-1:0]), // input [MC_ABITS-1:0]
			 .qa_ba (odd_rank_qa_ba[rank_x][MC_BANK_WIDTH-1:0]), // input [MC_BANK_WIDTH-1:0]
			 .qa_bg (odd_rank_qa_bg[rank_x][MC_BANK_GROUP-1:0]), // input [MC_BANK_GROUP-1:0]
			 .qa_par (rank_qa_par[rank_x]), // input
			 .qa_cke (rank_qa_cke[rank_x]), // input
			 .qa_odt (rank_qa_odt[rank_x]), // input
   `ifdef THREE_DS 
			 .qa_c (rank_qa_c[rank_x]), // input
   `endif
			 .qa_cs_n (rank_qa_cs_n[rank_x]), // input
	      
			 .qb_act_n (rank_qb_act_n[rank_x]), // input
			 .qb_addr (odd_rank_qb_addr[rank_x][MC_ABITS-1:0]), // input [MC_ABITS-1:0]
			 .qb_ba (odd_rank_qb_ba[rank_x][MC_BANK_WIDTH-1:0]), // input [MC_BANK_WIDTH-1:0]
			 .qb_bg (odd_rank_qb_bg[rank_x][MC_BANK_GROUP-1:0]), // input [MC_BANK_GROUP-1:0]
			 .qb_par (rank_qb_par[rank_x]), // input
			 .qb_cke (rank_qb_cke[rank_x]), // input
			 .qb_odt (rank_qb_odt[rank_x]), // input
   `ifdef THREE_DS 
			 .qb_c (rank_qb_c[rank_x]), // input
   `endif
			 .qb_cs_n (rank_qb_cs_n[rank_x]), // input
	      
			 .ck (rank_ck[rank_x*2+:2]), // input (ck[0]->ck_c, ck[1]->ck_t)
			 .reset_n (rank_reset_n[rank_x]), //input
	      
			 .dm_dbi_n (rank_dm_dbi_n[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]
			 .dq (rank_dq[rank_x][MC_DQ_WIDTH-1:0]), // inout [MC_DQ_WIDTH-1:0]
			 .dqs_t (rank_dqs_t[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]
			 .dqs_c (rank_dqs_c[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]

			 .alert_n (rank_alert_n[rank_x]) // output
			 );
	  end // block: mc_ca_mirroring_odd_rank
	else // !if( (MC_CA_MIRROR=="ON") && (rank_x%2==1) )
	  begin: even_ranks // for even ranks MC_CA_MIRROR does not take effect
	    // Integration of ddr4_rank.v
	    ddr4_rank #(
			.MC_DQ_WIDTH (MC_DQ_WIDTH),
			.MC_DQS_BITS (MC_DQS_BITS),
			.MC_DM_WIDTH (MC_DM_WIDTH),
			.MC_ABITS (MC_ABITS),
			.MC_BANK_WIDTH (MC_BANK_WIDTH),
			.MC_BANK_GROUP (MC_BANK_GROUP),
   `ifdef THREE_DS 
			.MC_LR_WIDTH (MC_LR_WIDTH),
   `endif
			.NUM_PHYSICAL_PARTS (NUM_PHYSICAL_PARTS),
			.CALIB_EN (CALIB_EN),
			.TOTAL_FBT_DELAY (TOTAL_FBT_DELAY),
			.MEM_PART_WIDTH (MEM_PART_WIDTH),
		//	.SDRAM (SDRAM),
			.DDR_SIM_MODEL(DDR_SIM_MODEL),
			.DM_DBI(DM_DBI),
      .CONFIGURED_DENSITY (CONFIGURED_DENSITY)
			)
	    u_ddr4_rank (
			 .qa_act_n (rank_qa_act_n[rank_x]), // input
			 .qa_addr (rank_qa_addr[rank_x][MC_ABITS-1:0]), // input [MC_ABITS-1:0]
			 .qa_ba (rank_qa_ba[rank_x][MC_BANK_WIDTH-1:0]), // input [MC_BANK_WIDTH-1:0]
			 .qa_bg (rank_qa_bg[rank_x][MC_BANK_GROUP-1:0]), // input [MC_BANK_GROUP-1:0]
			 .qa_par (rank_qa_par[rank_x]), // input
			 .qa_cke (rank_qa_cke[rank_x]), // input
			 .qa_odt (rank_qa_odt[rank_x]), // input
   `ifdef THREE_DS 
			 .qa_c (rank_qa_c[rank_x]), // input
   `endif
			 .qa_cs_n (rank_qa_cs_n[rank_x]), // input
	      
			 .qb_act_n (rank_qb_act_n[rank_x]), // input
			 .qb_addr (rank_qb_addr[rank_x][MC_ABITS-1:0]), // input [MC_ABITS-1:0]
			 .qb_ba (rank_qb_ba[rank_x][MC_BANK_WIDTH-1:0]), // input [MC_BANK_WIDTH-1:0]
			 .qb_bg (rank_qb_bg[rank_x][MC_BANK_GROUP-1:0]), // input [MC_BANK_GROUP-1:0]
			 .qb_par (rank_qb_par[rank_x]), // input
			 .qb_cke (rank_qb_cke[rank_x]), // input
			 .qb_odt (rank_qb_odt[rank_x]), // input
   `ifdef THREE_DS 
			 .qb_c (rank_qb_c[rank_x]), // input
   `endif
			 .qb_cs_n (rank_qb_cs_n[rank_x]), // input
	      
			 .ck (rank_ck[rank_x*2+:2]), // input (ck[0]->ck_c, ck[1]->ck_t)
			 .reset_n (rank_reset_n[rank_x]), //input
	      
			 .dm_dbi_n (rank_dm_dbi_n[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]
			 .dq (rank_dq[rank_x][MC_DQ_WIDTH-1:0]), // inout [MC_DQ_WIDTH-1:0]
			 .dqs_t (rank_dqs_t[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]
			 .dqs_c (rank_dqs_c[rank_x][MC_DQS_BITS-1:0]), // inout [MC_DQS_BITS-1:0]

			 .alert_n (rank_alert_n[rank_x]) // output
			 );
	  end // block: even_ranks
      end // block: rank_instances
  endgenerate

  
endmodule // ddr4_dimm
