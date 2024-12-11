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
module ddr4_rank #(
		   parameter MC_DQ_WIDTH = 16, // Memory DQ bus width
		   parameter MC_DQS_BITS = 4, // Number of DQS bits
		   parameter MC_DM_WIDTH = 4, // Number of DM bits
		   parameter MC_ABITS = 18, // Number of Address bits
		   parameter MC_BANK_WIDTH = 2, // Memory Bank address bits
		   parameter MC_BANK_GROUP = 2, // Memory Bank Groups
           `ifdef THREE_DS 
		   parameter MC_LR_WIDTH = 1, 
           `endif
		   parameter NUM_PHYSICAL_PARTS = 4, // Number of SDRAMs in a Single Rank
		   parameter CALIB_EN = "NO", // When is set to "YES" ,R2R and FBT delays will be added 
		   parameter TOTAL_FBT_DELAY = 2700, // Total Fly-by-Topology delay		   
		   parameter MEM_PART_WIDTH = "x4", // Single Device width
		   // Shows which SDRAMs are connected to side A(first half) and side B(second half) of RCD.
		   parameter DDR_SIM_MODEL = "MICRON", // "MICRON" or "DENALI" memory model
		   parameter DM_DBI = "", // Disables dm_dbi_n if set to NONE
       parameter UTYPE_density CONFIGURED_DENSITY = _4G
		   )
  (
   // side A of the RCD
   input 		     qa_act_n,
   input [MC_ABITS-1:0]      qa_addr,
   input [MC_BANK_WIDTH-1:0] qa_ba,
   input [MC_BANK_GROUP-1:0] qa_bg,
   `ifdef THREE_DS 
   input [MC_LR_WIDTH-1:0]   qa_c,
   `endif
   input 		     qa_par,
   input 		     qa_cke,
   input 		     qa_odt,
   input 		     qa_cs_n,
   // side B of the RCD
   input 		     qb_act_n,
   input [MC_ABITS-1:0]      qb_addr,
   input [MC_BANK_WIDTH-1:0] qb_ba,
   input [MC_BANK_GROUP-1:0] qb_bg,
   `ifdef THREE_DS 
   input [MC_LR_WIDTH-1:0]   qb_c,
   `endif
   input 		     qb_par,
   input 		     qb_cke,
   input 		     qb_odt,
   input 		     qb_cs_n,
  
   input [1:0] 		     ck, // ck[0]->ck_c, ck[1]->ck_t
   input 		     reset_n,

   inout [MC_DM_WIDTH-1:0]   dm_dbi_n,
   inout [MC_DQ_WIDTH-1:0]   dq,
   inout [MC_DQS_BITS-1:0]   dqs_t,
   inout [MC_DQS_BITS-1:0]   dqs_c,

   output reg 		     alert_n		  
   );

  genvar 		     device_x; // used in for loop in generate block (shows number of current device)
  genvar 		     device_y; // used in for loop in generate block (shows number of current device)

  
  // Local parameters
  localparam DRAM_WIDTH = (MEM_PART_WIDTH=="x4") ? 4 : 
                          (MEM_PART_WIDTH=="x8") ? 8 : 
			              16;
  localparam SDRAM_ADDR_BITS = 18 - MC_ABITS; // Redundants Address bits to SDRAM devices
  localparam DQ_PER_DEVICE = (MEM_PART_WIDTH=="x4") ? 4 : // DQ per Device is 4-bits
                             (MEM_PART_WIDTH=="x8") ? 8 : // DQ per Device is 8-bits
			     16; // DQ per Device is 16-bits
  localparam DM_PER_DEVICE  = (MEM_PART_WIDTH=="x16") ? 2 : 1; // DM per Device ==2 only for x16 Devices
  localparam DQS_PER_DEVICE = (MEM_PART_WIDTH=="x16") ? 2 : 1; // DQS per Device ==2 only for x16 Devices

  localparam MAX_NUM_COMPONENTS = (MEM_PART_WIDTH == "x4") ? 18 : // Max number of components for single Rank
                                  (MEM_PART_WIDTH == "x8") ? 9  :
				  5; // If MEM_PART_WIDTH == "x16"
  localparam RANK_FBT_DELAY = (TOTAL_FBT_DELAY*NUM_PHYSICAL_PARTS)/MAX_NUM_COMPONENTS; // FBT delay for a single Rank
  //localparam components_side_e [NUM_PHYSICAL_PARTS-1:0] SDRAM = { {(NUM_PHYSICAL_PARTS/2){SIDE_B}}, {(NUM_PHYSICAL_PARTS/2){SIDE_A}} }; // SDRAM
  localparam [NUM_PHYSICAL_PARTS-1:0] SDRAM = { {(NUM_PHYSICAL_PARTS/2){1'b1}}, {(NUM_PHYSICAL_PARTS/2){1'b0}} }; // SDRAM
  
  // sdram ddr4_model have static ports for address bits 0-17.
  // In case that the incoming from MC address signals have less than 18 bits, to upper bits will be added static 1'b1.
  wire [17:0] 		     ddr4_model_qa_addr;
  wire [17:0] 		     ddr4_model_qb_addr;
  
  wire 			     dm_pull_up; // used when DM_DBI="NONE". In that case to dm_dbi_n pin will be connected 1'b1.

  int 			     fbt_delay [NUM_PHYSICAL_PARTS]; // each word store the delay for a single device
    
  assign dm_pull_up = 1'b1; // used for dm_dbi_n pin of SDRAM when DM_DBI="NONE"

  // Add Redundants Address bits to SDRAM devices
  generate
    if(SDRAM_ADDR_BITS>0) // address signal is less than 18 bits
      begin: qx_addr_less_than_18_bits
	assign ddr4_model_qa_addr = {{SDRAM_ADDR_BITS{1'b1}}, qa_addr};
	assign ddr4_model_qb_addr = {{SDRAM_ADDR_BITS{1'b1}}, qb_addr};
      end
    else // qx_addr=18 bits
      begin: qx_addr_qual_to_18_bits
	assign ddr4_model_qa_addr = qa_addr;
	assign ddr4_model_qb_addr = qb_addr;
      end
  endgenerate 

  // Create the handle for the DIMM FBT delay generation constraint class
 // generate
 //   if(CALIB_EN=="YES")
 //     begin: create_fbt_delays

 //   // Create the handle DDR4_FBT_DELAYS
 //   rdimm_fbt_delays #(.TOTAL_DIMM_DLY(RANK_FBT_DELAY), .NO_OF_COMP (NUM_PHYSICAL_PARTS), .ENABLE(1) ) DDR4_FBT_DELAYS; //ENABLE FTB delay

 //   initial
 //     begin: initial_block_fbt_delays    
 //       DDR4_FBT_DELAYS = new();
 //       DDR4_FBT_DELAYS.reset_value();

 //       assert(DDR4_FBT_DELAYS.randomize()) // Randomize FBT delays for all SDRAM components		
 //   	  else
 //   	    `uvm_error("ddr4_rank.sv", "Randomization of DDR4_FBT_DELAYS FAILED")

 //       foreach(fbt_delay[i]) 
 //         fbt_delay[i] = DDR4_FBT_DELAYS.delay[i]; // Store the FBT delays for each components

 //     end // block: initial_block_fbt_delays
 //   	
 //     end // block: create_fbt_delays 
 // endgenerate
  
  // Instance of SDRAM Devices (parameterized for x4, x8 and x16 Devices)
  generate
	if (DDR_SIM_MODEL == "MICRON") 
    begin: Micron_model
    for(device_x=0; device_x<NUM_PHYSICAL_PARTS; device_x=device_x+1)
      begin: instance_of_sdram_devices
	
	DDR4_if #(.CONFIGURED_DQ_BITS (DRAM_WIDTH)) iDDR4(); // create iDDR4 interface	

	// Current SDRAM component will be connected to side A of the RCD
	if(SDRAM[device_x]==1'b0) // connect SDRAM to side A of the RCD
	  begin: sdram_to_side_a

	    // Add FBT delays
	    if(CALIB_EN=="YES") // Calibration is enabled
	      begin: add_fbt_delays_side_a
		
		always@(*)
		  begin: always_block_fbt_delays_side_a
		    iDDR4.CK        <= #(fbt_delay[device_x]) ck; // CK[0]==CK_c CK[1]==CK_t
		    iDDR4.ACT_n     <= #(fbt_delay[device_x]) qa_act_n; // input
		    iDDR4.RAS_n_A16 <= #(fbt_delay[device_x]) ddr4_model_qa_addr[16]; // input
		    iDDR4.CAS_n_A15 <= #(fbt_delay[device_x]) ddr4_model_qa_addr[15]; // input
		    iDDR4.WE_n_A14  <= #(fbt_delay[device_x]) ddr4_model_qa_addr[14]; // input
		    alert_n         <= #(fbt_delay[device_x]) iDDR4.ALERT_n; // output
		    iDDR4.PARITY    <= #(fbt_delay[device_x]) qa_par; // input
		    iDDR4.RESET_n   <= #(fbt_delay[device_x]) reset_n; // input
		    iDDR4.TEN       <= #(fbt_delay[device_x]) 1'b0; // input
		    iDDR4.CS_n      <= #(fbt_delay[device_x]) qa_cs_n; // input
		    iDDR4.CKE       <= #(fbt_delay[device_x]) qa_cke; // input
		    iDDR4.ODT       <= #(fbt_delay[device_x]) qa_odt; // input
   `ifdef THREE_DS 
		    iDDR4.C         <= #(fbt_delay[device_x]) qa_c; // input [MAX_RANK_BITS-1:0]
    `else
		    iDDR4.C         <= #(fbt_delay[device_x]) 1'b0; // input [MAX_RANK_BITS-1:0]
   `endif
		    iDDR4.BG        <= #(fbt_delay[device_x]) qa_bg; // input [MAX_BANK_GROUP_BITS-1:0]
		    iDDR4.BA        <= #(fbt_delay[device_x]) qa_ba; // input [MAX_BANK_BITS-1:0]
		    iDDR4.ADDR      <= #(fbt_delay[device_x]) ddr4_model_qa_addr[13:0]; // input [13:0]
		    iDDR4.ADDR_17   <= #(fbt_delay[device_x]) ddr4_model_qa_addr[17]; // input
		  end // block: always_block_fbt_delays_side_a
	      end // block: add_fbt_delays_side_a
	    else // !if(CALIB_EN=="YES")
	      // Calibration is disabled
	      begin: without_fbt_delays_side_a
		always@(*)
		  begin: always_block_without_fbt_delays_side_a
      	    	    iDDR4.CK        <= ck; // CK[0]==CK_c CK[1]==CK_t
		    iDDR4.ACT_n     <= qa_act_n; // input
		    iDDR4.RAS_n_A16 <= ddr4_model_qa_addr[16]; // input
		    iDDR4.CAS_n_A15 <= ddr4_model_qa_addr[15]; // input
		    iDDR4.WE_n_A14  <= ddr4_model_qa_addr[14]; // input
		    alert_n         <= iDDR4.ALERT_n; // output
		    iDDR4.PARITY    <= qa_par; // input
		    iDDR4.RESET_n   <= reset_n; // input
		    iDDR4.TEN       <= 1'b0; // input
		    iDDR4.CS_n      <= qa_cs_n; // input
		    iDDR4.CKE       <= qa_cke; // input
		    iDDR4.ODT       <= qa_odt; // input
   `ifdef THREE_DS 
		    iDDR4.C         <= qa_c; // input [MAX_RANK_BITS-1:0]
    `else
		    iDDR4.C         <= 1'b0; // input [MAX_RANK_BITS-1:0]
   `endif
		    iDDR4.BG        <= qa_bg; // input [MAX_BANK_GROUP_BITS-1:0]
		    iDDR4.BA        <= qa_ba; // input [MAX_BANK_BITS-1:0]
		    iDDR4.ADDR      <= ddr4_model_qa_addr[13:0]; // input [13:0]
		    iDDR4.ADDR_17   <= ddr4_model_qa_addr[17]; // input
		  end // block: always_ddr4_model_block_without_fbt_delays_side_a
	      end // block: without_fbt_delays_side_a

	  end // block: sdram_to_side_a
	else // !if(SDRAM[device_x]==SIDE_A)
	  // Current SDRAM component will be connected to side B of the RCD
	  begin: sdram_to_side_b

	    // Add FBT delays
	    if(CALIB_EN=="YES") // Calibration is enabled
	      begin: add_fbt_delays_side_b

		always@(*)				       
	          begin: always_block_fbt_delays_side_b
		    iDDR4.CK        <= #(fbt_delay[device_x]) ck; // CK[0]==CK_c CK[1]==CK_t
		    iDDR4.ACT_n     <= #(fbt_delay[device_x]) qb_act_n; // input
		    iDDR4.RAS_n_A16 <= #(fbt_delay[device_x]) ddr4_model_qb_addr[16]; // input
		    iDDR4.CAS_n_A15 <= #(fbt_delay[device_x]) ddr4_model_qb_addr[15]; // input
		    iDDR4.WE_n_A14  <= #(fbt_delay[device_x]) ddr4_model_qb_addr[14]; // input
		    alert_n         <= #(fbt_delay[device_x]) iDDR4.ALERT_n; // output
		    iDDR4.PARITY    <= #(fbt_delay[device_x]) qb_par; // input
		    iDDR4.RESET_n   <= #(fbt_delay[device_x]) reset_n; // input
		    iDDR4.TEN       <= #(fbt_delay[device_x]) 1'b0; // input
		    iDDR4.CS_n      <= #(fbt_delay[device_x]) qb_cs_n; // input
		    iDDR4.CKE       <= #(fbt_delay[device_x]) qb_cke; // input
		    iDDR4.ODT       <= #(fbt_delay[device_x]) qb_odt; // input
   `ifdef THREE_DS 
		    iDDR4.C         <= #(fbt_delay[device_x]) qb_c; // input [MAX_RANK_BITS-1:0]
    `else
		    iDDR4.C         <= #(fbt_delay[device_x]) 1'b0; // input [MAX_RANK_BITS-1:0]
   `endif
		    iDDR4.BG        <= #(fbt_delay[device_x]) qb_bg; // input [MAX_BANK_GROUP_BITS-1:0]
		    iDDR4.BA        <= #(fbt_delay[device_x]) qb_ba; // input [MAX_BANK_BITS-1:0]
		    // The RCD output inversion to side B address signal invert qb_addr[13]=1'b1.
		    // This is issue because the address to SDRAM will be out of bounds (max range is addr[13:0]='h1FFF), to resolve this issue we set qb_addr[13] to 1'b0.
		    //iDDR4.ADDR      <= #(fbt_delay[device_x]) {1'b0, ddr4_model_qb_addr[12:0]}; // input [13:0]
        iDDR4.ADDR      <= #(fbt_delay[device_x]) ddr4_model_qb_addr[13:0]; // input [13:0]
		    iDDR4.ADDR_17   <= #(fbt_delay[device_x]) ddr4_model_qb_addr[17]; // input
		  end // block: always_block_fbt_delays_side_b
	      end // block: add_fbt_delays_side_b
	    else // !if(CALIB_EN=="YES")
	      // Calibration is disabled
	      begin: without_fbt_delays_side_b
		always@(*)
		  begin: always_block_without_fbt_delays_side_b
		    iDDR4.CK        <= ck; // CK[0]==CK_c CK[1]==CK_t
		    iDDR4.ACT_n     <= qb_act_n; // input
		    iDDR4.RAS_n_A16 <= ddr4_model_qb_addr[16]; // input
		    iDDR4.CAS_n_A15 <= ddr4_model_qb_addr[15]; // input
		    iDDR4.WE_n_A14  <= ddr4_model_qb_addr[14]; // input
		    alert_n         <= iDDR4.ALERT_n; // output
		    iDDR4.PARITY    <= qb_par; // input
		    iDDR4.RESET_n   <= reset_n; // input
		    iDDR4.TEN       <= 1'b0; // input
		    iDDR4.CS_n      <= qb_cs_n; // input
		    iDDR4.CKE       <= qb_cke; // input
		    iDDR4.ODT       <= qb_odt; // input
   `ifdef THREE_DS 
		    iDDR4.C         <= qb_c; // input [MAX_RANK_BITS-1:0]
    `else
		    iDDR4.C         <= 1'b0; // input [MAX_RANK_BITS-1:0]
   `endif
		    iDDR4.BG        <= qb_bg; // input [MAX_BANK_GROUP_BITS-1:0]
		    iDDR4.BA        <= qb_ba; // input [MAX_BANK_BITS-1:0]
		    // The RCD output inversion to side B address signal invert qb_addr[13]=1'b1.
		    // This is issue because the address to SDRAM will be out of bounds (max range is addr[13:0]='h1FFF), to resolve this issue we set qb_addr[13] to 1'b0.
		    //iDDR4.ADDR      <= {1'b0, ddr4_model_qb_addr[12:0]}; // input [13:0]
        iDDR4.ADDR      <= ddr4_model_qb_addr[13:0]; // input [13:0]
		    iDDR4.ADDR_17   <= ddr4_model_qb_addr[17]; // input
		  end // block: always_block_without_fbt_delays_side_b		
	      end // block: without_fbt_delays_side_b
	    	    	    
	  end // block: sdram_to_side_b

	// Data bus signals are the same for side A and side B
	// Connecting of bi-directional data signals - dm, dq, dqs_t and dqs_c
	if (DM_DBI == "NONE")
	  begin: no_dm_dbi_n_side_b
	    assign dm_dbi_n[DM_PER_DEVICE*device_x+:DM_PER_DEVICE] = {(DM_PER_DEVICE){dm_pull_up}};
	    assign iDDR4.DM_n = {(DM_PER_DEVICE){dm_pull_up}};
	  end
	else
	  begin: enable_dm_dbi_n_side_b
      `ifdef XILINX_SIMULATOR
	    short bidiDM_n[DM_PER_DEVICE-1:0] (dm_dbi_n[DM_PER_DEVICE*device_x+:DM_PER_DEVICE], iDDR4.DM_n[DM_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DM_BITS-1:0]	
	  `else
        tran bidiDM_n[DM_PER_DEVICE-1:0] (dm_dbi_n[DM_PER_DEVICE*device_x+:DM_PER_DEVICE], iDDR4.DM_n[DM_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DM_BITS-1:0]	
	  `endif
      end
	      
    `ifdef XILINX_SIMULATOR
	short  bidiDQ[DQ_PER_DEVICE-1:0] (dq[DQ_PER_DEVICE*device_x+:DQ_PER_DEVICE], iDDR4.DQ[DQ_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQ_BITS-1:0]
	short  bidiDQS_t[DQS_PER_DEVICE-1:0] (dqs_t[DQS_PER_DEVICE*device_x+:DQS_PER_DEVICE], iDDR4.DQS_t[DQS_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQS_BITS-1:0]
	short  bidiDQS_c[DQS_PER_DEVICE-1:0] (dqs_c[DQS_PER_DEVICE*device_x+:DQS_PER_DEVICE], iDDR4.DQS_c[DQS_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQS_BITS-1:0]
	`else
    tran bidiDQ[DQ_PER_DEVICE-1:0] (dq[DQ_PER_DEVICE*device_x+:DQ_PER_DEVICE], iDDR4.DQ[DQ_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQ_BITS-1:0]
	tran bidiDQS_t[DQS_PER_DEVICE-1:0] (dqs_t[DQS_PER_DEVICE*device_x+:DQS_PER_DEVICE], iDDR4.DQS_t[DQS_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQS_BITS-1:0]
	tran bidiDQS_c[DQS_PER_DEVICE-1:0] (dqs_c[DQS_PER_DEVICE*device_x+:DQS_PER_DEVICE], iDDR4.DQS_c[DQS_PER_DEVICE-1:0]); // inout [MC_CONFIGURED_DQS_BITS-1:0]
	`endif
	
	assign iDDR4.ZQ = 1'b1; // input
	assign iDDR4.PWR = 1'b1; // input
	assign iDDR4.VREF_CA = 1'b1; // input
	assign iDDR4.VREF_DQ = 1'b1; // input 
	
	// Instance of MICRON ddr4_model
	if (DDR_SIM_MODEL == "MICRON") // instance of ddr4_model provided from MICRON
	  begin: micron_mem_model
        ddr4_model  #
          (
   `ifdef THREE_DS 
           .CONFIGURED_RANKS (4),
   `endif
           .CONFIGURED_DQ_BITS (DRAM_WIDTH),
           .CONFIGURED_DENSITY (CONFIGURED_DENSITY)
           ) u_ddr4_model(
				     .model_enable (), // inout
				     .iDDR4 (iDDR4)
				     );
	  end
	else if (DDR_SIM_MODEL == "DENALI") // instance of ddr4_model provided from Denali
	      begin: denali_mem_model
	    	// Instance of DENALI ddr4_model
		ddr4_model u_ddr4_model (
				  	 .model_enable (), // inout
				  	 .iDDR4 (iDDR4)
				  	 );
	      end
  	      end // block: sdram_to_side_b
      end // block: instance_of_sdram_devices
    else if (DDR_SIM_MODEL == "SAMSUNG") begin: SAMSUNG_MODEL_1
      for(device_y=0; device_y<NUM_PHYSICAL_PARTS; device_y=device_y+1)
      begin: instance_of_sdram_devices
      `ifdef THREE_DS
	     if (MC_LR_WIDTH== 1) begin // 3DS 2H parts 
	       // Current SDRAM component will be connected to side A of the RCD
	       if(SDRAM[device_y]==1'b0) // connect SDRAM to side A of the RCD
	       begin: sdram_to_side_a
              h2_b_model u_ddr4_model
              (
                 .CLK  (ck[1])
                ,.CLKB (ck[0])
                ,.CSB     (qa_cs_n)
                ,.ACTB    (qa_act_n)
                ,.RASB    (ddr4_model_qa_addr[16])
                ,.CASB    (ddr4_model_qa_addr[15])
                ,.WEB     (ddr4_model_qa_addr[14])
                ,.BA      (qa_ba)
                ,.BG      (qa_bg)
                ,.ADDR    (ddr4_model_qa_addr[13:0])
                ,.CKE     (qa_cke)
                ,.ODT     (qa_odt)
                ,.RESETB  (reset_n)
                ,.PAR_ERR  (qa_par)
                ,.TEN     (1'b0)
                ,.DQ_B     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
                ,.DQS_B    (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
                ,.DQSB_B   (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
                ,.DMB_B    (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
                ,.ALERTB  () 
	            ,.CID     ({1'b0,qa_c})   
                );
	         end // block: sdram_to_side_a
           else begin: sdram_to_side_b
             h2_b_model  u_ddr4_model
             (
                .CLK  (ck[1])
               ,.CLKB (ck[0])
               ,.CSB     (qb_cs_n)
               ,.ACTB    (qb_act_n)
               ,.RASB    (ddr4_model_qb_addr[16])
               ,.CASB    (ddr4_model_qb_addr[15])
               ,.WEB     (ddr4_model_qb_addr[14])
               ,.BA      (qb_ba)
               ,.BG      (qb_bg)
               ,.ADDR   (ddr4_model_qb_addr[13:0])
               ,.CKE     (qb_cke)
               ,.ODT     (qb_odt)
               ,.RESETB (reset_n)
               ,.PAR_ERR  (qb_par)
               ,.TEN      (1'b0)
               ,.DQ_B     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
               ,.DQS_B     (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
               ,.DQSB_B    (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
               ,.DMB_B    (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
               ,.ALERTB  () 
	           ,.CID     ({1'b0,qb_c})
             );
            end
         end else begin // 3DS 4H parts
	       // Current SDRAM component will be connected to side A of the RCD
	       if(SDRAM[device_y]==1'b0) // connect SDRAM to side A of the RCD
	       begin: sdram_to_side_a_4h
              h4_b_model u_ddr4_model
              (
                 .CLK  (ck[1])
                ,.CLKB (ck[0])
                ,.CSB     (qa_cs_n)
                ,.ACTB    (qa_act_n)
                ,.RASB    (ddr4_model_qa_addr[16])
                ,.CASB    (ddr4_model_qa_addr[15])
                ,.WEB     (ddr4_model_qa_addr[14])
                ,.BA      (qa_ba)
                ,.BG      (qa_bg)
                ,.ADDR    (ddr4_model_qa_addr[13:0])
                ,.CKE     (qa_cke)
                ,.ODT     (qa_odt)
                ,.RESETB  (reset_n)
                ,.PAR_ERR  (qa_par)
                ,.TEN     (1'b0)
                ,.DQ_B     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
                ,.DQS_B    (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
                ,.DQSB_B   (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
                ,.DMB_B    (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
                ,.ALERTB  () 
	            ,.CID     (qa_c)   
                );
	         end // block: sdram_to_side_a_4h
           else begin: sdram_to_side_b_4h
             h4_b_model  u_ddr4_model
             (
                .CLK  (ck[1])
               ,.CLKB (ck[0])
               ,.CSB     (qb_cs_n)
               ,.ACTB    (qb_act_n)
               ,.RASB    (ddr4_model_qb_addr[16])
               ,.CASB    (ddr4_model_qb_addr[15])
               ,.WEB     (ddr4_model_qb_addr[14])
               ,.BA      (qb_ba)
               ,.BG      (qb_bg)
               ,.ADDR   (ddr4_model_qb_addr[13:0])
               ,.CKE     (qb_cke)
               ,.ODT     (qb_odt)
               ,.RESETB (reset_n)
               ,.PAR_ERR  (qb_par)
               ,.TEN      (1'b0)
               ,.DQ_B     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
               ,.DQS_B     (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
               ,.DQSB_B    (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
               ,.DMB_B    (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
               ,.ALERTB  () 
	           ,.CID     (qb_c)
             );
            end
          end

    `else
	      // Current SDRAM component will be connected to side A of the RCD
	      if(SDRAM[device_y]==1'b0) // connect SDRAM to side A of the RCD
	      begin: sdram_to_side_a
            DDRIV u_ddr4_model
            (
               .clk_in  (ck[1])
              ,.clkb_in (ck[0])
              ,.csb     (qa_cs_n)
              ,.actb    (qa_act_n)
              ,.rasb    (ddr4_model_qa_addr[16])
              ,.casb    (ddr4_model_qa_addr[15])
              ,.web     (ddr4_model_qa_addr[14])
              ,.ba      (qa_ba)
              ,.bg      (qa_bg)
              ,.ad_in   (ddr4_model_qa_addr[13:0])
              ,.cke     (qa_cke)
              ,.odt     (qa_odt)
              ,.resetb  (reset_n)
              ,.parity  (qa_par)
              ,.cid     (2'b0)
              ,.ten     (1'b0)

              ,.dqi     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
              ,.dqs     (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
              ,.dqsb    (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
              ,.dmb     (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
              
              ,.alertb  ()
            );
	      end // block: sdram_to_side_a
        else begin: sdram_to_side_b
          DDRIV u_ddr4_model
          (
             .clk_in  (ck[1])
            ,.clkb_in (ck[0])
            ,.csb     (qb_cs_n)
            ,.actb    (qb_act_n)
            ,.rasb    (ddr4_model_qb_addr[16])
            ,.casb    (ddr4_model_qb_addr[15])
            ,.web     (ddr4_model_qb_addr[14])
            ,.ba      (qb_ba)
            ,.bg      (qb_bg)
            ,.ad_in   (ddr4_model_qb_addr[13:0])
            ,.cke     (qb_cke)
            ,.odt     (qb_odt)
            ,.resetb  (reset_n)
            ,.parity  (qb_par)
            ,.cid     (2'b0)
            ,.ten     (1'b0)

            ,.dqi     (dq[DQ_PER_DEVICE*device_y+:DQ_PER_DEVICE])
            ,.dqs     (dqs_t[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
            ,.dqsb    (dqs_c[DQS_PER_DEVICE*device_y+:DQS_PER_DEVICE])
            ,.dmb     (dm_dbi_n[DM_PER_DEVICE*device_y+:DM_PER_DEVICE])
            
            ,.alertb  ()
          );
       end
    `endif
     end
     end

  endgenerate

endmodule // ddr4_rank
