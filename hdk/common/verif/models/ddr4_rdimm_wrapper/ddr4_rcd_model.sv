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
module ddr4_rcd_model #(
			parameter tCK = 1000, // CK clock period in ps
			parameter tPDM = 0, // Propagation delay Timing - range= from 1000 to 1300 ps.
			parameter MC_CA_MIRROR = "OFF" // Address Mirroring "ON"/"OFF"
			)
  (
   output 	     BCKE, BCK_c, BCK_t, BODT, BVREFCA, CPCAP, NU3, QAC2, QBC2, QVREFCA,		     
		     
   output reg 	     Y0_c, Y0_t, Y1_c, Y1_t, Y2_c, Y2_t, Y3_c, Y3_t, QRST_n,
   
   inout 	     ALERT_n, ERROR_IN_n, NU1, RFU1, SDA,

   input 	     AVDD, AVSS, BFUNC, CK_c, CK_t, DACT_n, DC0, DC1, DC2, DCS0_n,
		     DCS1_n, DPAR, DRST_n, NU0, NU2, PVDD, PVSS, RFU0, RFU2, RFU3, SA0,
		     SA1, SA2, SCL, VDD, VDD1, VDDSPD, VREFCA, VSS, VSS1, ZQCAL,

   output reg [17:0] QAA,
   output reg 	     QAACT_n,
   output reg [1:0]  QABA,
   output reg [1:0]  QABG,
   output reg 	     QAC0,
   output reg 	     QAC1,
   output reg [1:0]  QACKE,
   output reg 	     QACS0_n,
   output reg 	     QACS1_n,
   output reg [1:0]  QAODT,
   output reg 	     QAPAR,

   output reg [17:0] QBA,
   output reg 	     QBACT_n,
   output reg [1:0]  QBBA,
   output reg [1:0]  QBBG,
   output reg 	     QBC0,
   output reg 	     QBC1,
   output reg [1:0]  QBCKE,
   output reg 	     QBCS0_n, 
   output reg 	     QBCS1_n, 
   output reg [1:0]  QBODT,
   output reg 	     QBPAR,
   
   output [3:0]      BCOM,

   input [1:0] 	     DODT,
   input [1:0] 	     DBA,
   input [17:0]      DA,
   input [1:0] 	     DBG,
   input [1:0] 	     DCKE
   );
  
  // Inputs with one cycle delay
  reg [17:0] 	 DA_z1;
  reg 		 DACT_n_z1;
  reg [1:0] 	 DBA_z1;
  reg [1:0] 	 DBG_z1;
  reg 		 DCS0_n_z1;
  reg 		 DCS1_n_z1;  
  reg 		 DC0_z1;
  reg 		 DC1_z1;
  reg [1:0] 	 DCKE_z1;
  reg [1:0] 	 DODT_z1;
  reg 		 DPAR_z1;
  
  wire 		 mrs_to_side_a; // Asserted when MRS command to side A is detected
  wire 		 mrs_to_side_b; // Asserted when MRS command to side B is detected
  wire 		 odd_rank_mrs_side_a; // Used for odd ranks when CA Mirroring is enabled - Asserted when MRS command to side A is detected
  wire 		 odd_rank_mrs_side_b; // Used for odd ranks when CA Mirroring is enabled - Asserted when MRS command to side B is detected

  // Decoding of CS signals for MRS commands
  wire 		 qa_cs0_n;
  wire 		 qa_cs1_n;
  wire 		 qa_c0;
  wire 		 qa_c1;
  wire 		 qb_cs0_n;
  wire 		 qb_cs1_n;
  wire 		 qb_c0;
  wire 		 qb_c1;
   
  // One cycle delay of Input signals
  always@(*)
    begin: input_signals_clock_delay
      DA_z1     <= #tCK DA;
      DACT_n_z1 <= #tCK DACT_n;
      DBA_z1    <= #tCK DBA;
      DBG_z1    <= #tCK DBG;
      DC0_z1    <= #tCK DC0;
      DC1_z1    <= #tCK DC1;
      DCKE_z1   <= #tCK DCKE;
      DCS0_n_z1 <= #tCK DCS0_n;
      DCS1_n_z1 <= #tCK DCS1_n;
      DODT_z1   <= #tCK DODT;
      DPAR_z1   <= #tCK DPAR;
    end // block: input_signals_clock_delay
  
  // Clock and reset signals
  always@(*)
    begin: clock_reset_signals
      Y0_c <= #tPDM CK_c;
      Y0_t <= #tPDM CK_t;
      Y1_c <= #tPDM CK_c;
      Y1_t <= #tPDM CK_t;
      Y2_c <= #tPDM CK_c;
      Y2_t <= #tPDM CK_t;
      Y3_c <= #tPDM CK_c;
      Y3_t <= #tPDM CK_t;
      QRST_n <= DRST_n;
    end // block: clock_reset_signals
  
  // Detection of MRS Commands
  // If DBG_z1[1]==1'b0 MRS is sent to Side A SDRAMs, else DBG_z1[1]==1'b1 MRS is sent to Side B SDRAMs.
  assign mrs_to_side_a = (DACT_n_z1==1'b1 && DA_z1[16:14]==3'b0 && DBG_z1[1]==1'b0) ? 1'b1 : 1'b0; // MRS Command is to SDRAMs connected to side A
  assign mrs_to_side_b = (DACT_n_z1==1'b1 && DA_z1[16:14]==3'b0 && DBG_z1[1]==1'b1) ? 1'b1 : 1'b0; // MRS Command is to SDRAMs connected to side B
  // When CA MIRRORING is enabled: DBG_z1[0]==1'b0 MRS is sent to Side A SDRAMs, else DBG_z1[0]==1'b1 MRS is sent to Side B SDRAMs. 
  assign odd_rank_mrs_side_a = (DACT_n_z1==1'b1 && DA_z1[16:14]==3'b0 && DBG_z1[0]==1'b0) ? 1'b1 : 1'b0; // ODD Rank - MRS Command is to SDRAMs connected to side A
  assign odd_rank_mrs_side_b = (DACT_n_z1==1'b1 && DA_z1[16:14]==3'b0 && DBG_z1[0]==1'b1) ? 1'b1 : 1'b0; // ODD Rank - MRS Command is to SDRAMs connected to side B 

  // Chip select decoding is necessary for MRS commands
  // CA Mirroring take effect only under ODD Ranks, respectively to ODD Chip select signals (Qx_CS1_n and Qx_C1)
  generate
    if(MC_CA_MIRROR == "ON")
      begin: ca_mirroring_enabled
	assign qa_cs0_n = (mrs_to_side_b && ~DCS0_n_z1) ? 1'b1 : DCS0_n_z1;       // Even Rank
	assign qa_cs1_n = (odd_rank_mrs_side_b && ~DCS1_n_z1) ? 1'b1 : DCS1_n_z1; // Odd Rank
	assign qa_c0    = (mrs_to_side_b && ~DC0_z1) ? 1'b1 : DC0_z1;             // Even Rank
	assign qa_c1    = (odd_rank_mrs_side_b && ~DC1_z1) ? 1'b1 : DC1_z1;       // Odd Rank
	
	assign qb_cs0_n = (mrs_to_side_a && ~DCS0_n_z1) ? 1'b1 : DCS0_n_z1;       // Even Rank	
	assign qb_cs1_n = (odd_rank_mrs_side_a && ~DCS1_n_z1) ? 1'b1 : DCS1_n_z1; // Odd Rank
	assign qb_c0    = (mrs_to_side_a && ~DC0_z1) ? 1'b1 : DC0_z1;             // Even Rank
	assign qb_c1    = (odd_rank_mrs_side_a && ~DC1_z1) ? 1'b1 : DC1_z1;       // Odd Rank
      end // block: ca_mirroring_enabled
    else
      begin: ca_mirroring_disabled
	assign qa_cs0_n = (mrs_to_side_b && ~DCS0_n_z1) ? 1'b1 : DCS0_n_z1;
	assign qa_cs1_n = (mrs_to_side_b && ~DCS1_n_z1) ? 1'b1 : DCS1_n_z1;
	assign qa_c0    = (mrs_to_side_b && ~DC0_z1) ? 1'b1 : DC0_z1;
	assign qa_c1    = (mrs_to_side_b && ~DC1_z1) ? 1'b1 : DC1_z1;
	
	assign qb_cs0_n = (mrs_to_side_a && ~DCS0_n_z1) ? 1'b1 : DCS0_n_z1;	
	assign qb_cs1_n = (mrs_to_side_a && ~DCS1_n_z1) ? 1'b1 : DCS1_n_z1;
	assign qb_c0    = (mrs_to_side_a && ~DC0_z1) ? 1'b1 : DC0_z1;
	assign qb_c1    = (mrs_to_side_a && ~DC1_z1) ? 1'b1 : DC1_z1;
      end // block: ca_mirroring_disabled
  endgenerate
  
  // Add tPDM time to Outputs Qx
  always@(*)
    begin: outputs_Qx
      // Outputs QA
      QAA     <= #tPDM DA_z1;
      QAACT_n <= #tPDM DACT_n_z1;
      QABA    <= #tPDM DBA_z1;
      QABG    <= #tPDM DBG_z1;
      QACKE   <= #tPDM DCKE_z1;
      QAODT   <= #tPDM DODT_z1;
      QAPAR   <= #tPDM DPAR_z1;
      QACS0_n <= #tPDM qa_cs0_n; // qa_cs_n [0]
      QACS1_n <= #tPDM qa_cs1_n; // qa_cs_n [1]
      QAC0    <= #tPDM qa_c0; // qa_cs_n [2]
      QAC1    <= #tPDM qa_c1; // qa_cs_n [3]	    
      // Outputs QB
      QBA     <= #tPDM {~DA_z1[17],    // Inverted
			 DA_z1[16:14], // Cannot be inverted - A16/RAS_n, A15/CAS_n, A14/WE_n
			~DA_z1[13],    // Inverted
			 DA_z1[12],    // A12 cannot be inverted as it is Burst Length
			~DA_z1[11],    // Inverted
			 DA_z1[10],    // A10 cannot be inverted as it is Auto Precharge
			~DA_z1[9:3],   // Inverted
			 DA_z1[2:0]};  // A0-A2 not inverted as they affects the burst start
      QBACT_n <= #tPDM DACT_n_z1;
      QBBA    <= #tPDM ~DBA_z1; // Inverted
      QBBG    <= #tPDM ~DBG_z1; // Inverted
      QBCKE   <= #tPDM DCKE_z1;
      QBODT   <= #tPDM DODT_z1;
      QBPAR   <= #tPDM DPAR_z1;
      QBCS0_n <= #tPDM qb_cs0_n; // qb_cs_n [0]
      QBCS1_n <= #tPDM qb_cs1_n; // qb_cs_n [1]
      QBC0    <= #tPDM qb_c0; // qb_cs_n [2]
      QBC1    <= #tPDM qb_c1; // qb_cs_n [3]
    end // block: outputs_Qx
	      		
endmodule
