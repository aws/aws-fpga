/******************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 1.1
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_v2_2_10_cal_debug_microblaze.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Thu Apr 18 2013
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_debug_microblaze module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ps / 1ps

module ddr4_v2_2_10_cal_debug_microblaze #
  (
   parameter CAL_STATUS_REG_SIZE = 7,
   parameter LRDIMM_CAL_SIZE     = 0,
   parameter RANKS_PER_SLOT      = 0,
   parameter RANK0_STATUS0_ADDR  = 0,
   parameter RANK1_STATUS0_ADDR  = 0,
   parameter RANK2_STATUS0_ADDR  = 0,
   parameter RANK3_STATUS0_ADDR  = 0,
   parameter ERROR0_ADDR         = 0,
   parameter ERROR1_ADDR         = 0,
   parameter ERROR_CODE_ADDR     = 0,
   parameter TCQ = 100
  )
  (
   input        clk,
   input        rst,
   input        IO_Addr_Strobe,
   input [27:0] IO_Address,
   input        IO_Write_Strobe,
   input [31:0] IO_Write_Data,
   
   input        cal_dbi_wr,
   input        cal_dbi_rd,
   
   input [8:0]  cal_pre_status,
   input [127:0] cal_r0_status,
   input [127:0] cal_r1_status,
   input [127:0] cal_r2_status,
   input [127:0] cal_r3_status,
   input [8:0]  cal_post_status,
   
   input        cal_error,
   input [7:0]  cal_error_bit,
   input [7:0]  cal_error_nibble,
   input [3:0]  cal_error_code,
   input        cal_warning,
   input [8:0]  cal_warning_nibble,
   input [8:0]  cal_warning_code
   );
   
   localparam CAL_DEBUG   = 28'h0800100;
   localparam DEBUG_RAM   = 28'h0900000;
   
   localparam CAL_DONE    = 28'h0800200;
   
   localparam DBG_DQS_GATE       = 0;
   localparam DBG_WRLVL          = 1;
   localparam DBG_RDLVL          = 2;
   localparam DBG_WRITE_DQS      = 3;
   localparam DBG_WRITE_CAL      = 4;
   localparam DBG_RDLVL_CMPLX    = 5;
   localparam DBG_READ_VREF      = 6;
   localparam DBG_WRITE_DQS_CMPLX= 7;
   localparam DBG_WRITE_VREF     = 8;
   localparam DBG_WRITE_READ     = 9;
   localparam DBG_MRANK_ADJUST   = 10;
   localparam DBG_DQS_TRACK      = 11;
   localparam DBG_SANITY_CHECK   = 12;
   localparam DBG_MARGIN         = 13;
   
   localparam INIT_CAL_RDY       = 0;
   localparam INIT_PHY_RDY       = 1;
   localparam INIT_PWR_UP_DONE   = 2;
   
   localparam DQS_GATE_FINE      = 0;
   localparam DQS_GATE_COARSE    = 1;
   localparam DQS_GATE_OFFSET    = 2;
   localparam DQS_GATE_GT_STAT   = 3;
   localparam DQS_GATE_RD_LAT    = 4;
   localparam DQS_GATE_RD_LAT_DLY= 5;
   localparam DQS_GATE_PAT_MATCH = 6;
   localparam DQS_GATE_PATTERN   = 7;
   localparam DQS_GATE_ERR_CHK   = 8;
   localparam DQS_GATE_FINE_L    = 9;
   localparam DQS_GATE_FINE_R    = 10;
   
   localparam WRLVL_COARSE        = 0;
   localparam WRLVL_SAMPLE        = 1;
   localparam WRLVL_ODELAY_OFFSET = 2;
   localparam WRLVL_COARSE_LEFT   = 3;
   localparam WRLVL_COARSE_RIGHT  = 4;
   localparam WRLVL_FINE          = 5;
   localparam WRLVL_FINE_LEFT     = 6;
   localparam WRLVL_FINE_RIGHT    = 7;
   localparam WRLVL_FINE_CENTER   = 8;
   localparam WRLVL_STEP_SIZE     = 9;
   localparam WRLVL_WARN          = 10;
   localparam WRLVL_ERR           = 11;

   localparam WL_ERR_STABLE_ZERO      = 0;
   localparam WL_ERR_STABLE_ONE       = 1;
   localparam WL_ERR_NO_LEFT_FINE     = 2;

   localparam WL_WARN_OFFSET_ZERO       = 0;
   localparam WL_WARN_STEP_SIZE_ZERO    = 1;
   localparam WL_WARN_NO_RIGHT_FINE     = 2;
   localparam WL_WARN_ODELAY_SATURATED  = 3;

   localparam RDLVL_BIT_VECTOR      = 0;
   localparam RDLVL_QTR             = 1;
   localparam RDLVL_IDELAY          = 2;
   localparam RDLVL_SAMPLES         = 3;
   localparam RDLVL_ERR_CHK         = 4;
   localparam RDLVL_LEFT            = 5;
   localparam RDLVL_RIGHT           = 6;
   localparam RDLVL_CENTER          = 7;
   localparam RDLVL_DESKEW_EDGE_ERR = 8;
   localparam RDLVL_CENTER_EDGE_ERR = 9;
   localparam RDLVL_NO_VALID_DATA   = 10;
   localparam RDLVL_TIMEOUT         = 11;
   localparam RDLVL_STATUS          = 12;
   
   localparam WRDQS_DQ_BIT_VECTOR   = 0;
   localparam WRDQS_DQ_TXPHASE      = 1;
   localparam WRDQS_DQ_ODELAY       = 2;
   localparam WRDQS_DQ_DLY0         = 3;
   localparam WRDQS_DQ_DLY1         = 4;
   localparam WRDQS_DQ_DESKEW       = 5;
   localparam WRDQS_DQ_STATUS       = 6;
   localparam WRDQS_DM_TXPHASE      = 7;
   localparam WRDQS_DM_ODELAY       = 8;
   localparam WRDQS_DM_DESKEW       = 9;
   localparam WRDQS_DM_LEFT         = 10;
   localparam WRDQS_DM_RIGHT        = 11;
   localparam WRDQS_DM_STATUS       = 12;
   localparam WRDQS_DQS_ODELAY      = 13;
   localparam WRDQS_WINDOW          = 14;
   
   localparam WRCAL_LATENCY         = 0;
   localparam WRCAL_COARSE          = 1;
   localparam WRCAL_ERR             = 2;
   
   localparam MULTIRANK_QTR         = 0;
   localparam MULTIRANK_IDELAY      = 1;
   localparam MULTIRANK_IDELAY_DBI  = 2;
   localparam MULTIRANK_GATE_COARSE = 3;
   localparam MULTIRANK_GATE_RD_LAT = 4;
   
   localparam TRACKING_SAMPLES      = 0;
   localparam TRACKING_GT_STATUS    = 1;
   localparam TRACKING_FINE         = 2;
   localparam TRACKING_COARSE       = 3;
   localparam TRACKING_DECISION_CNT = 4;
   localparam TRACKING_DECISION     = 5;
   localparam TRACKING_QTR          = 6;
   
   localparam VREF_BIT_VECTOR       = 0;
   localparam VREF_VALUE            = 1;
   localparam VREF_EYE_SIZE         = 2;
   
   localparam MARGIN_QTR            = 0;
   localparam MARGIN_LEFT           = 1;
   localparam MARGIN_RIGHT          = 2;
   localparam MARGIN_DQS            = 3;
   localparam MARGIN_DQ             = 4;
   
  reg [1:0] cal_dbi_wr_r;
  reg [1:0] cal_dbi_rd_r;

  //Simple Module to snoop the bus and display when it sees some kind of debug message
  reg         dbg_message_seen;
  reg         dbg_message_write;
  reg [3:0]   status_message_seen;
  reg [127:0]  status_reg;
  reg [127:0]  status_reg_rank0;
  reg [127:0]  status_reg_rank1;
  reg [127:0]  status_reg_rank2;
  reg [127:0]  status_reg_rank3;
  
  wire [3:0]  task_id;
  wire [3:0]  code;
  wire [11:0] payload;
  wire [1:0]  rank;
  wire [5:0]  nibble;
  wire [3:0]  bit_num;
  
  wire [4:0]  sanity_check_start_w;
  wire [4:0]  sanity_check_done_w;
  wire        sanity_check_start;
  wire        sanity_check_done;
  
  assign sanity_check_start_w[0] = status_reg_rank0[LRDIMM_CAL_SIZE + 26] | status_reg_rank1[LRDIMM_CAL_SIZE + 26] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 26] | status_reg_rank3[LRDIMM_CAL_SIZE + 26];
  assign sanity_check_start_w[1] = status_reg_rank0[LRDIMM_CAL_SIZE + 30] | status_reg_rank1[LRDIMM_CAL_SIZE + 30] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 30] | status_reg_rank3[LRDIMM_CAL_SIZE + 30];
  assign sanity_check_start_w[2] = status_reg_rank0[LRDIMM_CAL_SIZE + 34] | status_reg_rank1[LRDIMM_CAL_SIZE + 34] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 34] | status_reg_rank3[LRDIMM_CAL_SIZE + 34];
  assign sanity_check_start_w[3] = status_reg_rank0[LRDIMM_CAL_SIZE + 40] | status_reg_rank1[LRDIMM_CAL_SIZE + 40] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 40] | status_reg_rank3[LRDIMM_CAL_SIZE + 40];
  assign sanity_check_start_w[4] = status_reg_rank0[LRDIMM_CAL_SIZE + 44] | status_reg_rank1[LRDIMM_CAL_SIZE + 44] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 44] | status_reg_rank3[LRDIMM_CAL_SIZE + 44];
								   
  assign sanity_check_done_w[0]  = status_reg_rank0[LRDIMM_CAL_SIZE + 27] | status_reg_rank1[LRDIMM_CAL_SIZE + 27] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 27] | status_reg_rank3[LRDIMM_CAL_SIZE + 27];
  assign sanity_check_done_w[1]  = status_reg_rank0[LRDIMM_CAL_SIZE + 31] | status_reg_rank1[LRDIMM_CAL_SIZE + 31] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 31] | status_reg_rank3[LRDIMM_CAL_SIZE + 31];
  assign sanity_check_done_w[2]  = status_reg_rank0[LRDIMM_CAL_SIZE + 35] | status_reg_rank1[LRDIMM_CAL_SIZE + 35] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 35] | status_reg_rank3[LRDIMM_CAL_SIZE + 35];
  assign sanity_check_done_w[3]  = status_reg_rank0[LRDIMM_CAL_SIZE + 41] | status_reg_rank1[LRDIMM_CAL_SIZE + 41] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 41] | status_reg_rank3[LRDIMM_CAL_SIZE + 41];
  assign sanity_check_done_w[4]  = status_reg_rank0[LRDIMM_CAL_SIZE + 45] | status_reg_rank1[LRDIMM_CAL_SIZE + 45] | 
                                   status_reg_rank2[LRDIMM_CAL_SIZE + 45] | status_reg_rank3[LRDIMM_CAL_SIZE + 45];
								   
  assign sanity_check_start = |sanity_check_start_w;
  assign sanity_check_done = |sanity_check_done_w;

  always @ (posedge clk) begin
    if (rst)
	  dbg_message_write  <= #TCQ 1'b0;
	else if (IO_Addr_Strobe && IO_Address[27:16] == DEBUG_RAM[27:16] && IO_Write_Strobe)
	  dbg_message_write  <= #TCQ 1'b1;
	else
	  dbg_message_write  <= #TCQ 1'b0;
  end

  always @ (posedge clk) begin
    if (rst)
	  dbg_message_seen <= #TCQ 1'b0;
	else if (IO_Addr_Strobe && IO_Address == CAL_DEBUG)
	  dbg_message_seen <= #TCQ 1'b1;
	else
	  dbg_message_seen <= #TCQ 1'b0;
  end
  
  always @ (posedge clk) begin
    if (rst) begin
	  cal_dbi_wr_r <= #TCQ 2'b0;
	  cal_dbi_rd_r <= #TCQ 2'b0;
	end else begin
	  cal_dbi_wr_r[0] <= #TCQ cal_dbi_wr;
	  cal_dbi_wr_r[1] <= #TCQ cal_dbi_wr_r[0];
	  cal_dbi_rd_r[0] <= #TCQ cal_dbi_rd;
	  cal_dbi_rd_r[1] <= #TCQ cal_dbi_rd_r[0];
	end
  end
  
  //Status Messages
  always @ (posedge clk) begin
    if (rst)
	  status_message_seen <= #TCQ 'b0;
	else if (IO_Addr_Strobe && IO_Write_Strobe)
	  if (IO_Address[27:0] >= RANK0_STATUS0_ADDR && 
	      IO_Address[27:0] < (RANK0_STATUS0_ADDR + CAL_STATUS_REG_SIZE))
	    status_message_seen <= #TCQ 4'b0001;
	  else if (IO_Address[27:0] >= RANK1_STATUS0_ADDR && 
	           IO_Address[27:0] < (RANK1_STATUS0_ADDR + CAL_STATUS_REG_SIZE))
	    status_message_seen <= #TCQ 4'b0010;
	  else if (IO_Address[27:0] >= RANK2_STATUS0_ADDR && 
	           IO_Address[27:0] < (RANK2_STATUS0_ADDR + CAL_STATUS_REG_SIZE))
	    status_message_seen <= #TCQ 4'b0100;
	  else if (IO_Address[27:0] >= RANK3_STATUS0_ADDR && 
	           IO_Address[27:0] < (RANK3_STATUS0_ADDR + CAL_STATUS_REG_SIZE))
	    status_message_seen <= #TCQ 4'b1000;
	  else
	    status_message_seen <= #TCQ 'b0;
	else
	  status_message_seen <= #TCQ status_message_seen;
  end
  
  //One clock later since we have to let values propogate (update if more
  //pipeline required
  always @ (posedge clk) begin
    if (rst)
	  status_reg <= #TCQ 'b0;
	else if (status_message_seen[0])
	    status_reg <= #TCQ cal_r0_status;
	else if (status_message_seen[1])
	    status_reg <= #TCQ cal_r1_status;
	else if (status_message_seen[2])
	    status_reg <= #TCQ cal_r2_status;
	else if (status_message_seen[3])
	    status_reg <= #TCQ cal_r3_status;
	else
	  status_reg <= #TCQ status_reg;
  end
  
   always @ (posedge clk) begin
     if (rst)
	   status_reg_rank0 <= #TCQ 'b0;
	 else if (status_message_seen[0])
	   status_reg_rank0 <= #TCQ cal_r0_status;
	 else
	   status_reg_rank0 <= #TCQ status_reg_rank0;
   end
   
   always @ (posedge clk) begin
     if (rst)
	   status_reg_rank1 <= #TCQ 'b0;
	 else if (status_message_seen[1])
	   status_reg_rank1 <= #TCQ cal_r1_status;
	 else
	   status_reg_rank1 <= #TCQ status_reg_rank1;
   end
  
  always @ (posedge clk) begin
     if (rst)
	   status_reg_rank2 <= #TCQ 'b0;
	 else if (status_message_seen[2])
	   status_reg_rank2 <= #TCQ cal_r2_status;
	 else
	   status_reg_rank2 <= #TCQ status_reg_rank2;
   end
   
   always @ (posedge clk) begin
     if (rst)
	   status_reg_rank3 <= #TCQ 'b0;
	 else if (status_message_seen[3])
	   status_reg_rank3 <= #TCQ cal_r3_status;
	 else
	   status_reg_rank3 <= #TCQ status_reg_rank3;
   end
  
  assign task_id = IO_Write_Data[31:28];
  assign code    = IO_Write_Data[27:24];
  assign payload = IO_Write_Data[23:12];
  assign rank    = IO_Write_Data[11:10];
  assign nibble  = IO_Write_Data[9:4];
  assign bit_num = IO_Write_Data[3:0];

  //synthesis translate_off
  
  //DBI signals for the log
  always @ (posedge clk) begin
    if (!rst && (cal_dbi_wr_r[0] != cal_dbi_wr_r[1])) begin
	  if (cal_dbi_wr_r[0] == 1'b1 && cal_dbi_wr_r[1] == 1'b0)
	    $display ("DBG_uB: ********* DBI Write (Fabric) : ON  ********* %t", $time);
	  else if (cal_dbi_wr_r[0] == 1'b0 && cal_dbi_wr_r[1] == 1'b1)
	    $display ("DBG_uB: ********* DBI Write (Fabric) : OFF ********* %t", $time);
	end
	
	if (!rst && (cal_dbi_rd_r[0] != cal_dbi_rd_r[1])) begin
	  if (cal_dbi_rd_r[0] == 1'b1 && cal_dbi_rd_r[1] == 1'b0)
	    $display ("DBG_uB: ********* DBI Read (Fabric)  : ON  ********* %t", $time);
	  else if (cal_dbi_rd_r[0] == 1'b0 && cal_dbi_rd_r[1] == 1'b1)
	    $display ("DBG_uB: ********* DBI Read (Fabric)  : OFF ********* %t", $time);
	end
  end

  always @ (posedge clk) begin
    if (dbg_message_seen) begin
	  case (task_id)
		DBG_DQS_GATE : begin
		  $display ("DBG_uB: --------------- Task: DBG_DQS_GATE -----------------");
		  case (code)
	        DQS_GATE_FINE :
		      $display ("DBG_uB: fine = %d", payload);
		    DQS_GATE_COARSE :
		      $display ("DBG_uB:             coarse = %d", payload);
		    DQS_GATE_OFFSET :
		      $display ("DBG_uB: fine offset = %d", payload);
		    DQS_GATE_GT_STAT :
		      $display ("DBG_uB:                                GT_STATUS = %d", payload);
		    DQS_GATE_RD_LAT :
		      $display ("DBG_uB: Read latency = %d", payload);
			DQS_GATE_RD_LAT_DLY :
		      $display ("DBG_uB: Read latency Delay = %d", payload);
		    DQS_GATE_PAT_MATCH :
		      $display ("DBG_uB: Pattern Match = %d", payload);
			DQS_GATE_PATTERN :
		      $display ("DBG_uB: Pattern = %b", payload);
			DQS_GATE_ERR_CHK :
			  $display ("DBG_uB: Err chk reg = %b", payload);
			DQS_GATE_FINE_L :
			  $display ("DBG_uB: fine edge (left) = %d", payload);
			DQS_GATE_FINE_R :
			  $display ("DBG_uB: fine edge (right) = %d", payload);
	        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_WRLVL : begin
	//	  $display ("DBG_uB: --------------- Task: DBG_WRLVL --------------------");
		  case (code)
	      WRLVL_COARSE :
		      $display ("DBG_uB: WRLVL Coarse = %d", payload);
		    WRLVL_SAMPLE :
		      $display ("DBG_uB: WRLVL Sample = %h", payload);
        WRLVL_ODELAY_OFFSET :
          $display ("DBG_uB: WRLVL Coarse search ODELAY offset = %d", payload);
		    WRLVL_COARSE_LEFT :
          $display ("DBG_uB: WRLVL Coarse left (stable zero) value = %d", payload);
		    WRLVL_COARSE_RIGHT :
          $display ("DBG_uB: WRLVL Coarse right (stable one) value = %d", payload);
	      WRLVL_FINE :
		      $display ("DBG_uB: WRLVL Fine = %d", payload);
		    WRLVL_FINE_LEFT :
          $display ("DBG_uB: WRLVL Fine left (stable zero / noise edge) = %d", payload);
        WRLVL_FINE_RIGHT :
          $display ("DBG_uB: WRLVL Fine right (noise / stable one edge) = %d", payload);
		    WRLVL_FINE_CENTER :
          $display ("DBG_uB: WRLVL Fine noise center = %d", payload);
		    WRLVL_STEP_SIZE :
          $display ("DBG_uB: WRLVL Fine search step size = %d", payload);
        WRLVL_WARN:
          case(payload)
            WL_WARN_OFFSET_ZERO:      $display("DBG_uB: WRLVL Warn: ODELAY offset is zero");
            WL_WARN_STEP_SIZE_ZERO:   $display("DBG_uB: WRLVL Warn: Fine search step size is zero. Setting to 1 (minimum)");
            WL_WARN_NO_RIGHT_FINE:    $display("DBG_uB: WRLVL Warn: Couldn't find right side of noise region. Centering in region scanned");
            WL_WARN_ODELAY_SATURATED: $display("DBG_uB: WRLVL Warn: ODELAY taps saturated. Cannot fully preserve deskew component of DQ/DM bit");
            default:                  $display("DBG_uB: WRLVL Warn: code = $d, payload = %d", code, payload);
          endcase
		    WRLVL_ERR :
          case(payload)
            WL_ERR_STABLE_ZERO:   $display("DBG_uB: WRLVL Err: Couldn't find a stable zero during coarse search");
            WL_ERR_STABLE_ONE:    $display("DBG_uB: WRLVL Err: Couldn't find a stable one during coarse search");
            WL_ERR_NO_LEFT_FINE:  $display("DBG_uB: WRLVL Err: Couldn't find left edge of noise region");            
            default:              $display("DBG_uB: WRLVL Err: code = $d, payload = %d", code, payload);
          endcase
        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_RDLVL, DBG_RDLVL_CMPLX : begin
		  $display ("DBG_uB: --------------- Task: DBG_RDLVL --------------------");
		  case (code)
	        RDLVL_BIT_VECTOR :
			  $display ("DBG_uB: Bits in nibble for byte = %b", payload);
			RDLVL_QTR :
			  if (payload[9]==0)
		        $display ("DBG_uB: QTR DELAY (P) = %d", payload[8:0]);
			  else
			    $display ("DBG_uB: QTR DELAY (N) = %d", payload[8:0]);
		    RDLVL_IDELAY :
		      $display ("DBG_uB:             IDELAY = %d", payload);
		    RDLVL_SAMPLES :
		      $display ("DBG_uB: Samples left before err = %d", payload);
		    RDLVL_ERR_CHK :
		      $display ("DBG_uB:                           RAW err Reg = %b", payload);
			RDLVL_LEFT : begin
			  if (payload[9]==0)
			    $display ("DBG_uB: QTR LEFT Edge (P)= %d", payload[8:0]);
			  else
			    $display ("DBG_uB: QTR LEFT Edge (N)= %d", payload[8:0]);
			end
			RDLVL_RIGHT : begin
			  if (payload[9]==0)
			    $display ("DBG_uB: QTR RIGHT Edge (P)= %d", payload[8:0]);
			  else
			    $display ("DBG_uB: QTR RIGHT Edge (N)= %d", payload[8:0]);
			end
			RDLVL_CENTER : begin
			  if (payload[9]==0)
			    $display ("DBG_uB: QTR CENTER setting (P)= %d", payload[8:0]);
			  else
			    $display ("DBG_uB: QTR CENTER setting (N)= %d", payload[8:0]);
			end
		    RDLVL_DESKEW_EDGE_ERR :
		      $display ("DBG_uB: Deskew Edge not found = %d", payload);
			RDLVL_CENTER_EDGE_ERR : begin
			  if (payload[9]==0)
		        $display ("DBG_uB: Centering Edge not found (P)= %d", payload[8:0]);
			  else
			    $display ("DBG_uB: Centering Edge not found (N)= %d", payload[8:0]);
			end
			RDLVL_TIMEOUT : begin
			  $display ("DBG_uB: Timeout = %d", payload);
			end
		    RDLVL_NO_VALID_DATA : begin
		      $display ("DBG_uB: No valid data = %d", payload);
			end
			RDLVL_STATUS :
			  $display ("DBG_uB: RDLVL Status = %d", payload);
	        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_WRITE_DQS, DBG_WRITE_DQS_CMPLX : begin
		  $display ("DBG_uB: --------------- Task: DBG_DQS_CENTER ----------------");
          case (code)
		    WRDQS_DQ_BIT_VECTOR : begin
			  $display ("DBG_uB: Bits in nibble for byte = %b", payload);
			end
	        WRDQS_DQ_TXPHASE : begin
			  $display ("DBG_uB: TX_PHASE = %d", payload);
		    end
			WRDQS_DQ_ODELAY : begin
			  $display ("DBG_uB: ODELAY = %d", payload);
		    end
			WRDQS_DQ_DLY0 : begin
			  $display ("DBG_uB: DLY0 = %d", payload);
			end
			WRDQS_DQ_DLY1 : begin
			  $display ("DBG_uB: DLY1 = %d", payload);
			end
			WRDQS_DQ_DESKEW : begin
			  $display ("DBG_uB: DESKEW (DQS ODELAY) = %d", payload);
			end
			WRDQS_DQ_STATUS : begin
			  $display ("DBG_uB: WRDQS_DQ Status = %d", payload);
			end
			//------------------------ DM section ------------------------------
            WRDQS_DM_TXPHASE : begin
			  $display ("DBG_uB: TX_PHASE = %d", payload);
		    end
			WRDQS_DM_ODELAY : begin
			  $display ("DBG_uB: DM ODELAY = %d", payload);
		    end
			WRDQS_DM_DESKEW : begin
			  $display ("DBG_uB: DM DESKEW (DQS ODELAY) = %d", payload);
			end
			WRDQS_DM_LEFT : begin
			  $display ("DBG_uB: DM Left Margin = %d", payload);
			end
			WRDQS_DM_RIGHT : begin
			  $display ("DBG_uB: DM Right Margin = %d", payload);
			end
			WRDQS_DM_STATUS : begin
			  $display ("DBG_uB: WRDQS_DM Status = %d", payload);
			end
			WRDQS_DQS_ODELAY : begin
			  $display ("DBG_uB: DQS ODELAY = %d", payload);
			end
			WRDQS_WINDOW : begin
			  $display ("DBG_uB: WRDQS Min Window Size = %d", payload);
			end
			default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_WRITE_CAL : begin
		  $display ("DBG_uB: --------------- Task: DBG_WRITE_CAL ----------------");
		  case (code)
	        WRCAL_LATENCY :
			  $display ("DBG_uB: Write Cal Latency = %d", payload);
			WRCAL_COARSE :
		      $display ("DBG_uB: Write Cal Coarse Setting = %d", payload);
		    WRCAL_ERR :
		      $display ("DBG_uB: Write Cal ERR, max latency attempted = %d", payload);
	        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_READ_VREF, DBG_WRITE_VREF : begin
		  if (task_id == DBG_READ_VREF)
		    $display ("DBG_uB: --------------- Task: DBG_READ_VREF ----------------");
		  else
		    $display ("DBG_uB: --------------- Task: DBG_WRITE_VREF ----------------");
		  case (code)
	        VREF_BIT_VECTOR : begin
			  $display ("DBG_uB: Bits in nibble for byte = %b", payload); 
			end
			VREF_VALUE : begin
			  $display ("DBG_uB: VREF Setting = %d", payload); 
			end
			VREF_EYE_SIZE : begin
			  if (payload[9]==0)
		        $display ("DBG_uB: VREF Eye Size (P) = %d", payload[8:0]);
			  else
			    $display ("DBG_uB: VREF Eye Size (N) = %d", payload[8:0]);
			end
			default:
			  $display ("DBG_uB: code = %d, payload = %d", code, payload);
			endcase
		end
		DBG_WRITE_READ : begin
		  $display ("DBG_uB: --------------- Task: DBG_WRITE_READ = %H ----------------",IO_Write_Data);
		end
		DBG_MRANK_ADJUST : begin
		  $display ("DBG_uB: --------------- Task: MULTI-RANK ADJUST ---------------");
		  case (code)
			MULTIRANK_QTR : begin
		      if (payload[9]==0)
			    $display ("DBG_uB: Multi-Rank Common QTR setting (P)= %d", payload[8:0]);
			  else
			    $display ("DBG_uB: Multi-Rank Common QTR setting (N)= %d", payload[8:0]);
			end
			MULTIRANK_IDELAY : begin
			  $display ("DBG_uB: Multi-Rank Common IDELAY = %d", payload);
			end
			MULTIRANK_IDELAY_DBI : begin
			  $display ("DBG_uB: Multi-Rank Common IDELAY (DBI) = %d", payload);
			end
			MULTIRANK_GATE_COARSE : begin
			  $display ("DBG_uB: Multi-Rank DQS Gate Coarse = %d", payload);
			end
			MULTIRANK_GATE_RD_LAT : begin
			  $display ("DBG_uB: Multi-Rank DQS Gate Read Latency = %d", payload);
			end
	        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_DQS_TRACK : begin
		  $display ("DBG_uB: --------------- Task: DBG_DQS_TRACKING ----------------");
		  case (code)
			TRACKING_SAMPLES : begin
		      $display ("DBG_uB: Sample count = %d", payload);
			end
			TRACKING_GT_STATUS : begin
		      $display ("DBG_uB: GT_STATUS count = %d", payload);
			end
		    TRACKING_FINE : begin
		      $display ("DBG_uB: fine = %d", payload);
			end
			TRACKING_COARSE : begin
		      $display ("DBG_uB:             coarse = %d", payload);
			end
			TRACKING_DECISION_CNT : begin
		      $display ("DBG_uB: Decision Count = %d", payload);
			end
			TRACKING_DECISION : begin
		      $display ("DBG_uB: Decision = %d", payload);
			end
			TRACKING_QTR : begin
		      $display ("DBG_uB: %d fine taps = 1 course", payload);
			end
	        default:
		      $display ("DBG_uB: code = %d, payload = %d", code, payload);
          endcase
		end
		DBG_SANITY_CHECK : begin
		  $display ("DBG_uB: --------------- Task: DBG_SANITY_CHECK ----------------");
		  $display ("DBG_uB: Sanity Check Failure (nibble=%d)", payload);
		end
		DBG_MARGIN : begin
		  $display ("DBG_uB: --------------- Task: DBG_MARGIN ----------------");
		  case (code)
		    MARGIN_QTR : begin
			  if (payload[9]==0)
		        $display ("DBG_uB: QTR DELAY (P) = %d", payload[8:0]);
			  else
			    $display ("DBG_uB: QTR DELAY (N) = %d", payload[8:0]);
		    end
			MARGIN_LEFT : begin
			  if (payload[9]==0)
		        $display ("DBG_uB: Margin Left (P) = %d", payload[8:0]);
			  else
			    $display ("DBG_uB: Margin Left (N) = %d", payload[8:0]);
		    end
			MARGIN_RIGHT : begin
			  if (payload[9]==0)
		        $display ("DBG_uB: Margin Right (P) = %d", payload[8:0]);
			  else
			    $display ("DBG_uB: Margin Right (N) = %d", payload[8:0]);
		    end
			MARGIN_DQS: begin
		      $display ("DBG_uB: DQS Odelay = %d", payload[8:0]);
		    end
			MARGIN_DQ: begin
		      $display ("DBG_uB: DQ Odelay = %d", payload[8:0]);
		    end
			default:
			  $display ("DBG_uB: code = %d, payload = %d", code, payload);
	      endcase
		end
		default: begin
		  $display ("DBG_uB: --------------- Task: %d -------------------", task_id);
		  $display ("DBG_uB: code = %d, payload = %d", code, payload);
		end
	  endcase
	
	   $display ("DBG_uB: %d  %d  %d -- %t", rank, nibble, bit_num, $time);
	end
  end
 
  //------------------------ PRE CAL STATUS ------------------------------------
  always @(posedge cal_pre_status[0])
    if (!rst) begin
	  $display ("DBG_uB: ============== Pre Cal Status: %h ============", cal_pre_status);
      $display ("DBG_uB: Microblaze has started up %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_pre_status[3])
    if (!rst) begin
	  $display ("DBG_uB: ============== Pre Cal Status: %h ============", cal_pre_status);
      $display ("DBG_uB: Memory Initialization Complete %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_pre_status[4])
    if (!rst) begin
	  $display ("DBG_uB: ============== Pre Cal Status: %h ============", cal_pre_status);
      $display ("DBG_uB: XSDB setup complete %t", $time);
	  $display ("DBG_uB: ============================================");
	end

  //------------------------ CAL STATUS ----------------------------------------
  genvar rank_db;
  generate
    if(LRDIMM_CAL_SIZE > 0) begin :LRDIMM_CAL_REPORTING
      for(rank_db=0; rank_db < RANKS_PER_SLOT; rank_db++) begin

        // First slot calibration stages
        always @(posedge status_reg_rank0[rank_db*12 + 0]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MREP Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 1]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MREP Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 2]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Cycle Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 3]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Cycle Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 4]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Center Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 5]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Center Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 6]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d DWL Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 7]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d DWL Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 8]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Cycle Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 9]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Cycle Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 10]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Center Training Start %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank0[rank_db*12 + 11]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Center Training Done %t", (RANKS_PER_SLOT*0 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        // Second slot calibration stages
        always @(posedge status_reg_rank1[rank_db*12 + 0]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MREP Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 1]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MREP Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 2]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Cycle Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 3]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Cycle Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 4]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Center Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 5]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MRD Center Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 6]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d DWL Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 7]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d DWL Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 8]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Cycle Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 9]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Cycle Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 10]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Center Training Start %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

        always @(posedge status_reg_rank1[rank_db*12 + 11]) begin
          if (!rst) begin
            $display ("DBG_uB: ============== Status: %h ============", status_reg);
            $display ("DBG_uB: LRDIMM DB Rank %d MWD Center Training Done %t", (RANKS_PER_SLOT*1 + rank_db), $time);
            $display ("DBG_uB: ============================================");
          end
        end

      end // rank_db loop
    end // LRDIMM_CAL_REPORTING
  endgenerate

  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 0] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 0] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 0] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 0])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: DQS Gate/Bias Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 1] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 1] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 1] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 1])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: DQS Gate/Bias Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 2] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 2] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 2] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 2])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: DQS Gate Check Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 3] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 3] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 3] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 3])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: DQS Gate Check Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 4] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 4] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 4] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 4])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: WRLVL Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 5] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 5] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 5] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 5])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: WRLVL Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 6] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 6] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 6] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 6])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Per-bit Deskew Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 7] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 7] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 7] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 7])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Per-bit Deskew Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 8] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 8] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 8] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 8])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Per-bit Deskew Start (DBI) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 9] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 9] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 9] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 9])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Per-bit Deskew Done (DBI) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 10] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 10] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 10] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 10])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering Start (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 11] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 11] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 11] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 11])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering Done (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 12] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 12] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 12] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 12])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Sanity Check Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 13] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 13] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 13] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 13])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read Sanity Check Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 14] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 14] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 14] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 14])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Per-bit Deskew Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 15] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 15] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 15] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 15])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Per-bit Deskew Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 16] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 16] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 16] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 16])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Per-bit Deskew Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 17] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 17] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 17] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 17])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Per-bit Deskew Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 18] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 18] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 18] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 18])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Start (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 19] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 19] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 19] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 19])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Done (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 20] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 20] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 20] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 20])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Start (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 21] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 21] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 21] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 21])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Done (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 22] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 22] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 22] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 22])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering with DBI Start (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 23] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 23] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 23] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 23])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering with DBI Done (Simple) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 24] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 24] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 24] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 24])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write Latency Calibration Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 25] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 25] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 25] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 25])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write Latency Calibration Done %t", $time);	
	  $display ("DBG_uB: ============================================");
	end  
  
  always @(posedge sanity_check_start)
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write/Read Sanity Check Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end	 
  
  always @(posedge sanity_check_done)
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write/Read Sanity Check Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 28] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 28] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 28] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 28])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering Start (Complex) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 29] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 29] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 29] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 29])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read DQS Centering Done (Complex) %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 32] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 32] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 32] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 32])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read VREF training Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 33] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 33] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 33] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 33])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Read VREF training Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 36] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 36] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 36] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 36])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Start (Complex)%t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 37] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 37] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 37] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 37])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DQ Done (Complex)%t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 38] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 38] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 38] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 38])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Start (Complex)%t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 39] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 39] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 39] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 39])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write DQS-to-DM/DBI Done (Complex)%t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 42] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 42] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 42] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 42])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write VREF training Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 43] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 43] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 43] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 43])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write VREF training Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 46] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 46] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 46] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 46])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Multi-rank RDLVL Adjust Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end

  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 47] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 47] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 47] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 47])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Multi-rank RDLVL Adjust Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 50] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 50] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 50] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 50])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Multi-rank Adjustments and Checks Start %t", $time);
	  $display ("DBG_uB: ============================================");
	end

  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 51] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 51] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 51] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 51])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Multi-rank Adjustments and Checks Done %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 52] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 52] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 52] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 52])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write/Read Sanity Check Start (rank: %d) %t", (status_message_seen>>1), $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge status_reg_rank0[LRDIMM_CAL_SIZE + 53] or posedge status_reg_rank1[LRDIMM_CAL_SIZE + 53] or 
           posedge status_reg_rank2[LRDIMM_CAL_SIZE + 53] or posedge status_reg_rank3[LRDIMM_CAL_SIZE + 53])
    if (!rst && cal_pre_status[0]) begin
	  $display ("DBG_uB: ============== Status: %h ============", status_reg);
      $display ("DBG_uB: Write/Read Sanity Check Done (rank: %d) %t", (status_message_seen>>1), $time);
	  $display ("DBG_uB: ============================================");
	end

  //------------------------ POST CAL STATUS -----------------------------------
  
  always @(posedge cal_post_status[0])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", cal_post_status);
      $display ("DBG_uB: DQS Tracking Running %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_post_status[2])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", cal_post_status);
      $display ("DBG_uB: DQS Tracking Failed %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_post_status[3])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", cal_post_status);
      $display ("DBG_uB: Read Margin Check Running %t", $time);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_post_status[4])
    if (!rst) begin
	  $display ("DBG_uB: ============== Status: %h ============", cal_post_status);
      $display ("DBG_uB: Write Margin Check Running %t", $time);
	  $display ("DBG_uB: ============================================");
	end
  
  //end of Status Messages
  
  always @(posedge cal_error)
    if (!rst) begin
	  $display ("DBG_uB: ============================================");
      $display ("DBG_uB: CAL_FAILED %t", $time);
	  $display ("DBG_uB: Error Code:  %h", cal_error_code);
	  $display ("DBG_uB: Nibble/Byte: %d", cal_error_nibble);
	  $display ("DBG_uB: Bit:         %d", cal_error_bit);
	  $display ("DBG_uB: ============================================");
	end
	
  always @(posedge cal_warning)
    if (!rst) begin
	  $display ("DBG_uB: ============================================");
      $display ("DBG_uB: WARNING %t", $time);
	  $display ("DBG_uB: Warning Code: %h", cal_warning_code);
	  $display ("DBG_uB: Nibble/Byte:  %d", cal_warning_nibble);
	  $display ("DBG_uB: ============================================");
	end
	
  always @ (posedge clk) begin
	if (IO_Addr_Strobe && IO_Address == CAL_DONE) begin
	  if (IO_Write_Data[1] == 1) begin
	    $display ("DBG_uB: ============================================");
	    $display ("DBG_uB: CAL_DONE                  %t", $time);
	    $display ("DBG_uB: ============================================");
	  end else if (IO_Write_Data[0] == 1) begin
	    $display ("DBG_uB: en_vtc asserted                  %t", $time);
	  end
	end
  end
  
  //synthesis translate_on

endmodule

