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
//  /   /         Filename           : ddr4_v2_2_10_mc_periodic.sv
// /___/   /\     Date Last Modified : $Date: 2014/09/03 $
// \   \  /  \    Date Created       : Thu Feb 6 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_mc_periodic module
// Reference        :
// Revision History :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_periodic #(parameter
    TCQ    = 0.1
)(
    input clk,
    input rst,

    output reg       per_rd_req,
    output reg       per_cas_block_req,
    output reg       per_block_ref,
    output           gt_data_ready,

    input [31:0]     periodic_config, // spyglass disable W498
    input [31:0]     periodic_interval_config,
    input            rdCAS,
    input            refReq,
    input            per_rd_done,
    input            per_rd_accept
);

// Configuration
reg  periodic_config_read_enable;
reg  periodic_config_gap_enable;

// FSM encoding for high level periodic algorithm
//localparam IDLE                   = 9'b0_0000_0001;
//localparam INIT                   = 9'b0_0000_0010;
//localparam WAIT_INTERVAL          = 9'b0_0000_0100;
//localparam READ_INJ               = 9'b0_0000_1000;
//localparam WAIT_READ_INJ          = 9'b0_0001_0000;
//localparam GAP_INJ                = 9'b0_0010_0000;
//localparam WAIT_GAP_INJ           = 9'b0_0100_0000;
//localparam UPDATE_STATUS          = 9'b0_1000_0000;
//localparam CHECK_ENABLE           = 9'b1_0000_0000;

localparam IDLE                   = 4'b0000;
localparam INIT                   = 4'b0001;
localparam WAIT_INTERVAL          = 4'b0010;
localparam READ_INJ               = 4'b0011;
localparam WAIT_READ_INJ          = 4'b0100;
localparam GAP_INJ                = 4'b0101;
localparam WAIT_GAP_INJ           = 4'b0110;
localparam UPDATE_STATUS          = 4'b0111;
localparam CHECK_ENABLE           = 4'b1000;

// Periodic algorithm FSM
//reg [8:0]   periodic_state;
//reg [8:0]   periodic_state_nxt;
(* fsm_encoding = "sequential" *) reg [3:0]   periodic_state;
reg [3:0]   periodic_state_nxt;
reg         periodic_state_init;
reg         periodic_state_read_inj;
reg         periodic_state_gap_inj;
reg         periodic_state_update_status;

// FSM encoding for injection flow
//localparam INJ_IDLE              = 9'b0_0000_0001;
//localparam INJ_WAIT_REF          = 9'b0_0000_0010;
//localparam INJ_BLOCK_REF         = 9'b0_0000_0100;
//localparam INJ_BLOCK_NI          = 9'b0_0000_1000;
//localparam INJ_ISSUE_TXN         = 9'b0_0001_0000;
//localparam INJ_WAIT_TXN_RETURN   = 9'b0_0010_0000;
//localparam INJ_BLOCK_READ_CAS    = 9'b0_0100_0000;
//localparam INJ_WAIT_CAS_BLOCK    = 9'b0_1000_0000;
//localparam INJ_DONE              = 9'b1_0000_0000;

localparam INJ_IDLE              = 4'b0000;
localparam INJ_WAIT_REF          = 4'b0001;
localparam INJ_BLOCK_REF         = 4'b0010;
localparam INJ_BLOCK_NI          = 4'b0011;
localparam INJ_ISSUE_TXN         = 4'b0100;
localparam INJ_WAIT_TXN_RETURN   = 4'b0101;
localparam INJ_BLOCK_READ_CAS    = 4'b0110;
localparam INJ_WAIT_CAS_BLOCK    = 4'b0111;
localparam INJ_DONE              = 4'b1000;


// Injection flow FSM
//reg [8:0]   inject_state;
//reg [8:0]   inject_state_nxt;
(* fsm_encoding = "sequential" *)reg [3:0]   inject_state;
reg [3:0]   inject_state_nxt;
reg         inject_state_block_ref;
reg         inject_state_allow_ref;
reg         inject_state_read_inj;
reg         inject_state_gap_inj;
reg         inject_state_done;


// Interval tracking
reg [15:0] interval_counter_low;
reg [15:0] interval_counter_high;
reg        interval_counter_reset;
reg        interval_counter_low_ro;
reg        interval_hit_low;
reg        interval_hit_high;

// Read and 3 cycle gap accumulators
reg        read_accum;
reg [1:0]  gap_timer;
reg [2:0]  gap_pipe;
reg        gap_accum;

//******************************************************************************
// Interval tracking
//******************************************************************************

// The periodic read interval counter is 32 bits wide, allowing up to 14 second
// intervals assuming a 300MHz fabric.  The counter is broken up into two 16 bit
// counters for timing.

// Count fabric cycles when periodic FSM is not idle state.  Reset the counter
// when the interval is reached.
wire        interval_hit_low_nxt       = ( interval_counter_low  == periodic_interval_config[15: 0] );
wire        interval_hit_high_nxt      = ( interval_counter_high == periodic_interval_config[31:16] );
wire        interval_counter_reset_nxt = ( periodic_state == IDLE ) | ( interval_hit_low & interval_hit_high );

wire [15:0] interval_counter_low_nxt   = interval_counter_reset
                                         ? '0 : ( interval_counter_low + 16'b1 );

// Increment the high counter when the lower counter rolls over.
// Assert ro_nxt one cycle early to allow for the pipeline bewteen high and low counters.
// Block ro_nxt if the interval has already been hit to avoid incrementing the high count the cycle after a reset.
wire        interval_counter_low_ro_nxt = ( interval_counter_low == 16'hFFFE ) & ~interval_counter_reset;

wire [15:0] interval_counter_high_nxt   = interval_counter_reset  // spyglass disable W164a
                                          ? '0 : ( interval_counter_high + { 15'b0, interval_counter_low_ro } );


//******************************************************************************
// Read transaction and data bus gap cycle tracking
//******************************************************************************

// Track reads and gaps between reads with accumulators that reset at the start of each interval.
// A gap is defined as 3 consecutive fabric cycles without a rdCAS assertion.

wire        read_accum_nxt = ~interval_counter_reset & ( read_accum | rdCAS );

wire [2:0]  gap_pipe_nxt  = { gap_pipe[1:0], ~rdCAS }     & { 3 { ~interval_counter_reset } };
wire        gap_accum_nxt = ( gap_accum | ( &gap_pipe ) ) & ~interval_counter_reset;

//******************************************************************************
// Output
//******************************************************************************

// Block the ref FSM to arbitrate for access of the Group FSM inputs.
// The injection FSM will set and clear the ref block flag.
wire per_block_ref_nxt = ~inject_state_allow_ref & ( per_block_ref | inject_state_block_ref );

// Send out a single pulse to the Group FSMs to block the NI and inject a periodic read.
// This is only done if there have been no reads for an entire interval.
// Flop the periodic read txn request for timing.
wire per_rd_req_nxt = inject_state_read_inj;

// Send out a multi-cycle signal to the Ctrl block to block read CAS.
// This is only done if there have been no gaps of 3 consecutive fabric cycles for an entire interval.
// Flop for timing.
wire       gap_timer_nz    = | gap_timer;
wire [1:0] gap_timer_nxt   = inject_state_gap_inj ? 2'd3 : ( gap_timer - { 1'b0, gap_timer_nz } ); // spyglass disable W164a
wire per_cas_block_req_nxt = gap_timer_nz;

// Send pulse to uB to indicate that it can go ahead and read new gt data
assign     gt_data_ready = periodic_state_update_status;

//******************************************************************************
// Periodic FSM
//******************************************************************************

wire  periodic_fsm_start = periodic_config_read_enable | periodic_config_gap_enable;
wire  interval_expired   = interval_hit_low & interval_hit_high;

always @(*) begin

  periodic_state_nxt             = periodic_state;
  periodic_state_init            = 1'b0;
  periodic_state_update_status   = 1'b0;
  periodic_state_read_inj        = 1'b0;
  periodic_state_gap_inj         = 1'b0;

  casez (periodic_state)
    IDLE: begin
      if (periodic_fsm_start) periodic_state_nxt = INIT;
    end
    INIT: begin
      periodic_state_init = 1'b1;
      periodic_state_nxt = WAIT_INTERVAL;
    end
    WAIT_INTERVAL: begin
      if ( interval_expired & ~read_accum ) begin
        periodic_state_nxt = READ_INJ;
      end else if ( interval_expired & ~gap_accum ) begin
        periodic_state_nxt = GAP_INJ;
      end else if ( interval_expired ) begin
        periodic_state_nxt = UPDATE_STATUS;
      end
    end
    READ_INJ: begin
      periodic_state_read_inj = 1'b1;
      periodic_state_nxt = WAIT_READ_INJ;
    end
    WAIT_READ_INJ: begin
      if ( inject_state_done ) periodic_state_nxt = UPDATE_STATUS;
    end
    GAP_INJ: begin
      periodic_state_gap_inj = 1'b1;
      periodic_state_nxt = WAIT_GAP_INJ;
    end
    WAIT_GAP_INJ: begin
      if ( inject_state_done ) periodic_state_nxt = UPDATE_STATUS;
    end
    UPDATE_STATUS: begin
      periodic_state_update_status = 1'b1;
      periodic_state_nxt = CHECK_ENABLE;
    end
    CHECK_ENABLE: begin
      if (periodic_fsm_start) periodic_state_nxt = WAIT_INTERVAL;
      else                    periodic_state_nxt = IDLE;
    end
    default: begin
      periodic_state_nxt = IDLE;
    end
  endcase

end //always

always @(posedge clk) begin
  if (rst) begin
    periodic_state <= #TCQ IDLE;
  end
  else begin
    periodic_state <= #TCQ periodic_state_nxt;
  end
end



//******************************************************************************
// Injection FSM
//******************************************************************************

wire gap_wait_done = ( gap_timer == 2'd1 );

always @(*) begin

  inject_state_nxt             = inject_state;
  inject_state_block_ref       = 1'b0;
  inject_state_allow_ref       = 1'b0;
  inject_state_read_inj        = 1'b0;
  inject_state_gap_inj         = 1'b0;
  inject_state_done            = 1'b0;

  casez (inject_state)
    IDLE: begin
      if ( periodic_state_read_inj ) inject_state_nxt = INJ_WAIT_REF;
      if ( periodic_state_gap_inj  ) inject_state_nxt = INJ_BLOCK_READ_CAS;
    end
    INJ_WAIT_REF: begin
      if ( ~refReq ) begin
        inject_state_block_ref = 1'b1;
        inject_state_nxt = INJ_BLOCK_REF;
      end
    end
    INJ_BLOCK_REF: begin
      if ( ~refReq ) begin
        inject_state_nxt = INJ_BLOCK_NI;
      end else begin
        inject_state_allow_ref = 1'b1;
        inject_state_nxt = INJ_WAIT_REF;
      end
    end
    INJ_BLOCK_NI: begin
      inject_state_read_inj = 1'b1;
      inject_state_nxt = INJ_ISSUE_TXN;
    end
    INJ_ISSUE_TXN: begin
      if ( per_rd_accept ) begin
        inject_state_nxt = INJ_WAIT_TXN_RETURN;
        inject_state_allow_ref = 1'b1;
      end
    end
    INJ_WAIT_TXN_RETURN: begin
      if ( per_rd_done ) begin
        inject_state_nxt = INJ_DONE;
      end
    end
    INJ_BLOCK_READ_CAS: begin
      inject_state_gap_inj = 1'b1;
      inject_state_nxt = INJ_WAIT_CAS_BLOCK;
    end
    INJ_WAIT_CAS_BLOCK: begin
      if (gap_wait_done ) begin
        inject_state_nxt = INJ_DONE;
      end
    end
    INJ_DONE: begin
      inject_state_done = 1'b1;
      inject_state_nxt = INJ_IDLE;
    end
    default: begin
      inject_state_nxt = INJ_IDLE;
    end
  endcase

end //always

always @(posedge clk) begin
  if (rst) begin
    inject_state <= #TCQ INJ_IDLE;
  end
  else begin
    inject_state <= #TCQ inject_state_nxt;
  end
end


//******************************************************************************
// Flops
//******************************************************************************

// General reset flops
always @(posedge clk) begin
  if (rst) begin
    per_block_ref   <= #TCQ 1'b0;
    interval_counter_low  <= #TCQ 16'b0;
    interval_counter_high <= #TCQ 16'b0;
    read_accum            <= #TCQ 1'b0;
    gap_accum             <= #TCQ 1'b0;
    gap_timer             <= #TCQ 2'b0;
  end
  else begin
    per_block_ref   <= #TCQ per_block_ref_nxt;
    interval_counter_low  <= #TCQ interval_counter_low_nxt;
    interval_counter_high <= #TCQ interval_counter_high_nxt;
    read_accum            <= #TCQ read_accum_nxt;
    gap_accum             <= #TCQ gap_accum_nxt;
    gap_timer             <= #TCQ gap_timer_nxt;
  end
end


// General non-reset flops
always @(posedge clk) begin
  periodic_config_read_enable <= #TCQ periodic_config[0];
  periodic_config_gap_enable  <= #TCQ periodic_config[1];
  per_rd_req                  <= #TCQ per_rd_req_nxt;
  per_cas_block_req           <= #TCQ per_cas_block_req_nxt;
  interval_counter_reset      <= #TCQ interval_counter_reset_nxt;
  interval_counter_low_ro     <= #TCQ interval_counter_low_ro_nxt;
  interval_hit_low            <= #TCQ interval_hit_low_nxt;
  interval_hit_high           <= #TCQ interval_hit_high_nxt;
  gap_pipe                    <= #TCQ gap_pipe_nxt;
end

//synopsys translate_off
reg [103:0] periodic_state_name;

always @(*) casez (periodic_state)
  IDLE          : periodic_state_name       = "IDLE";
  INIT          : periodic_state_name       = "INIT";
  WAIT_INTERVAL : periodic_state_name       = "WAIT_INTERVAL";
  READ_INJ      : periodic_state_name       = "READ_INJ";
  WAIT_READ_INJ : periodic_state_name       = "WAIT_READ_INJ";
  GAP_INJ       : periodic_state_name       = "GAP_INJ";
  WAIT_GAP_INJ  : periodic_state_name       = "WAIT_GAP_INJ";
  UPDATE_STATUS : periodic_state_name       = "UPDATE_STATUS";
  CHECK_ENABLE  : periodic_state_name       = "CHECK_ENABLE";
  default       : periodic_state_name       = "p_state_err";
endcase

reg [151:0] inject_state_name;

always @(*) casez (inject_state)
  INJ_IDLE              : inject_state_name = "INJ_IDLE";
  INJ_WAIT_REF          : inject_state_name = "INJ_WAIT_REF";
  INJ_BLOCK_REF         : inject_state_name = "INJ_BLOCK_REF";
  INJ_BLOCK_NI          : inject_state_name = "INJ_BLOCK_NI";
  INJ_ISSUE_TXN         : inject_state_name = "INJ_ISSUE_TXN";
  INJ_WAIT_TXN_RETURN   : inject_state_name = "INJ_WAIT_TXN_RETURN";
  INJ_BLOCK_READ_CAS    : inject_state_name = "INJ_BLOCK_READ_CAS";
  INJ_WAIT_CAS_BLOCK    : inject_state_name = "INJ_WAIT_CAS_BLOCK";
  INJ_DONE              : inject_state_name = "INJ_DONE";
  default               : inject_state_name = "i_state_err";
endcase


`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

// Low interval count expired
wire   e_mc_per_000 = interval_hit_low_nxt & ( | periodic_interval_config[15: 0] );
always @(posedge clk) mc_per_000: if (~rst) cover property (e_mc_per_000);

// High interval count expired
wire   e_mc_per_001 = interval_hit_low_nxt & ( | periodic_interval_config[15: 0] )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_001: if (~rst) cover property (e_mc_per_001);

// Corner case intervals
wire   e_mc_per_002 = interval_hit_low_nxt & ( periodic_interval_config[15: 0] == 16'h0000 )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_002: if (~rst) cover property (e_mc_per_002);

// Corner case intervals
wire   e_mc_per_003 = interval_hit_low_nxt & ( periodic_interval_config[15: 0] == 16'h0001 )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_003: if (~rst) cover property (e_mc_per_003);

// Corner case intervals
wire   e_mc_per_004 = interval_hit_low_nxt & ( periodic_interval_config[15: 0] == 16'hFFFD )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_004: if (~rst) cover property (e_mc_per_004);

// Corner case intervals
wire   e_mc_per_005 = interval_hit_low_nxt & ( periodic_interval_config[15: 0] == 16'hFFFE )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_005: if (~rst) cover property (e_mc_per_005);

// Corner case intervals
wire   e_mc_per_006 = interval_hit_low_nxt & ( periodic_interval_config[15: 0] == 16'hFFFF )
                      & interval_hit_high_nxt & ( | periodic_interval_config[31:16] );
always @(posedge clk) mc_per_006: if (~rst) cover property (e_mc_per_006);

// System read just missed current interval
wire   e_mc_per_007 = interval_counter_reset & ~read_accum & rdCAS;
always @(posedge clk) mc_per_007: if (~rst) cover property (e_mc_per_007);

// System gap just missed current interval
wire   e_mc_per_008 = ~gap_accum & ( &gap_pipe ) & interval_counter_reset;
always @(posedge clk) mc_per_008: if (~rst) cover property (e_mc_per_008);

// Periodic read injection request forced to retry due to refresh
wire   e_mc_per_009 = inject_state_allow_ref & per_block_ref & ( inject_state == INJ_BLOCK_REF );
always @(posedge clk) mc_per_009: if (~rst) cover property (e_mc_per_009);

// Periodic read injection blocked by refresh
wire   e_mc_per_010 = ( inject_state == INJ_WAIT_REF ) & refReq;
always @(posedge clk) mc_per_010: if (~rst) cover property (e_mc_per_010);

// Periodic read issued
reg    e_per_rd_accept_ff;
wire   e_per_rd_accept_nxt = ~per_rd_done & ( e_per_rd_accept_ff | per_rd_accept );
always @(posedge clk) begin
  if (rst) begin
    e_per_rd_accept_ff <= #TCQ '0;
  end else begin
    e_per_rd_accept_ff <= #TCQ e_per_rd_accept_nxt;
  end
end
wire   e_mc_per_011 = ( inject_state == INJ_WAIT_TXN_RETURN ) & e_per_rd_accept_ff & per_rd_done;
always @(posedge clk) mc_per_011: if (~rst) cover property (e_mc_per_011);

// Periodic gap injection
wire   e_mc_per_012 = ( inject_state == INJ_WAIT_CAS_BLOCK ) & gap_wait_done;
always @(posedge clk) mc_per_012: if (~rst) cover property (e_mc_per_012);

// Periodic read and gap injection in same sim
reg  e_per_rd_issued;
reg  e_per_gap_issued;
wire e_per_rd_issued_nxt  = ( ~ ( e_per_rd_issued & e_per_gap_issued ) ) & ( e_per_rd_issued  | e_mc_per_011 );
wire e_per_gap_issued_nxt = ( ~ ( e_per_rd_issued & e_per_gap_issued ) ) & ( e_per_gap_issued | e_mc_per_012 );
always @(posedge clk) begin
  if (rst) begin
    e_per_rd_issued  <= #TCQ '0;
    e_per_gap_issued <= #TCQ '0;
  end else begin
    e_per_rd_issued  <= #TCQ e_per_rd_issued_nxt;
    e_per_gap_issued <= #TCQ e_per_gap_issued_nxt;
  end
end
wire   e_mc_per_013 = e_per_rd_issued & e_per_gap_issued;
always @(posedge clk) mc_per_013: if (~rst) cover property (e_mc_per_013);



// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Spurious per_rd_accept
wire   a_mc_per_000 = e_per_rd_accept_ff & per_rd_accept;
always @(posedge clk) if (~rst) assert property (~a_mc_per_000);

// No reads and no read gap in same interval
wire   a_mc_per_001 = interval_expired & ~read_accum & ~gap_accum & periodic_config_read_enable & periodic_config_gap_enable;
always @(posedge clk) if (~rst) assert property (~a_mc_per_001);



`endif

//synopsys translate_on

endmodule


