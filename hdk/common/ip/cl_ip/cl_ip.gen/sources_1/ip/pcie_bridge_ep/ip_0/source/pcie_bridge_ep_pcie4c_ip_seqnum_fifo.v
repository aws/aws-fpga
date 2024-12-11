//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_ep_pcie4c_ip_seqnum_fifo.v
// Version    : 1.0 
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_seqnum_fifo #(

  // Parameters

  parameter            TCQ                               = 1,
  parameter 		       RAM_WIDTH                         = 6,
  parameter 		       RAM_DEPTH                         = 4,
  parameter 		       ADDR_WIDTH                        = 2,
  parameter 		       FIFO_FULL_HIGH_THRESHOLD          = 3'd4,
  parameter 		       FIFO_FULL_LOW_THRESHOLD           = 3'd1,

  parameter 		       IN_FSM_SIZE                       = 2,
  parameter 		       IN_FSM_IDLE                       = 2'b01,
  parameter 		       IN_FSM_CHANGE                     = 2'b10,
  parameter            NO_UPDATE_PREV_DATA_ON_FIFO_FULL  = 1'b0
  )
  (
  input 	                    core_reset_n_i,
  input                       core_clk_i,

  input                       user_reset_n_i,
  input                       user_clk_i,

  input  [(RAM_WIDTH-1):0]    data_i, 
  output [(RAM_WIDTH-1):0]    data_o

  );  


  // Local Registers

  reg [RAM_WIDTH-1:0] 	       reg_ram[RAM_DEPTH-1:0];

  integer                      index;
  reg [ADDR_WIDTH:0] 	       write_addr;
  reg [ADDR_WIDTH:0] 	       write_addr_read_clk;
  reg [ADDR_WIDTH:0] 	       read_addr;
  reg [ADDR_WIDTH:0] 	       read_addr_wrclk;
  reg 			       fifo_full;

  reg [(IN_FSM_SIZE-1):0]      reg_in_fsm_state /* synthesis syn_state_machine=1 */;
  reg [(IN_FSM_SIZE-1):0]      reg_in_fsm_next_state;

  reg [(RAM_WIDTH-1):0]        reg_prev_data;
  reg [(RAM_WIDTH-1):0]        reg_out_data;

  reg [(RAM_WIDTH-1):0]        data_int;

  // Local wires

  wire [ADDR_WIDTH:0] 	       write_addr_next;
  wire [ADDR_WIDTH:0] 	       read_addr_next;
  wire [ADDR_WIDTH:0] 	       read_side_occupancy;
  wire [ADDR_WIDTH:0] 	       write_side_occupancy;
  wire 			       read_data_valid;
  wire 			       fifo_empty;
  wire 			       write_enable;
  wire [RAM_WIDTH-1:0] 	       ram_write_data;
  wire [RAM_WIDTH-1:0] 	       ram_read_data;

  wire [(RAM_WIDTH-1):0]       prev_data_w;
 
  wire [(IN_FSM_SIZE-1):0]     in_fsm_state_w;

  //  Capture data_i
  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      data_int <= #(TCQ) {RAM_WIDTH{1'b0}};
    else 
      data_int <= #(TCQ) data_i;

  // Capture LTSSM state on change
  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      reg_prev_data <= #(TCQ) {RAM_WIDTH{1'b0}};
    else if (((data_int != prev_data_w) || (in_fsm_state_w == IN_FSM_CHANGE) ) & 
	     (~NO_UPDATE_PREV_DATA_ON_FIFO_FULL | (~fifo_full & NO_UPDATE_PREV_DATA_ON_FIFO_FULL)))
      reg_prev_data <= #(TCQ) data_int;
  
  // FSM Looks for change in the LTSSM state

  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      reg_in_fsm_state <= #(TCQ) IN_FSM_IDLE;
    else
      reg_in_fsm_state <= #(TCQ) reg_in_fsm_next_state;

  // FSM Next State Logic

  always @( * )
    case (in_fsm_state_w)
      IN_FSM_IDLE :
        if (data_int != reg_prev_data)
          reg_in_fsm_next_state = IN_FSM_CHANGE;
        else
          reg_in_fsm_next_state = IN_FSM_IDLE;
      IN_FSM_CHANGE : 
        reg_in_fsm_next_state = IN_FSM_IDLE;
      default : 
        reg_in_fsm_next_state = IN_FSM_IDLE;
    endcase   

  // FIFO Write Side Processes

  assign  ram_write_data = data_int;
  //assign  write_enable = (data_int != prev_data_w) || (in_fsm_state_w == IN_FSM_CHANGE);
  assign  write_enable = (data_int[6]);
  assign  write_addr_next = write_addr + {{ADDR_WIDTH{1'b0}}, 1'b1};

  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      write_addr <= {ADDR_WIDTH+1{1'b0}};
    else if (write_enable & ~fifo_full)
      write_addr <= write_addr_next;

  // Write into RAM 
  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      begin
	for (index=0; index < RAM_DEPTH; index=index+1)
	  reg_ram[index] <= {RAM_WIDTH{1'b0}};
      end
    else if (write_enable)
      reg_ram[write_addr[ADDR_WIDTH-1:0]] <= ram_write_data;

  // FIFO Read Side Processes

  assign      read_addr_next = read_addr +  {{ADDR_WIDTH-1{1'b0}}, 1'b1};

  always @(posedge user_clk_i or negedge user_reset_n_i)
    if (~user_reset_n_i)
      read_addr <= {ADDR_WIDTH+1{1'b0}};
    else if (read_data_valid)
      read_addr <= read_addr_next;

  // Convert write pointer to the read clk domain
  always @(posedge user_clk_i or negedge user_reset_n_i)
    if (~user_reset_n_i)
      write_addr_read_clk <= {ADDR_WIDTH+1{1'b0}};
    else
      write_addr_read_clk <= write_addr;
  
  // Maintain read-side occupancy
  assign read_side_occupancy = (write_addr_read_clk - read_addr);
  assign fifo_empty = (read_side_occupancy == {ADDR_WIDTH+1{1'b0}});
  assign read_data_valid = ~fifo_empty;
  assign ram_read_data = reg_ram[read_addr[ADDR_WIDTH-1:0]];

  /* convert read pointer to write clock domain */
  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      read_addr_wrclk <= {ADDR_WIDTH+1{1'b0}};
    else
      read_addr_wrclk <= read_addr;

  assign write_side_occupancy = write_addr - read_addr_wrclk;

  // Generate FIFO full condition
  always @(posedge core_clk_i or negedge core_reset_n_i)
    if (~core_reset_n_i)
      fifo_full <= 1'b0;
    else
      if (write_side_occupancy[ADDR_WIDTH] ||
	  (write_side_occupancy[ADDR_WIDTH-1:0] == FIFO_FULL_HIGH_THRESHOLD))
	fifo_full <= 1'b1;
      else
	// Clear when FIFO occupancy goes below low threshold
	if (~write_side_occupancy[ADDR_WIDTH] &&
	    (write_side_occupancy[ADDR_WIDTH-1:0] <= FIFO_FULL_LOW_THRESHOLD))
	  fifo_full <= 1'b0;

  // Latch Last
  always @(posedge user_clk_i or negedge user_reset_n_i)
    if (~user_reset_n_i)
      reg_out_data <= #(TCQ) {RAM_WIDTH{1'b0}};
    else
      if (read_data_valid)
        reg_out_data <= #(TCQ) ram_read_data;
      else
	reg_out_data <= #(TCQ) 'h0;

  // Assignments

  assign in_fsm_state_w = reg_in_fsm_state;
  assign data_o = reg_out_data;
  assign prev_data_w = reg_prev_data; 
  
endmodule // pcie3_ccm_fifo
