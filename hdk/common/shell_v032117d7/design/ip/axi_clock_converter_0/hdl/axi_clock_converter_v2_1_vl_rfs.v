// -- (c) Copyright 2011 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Register Slice
//   Generic single-channel AXI pipeline register on forward and/or reverse signal path
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axic_sync_clock_converter
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_clock_converter_v2_1_10_axic_sync_clock_converter # (
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  parameter C_FAMILY     = "virtex6",
  parameter integer C_PAYLOAD_WIDTH = 32,
  parameter integer C_S_ACLK_RATIO = 1,
  parameter integer C_M_ACLK_RATIO = 1 ,
  parameter integer C_MODE = 0  // 0 = light-weight (1-deep); 1 = fully-pipelined (2-deep)
  )
 (
///////////////////////////////////////////////////////////////////////////////
// Port Declarations
///////////////////////////////////////////////////////////////////////////////
  input wire                    SAMPLE_CYCLE_EARLY,
  input wire                    SAMPLE_CYCLE,
  // Slave side
  input  wire                        S_ACLK,
  input  wire                        S_ARESETN,
  input  wire [C_PAYLOAD_WIDTH-1:0] S_PAYLOAD,
  input  wire                        S_VALID,
  output wire                        S_READY,

  // Master side
  input  wire                        M_ACLK,
  input  wire                        M_ARESETN,
  output wire [C_PAYLOAD_WIDTH-1:0] M_PAYLOAD,
  output wire                        M_VALID,
  input  wire                        M_READY
);

////////////////////////////////////////////////////////////////////////////////
// Functions
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam [1:0] ZERO = 2'b10;
localparam [1:0] ONE  = 2'b11;
localparam [1:0] TWO  = 2'b01;
localparam [1:0] INIT = 2'b00;
localparam integer P_LIGHT_WT = 0;
localparam integer P_FULLY_REG = 1;

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////

generate
  if (C_S_ACLK_RATIO == C_M_ACLK_RATIO) begin : gen_passthru
    assign M_PAYLOAD = S_PAYLOAD;
    assign M_VALID   = S_VALID;
    assign S_READY   = M_READY;      
  end else begin : gen_sync_clock_converter
    wire s_sample_cycle;
    wire s_sample_cycle_early;
    wire m_sample_cycle;
    wire m_sample_cycle_early;

    wire slow_aclk;
    wire slow_areset;
    wire s_areset_r;
    wire m_areset_r;
   
    reg  s_tready_r; 
    wire s_tready_ns; 
    reg  m_tvalid_r; 
    wire m_tvalid_ns; 
    reg  [C_PAYLOAD_WIDTH-1:0] m_tpayload_r;
    reg  [C_PAYLOAD_WIDTH-1:0] m_tstorage_r;
    wire [C_PAYLOAD_WIDTH-1:0] m_tpayload_ns; 
    wire [C_PAYLOAD_WIDTH-1:0] m_tstorage_ns; 
    reg  m_tready_hold;
    wire m_tready_sample;
    wire load_tpayload;
    wire load_tstorage;
    wire load_tpayload_from_tstorage;
    reg [1:0] state;
    reg [1:0] next_state;
    
    reg s_aresetn_r = 1'b0; // Reset delay register
    always @(posedge S_ACLK) begin
      if (~S_ARESETN | ~M_ARESETN) begin
        s_aresetn_r <= 1'b0;
      end else begin
        s_aresetn_r <= S_ARESETN & M_ARESETN;
      end
    end
    assign s_areset_r = ~s_aresetn_r;

    reg m_aresetn_r = 1'b0; // Reset delay register
    always @(posedge M_ACLK) begin
      if (~S_ARESETN | ~M_ARESETN) begin
        m_aresetn_r <= 1'b0;
      end else begin
        m_aresetn_r <= S_ARESETN & M_ARESETN;
      end
    end
    assign m_areset_r = ~m_aresetn_r;

    if (C_S_ACLK_RATIO > C_M_ACLK_RATIO) begin : gen_slowclk_mi
      assign slow_aclk = M_ACLK;
    end else begin : gen_slowclk_si
      assign slow_aclk = S_ACLK;
    end
  
    assign slow_areset = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? m_areset_r : s_areset_r;
    assign s_sample_cycle_early = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? SAMPLE_CYCLE_EARLY : 1'b1;
    assign s_sample_cycle       = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? SAMPLE_CYCLE : 1'b1;
    assign m_sample_cycle_early = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? 1'b1 : SAMPLE_CYCLE_EARLY;
    assign m_sample_cycle       = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? 1'b1 : SAMPLE_CYCLE;

    // Output flop for S_READY, value is encoded into state machine.
    assign s_tready_ns = (C_S_ACLK_RATIO > C_M_ACLK_RATIO) ? state[1] & (state != INIT) : next_state[1];

    always @(posedge S_ACLK) begin 
      if (s_areset_r) begin
        s_tready_r <= 1'b0;
      end
      else begin
        s_tready_r <= s_sample_cycle_early ? s_tready_ns : 1'b0;
      end
    end

    assign S_READY = s_tready_r;

    // Output flop for M_VALID
    assign m_tvalid_ns = next_state[0];

    always @(posedge M_ACLK) begin 
      if (m_areset_r) begin
        m_tvalid_r <= 1'b0;
      end
      else begin
        m_tvalid_r <= m_sample_cycle ? m_tvalid_ns : m_tvalid_r & ~M_READY;
      end
    end

    assign M_VALID = m_tvalid_r;

    // Hold register for M_READY when M_ACLK is fast.
    always @(posedge M_ACLK) begin 
      if (m_areset_r) begin
        m_tready_hold <= 1'b0;
      end
      else begin
        m_tready_hold <= m_sample_cycle ? 1'b0 : m_tready_sample;
      end
    end

    assign m_tready_sample = (M_READY ) | m_tready_hold;
    // Output/storage flops for PAYLOAD
    assign m_tpayload_ns = ~load_tpayload ? m_tpayload_r :
                           load_tpayload_from_tstorage ? m_tstorage_r : 
                           S_PAYLOAD;

    assign m_tstorage_ns = C_MODE ? (load_tstorage ? S_PAYLOAD : m_tstorage_r) : 0;

    always @(posedge slow_aclk) begin 
      m_tpayload_r <= m_tpayload_ns;
      m_tstorage_r <= C_MODE ? m_tstorage_ns : 0;
    end

    assign M_PAYLOAD = m_tpayload_r;

    // load logic
    assign load_tstorage = C_MODE && (state != TWO);
    assign load_tpayload = m_tready_sample || (state == ZERO);
    assign load_tpayload_from_tstorage = C_MODE && (state == TWO) && m_tready_sample;
    
    // State machine
    always @(posedge slow_aclk) begin 
      state <= next_state;
    end

    always @* begin 
      if (slow_areset) begin 
        next_state = INIT;
      end else begin
        case (state)
          INIT: begin
            next_state = ZERO;
          end
          // No transaction stored locally
          ZERO: begin
            if (S_VALID) begin
              next_state = C_MODE ? ONE : TWO; // Push from empty
            end
            else begin
              next_state = ZERO;
            end
          end

          // One transaction stored locally
          ONE: begin
            if (C_MODE == 0) begin
              next_state = TWO;  // State ONE is inaccessible when C_MODE=0
            end 
            else if (m_tready_sample & ~S_VALID) begin 
              next_state = ZERO; // Read out one so move to ZERO
            end
            else if (~m_tready_sample & S_VALID) begin
              next_state = TWO;  // Got another one so move to TWO
            end
            else begin
              next_state = ONE;
            end
          end

          // Storage registers full
          TWO: begin 
            if (m_tready_sample) begin
              next_state = C_MODE ? ONE : ZERO; // Pop from full
            end
            else begin
              next_state = TWO;
            end
          end
        endcase // case (state)
      end
    end
  end // gen_sync_clock_converter
  endgenerate
endmodule

`default_nettype wire



// -- (c) Copyright 2011 - 2012 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Register Slice
//   Generic single-channel AXI pipeline register on forward and/or reverse signal path
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axic_sample_cycle_ratio
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_clock_converter_v2_1_10_axic_sample_cycle_ratio # (
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  parameter C_RATIO = 2 // Must be > 0
  )
 (
///////////////////////////////////////////////////////////////////////////////
// Port Declarations
///////////////////////////////////////////////////////////////////////////////
  input  wire                    SLOW_ACLK,
  input  wire                    FAST_ACLK,

  output wire                    SAMPLE_CYCLE_EARLY,
  output wire                    SAMPLE_CYCLE
);

////////////////////////////////////////////////////////////////////////////////
// Functions
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam P_DELAY = C_RATIO > 2 ? C_RATIO-1 : C_RATIO-1; 
////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
reg                slow_aclk_div2 = 0;
reg                posedge_finder_first;
reg                posedge_finder_second;
wire               first_edge;
wire               second_edge;
reg  [P_DELAY-1:0] sample_cycle_d;
(* shreg_extract = "no" *) reg                sample_cycle_r;


////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
generate
  if (C_RATIO == 1) begin : gen_always_sample
    assign SAMPLE_CYCLE_EARLY = 1'b1;
    assign SAMPLE_CYCLE = 1'b1;
  end
  else begin : gen_sample_cycle
    genvar i;
    always @(posedge SLOW_ACLK) begin 
      slow_aclk_div2 <= ~slow_aclk_div2;
    end

    // Find matching rising edges by clocking slow_aclk_div2 onto faster clock
    always @(posedge FAST_ACLK) begin 
      posedge_finder_first <= slow_aclk_div2;
    end
    always @(posedge FAST_ACLK) begin 
      posedge_finder_second <= ~slow_aclk_div2;
    end

    assign first_edge = slow_aclk_div2 & ~posedge_finder_first;
    assign second_edge = ~slow_aclk_div2 & ~posedge_finder_second;

    always @(*) begin 
      sample_cycle_d[P_DELAY-1] = first_edge | second_edge;
    end
   
    // delay the posedge alignment by C_RATIO - 1 to set the sample cycle as
    // the clock one cycle before the posedge.
    for (i = P_DELAY-1; i > 0; i = i - 1) begin : gen_delay
      always @(posedge FAST_ACLK) begin
        sample_cycle_d[i-1] <= sample_cycle_d[i];
      end
    end

    always @(posedge FAST_ACLK) begin 
      sample_cycle_r <= sample_cycle_d[0];
    end
    assign SAMPLE_CYCLE_EARLY = sample_cycle_d[0];
    assign SAMPLE_CYCLE = sample_cycle_r;
  end
endgenerate

endmodule // axisc_sample_cycle_ratio

`default_nettype wire


// -- (c) Copyright 2010 - 2016 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Clock converter module
//   Asynchronous clock converter when asynchronous M:N conversion
//   Bypass when synchronous and ratio between S and M clock is 1:1
//   Synchronous clock converter (S:M or M:S must be integer ratio)
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axi_clock_conv
//     fifo_generator
//     axic_sync_clock_converter
//       axic_sample_cycle_ratio
//
// PROTECTED NAMES:
//   Instance names "asyncfifo_*" are pattern-matched in core-level UCF.
//   Signal names "*_resync" are pattern-matched in core-level UCF.
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_clock_converter_v2_1_10_lite_async #(
  parameter integer C_DEST_SYNC_FF = 2,
  parameter integer C_SRC_SYNC_FF  = 2,
  parameter integer C_WIDTH        = 1
) (
  input wire                s_aclk,
  input wire                m_aclk,
  input wire                s_aresetn,
  input wire                m_aresetn,
  input wire                s_valid,
  output reg                s_ready,
  input wire [C_WIDTH-1:0]  s_payld,
  output reg                m_valid,
  input wire                m_ready,
  output wire [C_WIDTH-1:0] m_payld
);

reg   src_send = 1'b0;
reg   dest_ack = 1'b0;
wire  src_rcv;
wire  dest_req;

localparam SRC_IDLE           = 2'b00;
localparam SRC_DRV_SEND       = 2'b01;
localparam SRC_WAIT_RCV_DONE  = 2'b10;
reg [1:0] src_state = SRC_IDLE;

always @(posedge s_aclk) begin
  if (s_aresetn == 1'b0) begin
    s_ready <= 1'b0;
    src_send <= 1'b0;
    src_state <= SRC_IDLE;
  end else begin
    case (src_state)
      SRC_IDLE: begin
        if (s_valid) begin
          src_state <= SRC_DRV_SEND;
          src_send <= 1'b1;
        end
      end
      SRC_DRV_SEND: begin
        if (src_rcv) begin
          s_ready <= 1'b1;
          src_send <= 1'b0;
          src_state <= SRC_WAIT_RCV_DONE;
        end
      end
      SRC_WAIT_RCV_DONE: begin
        s_ready <= 1'b0;
        if (s_valid & !src_rcv) begin
          src_state <= SRC_DRV_SEND;
          src_send <= 1'b1;
        end else if (!src_rcv) begin
          src_state <= SRC_IDLE;
        end
      end
      default: begin
        s_ready <= 1'b0;
        src_send <= 1'b0;
        src_state <= SRC_IDLE;
      end
    endcase
  end
end

localparam DEST_IDLE           = 2'b00;
localparam DEST_DRV_VALID      = 2'b01;
localparam DEST_DRV_ACK        = 2'b10;
reg [1:0] dest_state = DEST_IDLE;

always @(posedge m_aclk) begin
  if (m_aresetn == 1'b0) begin
    m_valid <= 1'b0;
    dest_ack <= 1'b0;
    dest_state <= DEST_IDLE;
  end else begin
    case (dest_state)
      DEST_IDLE: begin
        if (dest_req) begin
          dest_state <= DEST_DRV_VALID;
          m_valid <= 1'b1;
        end else begin
          m_valid <= 1'b0;
          dest_ack <= 1'b0;
        end
      end
      DEST_DRV_VALID: begin
        if (m_ready & m_valid) begin
          dest_state <= DEST_DRV_ACK;
          m_valid <= 1'b0;
          dest_ack <= 1'b1;
        end
      end
      DEST_DRV_ACK: begin
        if (!dest_req) begin
          dest_state <= DEST_IDLE;
          dest_ack <= 1'b0;
        end
      end
      default: begin
        m_valid <= 1'b0;
        dest_ack <= 1'b0;
        dest_state <= DEST_IDLE;
      end
    endcase
  end
end

xpm_cdc_handshake #(
  .DEST_SYNC_FF   (C_DEST_SYNC_FF),
  .SRC_SYNC_FF    (C_SRC_SYNC_FF),
  .WIDTH          (C_WIDTH)
) handshake (
  .src_clk  (s_aclk),
  .src_in   (s_payld),
  .src_send (src_send),
  .src_rcv  (src_rcv),
  .dest_clk (m_aclk),
  .dest_out (m_payld),
  .dest_req (dest_req),
  .dest_ack (dest_ack)
);

endmodule



(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_clock_converter_v2_1_10_axi_clock_converter #
  (parameter         C_FAMILY = "virtex7",
   parameter integer C_AXI_ID_WIDTH = 5,                    // Width of all ID signals on SI and MI side.
                                                            // Range: >= 1.
   parameter integer C_AXI_ADDR_WIDTH = 32,                 // Width of s_axi_awaddr, s_axi_araddr, m_axi_awaddr and
                                                            // m_axi_araddr.
                                                            // Range: 32.
   parameter integer C_AXI_DATA_WIDTH = 32,       // Width of WDATA and RDATA (either side).
                                                            // Format: Bit32;
                                                            // Range: 'h00000020, 'h00000040, 'h00000080, 'h00000100.
   parameter integer C_S_AXI_ACLK_RATIO = 1,     // Clock frequency ratio of SI w.r.t. MI.
   parameter integer C_M_AXI_ACLK_RATIO = 1,     // (Slowest of all clock inputs should have ratio=1.)
                                                            // S:M or M:S must be integer ratio.
                                                            // Format: Bit32; Range: >='h00000001.
   parameter integer C_AXI_IS_ACLK_ASYNC = 1,            // Indicates whether S and M clocks are asynchronous.
                                                            // FUTURE FEATURE
                                                            // Format: Bit1. Range = 1'b0.
   parameter integer C_AXI_PROTOCOL = 0,         // Protocol of this SI/MI slot.
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS  = 1,      // 1 = Propagate all USER signals, 0 = Do not propagate.
   parameter integer C_AXI_AWUSER_WIDTH = 1,                // Width of AWUSER signals.
                                                            // Range: >= 1.
   parameter integer C_AXI_ARUSER_WIDTH = 1,                // Width of ARUSER signals.
                                                            // Range: >= 1.
   parameter integer C_AXI_WUSER_WIDTH = 1,                 // Width of WUSER signals.
                                                            // Range: >= 1.
   parameter integer C_AXI_RUSER_WIDTH = 1,                 // Width of RUSER signals.
                                                            // Range: >= 1.
   parameter integer C_AXI_BUSER_WIDTH = 1,                 // Width of BUSER signals.
                                                            // Range: >= 1.
   parameter integer C_AXI_SUPPORTS_WRITE = 1,              // Implement AXI write channels
   parameter integer C_AXI_SUPPORTS_READ = 1,               // Implement AXI read channels
   parameter integer C_SYNCHRONIZER_STAGE = 3
  )

  (
   // Slave Interface System Signals
   (* KEEP = "TRUE" *) input  wire        s_axi_aclk,
   (* KEEP = "TRUE" *) input  wire        s_axi_aresetn,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]       s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_awlen,
   input  wire [3-1:0]                  s_axi_awsize,
   input  wire [2-1:0]                  s_axi_awburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_awlock,
   input  wire [4-1:0]                    s_axi_awcache,
   input  wire [3-1:0]                    s_axi_awprot,
   input  wire [4-1:0]                    s_axi_awregion,
   input  wire [4-1:0]                    s_axi_awqos,
   input  wire [C_AXI_AWUSER_WIDTH-1:0]   s_axi_awuser,
   input  wire                            s_axi_awvalid,
   output wire                            s_axi_awready,

   // Slave Interface Write Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]       s_axi_wid,
   input  wire [C_AXI_DATA_WIDTH-1:0]     s_axi_wdata,
   input  wire [C_AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
   input  wire                            s_axi_wlast,
   input  wire [C_AXI_WUSER_WIDTH-1:0]    s_axi_wuser,
   input  wire                            s_axi_wvalid,
   output wire                            s_axi_wready,

   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]       s_axi_bid,
   output wire [2-1:0]                    s_axi_bresp,
   output wire [C_AXI_BUSER_WIDTH-1:0]    s_axi_buser,
   output wire                            s_axi_bvalid,
   input  wire                            s_axi_bready,

   // Slave Interface Read Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]       s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] s_axi_arlen,
   input  wire [3-1:0]                    s_axi_arsize,
   input  wire [2-1:0]                    s_axi_arburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] s_axi_arlock,
   input  wire [4-1:0]                    s_axi_arcache,
   input  wire [3-1:0]                    s_axi_arprot,
   input  wire [4-1:0]                    s_axi_arregion,
   input  wire [4-1:0]                    s_axi_arqos,
   input  wire [C_AXI_ARUSER_WIDTH-1:0]   s_axi_aruser,
   input  wire                            s_axi_arvalid,
   output wire                            s_axi_arready,

   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]       s_axi_rid,
   output wire [C_AXI_DATA_WIDTH-1:0]     s_axi_rdata,
   output wire [2-1:0]                    s_axi_rresp,
   output wire                            s_axi_rlast,
   output wire [C_AXI_RUSER_WIDTH-1:0]    s_axi_ruser,
   output wire                            s_axi_rvalid,
   input  wire                            s_axi_rready,

   // Master Interface System Signals
   (* KEEP = "TRUE" *) input  wire        m_axi_aclk,
   (* KEEP = "TRUE" *) input  wire        m_axi_aresetn,

   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]       m_axi_awid,
   output wire [C_AXI_ADDR_WIDTH-1:0]     m_axi_awaddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_awlen,
   output wire [3-1:0]                    m_axi_awsize,
   output wire [2-1:0]                    m_axi_awburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_awlock,
   output wire [4-1:0]                    m_axi_awcache,
   output wire [3-1:0]                    m_axi_awprot,
   output wire [4-1:0]                    m_axi_awregion,
   output wire [4-1:0]                    m_axi_awqos,
   output wire [C_AXI_AWUSER_WIDTH-1:0]   m_axi_awuser,
   output wire                            m_axi_awvalid,
   input  wire                            m_axi_awready,

   // Master Interface Write Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]       m_axi_wid,
   output wire [C_AXI_DATA_WIDTH-1:0]     m_axi_wdata,
   output wire [C_AXI_DATA_WIDTH/8-1:0]   m_axi_wstrb,
   output wire                            m_axi_wlast,
   output wire [C_AXI_WUSER_WIDTH-1:0]    m_axi_wuser,
   output wire                            m_axi_wvalid,
   input  wire                            m_axi_wready,

   // Master Interface Write Response Ports
   input  wire [C_AXI_ID_WIDTH-1:0]       m_axi_bid,
   input  wire [2-1:0]                    m_axi_bresp,
   input  wire [C_AXI_BUSER_WIDTH-1:0]    m_axi_buser,
   input  wire                            m_axi_bvalid,
   output wire                            m_axi_bready,

   // Master Interface Read Address Port
   output wire [C_AXI_ID_WIDTH-1:0]       m_axi_arid,
   output wire [C_AXI_ADDR_WIDTH-1:0]     m_axi_araddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] m_axi_arlen,
   output wire [3-1:0]                    m_axi_arsize,
   output wire [2-1:0]                    m_axi_arburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0] m_axi_arlock,
   output wire [4-1:0]                    m_axi_arcache,
   output wire [3-1:0]                    m_axi_arprot,
   output wire [4-1:0]                    m_axi_arregion,
   output wire [4-1:0]                    m_axi_arqos,
   output wire [C_AXI_ARUSER_WIDTH-1:0]   m_axi_aruser,
   output wire                            m_axi_arvalid,
   input  wire                            m_axi_arready,

   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]       m_axi_rid,
   input  wire [C_AXI_DATA_WIDTH-1:0]     m_axi_rdata,
   input  wire [2-1:0]                    m_axi_rresp,
   input  wire                            m_axi_rlast,
   input  wire [C_AXI_RUSER_WIDTH-1:0]    m_axi_ruser,
   input  wire                            m_axi_rvalid,
   output wire                            m_axi_rready);

  localparam integer P_AXI4 = 0;
  localparam integer P_AXI3 = 1;
  localparam integer P_AXILITE = 2;
  localparam integer P_LIGHT_WT = 0;
  localparam integer P_FULLY_REG = 1;
  localparam integer P_LUTRAM_ASYNC = 12;

  // Sample cycle ratio
  localparam  P_SI_LT_MI = (C_S_AXI_ACLK_RATIO < C_M_AXI_ACLK_RATIO);
  localparam integer P_ROUNDING_OFFSET = P_SI_LT_MI ? (C_S_AXI_ACLK_RATIO/2) : (C_M_AXI_ACLK_RATIO/2);
  localparam integer P_ACLK_RATIO = P_SI_LT_MI ?
    ((C_M_AXI_ACLK_RATIO + P_ROUNDING_OFFSET) / C_S_AXI_ACLK_RATIO) :
    ((C_S_AXI_ACLK_RATIO + P_ROUNDING_OFFSET) / C_M_AXI_ACLK_RATIO);

  // Write Address Port bit positions
  localparam integer C_AWUSER_RIGHT   = 0;
  localparam integer C_AWUSER_WIDTH     = (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? C_AXI_AWUSER_WIDTH : 0;
  localparam integer C_AWQOS_RIGHT    = C_AWUSER_RIGHT + C_AWUSER_WIDTH;
  localparam integer C_AWQOS_WIDTH      = (C_AXI_PROTOCOL != P_AXILITE) ? 4 : 0;
  localparam integer C_AWREGION_RIGHT = C_AWQOS_RIGHT + C_AWQOS_WIDTH;
  localparam integer C_AWREGION_WIDTH   = (C_AXI_PROTOCOL == P_AXI4) ? 4 : 0;
  localparam integer C_AWPROT_RIGHT   = C_AWREGION_RIGHT + C_AWREGION_WIDTH;
  localparam integer C_AWPROT_WIDTH     = 3;
  localparam integer C_AWCACHE_RIGHT  = C_AWPROT_RIGHT + C_AWPROT_WIDTH;
  localparam integer C_AWCACHE_WIDTH    = (C_AXI_PROTOCOL != P_AXILITE) ? 4 : 0;
  localparam integer C_AWLOCK_RIGHT   = C_AWCACHE_RIGHT + C_AWCACHE_WIDTH;
  localparam integer C_AWLOCK_WIDTH     = (C_AXI_PROTOCOL == P_AXI4) ? 1 : (C_AXI_PROTOCOL == P_AXI3) ?  2 : 0;
  localparam integer C_AWBURST_RIGHT  = C_AWLOCK_RIGHT + C_AWLOCK_WIDTH;
  localparam integer C_AWBURST_WIDTH    = (C_AXI_PROTOCOL != P_AXILITE) ? 2 : 0;
  localparam integer C_AWSIZE_RIGHT   = C_AWBURST_RIGHT + C_AWBURST_WIDTH;
  localparam integer C_AWSIZE_WIDTH     = (C_AXI_PROTOCOL != P_AXILITE) ? 3 : 0;
  localparam integer C_AWLEN_RIGHT    = C_AWSIZE_RIGHT + C_AWSIZE_WIDTH;
  localparam integer C_AWLEN_WIDTH      = (C_AXI_PROTOCOL == P_AXI4) ? 8 : (C_AXI_PROTOCOL == P_AXI3) ? 4 : 0;
  localparam integer C_AWADDR_RIGHT   = C_AWLEN_RIGHT + C_AWLEN_WIDTH;
  localparam integer C_AWADDR_WIDTH     = C_AXI_ADDR_WIDTH;
  localparam integer C_AWID_RIGHT     = C_AWADDR_RIGHT + C_AWADDR_WIDTH;
  localparam integer C_AWID_WIDTH       = (C_AXI_PROTOCOL != P_AXILITE) ? C_AXI_ID_WIDTH : 0;
  localparam integer C_AW_WIDTH        = C_AWID_RIGHT + C_AWID_WIDTH;
  localparam integer C_FIFO_AW_WIDTH   = C_AWUSER_WIDTH+C_AWQOS_WIDTH+C_AWQOS_WIDTH+3+C_AWCACHE_WIDTH+C_AWLOCK_WIDTH+C_AWBURST_WIDTH+C_AWSIZE_WIDTH+C_AWLEN_WIDTH+C_AXI_ADDR_WIDTH+C_AWID_WIDTH;

  // Write Data Port bit positions
  localparam integer C_WUSER_RIGHT   = 0;
  localparam integer C_WUSER_WIDTH     = (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? C_AXI_WUSER_WIDTH : 0;
  localparam integer C_WLAST_RIGHT   = C_WUSER_RIGHT + C_WUSER_WIDTH;
  localparam integer C_WLAST_WIDTH     = (C_AXI_PROTOCOL != P_AXILITE) ? 1 : 0;
  localparam integer C_WSTRB_RIGHT   = C_WLAST_RIGHT + C_WLAST_WIDTH;
  localparam integer C_WSTRB_WIDTH     = C_AXI_DATA_WIDTH/8;
  localparam integer C_WDATA_RIGHT   = C_WSTRB_RIGHT + C_WSTRB_WIDTH;
  localparam integer C_WDATA_WIDTH     = C_AXI_DATA_WIDTH;
  localparam integer C_WID_RIGHT     = C_WDATA_RIGHT + C_WDATA_WIDTH;
  localparam integer C_WID_WIDTH       = (C_AXI_PROTOCOL == P_AXI3) ? C_AXI_ID_WIDTH : 0;
  localparam integer C_W_WIDTH        = C_WID_RIGHT + C_WID_WIDTH;
  localparam integer C_FIFO_W_WIDTH   = C_WUSER_WIDTH + C_WLAST_WIDTH + C_AXI_DATA_WIDTH/8 + C_AXI_DATA_WIDTH + C_WID_WIDTH;

  // Write Response Port bit positions
  localparam integer C_BUSER_RIGHT   = 0;
  localparam integer C_BUSER_WIDTH     = (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? C_AXI_BUSER_WIDTH : 0;
  localparam integer C_BRESP_RIGHT   = C_BUSER_RIGHT + C_BUSER_WIDTH;
  localparam integer C_BRESP_WIDTH     = 2;
  localparam integer C_BID_RIGHT     = C_BRESP_RIGHT + C_BRESP_WIDTH;
  localparam integer C_BID_WIDTH       = (C_AXI_PROTOCOL != P_AXILITE) ? C_AXI_ID_WIDTH : 0;
  localparam integer C_B_WIDTH        = C_BID_RIGHT + C_BID_WIDTH;
  localparam integer C_FIFO_B_WIDTH    = C_BUSER_WIDTH + 2 + C_BID_WIDTH;

  // Read Address Port bit positions
  localparam integer C_ARUSER_RIGHT   = 0;
  localparam integer C_ARUSER_WIDTH     = (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? C_AXI_ARUSER_WIDTH : 0;
  localparam integer C_ARQOS_RIGHT    = C_ARUSER_RIGHT + C_ARUSER_WIDTH;
  localparam integer C_ARQOS_WIDTH      = (C_AXI_PROTOCOL != P_AXILITE) ? 4 : 0;
  localparam integer C_ARREGION_RIGHT = C_ARQOS_RIGHT + C_ARQOS_WIDTH;
  localparam integer C_ARREGION_WIDTH   = (C_AXI_PROTOCOL == P_AXI4) ? 4 : 0;
  localparam integer C_ARPROT_RIGHT   = C_ARREGION_RIGHT + C_ARREGION_WIDTH;
  localparam integer C_ARPROT_WIDTH     = 3;
  localparam integer C_ARCACHE_RIGHT  = C_ARPROT_RIGHT + C_ARPROT_WIDTH;
  localparam integer C_ARCACHE_WIDTH    = (C_AXI_PROTOCOL != P_AXILITE) ? 4 : 0;
  localparam integer C_ARLOCK_RIGHT   = C_ARCACHE_RIGHT + C_ARCACHE_WIDTH;
  localparam integer C_ARLOCK_WIDTH     = (C_AXI_PROTOCOL == P_AXI4) ? 1 : (C_AXI_PROTOCOL == P_AXI3) ?  2 : 0;
  localparam integer C_ARBURST_RIGHT  = C_ARLOCK_RIGHT + C_ARLOCK_WIDTH;
  localparam integer C_ARBURST_WIDTH    = (C_AXI_PROTOCOL != P_AXILITE) ? 2 : 0;
  localparam integer C_ARSIZE_RIGHT   = C_ARBURST_RIGHT + C_ARBURST_WIDTH;
  localparam integer C_ARSIZE_WIDTH     = (C_AXI_PROTOCOL != P_AXILITE) ? 3 : 0;
  localparam integer C_ARLEN_RIGHT    = C_ARSIZE_RIGHT + C_ARSIZE_WIDTH;
  localparam integer C_ARLEN_WIDTH      = (C_AXI_PROTOCOL == P_AXI4) ? 8 : (C_AXI_PROTOCOL == P_AXI3) ? 4 : 0;
  localparam integer C_ARADDR_RIGHT   = C_ARLEN_RIGHT + C_ARLEN_WIDTH;
  localparam integer C_ARADDR_WIDTH     = C_AXI_ADDR_WIDTH;
  localparam integer C_ARID_RIGHT     = C_ARADDR_RIGHT + C_ARADDR_WIDTH;
  localparam integer C_ARID_WIDTH       = (C_AXI_PROTOCOL != P_AXILITE) ? C_AXI_ID_WIDTH : 0;
  localparam integer C_AR_WIDTH        = C_ARID_RIGHT + C_ARID_WIDTH;
  localparam integer C_FIFO_AR_WIDTH   = C_ARUSER_WIDTH+C_ARQOS_WIDTH+C_ARQOS_WIDTH+3+C_ARCACHE_WIDTH+C_ARLOCK_WIDTH+C_ARBURST_WIDTH+C_ARSIZE_WIDTH+C_ARLEN_WIDTH+C_AXI_ADDR_WIDTH+C_ARID_WIDTH;

  // Read Data Ports bit positions
  localparam integer C_RUSER_RIGHT   = 0;
  localparam integer C_RUSER_WIDTH     = (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? C_AXI_RUSER_WIDTH : 0;
  localparam integer C_RLAST_RIGHT   = C_RUSER_RIGHT + C_RUSER_WIDTH;
  localparam integer C_RLAST_WIDTH     = (C_AXI_PROTOCOL != P_AXILITE) ? 1 : 0;
  localparam integer C_RRESP_RIGHT   = C_RLAST_RIGHT + C_RLAST_WIDTH;
  localparam integer C_RRESP_WIDTH     = 2;
  localparam integer C_RDATA_RIGHT   = C_RRESP_RIGHT + C_RRESP_WIDTH;
  localparam integer C_RDATA_WIDTH     = C_AXI_DATA_WIDTH;
  localparam integer C_RID_RIGHT     = C_RDATA_RIGHT + C_RDATA_WIDTH;
  localparam integer C_RID_WIDTH       = (C_AXI_PROTOCOL != P_AXILITE) ? C_AXI_ID_WIDTH : 0;
  localparam integer C_R_WIDTH        = C_RID_RIGHT + C_RID_WIDTH;
  localparam integer C_FIFO_R_WIDTH   = C_RUSER_WIDTH + C_RLAST_WIDTH + 2 + C_AXI_DATA_WIDTH + C_RID_WIDTH;

  generate
    if ((C_AXI_IS_ACLK_ASYNC == 0) && (P_ACLK_RATIO == 1)) begin : gen_bypass
      
      // Write address port
      assign m_axi_awid     = s_axi_awid;
      assign m_axi_awaddr   = s_axi_awaddr;
      assign m_axi_awlen    = s_axi_awlen;
      assign m_axi_awsize   = s_axi_awsize;
      assign m_axi_awburst  = s_axi_awburst;
      assign m_axi_awlock   = s_axi_awlock;
      assign m_axi_awcache  = s_axi_awcache;
      assign m_axi_awprot   = s_axi_awprot;
      assign m_axi_awregion = s_axi_awregion;
      assign m_axi_awqos    = s_axi_awqos;
      assign m_axi_awuser   = s_axi_awuser;
      assign m_axi_awvalid  = s_axi_awvalid;
      assign s_axi_awready  = m_axi_awready;

      // Write Data Port
      assign m_axi_wid      = s_axi_wid;
      assign m_axi_wdata    = s_axi_wdata;
      assign m_axi_wstrb    = s_axi_wstrb;
      assign m_axi_wlast    = s_axi_wlast;
      assign m_axi_wuser    = s_axi_wuser;
      assign m_axi_wvalid   = s_axi_wvalid;
      assign s_axi_wready   = m_axi_wready;

      // Write Response Port
      assign s_axi_bid      = m_axi_bid;
      assign s_axi_bresp    = m_axi_bresp;
      assign s_axi_buser    = m_axi_buser;
      assign s_axi_bvalid   = m_axi_bvalid;
      assign m_axi_bready   = s_axi_bready;

      // Read Address Port
      assign m_axi_arid     = s_axi_arid;
      assign m_axi_araddr   = s_axi_araddr;
      assign m_axi_arlen    = s_axi_arlen;
      assign m_axi_arsize   = s_axi_arsize;
      assign m_axi_arburst  = s_axi_arburst;
      assign m_axi_arlock   = s_axi_arlock;
      assign m_axi_arcache  = s_axi_arcache;
      assign m_axi_arprot   = s_axi_arprot;
      assign m_axi_arregion = s_axi_arregion;
      assign m_axi_arqos    = s_axi_arqos;
      assign m_axi_aruser   = s_axi_aruser;
      assign m_axi_arvalid  = s_axi_arvalid;
      assign s_axi_arready  = m_axi_arready;

      // Read Data Port
      assign s_axi_rid      = m_axi_rid;
      assign s_axi_rdata    = m_axi_rdata;
      assign s_axi_rresp    = m_axi_rresp;
      assign s_axi_rlast    = m_axi_rlast;
      assign s_axi_ruser    = m_axi_ruser;
      assign s_axi_rvalid   = m_axi_rvalid;
      assign m_axi_rready   = s_axi_rready;
      
    end else begin : gen_clock_conv
      
      wire fast_aclk;
      wire slow_aclk;
      wire sample_cycle;
      wire sample_cycle_early;
    
      // Write Address Port FIFO data read and write
      wire [C_AW_WIDTH-1:0] s_aw_mesg ;
      wire [C_AW_WIDTH-1:0] m_aw_mesg ;
    
      // Write Data Port FIFO data read and write
      wire [C_W_WIDTH-1:0] s_w_mesg;
      wire [C_W_WIDTH-1:0] m_w_mesg;
    
      // Write Response Port FIFO data read and write
      wire [C_B_WIDTH-1:0] s_b_mesg;
      wire [C_B_WIDTH-1:0] m_b_mesg;
    
      // Read Address Port FIFO data read and write
      wire [C_AR_WIDTH-1:0] s_ar_mesg;
      wire [C_AR_WIDTH-1:0] m_ar_mesg;
    
      // Read Data Ports FIFO data read and write
      wire [C_R_WIDTH-1:0] s_r_mesg;
      wire [C_R_WIDTH-1:0] m_r_mesg;
    
      wire async_conv_reset_n;
      assign async_conv_reset_n = ~(~s_axi_aresetn | ~m_axi_aresetn);
      
      wire [C_AXI_ID_WIDTH-1:0]          si_cc_awid            ;
      wire [C_AXI_ADDR_WIDTH-1:0]        si_cc_awaddr          ;
      wire [((C_AXI_PROTOCOL!=1)?8:4)-1:0] si_cc_awlen           ;
      wire [3-1:0]                       si_cc_awsize          ;
      wire [2-1:0]                       si_cc_awburst         ;
      wire [((C_AXI_PROTOCOL!=1)?1:2)-1:0] si_cc_awlock          ;
      wire [4-1:0]                       si_cc_awcache         ;
      wire [3-1:0]                       si_cc_awprot          ;
      wire [4-1:0]                       si_cc_awregion        ;
      wire [4-1:0]                       si_cc_awqos           ;
      wire [C_AXI_AWUSER_WIDTH-1:0]      si_cc_awuser          ;
      wire                               si_cc_awvalid         ;
      wire                               si_cc_awready         ;
      wire [C_AXI_ID_WIDTH-1:0]          si_cc_wid            ;
      wire [C_AXI_DATA_WIDTH-1:0]        si_cc_wdata           ;
      wire [C_AXI_DATA_WIDTH/8-1:0]      si_cc_wstrb           ;
      wire                               si_cc_wlast           ;
      wire [C_AXI_WUSER_WIDTH-1:0]       si_cc_wuser           ;
      wire                               si_cc_wvalid          ;
      wire                               si_cc_wready          ;
      wire [C_AXI_ID_WIDTH-1:0]          si_cc_bid             ;
      wire [2-1:0]                       si_cc_bresp           ;
      wire [C_AXI_BUSER_WIDTH-1:0]       si_cc_buser           ;
      wire                               si_cc_bvalid          ;
      wire                               si_cc_bready          ;
      wire [C_AXI_ID_WIDTH-1:0]          si_cc_arid            ;
      wire [C_AXI_ADDR_WIDTH-1:0]        si_cc_araddr          ;
      wire [((C_AXI_PROTOCOL!=1)?8:4)-1:0] si_cc_arlen           ;
      wire [3-1:0]                       si_cc_arsize          ;
      wire [2-1:0]                       si_cc_arburst         ;
      wire [((C_AXI_PROTOCOL!=1)?1:2)-1:0] si_cc_arlock          ;
      wire [4-1:0]                       si_cc_arcache         ;
      wire [3-1:0]                       si_cc_arprot          ;
      wire [4-1:0]                       si_cc_arregion        ;
      wire [4-1:0]                       si_cc_arqos           ;
      wire [C_AXI_ARUSER_WIDTH-1:0]      si_cc_aruser          ;
      wire                               si_cc_arvalid         ;
      wire                               si_cc_arready         ;
      wire [C_AXI_ID_WIDTH-1:0]          si_cc_rid             ;
      wire [C_AXI_DATA_WIDTH-1:0]        si_cc_rdata           ;
      wire [2-1:0]                       si_cc_rresp           ;
      wire                               si_cc_rlast           ;
      wire [C_AXI_RUSER_WIDTH-1:0]       si_cc_ruser           ;
      wire                               si_cc_rvalid          ;
      wire                               si_cc_rready          ;
      
      wire [C_AXI_ID_WIDTH-1:0]         cc_mi_awid            ;
      wire [C_AXI_ADDR_WIDTH-1:0]       cc_mi_awaddr          ;
      wire [((C_AXI_PROTOCOL!=1)?8:4)-1:0] cc_mi_awlen           ;
      wire [3-1:0]                      cc_mi_awsize          ;
      wire [2-1:0]                      cc_mi_awburst         ;
      wire [((C_AXI_PROTOCOL!=1)?1:2)-1:0] cc_mi_awlock          ;
      wire [4-1:0]                      cc_mi_awcache         ;
      wire [3-1:0]                      cc_mi_awprot          ;
      wire [4-1:0]                      cc_mi_awregion        ;
      wire [4-1:0]                      cc_mi_awqos           ;
      wire [C_AXI_AWUSER_WIDTH-1:0]     cc_mi_awuser          ;
      wire                              cc_mi_awvalid         ;
      wire                              cc_mi_awready         ;
      wire [C_AXI_ID_WIDTH-1:0]         cc_mi_wid             ;
      wire [C_AXI_DATA_WIDTH-1:0]       cc_mi_wdata           ;
      wire [C_AXI_DATA_WIDTH/8-1:0]     cc_mi_wstrb           ;
      wire                              cc_mi_wlast           ;
      wire [C_AXI_WUSER_WIDTH-1:0]      cc_mi_wuser           ;
      wire                              cc_mi_wvalid          ;
      wire                              cc_mi_wready          ;
      wire [C_AXI_ID_WIDTH-1:0]         cc_mi_bid             ;
      wire [2-1:0]                      cc_mi_bresp           ;
      wire [C_AXI_BUSER_WIDTH-1:0]      cc_mi_buser           ;
      wire                              cc_mi_bvalid          ;
      wire                              cc_mi_bready          ;
      wire [C_AXI_ID_WIDTH-1:0]         cc_mi_arid            ;
      wire [C_AXI_ADDR_WIDTH-1:0]       cc_mi_araddr          ;
      wire [((C_AXI_PROTOCOL!=1)?8:4)-1:0] cc_mi_arlen           ;
      wire [3-1:0]                      cc_mi_arsize          ;
      wire [2-1:0]                      cc_mi_arburst         ;
      wire [((C_AXI_PROTOCOL!=1)?1:2)-1:0] cc_mi_arlock          ;
      wire [4-1:0]                      cc_mi_arcache         ;
      wire [3-1:0]                      cc_mi_arprot          ;
      wire [4-1:0]                      cc_mi_arregion        ;
      wire [4-1:0]                      cc_mi_arqos           ;
      wire [C_AXI_ARUSER_WIDTH-1:0]     cc_mi_aruser          ;
      wire                              cc_mi_arvalid         ;
      wire                              cc_mi_arready         ;
      wire [C_AXI_ID_WIDTH-1:0]         cc_mi_rid             ;
      wire [C_AXI_DATA_WIDTH-1:0]       cc_mi_rdata           ;
      wire [2-1:0]                      cc_mi_rresp           ;
      wire                              cc_mi_rlast           ;
      wire [C_AXI_RUSER_WIDTH-1:0]      cc_mi_ruser           ;
      wire                              cc_mi_rvalid          ;
      wire                              cc_mi_rready          ;
      
    // Tie-offs
      assign si_cc_awid      = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_awid : 0 ;
      assign si_cc_awaddr    = (C_AXI_SUPPORTS_WRITE ) ? s_axi_awaddr : 0 ;
      assign si_cc_awlen     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE)) ? ((C_AXI_PROTOCOL!=P_AXI3 ) ? s_axi_awlen : {4'b0000, s_axi_awlen[3:0]}) : 0 ;
      assign si_cc_awsize    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_awsize : 0 ;
      assign si_cc_awburst   = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_awburst : 0 ;
      assign si_cc_awlock    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? ((C_AXI_PROTOCOL==P_AXI3) ? s_axi_awlock : {1'b0, s_axi_awlock[0]}) : 0 ;
      assign si_cc_awcache   = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_awcache : 0 ;
      assign si_cc_awprot    = (C_AXI_SUPPORTS_WRITE ) ? s_axi_awprot : 0 ;
      assign si_cc_awqos     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_awqos : 0 ;
      assign si_cc_awregion  = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL==P_AXI4) ) ? s_axi_awregion : 0 ;
      assign si_cc_awuser    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? s_axi_awuser : 0 ;
      assign si_cc_awvalid   = (C_AXI_SUPPORTS_WRITE ) ? s_axi_awvalid : 0 ;
      assign si_cc_wid       = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL==P_AXI3) ) ? s_axi_wid : 0 ;
      assign si_cc_wdata     = (C_AXI_SUPPORTS_WRITE ) ? s_axi_wdata : 0 ;
      assign si_cc_wstrb     = (C_AXI_SUPPORTS_WRITE ) ? s_axi_wstrb : 0 ;
      assign si_cc_wlast     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_wlast : 1'b0 ;
      assign si_cc_wuser     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? s_axi_wuser : 0 ;
      assign si_cc_wvalid    = (C_AXI_SUPPORTS_WRITE ) ? s_axi_wvalid : 0 ;
      assign si_cc_bready    = (C_AXI_SUPPORTS_WRITE ) ? s_axi_bready : 0 ;
      assign si_cc_arid      = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_arid : 0 ;
      assign si_cc_araddr    = (C_AXI_SUPPORTS_READ ) ? s_axi_araddr : 0 ;
      assign si_cc_arlen     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE)) ? ((C_AXI_PROTOCOL!=P_AXI3 ) ? s_axi_arlen : {4'b0000, s_axi_arlen[3:0]}) : 0 ;
      assign si_cc_arsize    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_arsize : 0 ;
      assign si_cc_arburst   = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_arburst : 0 ;
      assign si_cc_arlock    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? ((C_AXI_PROTOCOL==P_AXI3) ? s_axi_arlock : {1'b0, s_axi_arlock[0]}) : 0 ;
      assign si_cc_arcache   = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_arcache : 0 ;
      assign si_cc_arprot    = (C_AXI_SUPPORTS_READ ) ? s_axi_arprot : 0 ;
      assign si_cc_arqos     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? s_axi_arqos : 0 ;
      assign si_cc_arregion  = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL==P_AXI4) ) ? s_axi_arregion : 0 ;
      assign si_cc_aruser    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? s_axi_aruser : 0 ;
      assign si_cc_arvalid   = (C_AXI_SUPPORTS_READ ) ? s_axi_arvalid : 0 ;
      assign si_cc_rready    = (C_AXI_SUPPORTS_READ ) ? s_axi_rready : 0 ;                                       
                                                                                               
      assign s_axi_awready   = (C_AXI_SUPPORTS_WRITE ) ? si_cc_awready : 0 ;
      assign s_axi_wready    = (C_AXI_SUPPORTS_WRITE ) ? si_cc_wready : 0 ;
      assign s_axi_bid       = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? si_cc_bid : 0 ;
      assign s_axi_bresp     = (C_AXI_SUPPORTS_WRITE ) ? si_cc_bresp : 0 ;
      assign s_axi_buser     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? si_cc_buser : 0 ;
      assign s_axi_bvalid    = (C_AXI_SUPPORTS_WRITE ) ? si_cc_bvalid : 0 ;
      assign s_axi_arready   = (C_AXI_SUPPORTS_READ ) ? si_cc_arready : 0 ;
      assign s_axi_rid       = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? si_cc_rid : 0 ;
      assign s_axi_rdata     = (C_AXI_SUPPORTS_READ ) ? si_cc_rdata : 0 ;
      assign s_axi_rresp     = (C_AXI_SUPPORTS_READ ) ? si_cc_rresp : 0 ;
      assign s_axi_rlast     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? si_cc_rlast : 0 ;
      assign s_axi_ruser     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? si_cc_ruser : 0 ;
      assign s_axi_rvalid    = (C_AXI_SUPPORTS_READ ) ? si_cc_rvalid : 0 ;

      assign m_axi_awid      = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_awid : 0 ;
      assign m_axi_awaddr    = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_awaddr : 0 ;
      assign m_axi_awlen     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE)) ? ((C_AXI_PROTOCOL!=P_AXI3 ) ? cc_mi_awlen : cc_mi_awlen[3:0]) : 0 ;
      assign m_axi_awsize    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_awsize : 0 ;
      assign m_axi_awburst   = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_awburst : 0 ;
      assign m_axi_awlock    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? ((C_AXI_PROTOCOL==P_AXI3) ? cc_mi_awlock : cc_mi_awlock[0]) : 0 ;
      assign m_axi_awcache   = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_awcache : 0 ;
      assign m_axi_awprot    = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_awprot : 0 ;
      assign m_axi_awregion  = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL==P_AXI4) ) ? cc_mi_awregion : 0 ;
      assign m_axi_awqos     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_awqos : 0 ;
      assign m_axi_awuser    = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? cc_mi_awuser : 0 ;
      assign m_axi_awvalid   = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_awvalid : 0 ;
      assign m_axi_wid       = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL==P_AXI3) ) ? cc_mi_wid : 0 ;
      assign m_axi_wdata     = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_wdata : 0 ;
      assign m_axi_wstrb     = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_wstrb : 0 ;
      assign m_axi_wlast     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_wlast : 0 ;
      assign m_axi_wuser     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? cc_mi_wuser : 0 ;
      assign m_axi_wvalid    = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_wvalid : 0 ;
      assign m_axi_bready    = (C_AXI_SUPPORTS_WRITE ) ? cc_mi_bready : 0 ;
      assign m_axi_arid      = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_arid : 0 ;
      assign m_axi_araddr    = (C_AXI_SUPPORTS_READ ) ? cc_mi_araddr : 0 ;
      assign m_axi_arlen     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE)) ? ((C_AXI_PROTOCOL!=P_AXI3 ) ? cc_mi_arlen : cc_mi_arlen[3:0]) : 0 ;
      assign m_axi_arsize    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_arsize : 0 ;
      assign m_axi_arburst   = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_arburst : 0 ;
      assign m_axi_arlock    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? ((C_AXI_PROTOCOL==P_AXI3) ? cc_mi_arlock : cc_mi_arlock[0]) : 0 ;
      assign m_axi_arcache   = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_arcache : 0 ;
      assign m_axi_arprot    = (C_AXI_SUPPORTS_READ ) ? cc_mi_arprot : 0 ;
      assign m_axi_arregion  = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL==P_AXI4) ) ? cc_mi_arregion : 0 ;
      assign m_axi_arqos     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? cc_mi_arqos : 0 ;
      assign m_axi_aruser    = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? cc_mi_aruser : 0 ;
      assign m_axi_arvalid   = (C_AXI_SUPPORTS_READ ) ? cc_mi_arvalid : 0 ;
      assign m_axi_rready    = (C_AXI_SUPPORTS_READ ) ? cc_mi_rready : 0 ;
                                                                                                                                                                                                                                                                                        
      assign cc_mi_awready   = (C_AXI_SUPPORTS_WRITE ) ? m_axi_awready : 0 ;
      assign cc_mi_wready    = (C_AXI_SUPPORTS_WRITE ) ? m_axi_wready : 0 ;
      assign cc_mi_bid       = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) ) ? m_axi_bid : 0 ;
      assign cc_mi_bresp     = (C_AXI_SUPPORTS_WRITE ) ? m_axi_bresp : 0 ;
      assign cc_mi_buser     = (C_AXI_SUPPORTS_WRITE && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? m_axi_buser : 0 ;
      assign cc_mi_bvalid    = (C_AXI_SUPPORTS_WRITE ) ? m_axi_bvalid : 0 ;
      assign cc_mi_arready   = (C_AXI_SUPPORTS_READ ) ? m_axi_arready : 0 ;
      assign cc_mi_rid       = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? m_axi_rid : 0 ;
      assign cc_mi_rdata     = (C_AXI_SUPPORTS_READ ) ? m_axi_rdata : 0 ;
      assign cc_mi_rresp     = (C_AXI_SUPPORTS_READ ) ? m_axi_rresp : 0 ;
      assign cc_mi_rlast     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) ) ? m_axi_rlast : 1'b0 ;
      assign cc_mi_ruser     = (C_AXI_SUPPORTS_READ && (C_AXI_PROTOCOL!=P_AXILITE) && (C_AXI_SUPPORTS_USER_SIGNALS!=0) ) ? m_axi_ruser : 0 ;
      assign cc_mi_rvalid    = (C_AXI_SUPPORTS_READ ) ? m_axi_rvalid : 0 ;
      
      if ((C_AXI_IS_ACLK_ASYNC) && (C_AXI_PROTOCOL!=P_AXILITE)) begin : gen_async_conv
        
        fifo_generator_v13_1_3 #(
          .C_INTERFACE_TYPE(2),
          .C_AXI_TYPE((C_AXI_PROTOCOL == P_AXI4) ? 1 : (C_AXI_PROTOCOL == P_AXI3) ? 3 : 2),
          .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
          .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
          .C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
          .C_AXI_ARUSER_WIDTH(C_AXI_ARUSER_WIDTH),
          .C_AXI_AWUSER_WIDTH(C_AXI_AWUSER_WIDTH),
          .C_AXI_BUSER_WIDTH(C_AXI_BUSER_WIDTH),
          .C_AXI_RUSER_WIDTH(C_AXI_RUSER_WIDTH),
          .C_AXI_WUSER_WIDTH(C_AXI_WUSER_WIDTH),
          .C_HAS_AXI_ID((C_AXI_PROTOCOL != P_AXILITE) ? 1 : 0),
          .C_AXI_LEN_WIDTH((C_AXI_PROTOCOL != P_AXI3) ? 8 : 4),
          .C_AXI_LOCK_WIDTH((C_AXI_PROTOCOL != P_AXI3) ? 1 : 2),
          .C_HAS_AXI_ARUSER((C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? 1 : 0),
          .C_HAS_AXI_AWUSER((C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? 1 : 0),
          .C_HAS_AXI_BUSER((C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? 1 : 0),
          .C_HAS_AXI_RUSER((C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? 1 : 0),
          .C_HAS_AXI_WUSER((C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) ? 1 : 0),
          .C_DIN_WIDTH_RACH(C_FIFO_AR_WIDTH),
          .C_DIN_WIDTH_RDCH(C_FIFO_R_WIDTH),
          .C_DIN_WIDTH_WACH(C_FIFO_AW_WIDTH),
          .C_DIN_WIDTH_WDCH(C_FIFO_W_WIDTH),
          .C_DIN_WIDTH_WRCH(C_FIFO_B_WIDTH),
          .C_HAS_AXI_RD_CHANNEL(C_AXI_SUPPORTS_READ),
          .C_HAS_AXI_WR_CHANNEL(C_AXI_SUPPORTS_WRITE),
          .C_RACH_TYPE(C_AXI_SUPPORTS_READ ? 0 : 2),
          .C_RDCH_TYPE(C_AXI_SUPPORTS_READ ? 0 : 2),
          .C_WACH_TYPE(C_AXI_SUPPORTS_WRITE ? 0 : 2),
          .C_WDCH_TYPE(C_AXI_SUPPORTS_WRITE ? 0 : 2),
          .C_WRCH_TYPE(C_AXI_SUPPORTS_WRITE ? 0 : 2),
          .C_SYNCHRONIZER_STAGE(C_SYNCHRONIZER_STAGE),
          .C_COMMON_CLOCK(0),
          .C_COUNT_TYPE(0),
          .C_DATA_COUNT_WIDTH(10),
          .C_DEFAULT_VALUE("BlankString"),
          .C_DIN_WIDTH(18),
          .C_DOUT_RST_VAL("0"),
          .C_DOUT_WIDTH(18),
          .C_ENABLE_RLOCS(0),
          .C_FAMILY(C_FAMILY),
          .C_FULL_FLAGS_RST_VAL(1),
          .C_HAS_ALMOST_EMPTY(0),
          .C_HAS_ALMOST_FULL(0),
          .C_HAS_BACKUP(0),
          .C_HAS_DATA_COUNT(0),
          .C_HAS_INT_CLK(0),
          .C_HAS_MEMINIT_FILE(0),
          .C_HAS_OVERFLOW(0),
          .C_HAS_RD_DATA_COUNT(0),
          .C_HAS_RD_RST(0),
          .C_HAS_RST(1),
          .C_HAS_SRST(0),
          .C_HAS_UNDERFLOW(0),
          .C_HAS_VALID(0),
          .C_HAS_WR_ACK(0),
          .C_HAS_WR_DATA_COUNT(0),
          .C_HAS_WR_RST(0),
          .C_IMPLEMENTATION_TYPE(0),
          .C_INIT_WR_PNTR_VAL(0),
          .C_MEMORY_TYPE(1),
          .C_MIF_FILE_NAME("BlankString"),
          .C_OPTIMIZATION_MODE(0),
          .C_OVERFLOW_LOW(0),
          .C_PRELOAD_LATENCY(1),
          .C_PRELOAD_REGS(0),
          .C_PRIM_FIFO_TYPE("4kx4"),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL(2),
          .C_PROG_EMPTY_THRESH_NEGATE_VAL(3),
          .C_PROG_EMPTY_TYPE(0),
          .C_PROG_FULL_THRESH_ASSERT_VAL(1022),
          .C_PROG_FULL_THRESH_NEGATE_VAL(1021),
          .C_PROG_FULL_TYPE(0),
          .C_RD_DATA_COUNT_WIDTH(10),
          .C_RD_DEPTH(1024),
          .C_RD_FREQ(1),
          .C_RD_PNTR_WIDTH(10),
          .C_UNDERFLOW_LOW(0),
          .C_USE_DOUT_RST(1),
          .C_USE_ECC(0),
          .C_USE_EMBEDDED_REG(0),
          .C_USE_FIFO16_FLAGS(0),
          .C_USE_FWFT_DATA_COUNT(0),
          .C_VALID_LOW(0),
          .C_WR_ACK_LOW(0),
          .C_WR_DATA_COUNT_WIDTH(10),
          .C_WR_DEPTH(1024),
          .C_WR_FREQ(1),
          .C_WR_PNTR_WIDTH(10),
          .C_WR_RESPONSE_LATENCY(1),
          .C_MSGON_VAL(1),
          .C_ENABLE_RST_SYNC(1),
          .C_ERROR_INJECTION_TYPE(0),
          .C_HAS_SLAVE_CE(0),
          .C_HAS_MASTER_CE(0),
          .C_ADD_NGC_CONSTRAINT(0),
          .C_USE_COMMON_OVERFLOW(0),
          .C_USE_COMMON_UNDERFLOW(0),
          .C_USE_DEFAULT_SETTINGS(0),
          .C_HAS_AXIS_TDATA(1),
          .C_HAS_AXIS_TID(0),
          .C_HAS_AXIS_TDEST(0),
          .C_HAS_AXIS_TUSER(1),
          .C_HAS_AXIS_TREADY(1),
          .C_HAS_AXIS_TLAST(0),
          .C_HAS_AXIS_TSTRB(0),
          .C_HAS_AXIS_TKEEP(0),
          .C_AXIS_TDATA_WIDTH(8),
          .C_AXIS_TID_WIDTH(1),
          .C_AXIS_TDEST_WIDTH(1),
          .C_AXIS_TUSER_WIDTH(4),
          .C_AXIS_TSTRB_WIDTH(1),
          .C_AXIS_TKEEP_WIDTH(1),
          .C_AXIS_TYPE(0),
          .C_IMPLEMENTATION_TYPE_WACH(12),
          .C_IMPLEMENTATION_TYPE_WDCH(12),
          .C_IMPLEMENTATION_TYPE_WRCH(12),
          .C_IMPLEMENTATION_TYPE_RACH(12),
          .C_IMPLEMENTATION_TYPE_RDCH(12),
          .C_IMPLEMENTATION_TYPE_AXIS(11),
          .C_APPLICATION_TYPE_WACH(0),
          .C_APPLICATION_TYPE_WDCH(0),
          .C_APPLICATION_TYPE_WRCH(0),
          .C_APPLICATION_TYPE_RACH(0),
          .C_APPLICATION_TYPE_RDCH(0),
          .C_APPLICATION_TYPE_AXIS(0),
          .C_USE_ECC_WACH(0),
          .C_USE_ECC_WDCH(0),
          .C_USE_ECC_WRCH(0),
          .C_USE_ECC_RACH(0),
          .C_USE_ECC_RDCH(0),
          .C_USE_ECC_AXIS(0),
          .C_ERROR_INJECTION_TYPE_WACH(0),
          .C_ERROR_INJECTION_TYPE_WDCH(0),
          .C_ERROR_INJECTION_TYPE_WRCH(0),
          .C_ERROR_INJECTION_TYPE_RACH(0),
          .C_ERROR_INJECTION_TYPE_RDCH(0),
          .C_ERROR_INJECTION_TYPE_AXIS(0),
          .C_DIN_WIDTH_AXIS(1),
          .C_WR_DEPTH_WACH(16),
          .C_WR_DEPTH_WDCH(16),
          .C_WR_DEPTH_WRCH(16),
          .C_WR_DEPTH_RACH(16),
          .C_WR_DEPTH_RDCH(16),
          .C_WR_DEPTH_AXIS(1024),
          .C_WR_PNTR_WIDTH_WACH(4),
          .C_WR_PNTR_WIDTH_WDCH(4),
          .C_WR_PNTR_WIDTH_WRCH(4),
          .C_WR_PNTR_WIDTH_RACH(4),
          .C_WR_PNTR_WIDTH_RDCH(4),
          .C_WR_PNTR_WIDTH_AXIS(10),
          .C_HAS_DATA_COUNTS_WACH(0),
          .C_HAS_DATA_COUNTS_WDCH(0),
          .C_HAS_DATA_COUNTS_WRCH(0),
          .C_HAS_DATA_COUNTS_RACH(0),
          .C_HAS_DATA_COUNTS_RDCH(0),
          .C_HAS_DATA_COUNTS_AXIS(0),
          .C_HAS_PROG_FLAGS_WACH(0),
          .C_HAS_PROG_FLAGS_WDCH(0),
          .C_HAS_PROG_FLAGS_WRCH(0),
          .C_HAS_PROG_FLAGS_RACH(0),
          .C_HAS_PROG_FLAGS_RDCH(0),
          .C_HAS_PROG_FLAGS_AXIS(0),
          .C_PROG_FULL_TYPE_WACH(0),
          .C_PROG_FULL_TYPE_WDCH(0),
          .C_PROG_FULL_TYPE_WRCH(0),
          .C_PROG_FULL_TYPE_RACH(0),
          .C_PROG_FULL_TYPE_RDCH(0),
          .C_PROG_FULL_TYPE_AXIS(0),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WACH(15),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WDCH(15),
          .C_PROG_FULL_THRESH_ASSERT_VAL_WRCH(15),
          .C_PROG_FULL_THRESH_ASSERT_VAL_RACH(15),
          .C_PROG_FULL_THRESH_ASSERT_VAL_RDCH(15),
          .C_PROG_FULL_THRESH_ASSERT_VAL_AXIS(1023),
          .C_PROG_EMPTY_TYPE_WACH(0),
          .C_PROG_EMPTY_TYPE_WDCH(0),
          .C_PROG_EMPTY_TYPE_WRCH(0),
          .C_PROG_EMPTY_TYPE_RACH(0),
          .C_PROG_EMPTY_TYPE_RDCH(0),
          .C_PROG_EMPTY_TYPE_AXIS(0),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH(13),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH(13),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH(13),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH(13),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH(13),
          .C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS(1021),
          .C_REG_SLICE_MODE_WACH(0),
          .C_REG_SLICE_MODE_WDCH(0),
          .C_REG_SLICE_MODE_WRCH(0),
          .C_REG_SLICE_MODE_RACH(0),
          .C_REG_SLICE_MODE_RDCH(0),
          .C_REG_SLICE_MODE_AXIS(0)
          )
          asyncfifo_axi (
            .s_aclk(s_axi_aclk),
            .m_aclk(m_axi_aclk),
            .s_aresetn(async_conv_reset_n),
            .s_axi_awid           (si_cc_awid),
            .s_axi_awaddr         (si_cc_awaddr),
            .s_axi_awlen          (si_cc_awlen),
            .s_axi_awsize         (si_cc_awsize),
            .s_axi_awburst        (si_cc_awburst),
            .s_axi_awlock         (si_cc_awlock),
            .s_axi_awcache        (si_cc_awcache),
            .s_axi_awprot         (si_cc_awprot),
            .s_axi_awqos          (si_cc_awqos),
            .s_axi_awregion       (si_cc_awregion),
            .s_axi_awuser         (si_cc_awuser),
            .s_axi_awvalid        (si_cc_awvalid),
            .s_axi_awready        (si_cc_awready),
            .s_axi_wid            (si_cc_wid),
            .s_axi_wdata          (si_cc_wdata),
            .s_axi_wstrb          (si_cc_wstrb),
            .s_axi_wlast          (si_cc_wlast),
            .s_axi_wuser          (si_cc_wuser),
            .s_axi_wvalid         (si_cc_wvalid),
            .s_axi_wready         (si_cc_wready),
            .s_axi_bid            (si_cc_bid),
            .s_axi_bresp          (si_cc_bresp),
            .s_axi_buser          (si_cc_buser),
            .s_axi_bvalid         (si_cc_bvalid),
            .s_axi_bready         (si_cc_bready),
            .m_axi_awid           (cc_mi_awid),
            .m_axi_awaddr         (cc_mi_awaddr),
            .m_axi_awlen          (cc_mi_awlen),
            .m_axi_awsize         (cc_mi_awsize),
            .m_axi_awburst        (cc_mi_awburst),
            .m_axi_awlock         (cc_mi_awlock),
            .m_axi_awcache        (cc_mi_awcache),
            .m_axi_awprot         (cc_mi_awprot),
            .m_axi_awqos          (cc_mi_awqos),
            .m_axi_awregion       (cc_mi_awregion),
            .m_axi_awuser         (cc_mi_awuser),
            .m_axi_awvalid        (cc_mi_awvalid),
            .m_axi_awready        (cc_mi_awready),
            .m_axi_wid            (cc_mi_wid),
            .m_axi_wdata          (cc_mi_wdata),
            .m_axi_wstrb          (cc_mi_wstrb),
            .m_axi_wlast          (cc_mi_wlast),
            .m_axi_wuser          (cc_mi_wuser),
            .m_axi_wvalid         (cc_mi_wvalid),
            .m_axi_wready         (cc_mi_wready),
            .m_axi_bid            (cc_mi_bid),
            .m_axi_bresp          (cc_mi_bresp),
            .m_axi_buser          (cc_mi_buser),
            .m_axi_bvalid         (cc_mi_bvalid),
            .m_axi_bready         (cc_mi_bready),
            .s_axi_arid           (si_cc_arid),
            .s_axi_araddr         (si_cc_araddr),
            .s_axi_arlen          (si_cc_arlen),
            .s_axi_arsize         (si_cc_arsize),
            .s_axi_arburst        (si_cc_arburst),
            .s_axi_arlock         (si_cc_arlock),
            .s_axi_arcache        (si_cc_arcache),
            .s_axi_arprot         (si_cc_arprot),
            .s_axi_arqos          (si_cc_arqos),
            .s_axi_arregion       (si_cc_arregion),
            .s_axi_aruser         (si_cc_aruser),
            .s_axi_arvalid        (si_cc_arvalid),
            .s_axi_arready        (si_cc_arready),
            .s_axi_rid            (si_cc_rid),
            .s_axi_rdata          (si_cc_rdata),
            .s_axi_rresp          (si_cc_rresp),
            .s_axi_rlast          (si_cc_rlast),
            .s_axi_ruser          (si_cc_ruser),
            .s_axi_rvalid         (si_cc_rvalid),
            .s_axi_rready         (si_cc_rready),
            .m_axi_arid           (cc_mi_arid),
            .m_axi_araddr         (cc_mi_araddr),
            .m_axi_arlen          (cc_mi_arlen),
            .m_axi_arsize         (cc_mi_arsize),
            .m_axi_arburst        (cc_mi_arburst),
            .m_axi_arlock         (cc_mi_arlock),
            .m_axi_arcache        (cc_mi_arcache),
            .m_axi_arprot         (cc_mi_arprot),
            .m_axi_arqos          (cc_mi_arqos),
            .m_axi_arregion       (cc_mi_arregion),
            .m_axi_aruser         (cc_mi_aruser),
            .m_axi_arvalid        (cc_mi_arvalid),
            .m_axi_arready        (cc_mi_arready),
            .m_axi_rid            (cc_mi_rid),
            .m_axi_rdata          (cc_mi_rdata),
            .m_axi_rresp          (cc_mi_rresp),
            .m_axi_rlast          (cc_mi_rlast),
            .m_axi_ruser          (cc_mi_ruser),
            .m_axi_rvalid         (cc_mi_rvalid),
            .m_axi_rready         (cc_mi_rready),
            .m_aclk_en(1'b1),
            .s_aclk_en(1'b1),
            .almost_empty(),
            .almost_full(),
            .axis_data_count(),
            .axis_dbiterr(),
            .axis_injectdbiterr(1'b0),
            .axis_injectsbiterr(1'b0),
            .axis_overflow(),
            .axis_prog_empty(),
            .axis_prog_empty_thresh(10'b0),
            .axis_prog_full(),
            .axis_prog_full_thresh(10'b0),
            .axis_rd_data_count(),
            .axis_sbiterr(),
            .axis_underflow(),
            .axis_wr_data_count(),
            .axi_ar_data_count(),
            .axi_ar_dbiterr(),
            .axi_ar_injectdbiterr(1'b0),
            .axi_ar_injectsbiterr(1'b0),
            .axi_ar_overflow(),
            .axi_ar_prog_empty(),
            .axi_ar_prog_empty_thresh(4'b0),
            .axi_ar_prog_full(),
            .axi_ar_prog_full_thresh(4'b0),
            .axi_ar_rd_data_count(),
            .axi_ar_sbiterr(),
            .axi_ar_underflow(),
            .axi_ar_wr_data_count(),
            .axi_aw_data_count(),
            .axi_aw_dbiterr(),
            .axi_aw_injectdbiterr(1'b0),
            .axi_aw_injectsbiterr(1'b0),
            .axi_aw_overflow(),
            .axi_aw_prog_empty(),
            .axi_aw_prog_empty_thresh(4'b0),
            .axi_aw_prog_full(),
            .axi_aw_prog_full_thresh(4'b0),
            .axi_aw_rd_data_count(),
            .axi_aw_sbiterr(),
            .axi_aw_underflow(),
            .axi_aw_wr_data_count(),
            .axi_b_data_count(),
            .axi_b_dbiterr(),
            .axi_b_injectdbiterr(1'b0),
            .axi_b_injectsbiterr(1'b0),
            .axi_b_overflow(),
            .axi_b_prog_empty(),
            .axi_b_prog_empty_thresh(4'b0),
            .axi_b_prog_full(),
            .axi_b_prog_full_thresh(4'b0),
            .axi_b_rd_data_count(),
            .axi_b_sbiterr(),
            .axi_b_underflow(),
            .axi_b_wr_data_count(),
            .axi_r_data_count(),
            .axi_r_dbiterr(),
            .axi_r_injectdbiterr(1'b0),
            .axi_r_injectsbiterr(1'b0),
            .axi_r_overflow(),
            .axi_r_prog_empty(),
            .axi_r_prog_empty_thresh(4'b0),
            .axi_r_prog_full(),
            .axi_r_prog_full_thresh(4'b0),
            .axi_r_rd_data_count(),
            .axi_r_sbiterr(),
            .axi_r_underflow(),
            .axi_r_wr_data_count(),
            .axi_w_data_count(),
            .axi_w_dbiterr(),
            .axi_w_injectdbiterr(1'b0),
            .axi_w_injectsbiterr(1'b0),
            .axi_w_overflow(),
            .axi_w_prog_empty(),
            .axi_w_prog_empty_thresh(4'b0),
            .axi_w_prog_full(),
            .axi_w_prog_full_thresh(4'b0),
            .axi_w_rd_data_count(),
            .axi_w_sbiterr(),
            .axi_w_underflow(),
            .axi_w_wr_data_count(),
            .backup(1'b0),
            .backup_marker(1'b0),
            .clk(1'b0),
            .data_count(),
            .dbiterr(),
            .din(18'b0),
            .dout(),
            .empty(),
            .full(),
            .injectdbiterr(1'b0),
            .injectsbiterr(1'b0),
            .int_clk(1'b0),
            .m_axis_tdata(),
            .m_axis_tdest(),
            .m_axis_tid(),
            .m_axis_tkeep(),
            .m_axis_tlast(),
            .m_axis_tready(1'b0),
            .m_axis_tstrb(),
            .m_axis_tuser(),
            .m_axis_tvalid(),
            .overflow(),
            .prog_empty(),
            .prog_empty_thresh(10'b0),
            .prog_empty_thresh_assert(10'b0),
            .prog_empty_thresh_negate(10'b0),
            .prog_full(),
            .prog_full_thresh(10'b0),
            .prog_full_thresh_assert(10'b0),
            .prog_full_thresh_negate(10'b0),
            .rd_clk(1'b0),
            .rd_data_count(),
            .rd_en(1'b0),
            .rd_rst(1'b0),
            .rst(1'b0),
            .sbiterr(),
            .srst(1'b0),
            .s_axis_tdata(8'b0),
            .s_axis_tdest(1'b0),
            .s_axis_tid(1'b0),
            .s_axis_tkeep(1'b0),
            .s_axis_tlast(1'b0),
            .s_axis_tready(),
            .s_axis_tstrb(1'b0),
            .s_axis_tuser(4'b0),
            .s_axis_tvalid(1'b0),
            .underflow(),
            .valid(),
            .wr_ack(),
            .wr_clk(1'b0),
            .wr_data_count(),
            .wr_en(1'b0),
            .wr_rst(1'b0),
            .wr_rst_busy(),
            .rd_rst_busy(),
            .sleep(1'b0)
        );
      end else if ((C_AXI_IS_ACLK_ASYNC) && (C_AXI_PROTOCOL==P_AXILITE)) begin : gen_async_lite_conv
        localparam C_AXI_SUPPORTS_REGION_SIGNALS = (C_AXI_PROTOCOL == 0) ? 1 : 0;
        `include "axi_infrastructure_v1_1_0.vh"

        wire [G_AXI_AWPAYLOAD_WIDTH-1:0] s_awpayload;
        wire [G_AXI_AWPAYLOAD_WIDTH-1:0] m_awpayload;
        wire [G_AXI_WPAYLOAD_WIDTH-1:0] s_wpayload;
        wire [G_AXI_WPAYLOAD_WIDTH-1:0] m_wpayload;
        wire [G_AXI_BPAYLOAD_WIDTH-1:0] s_bpayload;
        wire [G_AXI_BPAYLOAD_WIDTH-1:0] m_bpayload;
        wire [G_AXI_ARPAYLOAD_WIDTH-1:0] s_arpayload;
        wire [G_AXI_ARPAYLOAD_WIDTH-1:0] m_arpayload;
        wire [G_AXI_RPAYLOAD_WIDTH-1:0] s_rpayload;
        wire [G_AXI_RPAYLOAD_WIDTH-1:0] m_rpayload;

        axi_infrastructure_v1_1_0_axi2vector #( 
          .C_AXI_PROTOCOL                ( C_AXI_PROTOCOL                ) ,
          .C_AXI_ID_WIDTH                ( C_AXI_ID_WIDTH                ) ,
          .C_AXI_ADDR_WIDTH              ( C_AXI_ADDR_WIDTH              ) ,
          .C_AXI_DATA_WIDTH              ( C_AXI_DATA_WIDTH              ) ,
          .C_AXI_SUPPORTS_USER_SIGNALS   ( C_AXI_SUPPORTS_USER_SIGNALS   ) ,
          .C_AXI_SUPPORTS_REGION_SIGNALS ( C_AXI_SUPPORTS_REGION_SIGNALS ) ,
          .C_AXI_AWUSER_WIDTH            ( C_AXI_AWUSER_WIDTH            ) ,
          .C_AXI_ARUSER_WIDTH            ( C_AXI_ARUSER_WIDTH            ) ,
          .C_AXI_WUSER_WIDTH             ( C_AXI_WUSER_WIDTH             ) ,
          .C_AXI_RUSER_WIDTH             ( C_AXI_RUSER_WIDTH             ) ,
          .C_AXI_BUSER_WIDTH             ( C_AXI_BUSER_WIDTH             ) ,
          .C_AWPAYLOAD_WIDTH             ( G_AXI_AWPAYLOAD_WIDTH         ) ,
          .C_WPAYLOAD_WIDTH              ( G_AXI_WPAYLOAD_WIDTH          ) ,
          .C_BPAYLOAD_WIDTH              ( G_AXI_BPAYLOAD_WIDTH          ) ,
          .C_ARPAYLOAD_WIDTH             ( G_AXI_ARPAYLOAD_WIDTH         ) ,
          .C_RPAYLOAD_WIDTH              ( G_AXI_RPAYLOAD_WIDTH          ) 
        )
        axi2vec ( 
          .s_axi_awid      ( si_cc_awid      ) ,
          .s_axi_awaddr    ( si_cc_awaddr    ) ,
          .s_axi_awlen     ( s_axi_awlen     ) ,
          .s_axi_awsize    ( si_cc_awsize    ) ,
          .s_axi_awburst   ( si_cc_awburst   ) ,
          .s_axi_awlock    ( s_axi_awlock    ) ,
          .s_axi_awcache   ( si_cc_awcache   ) ,
          .s_axi_awprot    ( si_cc_awprot    ) ,
          .s_axi_awqos     ( si_cc_awqos     ) ,
          .s_axi_awuser    ( si_cc_awuser    ) ,
          .s_axi_awregion  ( si_cc_awregion  ) ,
          .s_axi_wid       ( si_cc_wid       ) ,
          .s_axi_wdata     ( si_cc_wdata     ) ,
          .s_axi_wstrb     ( si_cc_wstrb     ) ,
          .s_axi_wlast     ( si_cc_wlast     ) ,
          .s_axi_wuser     ( si_cc_wuser     ) ,
          .s_axi_bid       ( si_cc_bid       ) ,
          .s_axi_bresp     ( si_cc_bresp     ) ,
          .s_axi_buser     ( si_cc_buser     ) ,
          .s_axi_arid      ( si_cc_arid      ) ,
          .s_axi_araddr    ( si_cc_araddr    ) ,
          .s_axi_arlen     ( s_axi_arlen     ) ,
          .s_axi_arsize    ( si_cc_arsize    ) ,
          .s_axi_arburst   ( si_cc_arburst   ) ,
          .s_axi_arlock    ( s_axi_arlock    ) ,
          .s_axi_arcache   ( si_cc_arcache   ) ,
          .s_axi_arprot    ( si_cc_arprot    ) ,
          .s_axi_arqos     ( si_cc_arqos     ) ,
          .s_axi_aruser    ( si_cc_aruser    ) ,
          .s_axi_arregion  ( si_cc_arregion  ) ,
          .s_axi_rid       ( si_cc_rid       ) ,
          .s_axi_rdata     ( si_cc_rdata     ) ,
          .s_axi_rresp     ( si_cc_rresp     ) ,
          .s_axi_rlast     ( si_cc_rlast     ) ,
          .s_axi_ruser     ( si_cc_ruser     ) ,
          .s_awpayload     ( s_awpayload ) ,
          .s_wpayload      ( s_wpayload  ) ,
          .s_bpayload      ( s_bpayload  ) ,
          .s_arpayload     ( s_arpayload ) ,
          .s_rpayload      ( s_rpayload  ) 
        );

        axi_clock_converter_v2_1_10_lite_async #(
          .C_DEST_SYNC_FF (2),
          .C_SRC_SYNC_FF  (2),
          .C_WIDTH        (G_AXI_AWPAYLOAD_WIDTH)
        ) aw_handshake (
          .s_aclk   (s_axi_aclk),
          .m_aclk   (m_axi_aclk),
          .s_aresetn(s_axi_aresetn),
          .m_aresetn(m_axi_aresetn),
          .s_valid  (si_cc_awvalid),
          .s_ready  (si_cc_awready),
          .s_payld  (s_awpayload),
          .m_valid  (cc_mi_awvalid),
          .m_ready  (cc_mi_awready),
          .m_payld  (m_awpayload)
        );

        axi_clock_converter_v2_1_10_lite_async #(
          .C_DEST_SYNC_FF (2),
          .C_SRC_SYNC_FF  (2),
          .C_WIDTH        (G_AXI_ARPAYLOAD_WIDTH)
        ) ar_handshake (
          .s_aclk   (s_axi_aclk),
          .m_aclk   (m_axi_aclk),
          .s_aresetn(s_axi_aresetn),
          .m_aresetn(m_axi_aresetn),
          .s_valid  (si_cc_arvalid),
          .s_ready  (si_cc_arready),
          .s_payld  (s_arpayload),
          .m_valid  (cc_mi_arvalid),
          .m_ready  (cc_mi_arready),
          .m_payld  (m_arpayload)
        );

        axi_clock_converter_v2_1_10_lite_async #(
          .C_DEST_SYNC_FF (2),
          .C_SRC_SYNC_FF  (2),
          .C_WIDTH        (G_AXI_WPAYLOAD_WIDTH)
        ) w_handshake (
          .s_aclk   (s_axi_aclk),
          .m_aclk   (m_axi_aclk),
          .s_aresetn(s_axi_aresetn),
          .m_aresetn(m_axi_aresetn),
          .s_valid  (si_cc_wvalid),
          .s_ready  (si_cc_wready),
          .s_payld  (s_wpayload),
          .m_valid  (cc_mi_wvalid),
          .m_ready  (cc_mi_wready),
          .m_payld  (m_wpayload)
        );

        axi_clock_converter_v2_1_10_lite_async #(
          .C_DEST_SYNC_FF (2),
          .C_SRC_SYNC_FF  (2),
          .C_WIDTH        (G_AXI_BPAYLOAD_WIDTH)
        ) b_handshake (
          .s_aclk   (m_axi_aclk),
          .m_aclk   (s_axi_aclk),
          .s_aresetn(m_axi_aresetn),
          .m_aresetn(s_axi_aresetn),
          .s_valid  (cc_mi_bvalid),
          .s_ready  (cc_mi_bready),
          .s_payld  (m_bpayload),
          .m_valid  (si_cc_bvalid),
          .m_ready  (si_cc_bready),
          .m_payld  (s_bpayload)
        );

        axi_clock_converter_v2_1_10_lite_async #(
          .C_DEST_SYNC_FF (2),
          .C_SRC_SYNC_FF  (2),
          .C_WIDTH        (G_AXI_RPAYLOAD_WIDTH)
        ) r_handshake (
          .s_aclk   (m_axi_aclk),
          .m_aclk   (s_axi_aclk),
          .s_aresetn(m_axi_aresetn),
          .m_aresetn(s_axi_aresetn),
          .s_valid  (cc_mi_rvalid),
          .s_ready  (cc_mi_rready),
          .s_payld  (m_rpayload),
          .m_valid  (si_cc_rvalid),
          .m_ready  (si_cc_rready),
          .m_payld  (s_rpayload)
        );

        axi_infrastructure_v1_1_0_vector2axi #( 
          .C_AXI_PROTOCOL                ( C_AXI_PROTOCOL                ) ,
          .C_AXI_ID_WIDTH                ( C_AXI_ID_WIDTH                ) ,
          .C_AXI_ADDR_WIDTH              ( C_AXI_ADDR_WIDTH              ) ,
          .C_AXI_DATA_WIDTH              ( C_AXI_DATA_WIDTH              ) ,
          .C_AXI_SUPPORTS_USER_SIGNALS   ( C_AXI_SUPPORTS_USER_SIGNALS   ) ,
          .C_AXI_SUPPORTS_REGION_SIGNALS ( C_AXI_SUPPORTS_REGION_SIGNALS ) ,
          .C_AXI_AWUSER_WIDTH            ( C_AXI_AWUSER_WIDTH            ) ,
          .C_AXI_ARUSER_WIDTH            ( C_AXI_ARUSER_WIDTH            ) ,
          .C_AXI_WUSER_WIDTH             ( C_AXI_WUSER_WIDTH             ) ,
          .C_AXI_RUSER_WIDTH             ( C_AXI_RUSER_WIDTH             ) ,
          .C_AXI_BUSER_WIDTH             ( C_AXI_BUSER_WIDTH             ) ,
          .C_AWPAYLOAD_WIDTH             ( G_AXI_AWPAYLOAD_WIDTH         ) ,
          .C_WPAYLOAD_WIDTH              ( G_AXI_WPAYLOAD_WIDTH          ) ,
          .C_BPAYLOAD_WIDTH              ( G_AXI_BPAYLOAD_WIDTH          ) ,
          .C_ARPAYLOAD_WIDTH             ( G_AXI_ARPAYLOAD_WIDTH         ) ,
          .C_RPAYLOAD_WIDTH              ( G_AXI_RPAYLOAD_WIDTH          ) 
        )
        vec2axi ( 
          .m_awpayload    ( m_awpayload    ) ,
          .m_wpayload     ( m_wpayload     ) ,
          .m_bpayload     ( m_bpayload     ) ,
          .m_arpayload    ( m_arpayload    ) ,
          .m_rpayload     ( m_rpayload     ) ,
          .m_axi_awid     ( cc_mi_awid     ) ,
          .m_axi_awaddr   ( cc_mi_awaddr   ) ,
          .m_axi_awlen    ( cc_mi_awlen    ) ,
          .m_axi_awsize   ( cc_mi_awsize   ) ,
          .m_axi_awburst  ( cc_mi_awburst  ) ,
          .m_axi_awlock   ( cc_mi_awlock   ) ,
          .m_axi_awcache  ( cc_mi_awcache  ) ,
          .m_axi_awprot   ( cc_mi_awprot   ) ,
          .m_axi_awqos    ( cc_mi_awqos    ) ,
          .m_axi_awuser   ( cc_mi_awuser   ) ,
          .m_axi_awregion ( cc_mi_awregion ) ,
          .m_axi_wid      ( cc_mi_wid      ) ,
          .m_axi_wdata    ( cc_mi_wdata    ) ,
          .m_axi_wstrb    ( cc_mi_wstrb    ) ,
          .m_axi_wlast    ( cc_mi_wlast    ) ,
          .m_axi_wuser    ( cc_mi_wuser    ) ,
          .m_axi_bid      ( cc_mi_bid      ) ,
          .m_axi_bresp    ( cc_mi_bresp    ) ,
          .m_axi_buser    ( cc_mi_buser    ) ,
          .m_axi_arid     ( cc_mi_arid     ) ,
          .m_axi_araddr   ( cc_mi_araddr   ) ,
          .m_axi_arlen    ( cc_mi_arlen    ) ,
          .m_axi_arsize   ( cc_mi_arsize   ) ,
          .m_axi_arburst  ( cc_mi_arburst  ) ,
          .m_axi_arlock   ( cc_mi_arlock   ) ,
          .m_axi_arcache  ( cc_mi_arcache  ) ,
          .m_axi_arprot   ( cc_mi_arprot   ) ,
          .m_axi_arqos    ( cc_mi_arqos    ) ,
          .m_axi_aruser   ( cc_mi_aruser   ) ,
          .m_axi_arregion ( cc_mi_arregion ) ,
          .m_axi_rid      ( cc_mi_rid      ) ,
          .m_axi_rdata    ( cc_mi_rdata    ) ,
          .m_axi_rresp    ( cc_mi_rresp    ) ,
          .m_axi_rlast    ( cc_mi_rlast    ) ,
          .m_axi_ruser    ( cc_mi_ruser    ) 
        );

      end else begin : gen_sync_conv
        
        assign {fast_aclk, slow_aclk} = P_SI_LT_MI ? {m_axi_aclk, s_axi_aclk} : {s_axi_aclk, m_axi_aclk};
    
        // Sample cycle used to determine when to assert a signal on a fast clock
        // to be flopped onto a slow clock.
        axi_clock_converter_v2_1_10_axic_sample_cycle_ratio #(
          .C_RATIO ( P_ACLK_RATIO )
        )
        axic_sample_cycle_inst (
          .SLOW_ACLK          ( slow_aclk               ) ,
          .FAST_ACLK          ( fast_aclk               ) ,
          .SAMPLE_CYCLE_EARLY ( sample_cycle_early ) ,
          .SAMPLE_CYCLE       ( sample_cycle       )
        );
    
      ////////////////////////////////////////////////////////////////////////////////
      // AXI write channels
      ////////////////////////////////////////////////////////////////////////////////
        if (C_AXI_SUPPORTS_WRITE) begin : gen_conv_write_ch
    
          // Write Address Port
          assign s_aw_mesg[C_AWADDR_RIGHT+:C_AWADDR_WIDTH]     = si_cc_awaddr   ;
          assign s_aw_mesg[C_AWPROT_RIGHT+:C_AWPROT_WIDTH]     = si_cc_awprot   ;
          assign cc_mi_awaddr   = m_aw_mesg[C_AWADDR_RIGHT+:C_AWADDR_WIDTH];
          assign cc_mi_awprot   = m_aw_mesg[C_AWPROT_RIGHT+:C_AWPROT_WIDTH];
          if (C_AXI_PROTOCOL == P_AXI4) begin : gen_aw_axi4
            assign s_aw_mesg[C_AWID_RIGHT+:C_AWID_WIDTH]         = si_cc_awid     ;
            assign s_aw_mesg[C_AWLEN_RIGHT+:C_AWLEN_WIDTH]       = si_cc_awlen    ;
            assign s_aw_mesg[C_AWSIZE_RIGHT+:C_AWSIZE_WIDTH]     = si_cc_awsize   ;
            assign s_aw_mesg[C_AWBURST_RIGHT+:C_AWBURST_WIDTH]   = si_cc_awburst  ;
            assign s_aw_mesg[C_AWLOCK_RIGHT+:C_AWLOCK_WIDTH]     = si_cc_awlock[0] ;
            assign s_aw_mesg[C_AWCACHE_RIGHT+:C_AWCACHE_WIDTH]   = si_cc_awcache  ;
            assign s_aw_mesg[C_AWREGION_RIGHT+:C_AWREGION_WIDTH] = si_cc_awregion ;
            assign s_aw_mesg[C_AWQOS_RIGHT+:C_AWQOS_WIDTH]       = si_cc_awqos    ;
            assign cc_mi_awid     = m_aw_mesg[C_AWID_RIGHT+:C_AWID_WIDTH];
            assign cc_mi_awlen    = m_aw_mesg[C_AWLEN_RIGHT+:C_AWLEN_WIDTH];
            assign cc_mi_awsize   = m_aw_mesg[C_AWSIZE_RIGHT+:C_AWSIZE_WIDTH];
            assign cc_mi_awburst  = m_aw_mesg[C_AWBURST_RIGHT+:C_AWBURST_WIDTH];
            assign cc_mi_awlock   = m_aw_mesg[C_AWLOCK_RIGHT+:C_AWLOCK_WIDTH];
            assign cc_mi_awcache  = m_aw_mesg[C_AWCACHE_RIGHT+:C_AWCACHE_WIDTH];
            assign cc_mi_awregion = m_aw_mesg[C_AWREGION_RIGHT+:C_AWREGION_WIDTH];
            assign cc_mi_awqos    = m_aw_mesg[C_AWQOS_RIGHT+:C_AWQOS_WIDTH];
          end else if (C_AXI_PROTOCOL == P_AXI3) begin : gen_aw_axi3
            assign s_aw_mesg[C_AWID_RIGHT+:C_AWID_WIDTH]         = si_cc_awid     ;
            assign s_aw_mesg[C_AWLEN_RIGHT+:C_AWLEN_WIDTH]       = si_cc_awlen[3:0] ;
            assign s_aw_mesg[C_AWSIZE_RIGHT+:C_AWSIZE_WIDTH]     = si_cc_awsize   ;
            assign s_aw_mesg[C_AWBURST_RIGHT+:C_AWBURST_WIDTH]   = si_cc_awburst  ;
            assign s_aw_mesg[C_AWLOCK_RIGHT+:C_AWLOCK_WIDTH]     = si_cc_awlock   ;
            assign s_aw_mesg[C_AWCACHE_RIGHT+:C_AWCACHE_WIDTH]   = si_cc_awcache  ;
            assign s_aw_mesg[C_AWQOS_RIGHT+:C_AWQOS_WIDTH]       = si_cc_awqos    ;
            assign cc_mi_awid     = m_aw_mesg[C_AWID_RIGHT+:C_AWID_WIDTH];
            assign cc_mi_awlen    = m_aw_mesg[C_AWLEN_RIGHT+:C_AWLEN_WIDTH];
            assign cc_mi_awsize   = m_aw_mesg[C_AWSIZE_RIGHT+:C_AWSIZE_WIDTH];
            assign cc_mi_awburst  = m_aw_mesg[C_AWBURST_RIGHT+:C_AWBURST_WIDTH];
            assign cc_mi_awlock   = m_aw_mesg[C_AWLOCK_RIGHT+:C_AWLOCK_WIDTH];
            assign cc_mi_awcache  = m_aw_mesg[C_AWCACHE_RIGHT+:C_AWCACHE_WIDTH];
            assign cc_mi_awqos    = m_aw_mesg[C_AWQOS_RIGHT+:C_AWQOS_WIDTH];
          end
          if (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) begin : gen_aw_user
            assign s_aw_mesg[C_AWUSER_RIGHT+:C_AWUSER_WIDTH]  = si_cc_awuser;
            assign cc_mi_awuser = m_aw_mesg[C_AWUSER_RIGHT+:C_AWUSER_WIDTH];
          end
    
          axi_clock_converter_v2_1_10_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH ( C_AW_WIDTH ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE(P_LIGHT_WT)
          )
          aw_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( s_axi_aclk     ) ,
            .S_ARESETN  ( s_axi_aresetn ) ,
            .S_PAYLOAD ( s_aw_mesg ) ,
            .S_VALID   ( si_cc_awvalid   ) ,
            .S_READY   ( si_cc_awready   ) ,
            .M_ACLK     ( m_axi_aclk     ) ,
            .M_ARESETN ( m_axi_aresetn ) ,
            .M_PAYLOAD ( m_aw_mesg ) ,
            .M_VALID   ( cc_mi_awvalid   ) ,
            .M_READY   ( cc_mi_awready   )
          );
    
          // Write Data Port
          assign s_w_mesg[C_WDATA_RIGHT+:C_WDATA_WIDTH] = si_cc_wdata; 
          assign s_w_mesg[C_WSTRB_RIGHT+:C_WSTRB_WIDTH] = si_cc_wstrb; 
          assign cc_mi_wdata    = m_w_mesg[C_WDATA_RIGHT+:C_WDATA_WIDTH];
          assign cc_mi_wstrb    = m_w_mesg[C_WSTRB_RIGHT+:C_WSTRB_WIDTH];
          if (C_AXI_PROTOCOL == P_AXI4) begin : gen_w_axi4
            assign s_w_mesg[C_WLAST_RIGHT+:C_WLAST_WIDTH] = si_cc_wlast;
            assign cc_mi_wlast    = m_w_mesg[C_WLAST_RIGHT+:C_WLAST_WIDTH];
          end else if (C_AXI_PROTOCOL == P_AXI3) begin : gen_w_axi3
            assign s_w_mesg[C_WID_RIGHT+:C_WID_WIDTH]     = si_cc_wid; 
            assign s_w_mesg[C_WLAST_RIGHT+:C_WLAST_WIDTH] = si_cc_wlast;
            assign cc_mi_wid      = m_w_mesg[C_WID_RIGHT+:C_WID_WIDTH];
            assign cc_mi_wlast    = m_w_mesg[C_WLAST_RIGHT+:C_WLAST_WIDTH];
          end
          if (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) begin : gen_w_user
            assign s_w_mesg[C_WUSER_RIGHT+:C_WUSER_WIDTH]  = si_cc_wuser;
            assign cc_mi_wuser = m_w_mesg[C_WUSER_RIGHT+:C_WUSER_WIDTH];
          end
    
          axi_clock_converter_v2_1_10_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH  ( C_W_WIDTH ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE           ((C_AXI_PROTOCOL == P_AXILITE) ? P_LIGHT_WT : P_FULLY_REG)
          )
          w_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( s_axi_aclk     ) ,
            .S_ARESETN  ( s_axi_aresetn ) ,
            .S_PAYLOAD ( s_w_mesg ) ,
            .S_VALID   ( si_cc_wvalid   ) ,
            .S_READY   ( si_cc_wready   ) ,
            .M_ACLK     ( m_axi_aclk     ) ,
            .M_ARESETN ( m_axi_aresetn ) ,
            .M_PAYLOAD ( m_w_mesg ) ,
            .M_VALID   ( cc_mi_wvalid   ) ,
            .M_READY   ( cc_mi_wready   )
          );
    
          // Write Response Port
          assign m_b_mesg[C_BRESP_RIGHT+:C_BRESP_WIDTH] = cc_mi_bresp;
          assign si_cc_bresp    = s_b_mesg[C_BRESP_RIGHT+:C_BRESP_WIDTH];
          if (C_AXI_PROTOCOL != P_AXILITE) begin : gen_b_axi
            assign m_b_mesg[C_BID_RIGHT+:C_BID_WIDTH]     = cc_mi_bid;
            assign si_cc_bid      = s_b_mesg[C_BID_RIGHT+:C_BID_WIDTH];
          end
          if (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) begin : gen_b_user
            assign m_b_mesg[C_BUSER_RIGHT+:C_BUSER_WIDTH] = cc_mi_buser;
            assign si_cc_buser  = s_b_mesg[C_BUSER_RIGHT+:C_BUSER_WIDTH];
          end
    
          axi_clock_converter_v2_1_10_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH ( C_B_WIDTH ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE(P_LIGHT_WT)
          )
          b_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( m_axi_aclk     ) ,
            .S_ARESETN  ( m_axi_aresetn ) ,
            .S_PAYLOAD ( m_b_mesg ) ,
            .S_VALID   ( cc_mi_bvalid   ) ,
            .S_READY   ( cc_mi_bready   ) ,
            .M_ACLK     ( s_axi_aclk     ) ,
            .M_ARESETN  ( s_axi_aresetn ) ,
            .M_PAYLOAD ( s_b_mesg ) ,
            .M_VALID   ( si_cc_bvalid   ) ,
            .M_READY   ( si_cc_bready   )
          );
    
        end else begin : gen_tieoff_write_ch
    
          // Write address port
          assign cc_mi_awid     = {C_AXI_ID_WIDTH{1'b0}};
          assign cc_mi_awaddr   = {C_AXI_ADDR_WIDTH{1'b0}};
          assign cc_mi_awlen    = {8{1'b0}};
          assign cc_mi_awsize   = {3{1'b0}};
          assign cc_mi_awburst  = {2{1'b0}};
          assign cc_mi_awlock   = {2{1'b0}};
          assign cc_mi_awcache  = {4{1'b0}};
          assign cc_mi_awprot   = {3{1'b0}};
          assign cc_mi_awregion = {4{1'b0}};
          assign cc_mi_awqos    = {4{1'b0}};
          assign cc_mi_awuser   = {C_AXI_AWUSER_WIDTH{1'b0}};
          assign cc_mi_awvalid  = 1'b0;
          assign si_cc_awready  = 1'b0;
    
          // Write data port
          assign cc_mi_wid      = {C_AXI_ID_WIDTH{1'b0}};
          assign cc_mi_wdata    = {C_AXI_DATA_WIDTH{1'b0}};
          assign cc_mi_wstrb    = {C_AXI_DATA_WIDTH/8{1'b0}};
          assign cc_mi_wlast    = 1'b0;
          assign cc_mi_wuser    = {C_AXI_WUSER_WIDTH{1'b0}};
          assign cc_mi_wvalid   = 1'b0;
          assign si_cc_wready   = 1'b0;
    
          // Write response port
          assign si_cc_bid      = {C_AXI_ID_WIDTH{1'b0}};
          assign si_cc_bresp    = {2{1'b0}};
          assign si_cc_buser    = {C_AXI_BUSER_WIDTH{1'b0}};
          assign si_cc_bvalid   = 1'b0;
          assign cc_mi_bready   = 1'b0;
        end
    
        ////////////////////////////////////////////////////////////////////////////////
        // AXI read channels
        ////////////////////////////////////////////////////////////////////////////////
    
        if (C_AXI_SUPPORTS_READ) begin : gen_conv_read_ch
    
          // Read Address Port
          assign s_ar_mesg[C_ARADDR_RIGHT+:C_ARADDR_WIDTH]     = si_cc_araddr   ;
          assign s_ar_mesg[C_ARPROT_RIGHT+:C_ARPROT_WIDTH]     = si_cc_arprot   ;
          assign cc_mi_araddr   = m_ar_mesg[C_ARADDR_RIGHT+:C_ARADDR_WIDTH];
          assign cc_mi_arprot   = m_ar_mesg[C_ARPROT_RIGHT+:C_ARPROT_WIDTH];
          if (C_AXI_PROTOCOL == P_AXI4) begin : gen_ar_axi4
            assign s_ar_mesg[C_ARID_RIGHT+:C_ARID_WIDTH]         = si_cc_arid     ;
            assign s_ar_mesg[C_ARLEN_RIGHT+:C_ARLEN_WIDTH]       = si_cc_arlen    ;
            assign s_ar_mesg[C_ARSIZE_RIGHT+:C_ARSIZE_WIDTH]     = si_cc_arsize   ;
            assign s_ar_mesg[C_ARBURST_RIGHT+:C_ARBURST_WIDTH]   = si_cc_arburst  ;
            assign s_ar_mesg[C_ARLOCK_RIGHT+:C_ARLOCK_WIDTH]     = si_cc_arlock[0] ;
            assign s_ar_mesg[C_ARCACHE_RIGHT+:C_ARCACHE_WIDTH]   = si_cc_arcache  ;
            assign s_ar_mesg[C_ARREGION_RIGHT+:C_ARREGION_WIDTH] = si_cc_arregion ;
            assign s_ar_mesg[C_ARQOS_RIGHT+:C_ARQOS_WIDTH]       = si_cc_arqos    ;
            assign cc_mi_arid     = m_ar_mesg[C_ARID_RIGHT+:C_ARID_WIDTH];
            assign cc_mi_arlen    = m_ar_mesg[C_ARLEN_RIGHT+:C_ARLEN_WIDTH];
            assign cc_mi_arsize   = m_ar_mesg[C_ARSIZE_RIGHT+:C_ARSIZE_WIDTH];
            assign cc_mi_arburst  = m_ar_mesg[C_ARBURST_RIGHT+:C_ARBURST_WIDTH];
            assign cc_mi_arlock   = m_ar_mesg[C_ARLOCK_RIGHT+:C_ARLOCK_WIDTH];
            assign cc_mi_arcache  = m_ar_mesg[C_ARCACHE_RIGHT+:C_ARCACHE_WIDTH];
            assign cc_mi_arregion = m_ar_mesg[C_ARREGION_RIGHT+:C_ARREGION_WIDTH];
            assign cc_mi_arqos    = m_ar_mesg[C_ARQOS_RIGHT+:C_ARQOS_WIDTH];
          end else if (C_AXI_PROTOCOL == P_AXI3) begin : gen_ar_axi3
            assign s_ar_mesg[C_ARID_RIGHT+:C_ARID_WIDTH]         = si_cc_arid     ;
            assign s_ar_mesg[C_ARLEN_RIGHT+:C_ARLEN_WIDTH]       = si_cc_arlen[3:0] ;
            assign s_ar_mesg[C_ARSIZE_RIGHT+:C_ARSIZE_WIDTH]     = si_cc_arsize   ;
            assign s_ar_mesg[C_ARBURST_RIGHT+:C_ARBURST_WIDTH]   = si_cc_arburst  ;
            assign s_ar_mesg[C_ARLOCK_RIGHT+:C_ARLOCK_WIDTH]     = si_cc_arlock   ;
            assign s_ar_mesg[C_ARCACHE_RIGHT+:C_ARCACHE_WIDTH]   = si_cc_arcache  ;
            assign s_ar_mesg[C_ARQOS_RIGHT+:C_ARQOS_WIDTH]       = si_cc_arqos    ;
            assign cc_mi_arid     = m_ar_mesg[C_ARID_RIGHT+:C_ARID_WIDTH];
            assign cc_mi_arlen    = m_ar_mesg[C_ARLEN_RIGHT+:C_ARLEN_WIDTH];
            assign cc_mi_arsize   = m_ar_mesg[C_ARSIZE_RIGHT+:C_ARSIZE_WIDTH];
            assign cc_mi_arburst  = m_ar_mesg[C_ARBURST_RIGHT+:C_ARBURST_WIDTH];
            assign cc_mi_arlock   = m_ar_mesg[C_ARLOCK_RIGHT+:C_ARLOCK_WIDTH];
            assign cc_mi_arcache  = m_ar_mesg[C_ARCACHE_RIGHT+:C_ARCACHE_WIDTH];
            assign cc_mi_arqos    = m_ar_mesg[C_ARQOS_RIGHT+:C_ARQOS_WIDTH];
          end
          if (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) begin : gen_ar_user
            assign s_ar_mesg[C_ARUSER_RIGHT+:C_ARUSER_WIDTH]  = si_cc_aruser;
            assign cc_mi_aruser = m_ar_mesg[C_ARUSER_RIGHT+:C_ARUSER_WIDTH];
          end
    
          axi_clock_converter_v2_1_10_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH ( C_AR_WIDTH ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE(P_LIGHT_WT)
          )
          ar_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( s_axi_aclk     ) ,
            .S_ARESETN  ( s_axi_aresetn ) ,
            .S_PAYLOAD ( s_ar_mesg ) ,
            .S_VALID   ( si_cc_arvalid   ) ,
            .S_READY   ( si_cc_arready   ) ,
            .M_ACLK     ( m_axi_aclk     ) ,
            .M_ARESETN  ( m_axi_aresetn ) ,
            .M_PAYLOAD ( m_ar_mesg ) ,
            .M_VALID   ( cc_mi_arvalid   ) ,
            .M_READY   ( cc_mi_arready   )
          );
    
          // Read Data Port
          assign m_r_mesg[C_RDATA_RIGHT+:C_RDATA_WIDTH] = cc_mi_rdata; 
          assign m_r_mesg[C_RRESP_RIGHT+:C_RRESP_WIDTH] = cc_mi_rresp; 
          assign si_cc_rdata    = s_r_mesg[C_RDATA_RIGHT+:C_RDATA_WIDTH];
          assign si_cc_rresp    = s_r_mesg[C_RRESP_RIGHT+:C_RRESP_WIDTH];
          if (C_AXI_PROTOCOL != P_AXILITE) begin : gen_r_axi
            assign m_r_mesg[C_RID_RIGHT+:C_RID_WIDTH]     = cc_mi_rid;   
            assign m_r_mesg[C_RLAST_RIGHT+:C_RLAST_WIDTH] = cc_mi_rlast;
            assign si_cc_rid      = s_r_mesg[C_RID_RIGHT+:C_RID_WIDTH];
            assign si_cc_rlast    = s_r_mesg[C_RLAST_RIGHT+:C_RLAST_WIDTH];
          end
          if (C_AXI_SUPPORTS_USER_SIGNALS && (C_AXI_PROTOCOL != P_AXILITE)) begin : gen_r_user
            assign m_r_mesg[C_RUSER_RIGHT+:C_RUSER_WIDTH] = cc_mi_ruser;
            assign si_cc_ruser  = s_r_mesg[C_RUSER_RIGHT+:C_RUSER_WIDTH];
          end
    
          axi_clock_converter_v2_1_10_axic_sync_clock_converter #(
            .C_FAMILY         ( C_FAMILY ) ,
            .C_PAYLOAD_WIDTH ( C_R_WIDTH ) ,
            .C_M_ACLK_RATIO   ( P_SI_LT_MI ? 1 : P_ACLK_RATIO ) ,
            .C_S_ACLK_RATIO   ( P_SI_LT_MI ? P_ACLK_RATIO : 1 ) ,
            .C_MODE((C_AXI_PROTOCOL == P_AXILITE) ? P_LIGHT_WT : P_FULLY_REG)
          )
          r_sync_clock_converter (
            .SAMPLE_CYCLE (sample_cycle),
            .SAMPLE_CYCLE_EARLY (sample_cycle_early),
            .S_ACLK     ( m_axi_aclk     ) ,
            .S_ARESETN  ( m_axi_aresetn ) ,
            .S_PAYLOAD ( m_r_mesg ) ,
            .S_VALID   ( cc_mi_rvalid   ) ,
            .S_READY   ( cc_mi_rready   ) ,
            .M_ACLK     ( s_axi_aclk     ) ,
            .M_ARESETN  ( s_axi_aresetn ) ,
            .M_PAYLOAD ( s_r_mesg ) ,
            .M_VALID   ( si_cc_rvalid   ) ,
            .M_READY   ( si_cc_rready   )
          );
    
        end else begin : gen_tieoff_read_ch
    
          // Read Address Port
          assign cc_mi_arid     = {C_AXI_ID_WIDTH{1'b0}};
          assign cc_mi_araddr   = {C_AXI_ADDR_WIDTH{1'b0}};
          assign cc_mi_arlen    = {8{1'b0}};
          assign cc_mi_arsize   = {3{1'b0}};
          assign cc_mi_arburst  = {2{1'b0}};
          assign cc_mi_arlock   = {2{1'b0}};
          assign cc_mi_arcache  = {4{1'b0}};
          assign cc_mi_arprot   = {3{1'b0}};
          assign cc_mi_arregion = {4{1'b0}};
          assign cc_mi_arqos    = {4{1'b0}};
          assign cc_mi_aruser   = {C_AXI_ARUSER_WIDTH{1'b0}};
          assign cc_mi_arvalid  = 1'b0;
          assign si_cc_arready  = 1'b0;
    
          // Read data port
          assign si_cc_rid      = {C_AXI_ID_WIDTH{1'b0}};
          assign si_cc_rdata    = {C_AXI_DATA_WIDTH{1'b0}};
          assign si_cc_rresp    = {2{1'b0}};
          assign si_cc_rlast    = 1'b0;
          assign si_cc_ruser    = {C_AXI_RUSER_WIDTH{1'b0}};
          assign si_cc_rvalid   = 1'b0;
          assign cc_mi_rready   = 1'b0;
        end
      end
    end

  endgenerate

endmodule



