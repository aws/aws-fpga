// =============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// =============================================================================


// CL AXI-LITE ADDER

`include "cl_clk_gen_defines.vh"

module cl_axil_adder (
  input  logic        clk,
  input  logic        rst_n,

  // AXI-Lite interface
  input  logic [31:0] s_axil_awaddr,
  input  logic        s_axil_awvalid,
  output logic        s_axil_awready,
  input  logic [31:0] s_axil_wdata,
  input  logic [3:0]  s_axil_wstrb,
  input  logic        s_axil_wvalid,
  output logic        s_axil_wready,
  output logic [1:0]  s_axil_bresp,
  output logic        s_axil_bvalid,
  input  logic        s_axil_bready,
  input  logic [31:0] s_axil_araddr,
  input  logic        s_axil_arvalid,
  output logic        s_axil_arready,
  output logic [31:0] s_axil_rdata,
  output logic [1:0]  s_axil_rresp,
  output logic        s_axil_rvalid,
  input  logic        s_axil_rready
);

//----------------------------
// Internal signals
//----------------------------

  // FSM states
  typedef enum logic [2:0] {
    IDLE       = 3'd0,
    WRITE_WAIT = 3'd1,
    WRITE      = 3'd2,
    WRITE_RESP = 3'd3,
    READ       = 3'd4
  } axil_state_t;

  axil_state_t current_state = IDLE;
  axil_state_t next_state;

  // Control and status signals
  logic start_pulse     = 1'b0;
  logic ready_flag      = 1'b0;
  logic sum_read_flag   = 1'b0;
  logic carry_read_flag = 1'b0;

  // Handshake signals
  logic data_wr_handshake;
  logic addr_rd_handshake;
  logic addr_wr_handshake;
  logic bresp_handshake;
  logic data_rd_handshake;

  // Register access logic
  logic [31:0] reg_operand_a      = 32'h0;
  logic [31:0] reg_operand_b      = 32'h0;
  logic [31:0] reg_sum            = 32'h0;
  logic [31:0] reg_carry          = 32'h0;
  logic [31:0] reg_control_status = 32'h0;

  // Address and data capture
  logic [31:0] write_addr = 32'h0;
  logic [31:0] write_data = 32'h0;

//-------------------------------------------------
// AXI-Lite Handshake & FSM
//-------------------------------------------------

// Handshake signals
always_comb begin
  addr_wr_handshake = s_axil_awvalid && s_axil_awready;
  data_wr_handshake = s_axil_wvalid  && s_axil_wready;
  bresp_handshake   = s_axil_bvalid  && s_axil_bready;
  addr_rd_handshake = s_axil_arvalid && s_axil_arready;
  data_rd_handshake = s_axil_rvalid  && s_axil_rready;
end

// FSM next state logic
always_comb begin
  next_state = current_state;
  case (current_state)

    IDLE: begin
      if (addr_wr_handshake && data_wr_handshake)
        next_state = WRITE;
      else if (addr_wr_handshake || data_wr_handshake)
        next_state = WRITE_WAIT;
      else if (addr_rd_handshake)
        next_state = READ;
    end

    WRITE_WAIT: begin
      if (addr_wr_handshake || data_wr_handshake)
        next_state = WRITE;
    end

    WRITE: begin
      next_state = WRITE_RESP;
    end

    WRITE_RESP: begin
      if (bresp_handshake)
        next_state = IDLE;
    end

    READ: begin
      if (data_rd_handshake)
        next_state = IDLE;
    end

    default: begin
      next_state = IDLE;
    end
  endcase
end

// FSM state register
always_ff @(posedge clk) begin
  if (!rst_n)
    current_state <= IDLE;
  else
    current_state <= next_state;
end

//============================================
// AXI-Lite CONTROL PATH
//============================================

// Address and data capture
always_ff @(posedge clk) begin
  if (addr_wr_handshake)
    write_addr <= s_axil_awaddr;
  if (data_wr_handshake)
    write_data <= s_axil_wdata;
end

// AXI-Lite output signals
always_ff @(posedge clk) begin
  if (!rst_n) begin
    s_axil_awready <= 1'b1;
    s_axil_wready  <= 1'b1;
    s_axil_bvalid  <= 1'b0;
    s_axil_bresp   <= 2'b00;
    s_axil_arready <= 1'b1;
    s_axil_rvalid  <= 1'b0;
    s_axil_rresp   <= 2'b00;
  end
  else begin
    s_axil_awready <= (next_state == IDLE) || (next_state == WRITE_WAIT);
    s_axil_wready  <= (next_state == IDLE) || (next_state == WRITE_WAIT);
    s_axil_bvalid  <= (next_state == WRITE_RESP);
    s_axil_bresp   <= `AXI_RESP_OKAY;
    s_axil_arready <= (next_state == IDLE);
    s_axil_rvalid  <= (next_state == READ);
    s_axil_rresp   <= `AXI_RESP_OKAY;
  end
end

//============================================
// AXI-Lite DATA PATH
//============================================

// Register writes
always_ff @(posedge clk) begin
  if (!rst_n) begin
    reg_operand_a <= 32'h0;
    reg_operand_b <= 32'h0;
  end else begin
    if (current_state == WRITE) begin
      case (write_addr)
        `ADDR_OPERAND_A : reg_operand_a <= write_data;
        `ADDR_OPERAND_B : reg_operand_b <= write_data;
      endcase
    end
  end
end

// Register reads
always_ff @(posedge clk) begin
  if (addr_rd_handshake) begin
    case (s_axil_araddr)
      `ADDR_OPERAND_A      : s_axil_rdata <= reg_operand_a;
      `ADDR_OPERAND_B      : s_axil_rdata <= reg_operand_b;
      `ADDR_SUM            : s_axil_rdata <= reg_sum;
      `ADDR_CARRY          : s_axil_rdata <= reg_carry;
      `ADDR_CONTROL_STATUS : s_axil_rdata <= reg_control_status;
      default              : s_axil_rdata <= `INVALID_ADDR_RESP;
    endcase
  end
end

//============================================
// APPLICATION LOGIC
//============================================

// Start pulse generation
always_ff @(posedge clk) begin
  start_pulse <= 1'b0;
  if (current_state == WRITE)
    start_pulse <= (write_addr == `ADDR_CONTROL_STATUS) && write_data[0];
end

// Addition logic
always_ff @(posedge clk) begin
  if (!rst_n) begin
    reg_sum   <= 32'h0;
    reg_carry <= 32'h0;
  end
  else if (start_pulse)
    {reg_carry[0], reg_sum} <= reg_operand_a + reg_operand_b;
end

// Ready flag
always_ff @(posedge clk) begin
  if (start_pulse)
    ready_flag <= 1'b1;
  else if (sum_read_flag && carry_read_flag)
    ready_flag <= 1'b0;
end

// Read flags
always_ff @(posedge clk) begin
  if (start_pulse) begin
    sum_read_flag   <= 1'b0;
    carry_read_flag <= 1'b0;
  end
  else if (addr_rd_handshake) begin
    if (s_axil_araddr == `ADDR_SUM)
      sum_read_flag <= 1'b1;
    if (s_axil_araddr == `ADDR_CARRY)
      carry_read_flag <= 1'b1;
  end
end

// Control/status register
always_ff @(posedge clk) begin
  if (!rst_n)
    reg_control_status <= 32'h0;
  else
    reg_control_status <= {30'h0, ready_flag, start_pulse};
end

endmodule
