// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

module hello_world 


	(
		input logic  s_axi_aclk,
		input logic  s_axi_aresetn,
		input logic [31 : 0] s_axi_awaddr,
		input logic [2 : 0] s_axi_awprot,

		input logic  s_axi_awvalid,

		output logic  s_axi_awready,
		input logic [31 : 0] s_axi_wdata,
    
		input logic [3 : 0] s_axi_wstrb,

		input logic  s_axi_wvalid,

		output logic  s_axi_wready,

		output logic [1 : 0] s_axi_bresp,

		output logic  s_axi_bvalid,

		input logic  s_axi_bready,
		input logic [31 : 0] s_axi_araddr,

		input logic [2 : 0] s_axi_arprot,

		input logic  s_axi_arvalid,

		output logic  s_axi_arready,
		output logic [31 : 0] s_axi_rdata,
		output logic [1 : 0] s_axi_rresp,

		output logic  s_axi_rvalid,
		input logic  s_axi_rready,
		input logic [15:0] vdip,
		output logic [15:0] vled
	);

`include "cl_common_defines.vh" // CL Defines for cl_hello_world



//-------------------------------------------------
// Wires
//-------------------------------------------------
  logic        arvalid_q;
  logic [31:0] araddr_q;
  logic [31:0] hello_world_q_byte_swapped;
  logic [15:0] vled_q;
  logic [15:0] pre_cl_sh_status_vled;
  logic [15:0] sh_cl_status_vdip_q;
  logic [15:0] sh_cl_status_vdip_q2;
  logic [31:0] hello_world_q;




//--------------------------------------------------------------
// PCIe OCL AXI-L Slave Accesses (accesses from PCIe AppPF BAR0)
//--------------------------------------------------------------
// Only supports single-beat accesses.

   logic        awvalid;
   logic [31:0] awaddr;
   logic        wvalid;
   logic [31:0] wdata;
   logic [3:0]  wstrb;
   logic        bready;
   logic        arvalid;
   logic [31:0] araddr;
   logic        rready;



   // Inputs
   assign awvalid         = s_axi_awvalid;
   assign awaddr[31:0]    = s_axi_awaddr;
   assign wvalid          = s_axi_wvalid;
   assign wdata[31:0]     = s_axi_wdata;
   assign wstrb[3:0]      = s_axi_wstrb;
   assign bready          = s_axi_bready;
   assign arvalid         = s_axi_arvalid;
   assign araddr[31:0]    = s_axi_araddr;
   assign rready          = s_axi_rready;



// Write Request
logic        wr_active;
logic [31:0] wr_addr;

always_ff @(posedge s_axi_aclk)
  if (!s_axi_aresetn) begin
     wr_active <= 0;
     wr_addr   <= 0;
  end
  else begin
     wr_active <=  wr_active && s_axi_bvalid  && bready ? 1'b0     :
                  ~wr_active && awvalid           ? 1'b1     :
                                                    wr_active;
     wr_addr <= awvalid && ~wr_active ? awaddr : wr_addr     ;
  end

assign s_axi_awready = ~wr_active;
assign s_axi_wready  =  wr_active && wvalid;

// Write Response
always_ff @(posedge s_axi_aclk)
  if (!s_axi_aresetn) 
    s_axi_bvalid <= 0;
  else
    s_axi_bvalid <=  s_axi_bvalid &&  bready           ? 1'b0  : 
                         ~s_axi_bvalid && s_axi_wready ? 1'b1  :
                                             s_axi_bvalid;
assign s_axi_bresp = 0;

// Read Request
always_ff @(posedge s_axi_aclk)
   if (!s_axi_aresetn) begin
      arvalid_q <= 0;
      araddr_q  <= 0;
   end
   else begin
      arvalid_q <= arvalid;
      araddr_q  <= arvalid ? araddr : araddr_q;
   end

assign s_axi_arready = !arvalid_q && !s_axi_rvalid;

// Read Response
always_ff @(posedge s_axi_aclk)
   if (!s_axi_aresetn)
   begin
      s_axi_rvalid <= 0;
      s_axi_rdata  <= 0;
      s_axi_rresp  <= 0;
   end
   else if (s_axi_rvalid && rready)
   begin
      s_axi_rvalid <= 0;
      s_axi_rdata  <= 0;
      s_axi_rresp  <= 0;
   end
   else if (arvalid_q) 
   begin
      s_axi_rvalid <= 1;
      s_axi_rdata  <= (araddr_q == `HELLO_WORLD_REG_ADDR) ? hello_world_q_byte_swapped[31:0]:
                (araddr_q == `VLED_REG_ADDR       ) ? {16'b0,vled_q[15:0]            }:
                                                      `UNIMPLEMENTED_REG_VALUE        ;
      s_axi_rresp  <= 0;
   end

//-------------------------------------------------
// Hello World Register
//-------------------------------------------------
// When read it, returns the byte-flipped value.

always_ff @(posedge s_axi_aclk)
   if (!s_axi_aresetn) begin                    // Reset
      hello_world_q[31:0] <= 32'h0000_0000;
   end
   else if (s_axi_wready & (wr_addr == `HELLO_WORLD_REG_ADDR)) begin  
      hello_world_q[31:0] <= wdata[31:0];
   end
   else begin                                // Hold Value
      hello_world_q[31:0] <= hello_world_q[31:0];
   end

assign hello_world_q_byte_swapped[31:0] = {hello_world_q[7:0],   hello_world_q[15:8],
                                           hello_world_q[23:16], hello_world_q[31:24]};

//-------------------------------------------------
// Virtual LED Register
//-------------------------------------------------
// Flop/synchronize interface signals
always_ff @(posedge s_axi_aclk)
   if (!s_axi_aresetn) begin                    // Reset
      sh_cl_status_vdip_q[15:0]  <= 16'h0000;
      sh_cl_status_vdip_q2[15:0] <= 16'h0000;
      vled[15:0]    <= 16'h0000;
   end
   else begin
      sh_cl_status_vdip_q[15:0]  <= vdip[15:0];
      sh_cl_status_vdip_q2[15:0] <= sh_cl_status_vdip_q[15:0];
      vled[15:0]    <= pre_cl_sh_status_vled[15:0];
   end

// The register contains 16 read-only bits corresponding to 16 LED's.
// For this example, the virtual LED register shadows the hello_world
// register.
// The same LED values can be read from the CL to Shell interface
// by using the linux FPGA tool: $ fpga-get-virtual-led -S 0

always_ff @(posedge s_axi_aclk)
   if (!s_axi_aresetn) begin                    // Reset
      vled_q[15:0] <= 16'h0000;
   end
   else begin
      vled_q[15:0] <= hello_world_q[15:0];
   end

// The Virtual LED outputs will be masked with the Virtual DIP switches.
assign pre_cl_sh_status_vled[15:0] = vled_q[15:0] & sh_cl_status_vdip_q2[15:0];






endmodule





