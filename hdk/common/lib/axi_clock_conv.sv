// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


//Register slice with parameterizable ID to get rid of compile warnings (can add more parameters if need).
// Currently this is only used in RL, can extend to Static if needed.

module  axi_clock_conv #(parameter ID_WIDTH=16, USER_WIDTH=19) (
   input s_clk,
   input s_rst_n,

   input m_clk,
   input m_rst_n,

   axi4_bus_t.slave s_axi,
   axi4_bus_t.master m_axi
   );

logic[15:0] s_awid, s_arid, s_bid, s_rid;
logic[15:0] m_awid, m_arid, m_bid, m_rid;

logic[18:0] s_awuser, s_aruser;
logic[18:0] m_awuser, m_aruser;

assign s_awid = s_axi.awid;
assign s_arid = s_axi.arid;
assign s_axi.bid = s_bid;
assign s_axi.rid = s_rid;

assign m_axi.awid = m_awid;
assign m_axi.arid = m_arid;
assign m_bid = m_axi.bid;
assign m_rid = m_axi.rid;

assign s_awuser = s_axi.awuser;
assign s_aruser = s_axi.aruser;

assign m_axi.awuser = m_awuser;
assign m_axi.aruser = m_aruser;

cl_axi_clock_converter AXI_CLOCK_CONVERTER (
   .s_axi_aclk(s_clk),
   .s_axi_aresetn(s_rst_n),

   .m_axi_aclk(m_clk),
   .m_axi_aresetn(m_rst_n),

   .s_axi_awid    (s_awid   ),
   .s_axi_awaddr  (s_axi.awaddr ),
   .s_axi_awlen   (s_axi.awlen  ),
   .s_axi_awvalid (s_axi.awvalid),
   .s_axi_awsize  (s_axi.awsize ),
   .s_axi_awuser  (s_awuser ),
   .s_axi_awready (s_axi.awready),
   .s_axi_wdata   (s_axi.wdata  ),
   .s_axi_wstrb   (s_axi.wstrb  ),
   .s_axi_wlast   (s_axi.wlast  ),
   .s_axi_wvalid  (s_axi.wvalid ),
   .s_axi_wready  (s_axi.wready ),
   .s_axi_bid     (s_bid    ),
   .s_axi_bresp   (s_axi.bresp  ),
   .s_axi_bvalid  (s_axi.bvalid ),
   .s_axi_bready  (s_axi.bready ),
   .s_axi_arid    (s_arid   ),
   .s_axi_araddr  (s_axi.araddr ),
   .s_axi_arlen   (s_axi.arlen  ),
   .s_axi_aruser  (s_aruser ),
   .s_axi_arvalid (s_axi.arvalid),
   .s_axi_arsize  (s_axi.arsize ),
   .s_axi_arready (s_axi.arready),
   .s_axi_rid     (s_rid    ),
   .s_axi_rdata   (s_axi.rdata  ),
   .s_axi_rresp   (s_axi.rresp  ),
   .s_axi_rlast   (s_axi.rlast  ),
   .s_axi_rvalid  (s_axi.rvalid ),
   .s_axi_rready  (s_axi.rready ),

   .m_axi_awid    (m_awid   ),
   .m_axi_awaddr  (m_axi.awaddr ),
   .m_axi_awlen   (m_axi.awlen  ),
   .m_axi_awvalid (m_axi.awvalid),
   .m_axi_awsize  (m_axi.awsize ),
   .m_axi_awuser  (m_awuser ),
   .m_axi_awready (m_axi.awready),
   .m_axi_wdata   (m_axi.wdata  ),
   .m_axi_wstrb   (m_axi.wstrb  ),
   .m_axi_wlast   (m_axi.wlast  ),
   .m_axi_wvalid  (m_axi.wvalid ),
   .m_axi_wready  (m_axi.wready ),
   .m_axi_bid     (m_bid    ),
   .m_axi_bresp   (m_axi.bresp  ),
   .m_axi_bvalid  (m_axi.bvalid ),
   .m_axi_bready  (m_axi.bready ),
   .m_axi_arid    (m_arid   ),
   .m_axi_araddr  (m_axi.araddr ),
   .m_axi_arlen   (m_axi.arlen  ),
   .m_axi_aruser  (m_aruser ),
   .m_axi_arvalid (m_axi.arvalid),
   .m_axi_arsize  (m_axi.arsize ),
   .m_axi_arready (m_axi.arready),
   .m_axi_rid     (m_rid    ),
   .m_axi_rdata   (m_axi.rdata  ),
   .m_axi_rresp   (m_axi.rresp  ),
   .m_axi_rlast   (m_axi.rlast  ),
   .m_axi_rvalid  (m_axi.rvalid ),
   .m_axi_rready  (m_axi.rready ),

   .s_axi_awburst  (2'b01 ),
   .s_axi_awlock   (1'b0  ),
   .s_axi_awcache  (4'b00 ),
   .s_axi_awprot   (3'b10 ),
   .s_axi_awregion (4'b0  ),
   .s_axi_awqos    (4'b0  ),
   .s_axi_arburst  (2'b01 ),
   .s_axi_arlock   (1'b0  ),
   .s_axi_arcache  (4'b00 ),
   .s_axi_arprot   (3'b10 ),
   .s_axi_arregion (4'b0  ),
   .s_axi_arqos    (4'b0  ),

   .m_axi_awburst  (m_axi.awburst),
   .m_axi_awlock   (),
   .m_axi_awcache  (),
   .m_axi_awprot   (),
   .m_axi_awregion (),
   .m_axi_awqos    (),
   .m_axi_arburst  (m_axi.arburst),
   .m_axi_arlock   (),
   .m_axi_arcache  (),
   .m_axi_arprot   (),
   .m_axi_arregion (),
   .m_axi_arqos    ()
);

endmodule
