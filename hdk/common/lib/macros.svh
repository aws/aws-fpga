// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


`ifndef _MACROS_SVH_
`define _MACROS_SVH_

// lib_pipe instantiation
`define LIB_PIPE(instance_name, num_stages, width, clk_name, rst_n_name, src_bus, dest_bus)\
     lib_pipe #(.WIDTH(width), .STAGES(num_stages)) instance_name ( \
     .clk (clk_name),     \
     .rst_n (rst_n_name), \
     .in_bus  (src_bus),  \
     .out_bus (dest_bus)  \
     )

// cfg_bus pipeline instationtion
// Use reset only for control signals. Do not use reset for data/addr buses
`define CFG_BUS_PIPE(instance_name, num_stages, clk_name, rst_n_name, src_cfg_bus, dest_cfg_bus, addr_width, data_width)\
`LIB_PIPE(``instance_name``_CTL , num_stages, (1+1+1)   , clk_name, rst_n_name, {src_cfg_bus.wr, src_cfg_bus.rd, dest_cfg_bus.ack}, {dest_cfg_bus.wr, dest_cfg_bus.rd, src_cfg_bus.ack}); \
`LIB_PIPE(``instance_name``_DATA, num_stages, (addr_width+data_width+data_width), clk_name,       1'b1, {src_cfg_bus.addr, src_cfg_bus.wdata, dest_cfg_bus.rdata}, {dest_cfg_bus.addr, dest_cfg_bus.wdata, src_cfg_bus.rdata})

// Connect AXI-Lite ports (can be master or slave as indicated by port_prefix)
// The address width is used.  Note if the module connecting to has a different address width will
// get a compile warning.
`define CONNECT_AXIL_PORTS_W_ADDR_WIDTH(port_prefix, axil_bus, addr_width)\
    .``port_prefix``_axi_awaddr  (axil_bus.awaddr[(addr_width-1):0]),   \
    .``port_prefix``_axi_awvalid (axil_bus.awvalid ),                   \
    .``port_prefix``_axi_awready (axil_bus.awready ),                   \
    .``port_prefix``_axi_wdata   (axil_bus.wdata   ),                   \
    .``port_prefix``_axi_wstrb   (axil_bus.wstrb   ),                   \
    .``port_prefix``_axi_wvalid  (axil_bus.wvalid  ),                   \
    .``port_prefix``_axi_wready  (axil_bus.wready  ),                   \
    .``port_prefix``_axi_bresp   (axil_bus.bresp   ),                   \
    .``port_prefix``_axi_bvalid  (axil_bus.bvalid  ),                   \
    .``port_prefix``_axi_bready  (axil_bus.bready  ),                   \
    .``port_prefix``_axi_araddr  (axil_bus.araddr[(addr_width-1):0]),   \
    .``port_prefix``_axi_arvalid (axil_bus.arvalid ),                   \
    .``port_prefix``_axi_arready (axil_bus.arready ),                   \
    .``port_prefix``_axi_rdata   (axil_bus.rdata   ),                   \
    .``port_prefix``_axi_rresp   (axil_bus.rresp   ),                   \
    .``port_prefix``_axi_rvalid  (axil_bus.rvalid  ),                   \
    .``port_prefix``_axi_rready  (axil_bus.rready  )

// Connect Slave AXI-Lite ports
// The address width is used
`define CONNECT_SLAVE_AXIL_PORTS_W_ADDR_WIDTH(axil_bus, addr_width)\
`CONNECT_AXIL_PORTS_W_ADDR_WIDTH(s, axil_bus, addr_width)

// Connect Master AXI-Lite ports
// The address width is used
`define CONNECT_MASTER_AXIL_PORTS_W_ADDR_WIDTH(axil_bus, addr_width)\
`CONNECT_AXIL_PORTS_W_ADDR_WIDTH(m, axil_bus, addr_width)

// Connect AXI-Lite ports (can be master or slave as indicated by port_prefix)
// The address width is not used
`define CONNECT_AXIL_PORTS(port_prefix, axil_bus)\
    .``port_prefix``_axi_awaddr  (axil_bus.awaddr  ), \
    .``port_prefix``_axi_awvalid (axil_bus.awvalid ), \
    .``port_prefix``_axi_awready (axil_bus.awready ), \
    .``port_prefix``_axi_wdata   (axil_bus.wdata   ), \
    .``port_prefix``_axi_wstrb   (axil_bus.wstrb   ), \
    .``port_prefix``_axi_wvalid  (axil_bus.wvalid  ), \
    .``port_prefix``_axi_wready  (axil_bus.wready  ), \
    .``port_prefix``_axi_bresp   (axil_bus.bresp   ), \
    .``port_prefix``_axi_bvalid  (axil_bus.bvalid  ), \
    .``port_prefix``_axi_bready  (axil_bus.bready  ), \
    .``port_prefix``_axi_araddr  (axil_bus.araddr  ), \
    .``port_prefix``_axi_arvalid (axil_bus.arvalid ), \
    .``port_prefix``_axi_arready (axil_bus.arready ), \
    .``port_prefix``_axi_rdata   (axil_bus.rdata   ), \
    .``port_prefix``_axi_rresp   (axil_bus.rresp   ), \
    .``port_prefix``_axi_rvalid  (axil_bus.rvalid  ), \
    .``port_prefix``_axi_rready  (axil_bus.rready  )

// Connect Slave AXI-Lite ports
// The address width is not used
`define CONNECT_SLAVE_AXIL_PORTS(axil_bus)\
`CONNECT_AXIL_PORTS(s, axil_bus)

// Connect Master AXI-Lite ports
// The address width is not used
`define CONNECT_MASTER_AXIL_PORTS(axil_bus)\
`CONNECT_AXIL_PORTS(m, axil_bus)

// Connect AXI4 ports (can be master or slave as indicated by port_prefix)
// The address width is used
`define CONNECT_AXI4_PORTS_W_ADDR_WIDTH(port_prefix, axi4_bus, addr_width)\
    .``port_prefix``_axi_awid    (axi4_bus.awid   ),                   \
    .``port_prefix``_axi_awaddr  (axi4_bus.awaddr[(addr_width-1):0] ), \
    .``port_prefix``_axi_awlen   (axi4_bus.awlen  ),                   \
    .``port_prefix``_axi_awvalid (axi4_bus.awvalid),                   \
    .``port_prefix``_axi_awuser  (axi4_bus.awuser ),                   \
    .``port_prefix``_axi_awsize  (axi4_bus.awsize ),                   \
    .``port_prefix``_axi_awready (axi4_bus.awready),                   \
    .``port_prefix``_axi_wdata   (axi4_bus.wdata  ),                   \
    .``port_prefix``_axi_wstrb   (axi4_bus.wstrb  ),                   \
    .``port_prefix``_axi_wlast   (axi4_bus.wlast  ),                   \
    .``port_prefix``_axi_wuser   (axi4_bus.wuser  ),                   \
    .``port_prefix``_axi_wvalid  (axi4_bus.wvalid ),                   \
    .``port_prefix``_axi_wready  (axi4_bus.wready ),                   \
    .``port_prefix``_axi_bid     (axi4_bus.bid    ),                   \
    .``port_prefix``_axi_bresp   (axi4_bus.bresp  ),                   \
    .``port_prefix``_axi_bvalid  (axi4_bus.bvalid ),                   \
    .``port_prefix``_axi_buser   (axi4_bus.buser  ),                   \
    .``port_prefix``_axi_bready  (axi4_bus.bready ),                   \
    .``port_prefix``_axi_arid    (axi4_bus.arid   ),                   \
    .``port_prefix``_axi_araddr  (axi4_bus.araddr[(addr_width-1):0] ), \
    .``port_prefix``_axi_arlen   (axi4_bus.arlen  ),                   \
    .``port_prefix``_axi_arvalid (axi4_bus.arvalid),                   \
    .``port_prefix``_axi_aruser  (axi4_bus.aruser ),                   \
    .``port_prefix``_axi_arsize  (axi4_bus.arsize ),                   \
    .``port_prefix``_axi_arready (axi4_bus.arready),                   \
    .``port_prefix``_axi_rid     (axi4_bus.rid    ),                   \
    .``port_prefix``_axi_rdata   (axi4_bus.rdata  ),                   \
    .``port_prefix``_axi_rresp   (axi4_bus.rresp  ),                   \
    .``port_prefix``_axi_rlast   (axi4_bus.rlast  ),                   \
    .``port_prefix``_axi_ruser   (axi4_bus.ruser  ),                   \
    .``port_prefix``_axi_rvalid  (axi4_bus.rvalid ),                   \
    .``port_prefix``_axi_rready  (axi4_bus.rready )

// Connect Slave AXI4 ports
// The address width is used
`define CONNECT_SLAVE_AXI4_PORTS_W_ADDR_WIDTH(axi4_bus, addr_width)\
`CONNECT_AXI4_PORTS_W_ADDR_WIDTH(s, axi4_bus, addr_width)

// Connect Master AXI4 ports
// The address width is used
`define CONNECT_MASTER_AXI4_PORTS_W_ADDR_WIDTH(axi4_bus, addr_width)\
`CONNECT_AXI4_PORTS_W_ADDR_WIDTH(m, axi4_bus, addr_width)

// Connect AXI4 ports (can be master or slave as indicated by port_prefix)
// The address width is not used
//Don't think any block uses these    .``port_prefix``_axi_wuser   (axi4_bus.wuser  ), \
//Don't think any block uses these    .``port_prefix``_axi_buser   (axi4_bus.buser  ), \
//Don't think any block uses these    .``port_prefix``_axi_ruser   (axi4_bus.ruser  ), \
//    .``port_prefix``_axi_awuser  (axi4_bus.awuser ), \
//    .``port_prefix``_axi_aruser  (axi4_bus.aruser ), \
`define CONNECT_AXI4_PORTS(port_prefix, axi4_bus)    \
    .``port_prefix``_axi_awid    (axi4_bus.awid   ), \
    .``port_prefix``_axi_awaddr  (axi4_bus.awaddr ), \
    .``port_prefix``_axi_awlen   (axi4_bus.awlen  ), \
    .``port_prefix``_axi_awvalid (axi4_bus.awvalid), \
    .``port_prefix``_axi_awsize  (axi4_bus.awsize ), \
    .``port_prefix``_axi_awuser  (axi4_bus.awuser ), \
    .``port_prefix``_axi_awready (axi4_bus.awready), \
    .``port_prefix``_axi_wdata   (axi4_bus.wdata  ), \
    .``port_prefix``_axi_wstrb   (axi4_bus.wstrb  ), \
    .``port_prefix``_axi_wlast   (axi4_bus.wlast  ), \
    .``port_prefix``_axi_wvalid  (axi4_bus.wvalid ), \
    .``port_prefix``_axi_wready  (axi4_bus.wready ), \
    .``port_prefix``_axi_bid     (axi4_bus.bid    ), \
    .``port_prefix``_axi_bresp   (axi4_bus.bresp  ), \
    .``port_prefix``_axi_bvalid  (axi4_bus.bvalid ), \
    .``port_prefix``_axi_bready  (axi4_bus.bready ), \
    .``port_prefix``_axi_arid    (axi4_bus.arid   ), \
    .``port_prefix``_axi_araddr  (axi4_bus.araddr ), \
    .``port_prefix``_axi_arlen   (axi4_bus.arlen  ), \
    .``port_prefix``_axi_aruser  (axi4_bus.aruser ), \
    .``port_prefix``_axi_arvalid (axi4_bus.arvalid), \
    .``port_prefix``_axi_arsize  (axi4_bus.arsize ), \
    .``port_prefix``_axi_arready (axi4_bus.arready), \
    .``port_prefix``_axi_rid     (axi4_bus.rid    ), \
    .``port_prefix``_axi_rdata   (axi4_bus.rdata  ), \
    .``port_prefix``_axi_rresp   (axi4_bus.rresp  ), \
    .``port_prefix``_axi_rlast   (axi4_bus.rlast  ), \
    .``port_prefix``_axi_rvalid  (axi4_bus.rvalid ), \
    .``port_prefix``_axi_rready  (axi4_bus.rready )

// Connect AXI4 ports (can be master or slave as indicated by port_prefix)
// The address width is not used
`define CONNECT_AXI4_PORTS_NO_USER(port_prefix, axi4_bus)    \
    .``port_prefix``_axi_awid    (axi4_bus.awid   ), \
    .``port_prefix``_axi_awaddr  (axi4_bus.awaddr ), \
    .``port_prefix``_axi_awlen   (axi4_bus.awlen  ), \
    .``port_prefix``_axi_awvalid (axi4_bus.awvalid), \
    .``port_prefix``_axi_awsize  (axi4_bus.awsize ), \
    .``port_prefix``_axi_awready (axi4_bus.awready), \
    .``port_prefix``_axi_wdata   (axi4_bus.wdata  ), \
    .``port_prefix``_axi_wstrb   (axi4_bus.wstrb  ), \
    .``port_prefix``_axi_wlast   (axi4_bus.wlast  ), \
    .``port_prefix``_axi_wvalid  (axi4_bus.wvalid ), \
    .``port_prefix``_axi_wready  (axi4_bus.wready ), \
    .``port_prefix``_axi_bid     (axi4_bus.bid    ), \
    .``port_prefix``_axi_bresp   (axi4_bus.bresp  ), \
    .``port_prefix``_axi_bvalid  (axi4_bus.bvalid ), \
    .``port_prefix``_axi_bready  (axi4_bus.bready ), \
    .``port_prefix``_axi_arid    (axi4_bus.arid   ), \
    .``port_prefix``_axi_araddr  (axi4_bus.araddr ), \
    .``port_prefix``_axi_arlen   (axi4_bus.arlen  ), \
    .``port_prefix``_axi_arvalid (axi4_bus.arvalid), \
    .``port_prefix``_axi_arsize  (axi4_bus.arsize ), \
    .``port_prefix``_axi_arready (axi4_bus.arready), \
    .``port_prefix``_axi_rid     (axi4_bus.rid    ), \
    .``port_prefix``_axi_rdata   (axi4_bus.rdata  ), \
    .``port_prefix``_axi_rresp   (axi4_bus.rresp  ), \
    .``port_prefix``_axi_rlast   (axi4_bus.rlast  ), \
    .``port_prefix``_axi_rvalid  (axi4_bus.rvalid ), \
    .``port_prefix``_axi_rready  (axi4_bus.rready )

// Connect Slave AXI4 ports
// The address width is not used
`define CONNECT_SLAVE_AXI4_PORTS(axi4_bus)\
`CONNECT_AXI4_PORTS(s, axi4_bus)

// Connect Master AXI4 ports
// The address width is not used
`define CONNECT_MASTER_AXI4_PORTS(axi4_bus)\
`CONNECT_AXI4_PORTS(m, axi4_bus)

// Connect AXI-Stream ports (can be master or slave as indicated by port_prefix)
`define CONNECT_AXIS_PORTS(port_prefix, axis_bus) \
     .``port_prefix``_axis_tvalid  (axis_bus.valid  ), \
     .``port_prefix``_axis_tkeep   (axis_bus.keep   ), \
     .``port_prefix``_axis_tlast   (axis_bus.last   ), \
     .``port_prefix``_axis_tdata   (axis_bus.data   ), \
     .``port_prefix``_axis_tready  (axis_bus.ready  ), \
     .``port_prefix``_axis_tuser   (axis_bus.user   )

// Connect Slave AXI-Stream ports
`define CONNECT_SLAVE_AXIS_PORTS(axis_bus) \
`CONNECT_AXIS_PORTS(s, axis_bus)

// Connect Slave AXI-Master ports
`define CONNECT_MASTER_AXIS_PORTS(axis_bus) \
`CONNECT_AXIS_PORTS(m, axis_bus)

// AXI4 Register slice instance
`define AXI4_REG_SLC(module_name, instance_name, clk_name, rst_n_name, src_axi4_bus, dest_axi4_bus)\
     module_name instance_name (                \
     .aclk           (clk_name),                \
     .aresetn        (rst_n_name),              \
                                                \
     `CONNECT_SLAVE_AXI4_PORTS(src_axi4_bus),   \
     .s_axi_awburst  (2'b01 ),                  \
     .s_axi_awlock   (1'b0  ),                  \
     .s_axi_awcache  (4'b00 ),                  \
     .s_axi_awprot   (3'b10 ),                  \
     .s_axi_awregion (4'b0  ),                  \
     .s_axi_awqos    (4'b0  ),                  \
     .s_axi_arburst  (2'b01 ),                  \
     .s_axi_arlock   (1'b0  ),                  \
     .s_axi_arcache  (4'b00 ),                  \
     .s_axi_arprot   (3'b10 ),                  \
     .s_axi_arregion (4'b0  ),                  \
     .s_axi_arqos    (4'b0  ),                  \
                                                \
     `CONNECT_MASTER_AXI4_PORTS(dest_axi4_bus), \
     .m_axi_awburst  (dest_axi4_bus.awburst),   \
     .m_axi_awlock   (dest_axi4_bus.awlock),   \
     .m_axi_awcache  (dest_axi4_bus.awcache),   \
     .m_axi_awprot   (dest_axi4_bus.awprot),   \
     .m_axi_awregion (),                        \
     .m_axi_awqos    (dest_axi4_bus.awqos),   \
     .m_axi_arburst  (dest_axi4_bus.arburst),   \
     .m_axi_arlock   (dest_axi4_bus.arlock),   \
     .m_axi_arcache  (dest_axi4_bus.arcache),   \
     .m_axi_arprot   (dest_axi4_bus.arprot),   \
     .m_axi_arregion (),                        \
     .m_axi_arqos    (dest_axi4_bus.arqos)    \
   )


`define AXIL_REG_SLC(module_name, instance_name, clk_name, rst_n_name, src_axil_bus, dest_axil_bus)\
     module_name instance_name (                  \
     .aclk          (clk_name),                   \
     .aresetn       (rst_n_name),                 \
                                                  \
     `CONNECT_SLAVE_AXIL_PORTS(src_axil_bus),     \
     `CONNECT_MASTER_AXIL_PORTS(dest_axil_bus)    \
   );

`define AXIL_REG_SLC_W_ADDR_WIDTH(module_name, instance_name, clk_name, rst_n_name, src_axil_bus, dest_axil_bus, addr_width)\
     module_name instance_name (                  \
     .aclk          (clk_name),                   \
     .aresetn       (rst_n_name),                 \
                                                  \
     `CONNECT_SLAVE_AXIL_PORTS_W_ADDR_WIDTH(src_axil_bus, addr_width),     \
     `CONNECT_MASTER_AXIL_PORTS_W_ADDR_WIDTH(dest_axil_bus, addr_width)    \
   );



`define AXIS_REG_SLC(module_name, instance_name, clk_name, rst_n_name, src_axis_bus, dest_axis_bus)\
     module_name instance_name (                  \
     .aclk          (clk_name),                   \
     .aresetn       (rst_n_name),                 \
                                                  \
     `CONNECT_SLAVE_AXIS_PORTS (src_axis_bus),    \
     `CONNECT_MASTER_AXIS_PORTS (dest_axis_bus)   \
    );

`define DIFF_CLK_IBUFDS(module_name, instance_name, in_clk_p, in_clk_n, out_clk, out_clk_div2)\
     module_name instance_name (       \
     .CEB   (1'b0),                    \
     .I     (in_clk_p),                \
     .IB    (in_clk_n),                \
     .O     (out_clk),                 \
     .ODIV2 (out_clk_div2)             \
    );


//This adds burst, lock, cache, prot, region, qos signals
`define CONNECT_SLAVE_AXI4_PORTS_FULL(axi4_bus)\
    `CONNECT_SLAVE_AXI4_PORTS(axi4_bus)      \
    ,                                                    \
    .s_axi_awburst (2'b01),                              \
    .s_axi_awlock  (1'b0),                               \
    .s_axi_awcache (4'b00),                              \
    .s_axi_awprot  (3'b10),                              \
    .s_axi_awregion(4'b0),                               \
    .s_axi_awqos   (4'b0),                               \
    .s_axi_arburst (2'b01),                              \
    .s_axi_arlock  (1'b0),                               \
    .s_axi_arcache (4'b00),                              \
    .s_axi_arprot  (3'b10),                              \
    .s_axi_arregion(4'b0),                               \
    .s_axi_arqos   (4'b0)

//This adds burst, lock, cache, prot, region, qos signals (no connect)
`define CONNECT_MASTER_AXI4_PORTS_FULL(axi4_bus)            \
    `CONNECT_MASTER_AXI4_PORTS(axi4_bus)                    \
    ,                                                       \
    .m_axi_awburst (),                                      \
    .m_axi_awlock  (),                                      \
    .m_axi_awcache (),                                      \
    .m_axi_awprot  (),                                      \
    .m_axi_awregion(),                                      \
    .m_axi_awqos   (),                                      \
    .m_axi_arburst (),                                      \
    .m_axi_arlock  (),                                      \
    .m_axi_arcache (),                                      \
    .m_axi_arprot  (),                                      \
    .m_axi_arregion(),                                      \
    .m_axi_arqos   ()

//This is ISOLATION logic for a single AXI signal.  note first parameter is the
// isolated signal (signal we are assigning to).
`define AXI_ISOL_SIGNAL(isl_sig, sig, cfg_pr_isol, cfg_isol_deassert_rdy)  \
   assign isl_sig =  (cfg_pr_isol && cfg_isol_deassert_rdy)?   0:          \
                     (cfg_pr_isol)?                            1:          \
                                                               sig;

//This is ISOLATION for an entire AXI-L bus.  THe slave/master has same convention as register slice.
// slave is slave port on the "isolation" block, and is what the master connects to (i.e. Shell).
// master is the master port ont the "isolation" block and is what the downstream slave (i.e. CL) connects
// to.  Will apply the isolation to the master response signals, and apply to the slave side
`define AXIL_ISOLATION(slv_bus, mst_bus, pr_isol, cfg_isol_deassert_rdy)   \
   assign mst_bus.awaddr =     slv_bus.awaddr;                          \
   assign mst_bus.awvalid =    slv_bus.awvalid;                         \
   assign mst_bus.wdata =      slv_bus.wdata;                           \
   assign mst_bus.wstrb =      slv_bus.wstrb;                           \
   assign mst_bus.wvalid =     slv_bus.wvalid;                          \
   assign mst_bus.bready =     slv_bus.bready;                          \
   assign mst_bus.araddr =     slv_bus.araddr;                          \
   assign mst_bus.arvalid =    slv_bus.arvalid;                         \
   assign mst_bus.rready =     slv_bus.rready;                          \
                                                                              \
   assign slv_bus.bresp = mst_bus.bresp;                                \
   assign slv_bus.rdata = mst_bus.rdata;                                \
   assign slv_bus.rresp = mst_bus.rresp;                                \
                                                                              \
   `AXI_ISOL_SIGNAL(slv_bus.awready, mst_bus.awready, cfg_pr_isol, cfg_isol_deassert_rdy) \
   `AXI_ISOL_SIGNAL(slv_bus.wready,  mst_bus.wready, cfg_pr_isol, cfg_isol_deassert_rdy) \
   `AXI_ISOL_SIGNAL(slv_bus.bvalid,  mst_bus.bvalid, cfg_pr_isol, cfg_isol_deassert_rdy) \
   `AXI_ISOL_SIGNAL(slv_bus.arready, mst_bus.arready, cfg_pr_isol, cfg_isol_deassert_rdy) \
   `AXI_ISOL_SIGNAL(slv_bus.rvalid,  mst_bus.rvalid, cfg_pr_isol, cfg_isol_deassert_rdy)

//This is ISOLATION for an entire AXI-L bus.  THe slave/master has same convention as register slice.
// slave is slave port on the "isolation" block, and is what the master connects to (i.e. Shell).
// master is the master port ont the "isolation" block and is what the downstream slave (i.e. CL) connects
// to.  Will apply the isolation to the master response signals, and apply to the slave side
`define AXI_ISOLATION(slv_bus, mst_bus, pr_isol, cfg_isol_deassert_rdy)         \
   assign mst_bus.awid          = slv_bus.awid;         \
   assign mst_bus.awaddr        = slv_bus.awaddr;       \
   assign mst_bus.awlen         = slv_bus.awlen;        \
   assign mst_bus.awsize        = slv_bus.awsize;       \
   assign mst_bus.awvalid       = slv_bus.awvalid;      \
   assign mst_bus.wdata         = slv_bus.wdata;        \
   assign mst_bus.wstrb         = slv_bus.wstrb;        \
   assign mst_bus.wlast         = slv_bus.wlast;        \
   assign mst_bus.wvalid        = slv_bus.wvalid;       \
   assign mst_bus.bready        = slv_bus.bready;       \
   assign mst_bus.arid          = slv_bus.arid;         \
   assign mst_bus.araddr        = slv_bus.araddr;       \
   assign mst_bus.arlen         = slv_bus.arlen;        \
   assign mst_bus.arsize        = slv_bus.arsize;       \
   assign mst_bus.arvalid       = slv_bus.arvalid;      \
   assign mst_bus.rready        = slv_bus.rready;       \
                                                            \
   assign slv_bus.bid = mst_bus.bid;                    \
   assign slv_bus.bresp = mst_bus.bresp;                \
   assign slv_bus.rdata = mst_bus.rdata;                \
   assign slv_bus.rresp = mst_bus.rresp;                \
   assign slv_bus.rlast = mst_bus.rlast;                \
   assign slv_bus.rid = mst_bus.rid;                    \
                                                            \
   `AXI_ISOL_SIGNAL(slv_bus.awready, mst_bus.awready, pr_isol, cfg_isol_deassert_rdy)    \
   `AXI_ISOL_SIGNAL(slv_bus.wready, mst_bus.wready, pr_isol, cfg_isol_deassert_rdy)      \
   `AXI_ISOL_SIGNAL(slv_bus.arready, mst_bus.arready, pr_isol, cfg_isol_deassert_rdy)    \
                                                                                         \
   assign slv_bus.rvalid = pr_isol ? '0 : mst_bus.rvalid; \
   assign slv_bus.bvalid = pr_isol ? '0 : mst_bus.bvalid;

//Assign AXI-L bus (slave to master).  Uses same convention as Xilinx IP, "slave" is what
// an external master connects to, and "master" drives downstream logic.  Note when using
// this must be in an always_comb block
//
`define ASSIGN_AXIL_BUS(slave, master) \
      master.awaddr = slave.awaddr;      \
      master.awvalid = slave.awvalid;    \
      slave.awready = master.awready;    \
                                         \
      master.wdata = slave.wdata;        \
      master.wstrb = slave.wstrb;        \
      master.wvalid = slave.wvalid;      \
      slave.wready = master.wready;      \
                                         \
      slave.bresp = master.bresp;        \
      slave.bvalid = master.bvalid;      \
      master.bready = slave.bready;      \
                                         \
      master.araddr = slave.araddr;      \
      master.arvalid = slave.arvalid;    \
      slave.arready = master.arready;    \
                                         \
      slave.rdata = master.rdata;        \
      slave.rresp = master.rresp;        \
      slave.rvalid = master.rvalid;      \
      master.rready = slave.rready;

//Assign AXI bus (slave to master).
`define ASSIGN_AXI_BUS(slave, master)  \
   master.awid = slave.awid;           \
   master.awaddr = slave.awaddr;       \
   master.awlen = slave.awlen;         \
   master.awsize = slave.awsize;       \
   master.awuser = slave.awuser;       \
   master.awvalid = slave.awvalid;     \
   master.awburst = slave.awburst;     \
   master.awcache = slave.awcache;     \
   master.awlock = slave.awlock;       \
   master.awprot = slave.awprot;       \
   master.awqos = slave.awqos;         \
   slave.awready = master.awready;     \
                                       \
   master.wid = slave.wid;             \
   master.wdata = slave.wdata;         \
   master.wstrb = slave.wstrb;         \
   master.wlast = slave.wlast;         \
   master.wvalid = slave.wvalid;       \
   slave.wready = master.wready;       \
                                       \
   slave.bid = master.bid;             \
   slave.bresp = master.bresp;         \
   slave.bvalid = master.bvalid;       \
   master.bready = slave.bready;       \
                                       \
   master.arid = slave.arid;           \
   master.araddr = slave.araddr;       \
   master.arlen = slave.arlen;         \
   master.arsize = slave.arsize;       \
   master.aruser = slave.aruser;       \
   master.arvalid = slave.arvalid;     \
   master.arburst = slave.arburst;     \
   master.arcache = slave.arcache;     \
   master.arlock = slave.arlock;       \
   master.arprot = slave.arprot;       \
   master.arqos = slave.arqos;         \
   slave.arready = master.arready;     \
                                       \
   slave.rid = master.rid;             \
   slave.rdata = master.rdata;         \
   slave.rresp = master.rresp;         \
   slave.rlast = master.rlast;         \
   slave.rvalid = master.rvalid;       \
   master.rready = slave.rready;



//Assign AXIS bus (slave to master).
`define ASSIGN_AXIS_BUS(slave, master)  \
   master.valid = slave.valid;           \
   master.keep = slave.keep;           \
   master.last = slave.last;           \
   master.data = slave.data;           \
   master.user = slave.user;           \
   slave.ready = master.ready;

//Connect AXIS Bus
`define CONNECT_AXIS_BUS(port_prefix, axis_bus)\
   .``port_prefix``_axis_tvalid(axis_bus.valid),\
   .``port_prefix``_axis_tready(axis_bus.ready),\
   .``port_prefix``_axis_tdata(axis_bus.data),\
   .``port_prefix``_axis_tkeep(axis_bus.keep),\
   .``port_prefix``_axis_tlast(axis_bus.last)

//Connect AXIS Bus with USER
`define CONNECT_AXIS_BUS_USER(port_prefix, axis_bus)\
   .``port_prefix``_axis_tvalid(axis_bus.valid),\
   .``port_prefix``_axis_tready(axis_bus.ready),\
   .``port_prefix``_axis_tdata(axis_bus.data),\
   .``port_prefix``_axis_tkeep(axis_bus.keep),\
   .``port_prefix``_axis_tlast(axis_bus.last),\
   .``port_prefix``_axis_tuser(axis_bus.user)


//These macros allow for connections between interfaces and expanded interfaces.  This is done by not assuming
// the "." separator betwen bus name and AXI signal.
//Assign AXI bus (slave to master).
`define EXP_ASSIGN_AXI_BUS(slave, master)  \
   ``master``awid = ``slave``awid;           \
   ``master``awaddr = ``slave``awaddr;       \
   ``master``awlen = ``slave``awlen;         \
   ``master``awsize = ``slave``awsize;       \
   ``master``awuser = ``slave``awuser;       \
   ``master``awvalid = ``slave``awvalid;     \
   ``master``awburst = ``slave``awburst;     \
   ``master``awcache = ``slave``awcache;     \
   ``master``awlock = ``slave``awlock;       \
   ``master``awprot = ``slave``awprot;       \
   ``master``awqos = ``slave``awqos;         \
   ``slave``awready = ``master``awready;     \
                                                    \
   ``master``wid = ``slave``wid;             \
   ``master``wdata = ``slave``wdata;         \
   ``master``wstrb = ``slave``wstrb;         \
   ``master``wlast = ``slave``wlast;         \
   ``master``wvalid = ``slave``wvalid;       \
   ``slave``wready = ``master``wready;       \
                                                    \
   ``slave``bid = ``master``bid;             \
   ``slave``bresp = ``master``bresp;         \
   ``slave``bvalid = ``master``bvalid;       \
   ``master``bready = ``slave``bready;       \
                                                    \
   ``master``arid = ``slave``arid;           \
   ``master``araddr = ``slave``araddr;       \
   ``master``arlen = ``slave``arlen;         \
   ``master``arsize = ``slave``arsize;       \
   ``master``aruser = ``slave``aruser;       \
   ``master``arvalid = ``slave``arvalid;     \
   ``master``arburst = ``slave``arburst;     \
   ``master``arcache = ``slave``arcache;     \
   ``master``arlock = ``slave``arlock;       \
   ``master``arprot = ``slave``arprot;       \
   ``master``arqos = ``slave``arqos;         \
   ``slave``arready = ``master``arready;     \
                                                    \
   ``slave``rid = ``master``rid;             \
   ``slave``rdata = ``master``rdata;         \
   ``slave``rresp = ``master``rresp;         \
   ``slave``rlast = ``master``rlast;         \
   ``slave``rvalid = ``master``rvalid;       \
   ``master``rready = ``slave``rready;

`define EXP_ASSIGN_AXIL_BUS(slave, master) \
      ``master``awaddr = ``slave``awaddr;      \
      ``master``awvalid = ``slave``awvalid;    \
      ``slave``awready = ``master``awready;    \
                                                      \
      ``master``wdata = ``slave``wdata;        \
      ``master``wstrb = ``slave``wstrb;        \
      ``master``wvalid = ``slave``wvalid;      \
      ``slave``wready = ``master``wready;      \
                                                      \
      ``slave``bresp = ``master``bresp;        \
      ``slave``bvalid = ``master``bvalid;      \
      ``master``bready = ``slave``bready;      \
                                                      \
      ``master``araddr = ``slave``araddr;      \
      ``master``arvalid = ``slave``arvalid;    \
      ``slave``arready = ``master``arready;    \
                                                      \
      ``slave``rdata = ``master``rdata;        \
      ``slave``rresp = ``master``rresp;        \
      ``slave``rvalid = ``master``rvalid;      \
      ``master``rready = ``slave``rready;

`define EXP_ASSIGN_CFG_BUS(slave, master) \
   ``master``addr = ``slave``addr;        \
   ``master``wdata = ``slave``wdata;      \
   ``master``wr = ``slave``wr;            \
   ``master``rd = ``slave``rd;            \
   ``master``user = ``slave``user;        \
                                                 \
   ``slave``ack = ``master``ack;          \
   ``slave``rdata = ``master``rdata;

//bus_name is the port on the instace, if_name is the interface name to connect to
`define EXP_CONNECT_AXI_BUS(port_name, if_name)  \
   .port_name_awid(if_name.awid),           \
   .port_name_awaddr(if_name.awaddr),       \
   .port_name_awlen(if_name.awlen),         \
   .port_name_awsize(if_name.awsize),       \
   .port_name_awuser(if_name.awuser),       \
   .port_name_awvalid(if_name.awvalid),     \
   .port_name_awburst(if_name.awburst),     \
   .port_name_awcache(if_name.awcache),     \
   .port_name_awlock(if_name.awlock),       \
   .port_name_awprot(if_name.awprot),       \
   .port_name_awqos(if_name.awqos),         \
   .port_name_awready(if_name.awready),     \
                                       \
   .port_name_wid(if_name.wid),             \
   .port_name_wdata(if_name.wdata),         \
   .port_name_wstrb(if_name.wstrb),         \
   .port_name_wlast(if_name.wlast),         \
   .port_name_wvalid(if_name.wvalid),       \
   .port_name_wready(if_name.wready),       \
                                       \
   .port_name_bid(if_name.bid),             \
   .port_name_bresp(if_name.bresp),         \
   .port_name_bvalid(if_name.bvalid),       \
   .port_name_bready(if_name.bready),       \
                                             \
   .port_name_arid(if_name.arid),           \
   .port_name_araddr(if_name.araddr),       \
   .port_name_arlen(if_name.arlen),         \
   .port_name_arsize(if_name.arsize),       \
   .port_name_aruser(if_name.aruser),       \
   .port_name_arvalid(if_name.arvalid),     \
   .port_name_arburst(if_name.arburst),     \
   .port_name_arcache(if_name.arcache),     \
   .port_name_arlock(if_name.arlock),       \
   .port_name_arprot(if_name.arprot),       \
   .port_name_arqos(if_name.arqos),         \
   .port_name_arready(if_name.arready),     \
                                       \
   .port_name_rid(if_name.rid),             \
   .port_name_rdata(if_name.rdata),         \
   .port_name_rresp(if_name.rresp),         \
   .port_name_rlast(if_name.rlast),         \
   .port_name_rvalid(if_name.rvalid),       \
   .port_name_rready(if_name.rready)

`define EXP_CONNECT_AXIL_BUS(slave, master) \
      .port_name_awaddr(if_name.awaddr),      \
      .port_name_awvalid(if_name.awvalid),    \
      .port_name_awready(if_name.awready),    \
                                         \
      .port_name_wdata(if_name.wdata),        \
      .port_name_wstrb(if_name.wstrb),        \
      .port_name_wvalid(if_name.wvalid),      \
      .port_name_wready(if_name.wready),      \
                                         \
      .port_name_bresp(if_name.bresp),        \
      .port_name_bvalid(if_name.bvalid),      \
      .port_name_bready(if_name.bready),      \
                                         \
      .port_name_araddr(if_name.araddr),      \
      .port_name_arvalid(if_name.arvalid),    \
      .port_name_arready(if_name.arready),    \
                                         \
      .port_name_rdata(if_name.rdata),        \
      .port_name_rresp(if_name.rresp),        \
      .port_name_rvalid(if_name.rvalid),      \
      .port_name_rready(if_name.rready)

`define EXP_CONNECT_CFG_BUS(slave, master) \
   .port_name_addr(if_name.addr),        \
   .port_name_wdata(if_name.wdata),      \
   .port_name_wr(if_name.wr),            \
   .port_name_rd(if_name.rd),            \
   .port_name_user(if_name.user),        \
                                          \
   .port_name_ack(if_name.ack),          \
   .port_name_rdata(if_name.rdata)


`endif //  `ifndef _MACROS_SVH_
