module cl_sda_slv (

   input aclk,
   input aresetn,

   input [31:0] sda_cl_awaddr,
   input sda_cl_awvalid,
   output logic cl_sda_awready,

   input [31:0] sda_cl_wdata,
   input [3:0] sda_cl_wstrb,
   input sda_cl_wvalid,
   output logic cl_sda_wready,

   output logic [1:0] cl_sda_bresp,
   output logic cl_sda_bvalid,
   input sda_cl_bready,

   input [31:0] sda_cl_araddr,
   input sda_cl_arvalid,
   output logic cl_sda_arready,

   output logic [31:0] cl_sda_rdata,
   output logic [1:0] cl_sda_rresp,
   output logic cl_sda_rvalid,
   input sda_cl_rready

);

axi_bus_t sda_cl_q();

   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) AXIL_SDA_REG_SLC (
    .aclk          (aclk),
    .aresetn       (aresetn),
    .sync_rst_n    (1'b1),
    .s_axi_awid    (1'b0),
    .s_axi_awaddr  (sda_cl_awaddr),
    .s_axi_awlen   (8'h0),                                            
    .s_axi_awvalid (sda_cl_awvalid),
    .s_axi_awuser  (1'b0),
    .s_axi_awready (cl_sda_awready),
    .s_axi_wdata   (sda_cl_wdata),
    .s_axi_wstrb   (sda_cl_wstrb),
    .s_axi_wlast   (1'b0),
    .s_axi_wuser   (1'b0),
    .s_axi_wvalid  (sda_cl_wvalid),
    .s_axi_wready  (cl_sda_wready),
    .s_axi_bid     (1'b0),
    .s_axi_bresp   (cl_sda_bresp),
    .s_axi_bvalid  (cl_sda_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sda_cl_bready),
    .s_axi_arid    (1'b0),
    .s_axi_araddr  (sda_cl_araddr),
    .s_axi_arlen   (8'h0), 
    .s_axi_arvalid (sda_cl_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (cl_sda_arready),
    .s_axi_rid     (1'b0),
    .s_axi_rdata   (cl_sda_rdata),
    .s_axi_rresp   (cl_sda_rresp),
    .s_axi_rlast   (),
    .s_axi_ruser   (),
    .s_axi_rvalid  (cl_sda_rvalid),
    .s_axi_rready  (sda_cl_rready), 
    .m_axi_awid    (),
    .m_axi_awaddr  (sda_cl_q.awaddr), 
    .m_axi_awlen   (),
    .m_axi_awvalid (sda_cl_q.awvalid),
    .m_axi_awuser  (),
    .m_axi_awready (sda_cl_q.awready),
    .m_axi_wdata   (sda_cl_q.wdata),  
    .m_axi_wstrb   (sda_cl_q.wstrb),
    .m_axi_wvalid  (sda_cl_q.wvalid), 
    .m_axi_wlast   (),
    .m_axi_wuser   (),
    .m_axi_wready  (sda_cl_q.wready), 
    .m_axi_bresp   (sda_cl_q.bresp),  
    .m_axi_bvalid  (sda_cl_q.bvalid), 
    .m_axi_bid     (),
    .m_axi_buser   (1'b0),
    .m_axi_bready  (sda_cl_q.bready), 
    .m_axi_arid    (), 
    .m_axi_araddr  (sda_cl_q.araddr), 
    .m_axi_arlen   (), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sda_cl_q.arvalid),
    .m_axi_arready (sda_cl_q.arready),
    .m_axi_rid     (),  
    .m_axi_rdata   (sda_cl_q.rdata),  
    .m_axi_rresp   (sda_cl_q.rresp),  
    .m_axi_rlast   (),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (sda_cl_q.rvalid), 
    .m_axi_rready  (sda_cl_q.rready)
   );


   axil_slave  AXIL_SLAVE(
      .clk(aclk),
      .rst_n(aresetn),
     
      .awvalid(sda_cl_q.awvalid), 
      .awaddr({32'b0, sda_cl_q.awaddr}),
      .awready(sda_cl_q.awready),
      
      .wvalid(sda_cl_q.wvalid),
      .wdata(sda_cl_q.wdata),
      .wstrb(sda_cl_q.wstrb),
      .wready(sda_cl_q.wready),
     
      .bvalid(sda_cl_q.bvalid), 
      .bresp(sda_cl_q.bresp),
      .bready(sda_cl_q.bready),
                   
      .arvalid(sda_cl_q.arvalid),
      .araddr({32'b0, sda_cl_q.araddr}),
      .arready(sda_cl_q.arready),
                    
      .rvalid(sda_cl_q.rvalid),
      .rdata(sda_cl_q.rdata),
      .rresp(sda_cl_q.rresp),
        
      .rready(sda_cl_q.rready)
   );

endmodule
   
