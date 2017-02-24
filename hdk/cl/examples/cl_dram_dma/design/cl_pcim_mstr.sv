module cl_pcim_mstr (
   input aclk,
   input aresetn,

   cfg_bus_t cfg_bus,

   output logic[15:0] cl_sh_pcim_awid,
   output logic[63:0] cl_sh_pcim_awaddr,
   output logic[7:0] cl_sh_pcim_awlen,
   output logic[2:0] cl_sh_pcim_awsize,
   output logic cl_sh_pcim_awvalid,
   input sh_cl_pcim_awready,
   
   output logic[511:0] cl_sh_pcim_wdata,
   output logic[63:0] cl_sh_pcim_wstrb,
   output logic cl_sh_pcim_wlast,
   output logic cl_sh_pcim_wvalid,
   input sh_cl_pcim_wready,
   
   input logic[15:0] sh_cl_pcim_bid,
   input logic[1:0] sh_cl_pcim_bresp,
   input logic sh_cl_pcim_bvalid,
   output logic cl_sh_pcim_bready,
  
   output logic[15:0] cl_sh_pcim_arid,		                           
   output logic[63:0] cl_sh_pcim_araddr,
   output logic[7:0] cl_sh_pcim_arlen,
   output logic[2:0] cl_sh_pcim_arsize,
   output logic cl_sh_pcim_arvalid,
   input sh_cl_pcim_arready,
   
   input[15:0] sh_cl_pcim_rid,
   input[511:0] sh_cl_pcim_rdata,
   input[1:0] sh_cl_pcim_rresp,
   input sh_cl_pcim_rlast,
   input sh_cl_pcim_rvalid,
   output logic cl_sh_pcim_rready

);

axi_bus_t cl_sh_pcim_q();

   cl_tst #(.DATA_WIDTH(512)) CL_TST_PCI (
   
         .clk(aclk),
         .rst_n(aresetn),

         .cfg_addr(cfg_bus.addr),
         .cfg_wdata(cfg_bus.wdata),
         .cfg_wr(cfg_bus.wr),
         .cfg_rd(cfg_bus.rd),
         .tst_cfg_ack(cfg_bus.ack),
         .tst_cfg_rdata(cfg_bus.rdata),

         .atg_enable(),
  
         .awid(cl_sh_pcim_q.awid[5:0]),
         .awaddr(cl_sh_pcim_q.awaddr), 
         .awlen(cl_sh_pcim_q.awlen),
         .awvalid(cl_sh_pcim_q.awvalid),
         .awuser(),
         .awready(cl_sh_pcim_q.awready),

         .wid(),
         .wdata(cl_sh_pcim_q.wdata),
         .wstrb(cl_sh_pcim_q.wstrb),
         .wlast(cl_sh_pcim_q.wlast),
         .wvalid(cl_sh_pcim_q.wvalid),
         .wready(cl_sh_pcim_q.wready),

         .bid(cl_sh_pcim_q.bid[5:0]),
         .bresp(cl_sh_pcim_q.bresp),
         .bvalid(cl_sh_pcim_q.bvalid),
         .buser(18'h0),
         .bready(cl_sh_pcim_q.bready),

         .arid(cl_sh_pcim_q.arid[5:0]),
         .araddr(cl_sh_pcim_q.araddr),
         .arlen(cl_sh_pcim_q.arlen),
         .aruser(),
         .arvalid(cl_sh_pcim_q.arvalid),
         .arready(cl_sh_pcim_q.arready),

         .rid(cl_sh_pcim_q.rid[5:0]),
         .rdata(cl_sh_pcim_q.rdata),
         .rresp(cl_sh_pcim_q.rresp),
         .rlast(cl_sh_pcim_q.rlast),
         .ruser(18'h0),
         .rvalid(cl_sh_pcim_q.rvalid),
         .rready(cl_sh_pcim_q.rready)
      );


   // AXI4 register slice - For signals between CL and HL
   axi4_flop_fifo #(.ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(16), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) PCI_AXI4_REG_SLC (
     .aclk           (aclk),
     .aresetn        (aresetn),
     .sync_rst_n     (1'b1),
                                                                                                                         
     .s_axi_awid     ({11'b0, cl_sh_pcim_q.awid}),
     .s_axi_awaddr   (cl_sh_pcim_q.awaddr),
     .s_axi_awlen    (cl_sh_pcim_q.awlen),
     .s_axi_awuser   (1'b0),
     .s_axi_awvalid  (cl_sh_pcim_q.awvalid),
     .s_axi_awready  (cl_sh_pcim_q.awready),
     .s_axi_wdata    (cl_sh_pcim_q.wdata),
     .s_axi_wstrb    (cl_sh_pcim_q.wstrb),
     .s_axi_wlast    (cl_sh_pcim_q.wlast),
     .s_axi_wuser    (),
     .s_axi_wvalid   (cl_sh_pcim_q.wvalid),
     .s_axi_wready   (cl_sh_pcim_q.wready),
     .s_axi_bid      (cl_sh_pcim_q.bid),
     .s_axi_bresp    (cl_sh_pcim_q.bresp),
     .s_axi_buser    (),
     .s_axi_bvalid   (cl_sh_pcim_q.bvalid),
     .s_axi_bready   (cl_sh_pcim_q.bready),
     .s_axi_arid     ({11'b0, cl_sh_pcim_q.arid}),
     .s_axi_araddr   (cl_sh_pcim_q.araddr),
     .s_axi_arlen    (cl_sh_pcim_q.arlen),
     .s_axi_aruser   (1'b0),
     .s_axi_arvalid  (cl_sh_pcim_q.arvalid),
     .s_axi_arready  (cl_sh_pcim_q.arready),
     .s_axi_rid      (cl_sh_pcim_q.rid),
     .s_axi_rdata    (cl_sh_pcim_q.rdata),
     .s_axi_rresp    (cl_sh_pcim_q.rresp),
     .s_axi_rlast    (cl_sh_pcim_q.rlast),
     .s_axi_ruser    (),
     .s_axi_rvalid   (cl_sh_pcim_q.rvalid),
     .s_axi_rready   (cl_sh_pcim_q.rready),  

     .m_axi_awid     (cl_sh_pcim_awid),   
     .m_axi_awaddr   (cl_sh_pcim_awaddr), 
     .m_axi_awlen    (cl_sh_pcim_awlen),  
     .m_axi_awuser   (), 
     .m_axi_awvalid  (cl_sh_pcim_awvalid),
     .m_axi_awready  (sh_cl_pcim_awready),
     .m_axi_wdata    (cl_sh_pcim_wdata),  
     .m_axi_wstrb    (cl_sh_pcim_wstrb),  
     .m_axi_wlast    (cl_sh_pcim_wlast),  
     .m_axi_wuser    (),
     .m_axi_wvalid   (cl_sh_pcim_wvalid), 
     .m_axi_wready   (sh_cl_pcim_wready), 
     .m_axi_bid      (sh_cl_pcim_bid),    
     .m_axi_bresp    (sh_cl_pcim_bresp),  
     .m_axi_bvalid   (sh_cl_pcim_bvalid), 
     .m_axi_buser    (),
     .m_axi_bready   (cl_sh_pcim_bready), 
     .m_axi_arid     (cl_sh_pcim_arid),   
     .m_axi_araddr   (cl_sh_pcim_araddr), 
     .m_axi_arlen    (cl_sh_pcim_arlen),  
     .m_axi_aruser   (), 
     .m_axi_arvalid  (cl_sh_pcim_arvalid),
     .m_axi_arready  (sh_cl_pcim_arready),
     .m_axi_rid      (sh_cl_pcim_rid),    
     .m_axi_rdata    (sh_cl_pcim_rdata),  
     .m_axi_rresp    (sh_cl_pcim_rresp),  
     .m_axi_rlast    (sh_cl_pcim_rlast),  
     .m_axi_rvalid   (sh_cl_pcim_rvalid), 
     .m_axi_ruser    (),
     .m_axi_rready   (cl_sh_pcim_rready)
     );


endmodule
