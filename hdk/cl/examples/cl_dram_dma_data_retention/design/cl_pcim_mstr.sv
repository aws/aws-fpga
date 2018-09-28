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

module cl_pcim_mstr (
   input aclk,
   input aresetn,

   cfg_bus_t.master cfg_bus,

   axi_bus_t.slave cl_sh_pcim_bus

);

axi_bus_t cl_sh_pcim_q();


//-------------------------------------
// ATG for genrating PCIM AXI transfers
//-------------------------------------
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
  
         .awid(cl_sh_pcim_q.awid[8:0]),
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

         .bid(cl_sh_pcim_q.bid[8:0]),
         .bresp(cl_sh_pcim_q.bresp),
         .bvalid(cl_sh_pcim_q.bvalid),
         .buser(18'h0),
         .bready(cl_sh_pcim_q.bready),

         .arid(cl_sh_pcim_q.arid[8:0]),
         .araddr(cl_sh_pcim_q.araddr),
         .arlen(cl_sh_pcim_q.arlen),
         .aruser(),
         .arvalid(cl_sh_pcim_q.arvalid),
         .arready(cl_sh_pcim_q.arready),

         .rid(cl_sh_pcim_q.rid[8:0]),
         .rdata(cl_sh_pcim_q.rdata),
         .rresp(cl_sh_pcim_q.rresp),
         .rlast(cl_sh_pcim_q.rlast),
         .ruser(18'h0),
         .rvalid(cl_sh_pcim_q.rvalid),
         .rready(cl_sh_pcim_q.rready)
      );

//-------------------------------------
// flop the output of ATG
//-------------------------------------
   // AXI4 register slice - For signals between CL and HL
   axi_register_slice PCI_AXI4_REG_SLC (
     .aclk           (aclk),
     .aresetn        (aresetn),
                                                                                                                         
     .s_axi_awid     ({7'b0, cl_sh_pcim_q.awid[8:0]}),
     .s_axi_awaddr   (cl_sh_pcim_q.awaddr),
     .s_axi_awlen    (cl_sh_pcim_q.awlen),
     .s_axi_awsize   (3'h6),
     .s_axi_awvalid  (cl_sh_pcim_q.awvalid),
     .s_axi_awready  (cl_sh_pcim_q.awready),
     .s_axi_wdata    (cl_sh_pcim_q.wdata),
     .s_axi_wstrb    (cl_sh_pcim_q.wstrb),
     .s_axi_wlast    (cl_sh_pcim_q.wlast),
     .s_axi_wvalid   (cl_sh_pcim_q.wvalid),
     .s_axi_wready   (cl_sh_pcim_q.wready),
     .s_axi_bid      (cl_sh_pcim_q.bid),
     .s_axi_bresp    (cl_sh_pcim_q.bresp),
     .s_axi_bvalid   (cl_sh_pcim_q.bvalid),
     .s_axi_bready   (cl_sh_pcim_q.bready),
     .s_axi_arid     ({7'b0, cl_sh_pcim_q.arid[8:0]}),
     .s_axi_araddr   (cl_sh_pcim_q.araddr),
     .s_axi_arlen    (cl_sh_pcim_q.arlen),
     .s_axi_arsize   (3'h6),
     .s_axi_arvalid  (cl_sh_pcim_q.arvalid),
     .s_axi_arready  (cl_sh_pcim_q.arready),
     .s_axi_rid      (cl_sh_pcim_q.rid),
     .s_axi_rdata    (cl_sh_pcim_q.rdata),
     .s_axi_rresp    (cl_sh_pcim_q.rresp),
     .s_axi_rlast    (cl_sh_pcim_q.rlast),
     .s_axi_rvalid   (cl_sh_pcim_q.rvalid),
     .s_axi_rready   (cl_sh_pcim_q.rready),  

     .m_axi_awid     (cl_sh_pcim_bus.awid),   
     .m_axi_awaddr   (cl_sh_pcim_bus.awaddr), 
     .m_axi_awlen    (cl_sh_pcim_bus.awlen),  
     .m_axi_awsize   (cl_sh_pcim_bus.awsize), 
     .m_axi_awvalid  (cl_sh_pcim_bus.awvalid),
     .m_axi_awready  (cl_sh_pcim_bus.awready),
     .m_axi_wdata    (cl_sh_pcim_bus.wdata),  
     .m_axi_wstrb    (cl_sh_pcim_bus.wstrb),  
     .m_axi_wlast    (cl_sh_pcim_bus.wlast),  
     .m_axi_wvalid   (cl_sh_pcim_bus.wvalid), 
     .m_axi_wready   (cl_sh_pcim_bus.wready), 
     .m_axi_bid      (cl_sh_pcim_bus.bid),    
     .m_axi_bresp    (cl_sh_pcim_bus.bresp),  
     .m_axi_bvalid   (cl_sh_pcim_bus.bvalid), 
     .m_axi_bready   (cl_sh_pcim_bus.bready), 
     .m_axi_arid     (cl_sh_pcim_bus.arid),   
     .m_axi_araddr   (cl_sh_pcim_bus.araddr), 
     .m_axi_arlen    (cl_sh_pcim_bus.arlen),  
     .m_axi_arsize   (cl_sh_pcim_bus.arsize), 
     .m_axi_arvalid  (cl_sh_pcim_bus.arvalid),
     .m_axi_arready  (cl_sh_pcim_bus.arready),
     .m_axi_rid      (cl_sh_pcim_bus.rid),    
     .m_axi_rdata    (cl_sh_pcim_bus.rdata),  
     .m_axi_rresp    (cl_sh_pcim_bus.rresp),  
     .m_axi_rlast    (cl_sh_pcim_bus.rlast),  
     .m_axi_rvalid   (cl_sh_pcim_bus.rvalid), 
     .m_axi_rready   (cl_sh_pcim_bus.rready)
     );


endmodule
