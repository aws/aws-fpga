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

module cl_ila #( parameter DDR_A_PRESENT = 1) (

   input aclk,

   input drck,
   input shift,
   input tdi,
   input update,
   input sel,
   output logic tdo,
   input tms,
   input tck,
   input runtest,
   input reset,
   input capture,
   input bscanid_en,

   axi_bus_t sh_cl_dma_pcis_q,
   axi_bus_t lcl_cl_sh_ddra

);

//---------------------------- 
// Debug bridge
//---------------------------- 
 cl_debug_bridge CL_DEBUG_BRIDGE (
      .clk(aclk),
      .S_BSCAN_drck(drck),
      .S_BSCAN_shift(shift),
      .S_BSCAN_tdi(tdi),
      .S_BSCAN_update(update),
      .S_BSCAN_sel(sel),
      .S_BSCAN_tdo(tdo),
      .S_BSCAN_tms(tms),
      .S_BSCAN_tck(tck),
      .S_BSCAN_runtest(runtest),
      .S_BSCAN_reset(reset),
      .S_BSCAN_capture(capture),
      .S_BSCAN_bscanid_en(bscanid_en)
   );


//---------------------------- 
// Debug Core ILA for dmm pcis AXI4 interface 
//---------------------------- 
   ila_1 CL_DMA_ILA_0 (
                   .clk    (aclk),
                   .probe0 (sh_cl_dma_pcis_q.awvalid),
                   .probe1 (sh_cl_dma_pcis_q.awaddr),
                   .probe2 (2'b0),
                   .probe3 (sh_cl_dma_pcis_q.awready),
                   .probe4 (sh_cl_dma_pcis_q.wvalid),
                   .probe5 (sh_cl_dma_pcis_q.wstrb),
                   .probe6 (sh_cl_dma_pcis_q.wlast),
                   .probe7 (sh_cl_dma_pcis_q.wready),
                   .probe8 (1'b0),
                   .probe9 (1'b0),
                   .probe10 (sh_cl_dma_pcis_q.wdata),
                   .probe11 (1'b0),
                   .probe12 (sh_cl_dma_pcis_q.arready),
                   .probe13 (2'b0),
                   .probe14 (sh_cl_dma_pcis_q.rdata),
                   .probe15 (sh_cl_dma_pcis_q.araddr),
                   .probe16 (sh_cl_dma_pcis_q.arvalid),
                   .probe17 (3'b0),
                   .probe18 (3'b0),
                   .probe19 (sh_cl_dma_pcis_q.awid),
                   .probe20 (sh_cl_dma_pcis_q.arid),
                   .probe21 (sh_cl_dma_pcis_q.awlen),
                   .probe22 (sh_cl_dma_pcis_q.rlast),
                   .probe23 (3'b0), 
                   .probe24 (sh_cl_dma_pcis_q.rresp),
                   .probe25 (sh_cl_dma_pcis_q.rid),
                   .probe26 (sh_cl_dma_pcis_q.rvalid),
                   .probe27 (sh_cl_dma_pcis_q.arlen),
                   .probe28 (3'b0),
                   .probe29 (sh_cl_dma_pcis_q.bresp),
                   .probe30 (sh_cl_dma_pcis_q.rready),
                   .probe31 (4'b0),
                   .probe32 (4'b0),
                   .probe33 (4'b0),
                   .probe34 (4'b0),
                   .probe35 (sh_cl_dma_pcis_q.bvalid),
                   .probe36 (4'b0),
                   .probe37 (4'b0),
                   .probe38 (sh_cl_dma_pcis_q.bid),
                   .probe39 (sh_cl_dma_pcis_q.bready),
                   .probe40 (1'b0),
                   .probe41 (1'b0),
                   .probe42 (1'b0),
                   .probe43 (1'b0)
                   );
generate
begin:ddr_A_hookup
 if (DDR_A_PRESENT == 1) begin

//---------------------------- 
// Debug Core ILA for DDRA AXI4 interface monitoring 
//---------------------------- 
ila_1 CL_DDRA_ILA_0 (
                   .clk    (aclk),
                   .probe0 (lcl_cl_sh_ddra.awvalid),
                   .probe1 (lcl_cl_sh_ddra.awaddr),
                   .probe2 (2'b0),
                   .probe3 (lcl_cl_sh_ddra.awready),
                   .probe4 (lcl_cl_sh_ddra.wvalid),
                   .probe5 (lcl_cl_sh_ddra.wstrb),
                   .probe6 (lcl_cl_sh_ddra.wlast),
                   .probe7 (lcl_cl_sh_ddra.wready),
                   .probe8 (1'b0),
                   .probe9 (1'b0),
                   .probe10 (lcl_cl_sh_ddra.wdata),
                   .probe11 (1'b0),
                   .probe12 (lcl_cl_sh_ddra.arready),
                   .probe13 (2'b0),
                   .probe14 (lcl_cl_sh_ddra.rdata),
                   .probe15 (lcl_cl_sh_ddra.araddr),
                   .probe16 (lcl_cl_sh_ddra.arvalid),
                   .probe17 (3'b0),
                   .probe18 (3'b0),
                   .probe19 (lcl_cl_sh_ddra.awid[4:0]),
                   .probe20 (lcl_cl_sh_ddra.arid[4:0]),
                   .probe21 (lcl_cl_sh_ddra.awlen),
                   .probe22 (lcl_cl_sh_ddra.rlast),
                   .probe23 (3'b0), 
                   .probe24 (lcl_cl_sh_ddra.rresp),
                   .probe25 (lcl_cl_sh_ddra.rid[4:0]),
                   .probe26 (lcl_cl_sh_ddra.rvalid),
                   .probe27 (lcl_cl_sh_ddra.arlen),
                   .probe28 (3'b0),
                   .probe29 (lcl_cl_sh_ddra.bresp),
                   .probe30 (lcl_cl_sh_ddra.rready),
                   .probe31 (4'b0),
                   .probe32 (4'b0),
                   .probe33 (4'b0),
                   .probe34 (4'b0),
                   .probe35 (lcl_cl_sh_ddra.bvalid),
                   .probe36 (4'b0),
                   .probe37 (4'b0),
                   .probe38 (lcl_cl_sh_ddra.bid[4:0]),
                   .probe39 (lcl_cl_sh_ddra.bready),
                   .probe40 (1'b0),
                   .probe41 (1'b0),
                   .probe42 (1'b0),
                   .probe43 (1'b0)
                   );

end //if(DDR_A_PRESET)
end //label
endgenerate
endmodule

