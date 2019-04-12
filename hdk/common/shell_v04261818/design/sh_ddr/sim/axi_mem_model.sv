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
module axi_mem_model #( parameter NUM_MEM = 3, parameter ECC_EN = 0, parameter ECC_ADDR_HI = 'h410, parameter ECC_ADDR_LO = 'h400, parameter RND_ECC_EN = 0, parameter RND_ECC_WEIGHT = 100)
   (

   input clk_core,
   input rst_n,
    
   input[15:0] cl_sh_ddr_awid[NUM_MEM-1:0],
   input[63:0] cl_sh_ddr_awaddr[NUM_MEM-1:0],
   input[7:0] cl_sh_ddr_awlen[NUM_MEM-1:0],
   input[2:0] cl_sh_ddr_awsize[NUM_MEM-1:0],
   input[1:0] cl_sh_ddr_awburst[NUM_MEM-1:0],        //Note only INCR/WRAP supported.  If un-supported mode on this signal, will default to INCR
   //input[10:0] cl_sh_ddr_awuser[NUM_MEM-1:0],
   input cl_sh_ddr_awvalid[NUM_MEM-1:0],
   output logic[NUM_MEM-1:0] sh_cl_ddr_awready,

   input[15:0] cl_sh_ddr_wid[NUM_MEM-1:0],
   input[511:0] cl_sh_ddr_wdata[NUM_MEM-1:0],
   input[63:0] cl_sh_ddr_wstrb[NUM_MEM-1:0],
   input[NUM_MEM-1:0] cl_sh_ddr_wlast,
   input[NUM_MEM-1:0] cl_sh_ddr_wvalid,
   output logic[NUM_MEM-1:0] sh_cl_ddr_wready,

   output logic[15:0] sh_cl_ddr_bid[NUM_MEM-1:0],
   output logic[1:0] sh_cl_ddr_bresp[NUM_MEM-1:0],
   output logic[NUM_MEM-1:0] sh_cl_ddr_bvalid,
   input[NUM_MEM-1:0] cl_sh_ddr_bready,

   input[15:0] cl_sh_ddr_arid[NUM_MEM-1:0],
   input[63:0] cl_sh_ddr_araddr[NUM_MEM-1:0],
   input[7:0] cl_sh_ddr_arlen[NUM_MEM-1:0],
   input[2:0] cl_sh_ddr_arsize[NUM_MEM-1:0],
   //input[10:0] cl_sh_ddr_aruser[NUM_MEM-1:0],
   input[1:0] cl_sh_ddr_arburst[NUM_MEM-1:0],     //Note only INCR/WRAP supported.  If un-supported mode on this signal, will default to INCR
   input[NUM_MEM-1:0] cl_sh_ddr_arvalid,
   output logic[NUM_MEM-1:0] sh_cl_ddr_arready,

   output logic[15:0] sh_cl_ddr_rid[NUM_MEM-1:0],
   output logic[511:0] sh_cl_ddr_rdata[NUM_MEM-1:0],
   output logic[1:0] sh_cl_ddr_rresp[NUM_MEM-1:0],
   output logic[NUM_MEM-1:0] sh_cl_ddr_rlast,
   output logic[NUM_MEM-1:0] sh_cl_ddr_rvalid,
   input[NUM_MEM-1:0] cl_sh_ddr_rready
   );

   //----------------------------------------------------------
   // AXI memory model instantiation
   //----------------------------------------------------------
   generate
      for (genvar gi=0; gi<NUM_MEM; gi++)
         begin:bfm_inst
            axi4_slave_bfm #(.ECC_EN(ECC_EN), .ECC_ADDR_HI(ECC_ADDR_HI), .ECC_ADDR_LO(ECC_ADDR_LO), .RND_ECC_EN(RND_ECC_EN), .RND_ECC_WEIGHT(RND_ECC_WEIGHT)) u_bfm (
               .clk_core(clk_core),
	       .rst_n(rst_n),
               .cl_sh_ddr_awid(cl_sh_ddr_awid[gi]),
               .cl_sh_ddr_awaddr(cl_sh_ddr_awaddr[gi]),
               .cl_sh_ddr_awlen(cl_sh_ddr_awlen[gi]),
               .cl_sh_ddr_awsize(cl_sh_ddr_awsize[gi]),
               .cl_sh_ddr_awburst(cl_sh_ddr_awburst[gi]),
               .cl_sh_ddr_awvalid(cl_sh_ddr_awvalid[gi]),
               .sh_cl_ddr_awready(sh_cl_ddr_awready[gi]),

               .cl_sh_ddr_wid(cl_sh_ddr_wid[gi]),
               .cl_sh_ddr_wdata(cl_sh_ddr_wdata[gi]),
               .cl_sh_ddr_wstrb(cl_sh_ddr_wstrb[gi]),
               .cl_sh_ddr_wlast(cl_sh_ddr_wlast[gi]),
               .cl_sh_ddr_wvalid(cl_sh_ddr_wvalid[gi]),
               .sh_cl_ddr_wready(sh_cl_ddr_wready[gi]),
               
               .sh_cl_ddr_bid(sh_cl_ddr_bid[gi]),
               .sh_cl_ddr_bresp(sh_cl_ddr_bresp[gi]),
               .sh_cl_ddr_bvalid(sh_cl_ddr_bvalid[gi]),
               .cl_sh_ddr_bready(cl_sh_ddr_bready[gi]),

               .cl_sh_ddr_arid(cl_sh_ddr_arid[gi]),
               .cl_sh_ddr_araddr(cl_sh_ddr_araddr[gi]),
               .cl_sh_ddr_arlen(cl_sh_ddr_arlen[gi]),
               .cl_sh_ddr_arsize(cl_sh_ddr_arsize[gi]),
               .cl_sh_ddr_arburst(cl_sh_ddr_arburst[gi]),
               .cl_sh_ddr_arvalid(cl_sh_ddr_arvalid[gi]),
               .sh_cl_ddr_arready(sh_cl_ddr_arready[gi]),

               .sh_cl_ddr_rid(sh_cl_ddr_rid[gi]),
               .sh_cl_ddr_rdata(sh_cl_ddr_rdata[gi]),
               .sh_cl_ddr_rresp(sh_cl_ddr_rresp[gi]),
               .sh_cl_ddr_rlast(sh_cl_ddr_rlast[gi]),
               .sh_cl_ddr_rvalid(sh_cl_ddr_rvalid[gi]),
               .cl_sh_ddr_rready(cl_sh_ddr_rready[gi])
            );
         end // block: bfm_inst
   endgenerate
endmodule
