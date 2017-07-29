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

module cl_hello_world 

(
   `include "cl_ports.vh" // Fixed port definition

);

`include "cl_common_defines.vh"      // CL Defines for all examples
`include "cl_id_defines.vh"          // Defines for ID0 and ID1 (PCI ID's)
`include "cl_hello_world_defines.vh" // CL Defines for cl_hello_world

logic rst_main_n_sync;


//--------------------------------------------0
// Start with Tie-Off of Unused Interfaces
//---------------------------------------------
// the developer should use the next set of `include
// to properly tie-off any unused interface
// The list is put in the top of the module
// to avoid cases where developer may forget to
// remove it from the end of the file

`ifndef AXIL_OCL
`include "unused_sh_ocl_template.inc"
 localparam OCL_PRESENT = 0;
`else
 localparam OCL_PRESENT = 1;
`endif  

`ifndef AXIL_USR       
`include "unused_sh_bar1_template.inc"
 localparam USR_PRESENT = 0;
`else
 localparam USR_PRESENT = 1;
`endif  

`ifndef AXIL_SDA
`include "unused_cl_sda_template.inc"
 localparam SDA_PRESENT = 0;
`else
 localparam SDA_PRESENT = 1;
`endif  

`ifndef DMA_PCIS        
`include "unused_dma_pcis_template.inc"
 localparam PCIS_PRESENT = 0;
`else
 localparam PCIS_PRESENT = 1;
`endif  

`ifndef DDR4_SH
`include "unused_ddr_c_template.inc"
 localparam DDR4_SH_PRESENT = 0;
`else
 localparam DDR4_SH_PRESENT = 1;
`endif 

`ifndef DDR4_CL
`include "unused_ddr_a_b_d_template.inc"
 localparam DDR4_CL_PRESENT = 0;
`else
 localparam DDR4_CL_PRESENT = 1;
`endif 

`ifndef PCIM
`include "unused_pcim_template.inc"
 localparam PCIM_PRESENT = 0;
`else
 localparam PCIM_PRESENT = 1;
`endif 


`ifndef DISABLE_CHIPSCOPE_DEBUG
 localparam DEBUG_PRESENT = 1;
`else
 localparam DEBUG_PRESENT = 0;
`endif 

`include "unused_flr_template.inc"
`include "unused_apppf_irq_template.inc"


   
   localparam NUM_CFG_STGS_CL_DDR_ATG = 4;
   localparam NUM_CFG_STGS_SH_DDR_ATG = 4;
   localparam NUM_CFG_STGS_PCIE_ATG = 4;
   
//-------------------------------------------------
// Wires
//-------------------------------------------------

  axi_bus_t lcl_cl_sh_ddra();
  axi_bus_t lcl_cl_sh_ddrb();
  axi_bus_t lcl_cl_sh_ddrd();
  logic [2:0] lcl_sh_cl_ddr_is_ready;



//-------------------------------------------------
// ID Values (cl_hello_world_defines.vh)
//-------------------------------------------------
  assign cl_sh_id0[31:0] = `CL_SH_ID0;
  assign cl_sh_id1[31:0] = `CL_SH_ID1;

logic clk;
logic pipe_rst_n;
logic sync_rst_n;

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------
logic pre_sync_rst_n;



assign clk = clk_main_a0;

//reset synchronizer
lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(rst_main_n), .out_bus(pipe_rst_n));
   
always_ff @(negedge pipe_rst_n or posedge clk)
   if (!pipe_rst_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end




   //VHDL Wrapper
 //Wires
    logic [15:0] cl_sh_ddr_awid_vhdl;
    logic [63:0] cl_sh_ddr_awaddr_vhdl;
    logic [7:0] cl_sh_ddr_awlen_vhdl;
    logic [2:0] cl_sh_ddr_awsize_vhdl;
    logic  cl_sh_ddr_awvalid_vhdl;       
    logic [15:0] cl_sh_ddr_wid_vhdl;
    logic [511:0] cl_sh_ddr_wdata_vhdl;
    logic [63:0] cl_sh_ddr_wstrb_vhdl;
    logic  cl_sh_ddr_wlast_vhdl;
    logic  cl_sh_ddr_wvalid_vhdl;
    logic  cl_sh_ddr_bready_vhdl;      
    logic [15:0] cl_sh_ddr_arid_vhdl;
    logic [63:0] cl_sh_ddr_araddr_vhdl;
    logic [7:0] cl_sh_ddr_arlen_vhdl;
    logic [2:0] cl_sh_ddr_arsize_vhdl;
    logic  cl_sh_ddr_arvalid_vhdl;
    logic  cl_sh_ddr_rready_vhdl;

   logic cl_sh_dma_pcis_awready_vhdl;
   logic cl_sh_dma_pcis_wready_vhdl;
   logic[5:0] cl_sh_dma_pcis_bid_vhdl;
   logic[1:0] cl_sh_dma_pcis_bresp_vhdl;
   logic cl_sh_dma_pcis_bvalid_vhdl;
   logic cl_sh_dma_pcis_arready_vhdl;
   logic [5:0] cl_sh_dma_pcis_rid_vhdl;
   logic [511:0] cl_sh_dma_pcis_rdata_vhdl;
   logic [1:0] cl_sh_dma_pcis_rresp_vhdl;
   logic cl_sh_dma_pcis_rlast_vhdl;
   logic cl_sh_dma_pcis_rvalid_vhdl;

   logic ocl_sh_awready_vhdl;
   logic ocl_sh_wready_vhdl;
   logic ocl_sh_bvalid_vhdl;
   logic [1:0] ocl_sh_bresp_vhdl;
   logic ocl_sh_arready_vhdl;                                                                                                                       
   logic ocl_sh_rvalid_vhdl;
   logic [31:0] ocl_sh_rdata_vhdl;
   logic [1:0] ocl_sh_rresp_vhdl;


   logic bar1_sh_awready_vhdl;
   logic bar1_sh_wready_vhdl;                                                                                                   
   logic bar1_sh_bvalid_vhdl;
   logic [1:0] bar1_sh_bresp_vhdl;
   logic bar1_sh_arready_vhdl;                                                                                                                 
   logic bar1_sh_rvalid_vhdl;
   logic [31:0] bar1_sh_rdata_vhdl;
   logic [1:0] bar1_sh_rresp_vhdl;
                                                                                                                               

   logic cl_sda_awready_vhdl;
   logic cl_sda_wready_vhdl;
   logic cl_sda_bvalid_vhdl;
   logic [1:0] cl_sda_bresp_vhdl;
   logic cl_sda_arready_vhdl;
   logic cl_sda_rvalid_vhdl;
   logic [31:0] cl_sda_rdata_vhdl;
   logic [1:0] cl_sda_rresp_vhdl;

   logic[15:0] cl_sh_pcim_awid_vhdl;
   logic[63:0] cl_sh_pcim_awaddr_vhdl;
   logic[7:0] cl_sh_pcim_awlen_vhdl;
   logic[2:0] cl_sh_pcim_awsize_vhdl;
   logic[18:0] cl_sh_pcim_awuser_vhdl;
   				
   logic cl_sh_pcim_awvalid_vhdl;
   logic [511:0] cl_sh_pcim_wdata_vhdl;
   logic [63:0] cl_sh_pcim_wstrb_vhdl;
   logic cl_sh_pcim_wlast_vhdl;
   logic cl_sh_pcim_wvalid_vhdl;
   logic cl_sh_pcim_bready_vhdl;
   logic [15:0] cl_sh_pcim_arid_vhdl;
   logic [63:0] cl_sh_pcim_araddr_vhdl;
   logic [7:0] cl_sh_pcim_arlen_vhdl;
   logic [2:0] cl_sh_pcim_arsize_vhdl;
   logic [18:0] cl_sh_pcim_aruser_vhdl;
   logic cl_sh_pcim_arvalid_vhdl;
   logic cl_sh_pcim_rready_vhdl;

          
                
  cl_vhdl_wrapper
  #(
     .OCL_PRESENT(OCL_PRESENT),
     .USR_PRESENT(USR_PRESENT),
     .SDA_PRESENT(SDA_PRESENT),
     .PCIS_PRESENT(PCIS_PRESENT),
     .DDR4_SH_PRESENT(DDR4_SH_PRESENT),
     .DDR4_CL_PRESENT(DDR4_CL_PRESENT),     
     .PCIM_PRESENT(PCIM_PRESENT),
     .DEBUG_PRESENT(DEBUG_PRESENT)     
  ) cl_vhdl_wrapper
       (

        .DMA_PCIS_araddr(sh_cl_dma_pcis_araddr),
        .DMA_PCIS_arburst(2'b01),
        .DMA_PCIS_arcache(4'b0),
        .DMA_PCIS_arid(sh_cl_dma_pcis_arid),
        .DMA_PCIS_arlen(sh_cl_dma_pcis_arlen),
        .DMA_PCIS_arlock(1'b0),
        .DMA_PCIS_arprot(3'b0),
        .DMA_PCIS_arqos(4'b0),
        .DMA_PCIS_arready(cl_sh_dma_pcis_arready_vhdl),
        .DMA_PCIS_arregion(4'b0),
        .DMA_PCIS_arsize(sh_cl_dma_pcis_arsize),
        .DMA_PCIS_arvalid(sh_cl_dma_pcis_arvalid),
        .DMA_PCIS_awaddr(sh_cl_dma_pcis_awaddr),
        .DMA_PCIS_awburst(2'b01),
        .DMA_PCIS_awcache(4'b0),
        .DMA_PCIS_awid(sh_cl_dma_pcis_awid),
        .DMA_PCIS_awlen(sh_cl_dma_pcis_awlen),
        .DMA_PCIS_awlock(1'b0),
        .DMA_PCIS_awprot(3'b0),
        .DMA_PCIS_awqos(4'b0),
        .DMA_PCIS_awready(cl_sh_dma_pcis_awready_vhdl),
        .DMA_PCIS_awregion(4'b0),
        .DMA_PCIS_awsize(sh_cl_dma_pcis_awsize),
        .DMA_PCIS_awvalid(sh_cl_dma_pcis_awvalid),
        .DMA_PCIS_bid(cl_sh_dma_pcis_bid_vhdl),
        .DMA_PCIS_bready(sh_cl_dma_pcis_bready),
        .DMA_PCIS_bresp(cl_sh_dma_pcis_bresp_vhdl),
        .DMA_PCIS_bvalid(cl_sh_dma_pcis_bvalid_vhdl),
        .DMA_PCIS_rdata(cl_sh_dma_pcis_rdata_vhdl),
        .DMA_PCIS_rid(cl_sh_dma_pcis_rid_vhdl),
        .DMA_PCIS_rlast(cl_sh_dma_pcis_rlast_vhdl),
        .DMA_PCIS_rready(sh_cl_dma_pcis_rready),
        .DMA_PCIS_rresp(cl_sh_dma_pcis_rresp_vhdl),
        .DMA_PCIS_rvalid(cl_sh_dma_pcis_rvalid_vhdl),
        .DMA_PCIS_wdata(sh_cl_dma_pcis_wdata),
        .DMA_PCIS_wlast(sh_cl_dma_pcis_wlast),
        .DMA_PCIS_wready(cl_sh_dma_pcis_wready_vhdl),
        .DMA_PCIS_wstrb(sh_cl_dma_pcis_wstrb),
        .DMA_PCIS_wvalid(sh_cl_dma_pcis_wvalid),
                                                                                                                               
	.AXIL_OCL_araddr(sh_ocl_araddr),
        .AXIL_OCL_arprot(3'b000),	
        .AXIL_OCL_arready(ocl_sh_arready_vhdl),
        .AXIL_OCL_arvalid(sh_ocl_arvalid),
        .AXIL_OCL_awaddr(sh_ocl_awaddr),
        .AXIL_OCL_awprot(3'b000),        
        .AXIL_OCL_awready(ocl_sh_awready_vhdl),
        .AXIL_OCL_awvalid(sh_ocl_awvalid),
        .AXIL_OCL_bready(sh_ocl_bready),
        .AXIL_OCL_bresp(ocl_sh_bresp_vhdl),
        .AXIL_OCL_bvalid(ocl_sh_bvalid_vhdl),
        .AXIL_OCL_rdata(ocl_sh_rdata_vhdl),
        .AXIL_OCL_rready(sh_ocl_rready),
        .AXIL_OCL_rresp(ocl_sh_rresp_vhdl),
        .AXIL_OCL_rvalid(ocl_sh_rvalid_vhdl),
        .AXIL_OCL_wdata(sh_ocl_wdata),
        .AXIL_OCL_wready(ocl_sh_wready_vhdl),
        .AXIL_OCL_wstrb(sh_ocl_wstrb),
        .AXIL_OCL_wvalid(sh_ocl_wvalid),
  	
        .AXIL_USR_araddr(sh_bar1_araddr),
        .AXIL_USR_arprot(3'b000),
        .AXIL_USR_arready(bar1_sh_arready_vhdl),
        .AXIL_USR_arvalid(sh_bar1_arvalid),
        .AXIL_USR_awaddr(sh_bar1_awaddr),
        .AXIL_USR_awprot(3'b000),
        .AXIL_USR_awready(bar1_sh_awready_vhdl),
        .AXIL_USR_awvalid(sh_bar1_awvalid),
        .AXIL_USR_bready(sh_bar1_bready),
        .AXIL_USR_bresp(bar1_sh_bresp_vhdl),
        .AXIL_USR_bvalid(bar1_sh_bvalid_vhdl),
        .AXIL_USR_rdata(bar1_sh_rdata_vhdl),
        .AXIL_USR_rready(sh_bar1_rready),
        .AXIL_USR_rresp(bar1_sh_rresp_vhdl),
        .AXIL_USR_rvalid(bar1_sh_rvalid_vhdl),
        .AXIL_USR_wdata(sh_bar1_wdata),
        .AXIL_USR_wready(bar1_sh_wready_vhdl),
        .AXIL_USR_wstrb(sh_bar1_wstrb),
        .AXIL_USR_wvalid(sh_bar1_wvalid),   

        .AXIL_SDA_araddr(sda_cl_araddr),
        .AXIL_SDA_arprot(3'b000),      
        .AXIL_SDA_arready(cl_sda_arready_vhdl),
        .AXIL_SDA_arvalid(sda_cl_arvalid),
        .AXIL_SDA_awaddr(sda_cl_awaddr),
        .AXIL_SDA_awprot(3'b000),    
        .AXIL_SDA_awready(cl_sda_awready_vhdl),
        .AXIL_SDA_awvalid(sda_cl_awvalid),
        .AXIL_SDA_bready(sda_cl_bready),
        .AXIL_SDA_bresp(cl_sda_bresp_vhdl),
        .AXIL_SDA_bvalid(cl_sda_bvalid_vhdl),
        .AXIL_SDA_rdata(cl_sda_rdata_vhdl),
        .AXIL_SDA_rready(sda_cl_rready),
        .AXIL_SDA_rresp(cl_sda_rresp_vhdl),
        .AXIL_SDA_rvalid(cl_sda_rvalid_vhdl),
        .AXIL_SDA_wdata(sda_cl_wdata),
        .AXIL_SDA_wready(cl_sda_wready_vhdl),
        .AXIL_SDA_wstrb(sda_cl_wstrb),
        .AXIL_SDA_wvalid(sda_cl_wvalid),
  	
          .DDR4_SH_araddr(cl_sh_ddr_araddr_vhdl),
          //.DDR4_SH_arburst(),
          //.DDR4_SH_arcache(),
          //.DDR4_SH_arregion(),
          .DDR4_SH_arid(cl_sh_ddr_arid_vhdl),
          .DDR4_SH_arlen(cl_sh_ddr_arlen_vhdl),
          //.DDR4_SH_arprot(),
          .DDR4_SH_arready(sh_cl_ddr_arready),
          .DDR4_SH_arvalid(cl_sh_ddr_arvalid_vhdl),
          .DDR4_SH_awaddr(cl_sh_ddr_awaddr_vhdl),
          //.DDR4_SH_awburst(),
          //.DDR4_SH_awcache(),
          //.DDR4_SH_awregion(),
          .DDR4_SH_awsize(cl_sh_ddr_awsize_vhdl),                    
          .DDR4_SH_awid(cl_sh_ddr_awid_vhdl),
          .DDR4_SH_awlen(cl_sh_ddr_awlen_vhdl),
          //.DDR4_SH_awprot(),
          .DDR4_SH_awready(sh_cl_ddr_awready),
          .DDR4_SH_arsize(cl_sh_ddr_arsize_vhdl),          
          .DDR4_SH_awvalid(cl_sh_ddr_awvalid_vhdl),
          .DDR4_SH_bid(sh_cl_ddr_bid), 
          .DDR4_SH_bready(cl_sh_ddr_bready_vhdl),
          .DDR4_SH_bresp(sh_cl_ddr_bresp),
          .DDR4_SH_bvalid(sh_cl_ddr_bvalid),
          .DDR4_SH_rdata(sh_cl_ddr_rdata),
          .DDR4_SH_rid(sh_cl_ddr_rid),
          .DDR4_SH_rlast(sh_cl_ddr_rlast),
          .DDR4_SH_rready(cl_sh_ddr_rready_vhdl),
          .DDR4_SH_rresp(sh_cl_ddr_rresp),
          .DDR4_SH_rvalid(sh_cl_ddr_rvalid),
          .DDR4_SH_wdata(cl_sh_ddr_wdata_vhdl),
          .DDR4_SH_wlast(cl_sh_ddr_wlast_vhdl),
          .DDR4_SH_wready(sh_cl_ddr_wready),
          .DDR4_SH_wstrb(cl_sh_ddr_wstrb_vhdl),
          .DDR4_SH_wvalid(cl_sh_ddr_wvalid_vhdl),
          .DDR4_SH_READY(sh_cl_ddr_is_ready),
  
	.DDR4_A_araddr(lcl_cl_sh_ddra.araddr),
        //.DDR4_A_arburst(),
        //.DDR4_A_arcache(),        
        .DDR4_A_arid(lcl_cl_sh_ddra.arid),        
        .DDR4_A_arlen(lcl_cl_sh_ddra.arlen),
        //.DDR4_A_arlock(),
        //.DDR4_A_arprot(),
        //.DDR4_A_arqos(),
        .DDR4_A_arready(lcl_cl_sh_ddra.arready),
        //.DDR4_A_arregion(),
        .DDR4_A_arsize(lcl_cl_sh_ddra.arsize),
        .DDR4_A_arvalid(lcl_cl_sh_ddra.arvalid),
        .DDR4_A_awaddr(lcl_cl_sh_ddra.awaddr),
        //.DDR4_A_awburst(),
        //.DDR4_A_awcache(),
        .DDR4_A_awid(lcl_cl_sh_ddra.awid),
        .DDR4_A_awlen(lcl_cl_sh_ddra.awlen),
        //.DDR4_A_awlock(),
        //.DDR4_A_awprot(),
        //.DDR4_A_awqos(),
        .DDR4_A_awready(lcl_cl_sh_ddra.awready),
        //.DDR4_A_awregion(),
        .DDR4_A_awsize(lcl_cl_sh_ddra.awsize),
        .DDR4_A_awvalid(lcl_cl_sh_ddra.awvalid),
        .DDR4_A_bid(lcl_cl_sh_ddra.bid),
        .DDR4_A_bready(lcl_cl_sh_ddra.bready),
        .DDR4_A_bresp(lcl_cl_sh_ddra.bresp),
        .DDR4_A_bvalid(lcl_cl_sh_ddra.bvalid),
        .DDR4_A_rdata(lcl_cl_sh_ddra.rdata),
        .DDR4_A_rid(lcl_cl_sh_ddra.rid),
        .DDR4_A_rlast(lcl_cl_sh_ddra.rlast),
        .DDR4_A_rready(lcl_cl_sh_ddra.rready),
        .DDR4_A_rresp(lcl_cl_sh_ddra.rresp),
        .DDR4_A_rvalid(lcl_cl_sh_ddra.rvalid),
        .DDR4_A_wdata(lcl_cl_sh_ddra.wdata),
        .DDR4_A_wlast(lcl_cl_sh_ddra.wlast),
        .DDR4_A_wready(lcl_cl_sh_ddra.wready),
        .DDR4_A_wstrb(lcl_cl_sh_ddra.wstrb),
        .DDR4_A_wvalid(lcl_cl_sh_ddra.wvalid),
    
	.DDR4_B_araddr(lcl_cl_sh_ddrb.araddr),
        //.DDR4_B_arburst(),
        //.DDR4_B_arcache(),        
        .DDR4_B_arid(lcl_cl_sh_ddrb.arid),        
        .DDR4_B_arlen(lcl_cl_sh_ddrb.arlen),
        //.DDR4_B_arlock(),
        //.DDR4_B_arprot(),
        //.DDR4_B_arqos(),
        .DDR4_B_arready(lcl_cl_sh_ddrb.arready),
        //.DDR4_B_arregion(),
        .DDR4_B_arsize(lcl_cl_sh_ddrb.arsize),
        .DDR4_B_arvalid(lcl_cl_sh_ddrb.arvalid),
        .DDR4_B_awaddr(lcl_cl_sh_ddrb.awaddr),
        //.DDR4_B_awburst(),
        //.DDR4_B_awcache(),
        .DDR4_B_awid(lcl_cl_sh_ddrb.awid),
        .DDR4_B_awlen(lcl_cl_sh_ddrb.awlen),
        //.DDR4_B_awlock(),
        //.DDR4_B_awprot(),
        //.DDR4_B_awqos(),
        .DDR4_B_awready(lcl_cl_sh_ddrb.awready),
        //.DDR4_B_awregion(),
        .DDR4_B_awsize(lcl_cl_sh_ddrb.awsize),
        .DDR4_B_awvalid(lcl_cl_sh_ddrb.awvalid),
        .DDR4_B_bid(lcl_cl_sh_ddrb.bid),
        .DDR4_B_bready(lcl_cl_sh_ddrb.bready),
        .DDR4_B_bresp(lcl_cl_sh_ddrb.bresp),
        .DDR4_B_bvalid(lcl_cl_sh_ddrb.bvalid),
        .DDR4_B_rdata(lcl_cl_sh_ddrb.rdata),
        .DDR4_B_rid(lcl_cl_sh_ddrb.rid),
        .DDR4_B_rlast(lcl_cl_sh_ddrb.rlast),
        .DDR4_B_rready(lcl_cl_sh_ddrb.rready),
        .DDR4_B_rresp(lcl_cl_sh_ddrb.rresp),
        .DDR4_B_rvalid(lcl_cl_sh_ddrb.rvalid),
        .DDR4_B_wdata(lcl_cl_sh_ddrb.wdata),
        .DDR4_B_wlast(lcl_cl_sh_ddrb.wlast),
        .DDR4_B_wready(lcl_cl_sh_ddrb.wready),
        .DDR4_B_wstrb(lcl_cl_sh_ddrb.wstrb),
        .DDR4_B_wvalid(lcl_cl_sh_ddrb.wvalid),
  
	.DDR4_D_araddr(lcl_cl_sh_ddrd.araddr),
        //.DDR4_D_arburst(),
        //.DDR4_D_arcache(),        
        .DDR4_D_arid(lcl_cl_sh_ddrd.arid),        
        .DDR4_D_arlen(lcl_cl_sh_ddrd.arlen),
        //.DDR4_D_arlock(),
        //.DDR4_D_arprot(),
        //.DDR4_D_arqos(),
        .DDR4_D_arready(lcl_cl_sh_ddrd.arready),
        //.DDR4_D_arregion(),
        .DDR4_D_arsize(lcl_cl_sh_ddrd.arsize),
        .DDR4_D_arvalid(lcl_cl_sh_ddrd.arvalid),
        .DDR4_D_awaddr(lcl_cl_sh_ddrd.awaddr),
        //.DDR4_D_awburst(),
        //.DDR4_D_awcache(),
        .DDR4_D_awid(lcl_cl_sh_ddrd.awid),
        .DDR4_D_awlen(lcl_cl_sh_ddrd.awlen),
        //.DDR4_D_awlock(),
        //.DDR4_D_awprot(),
        //.DDR4_D_awqos(),
        .DDR4_D_awready(lcl_cl_sh_ddrd.awready),
        //.DDR4_D_awregion(),
        .DDR4_D_awsize(lcl_cl_sh_ddrd.awsize),
        .DDR4_D_awvalid(lcl_cl_sh_ddrd.awvalid),
        .DDR4_D_bid(lcl_cl_sh_ddrd.bid),
        .DDR4_D_bready(lcl_cl_sh_ddrd.bready),
        .DDR4_D_bresp(lcl_cl_sh_ddrd.bresp),
        .DDR4_D_bvalid(lcl_cl_sh_ddrd.bvalid),
        .DDR4_D_rdata(lcl_cl_sh_ddrd.rdata),
        .DDR4_D_rid(lcl_cl_sh_ddrd.rid),
        .DDR4_D_rlast(lcl_cl_sh_ddrd.rlast),
        .DDR4_D_rready(lcl_cl_sh_ddrd.rready),
        .DDR4_D_rresp(lcl_cl_sh_ddrd.rresp),
        .DDR4_D_rvalid(lcl_cl_sh_ddrd.rvalid),
        .DDR4_D_wdata(lcl_cl_sh_ddrd.wdata),
        .DDR4_D_wlast(lcl_cl_sh_ddrd.wlast),
        .DDR4_D_wready(lcl_cl_sh_ddrd.wready),
        .DDR4_D_wstrb(lcl_cl_sh_ddrd.wstrb),
        .DDR4_D_wvalid(lcl_cl_sh_ddrd.wvalid),
        
	.DDR4_A_READY(lcl_sh_cl_ddr_is_ready[0]),
	.DDR4_B_READY(lcl_sh_cl_ddr_is_ready[1]),
	.DDR4_D_READY(lcl_sh_cl_ddr_is_ready[2]),

	
        .PCIM_araddr(cl_sh_pcim_araddr_vhdl),
        //.PCIM_arburst(),
        //.PCIM_arcache(),
      
        .PCIM_arid(cl_sh_pcim_arid_vhdl),
        .PCIM_arlen(cl_sh_pcim_arlen_vhdl),
        //.PCIM_arlock(),
        //.PCIM_arprot(),
        //.PCIM_arqos(),
        .PCIM_arready(sh_cl_pcim_arready),
        //.PCIM_arregion(),
        .PCIM_arsize(cl_sh_pcim_arsize_vhdl),
        .PCIM_aruser(cl_sh_pcim_aruser_vhdl),
        .PCIM_arvalid(cl_sh_pcim_arvalid_vhdl),        
        .PCIM_awaddr(cl_sh_pcim_awaddr_vhdl),
        //.PCIM_awburst(),
        //.PCIM_awcache(),
      
        .PCIM_awid(cl_sh_pcim_awid_vhdl),
        .PCIM_awlen(cl_sh_pcim_awlen_vhdl),
        //.PCIM_awlock(),
        //.PCIM_awprot(),
        //.PCIM_awqos(),
        .PCIM_awready(sh_cl_pcim_awready),
        //.PCIM_awregion(),
        .PCIM_awsize(cl_sh_pcim_awsize_vhdl),
        .PCIM_awuser(cl_sh_pcim_awuser_vhdl),
        .PCIM_awvalid(cl_sh_pcim_awvalid_vhdl),
        
        .PCIM_bid(sh_cl_pcim_bid),
        .PCIM_bready(cl_sh_pcim_bready_vhdl),
        .PCIM_bresp(sh_cl_pcim_bresp),
        .PCIM_buser(18'h0),
        .PCIM_bvalid(sh_cl_pcim_bvalid),
        .PCIM_rdata(sh_cl_pcim_rdata),
        
        .PCIM_rid(sh_cl_pcim_rid),
        .PCIM_rlast(sh_cl_pcim_rlast),
        .PCIM_rready(cl_sh_pcim_rready_vhdl),
        .PCIM_rresp(sh_cl_pcim_rresp),
        .PCIM_ruser(18'h0),
        .PCIM_rvalid(sh_cl_pcim_rvalid),
        .PCIM_wdata(cl_sh_pcim_wdata_vhdl),
        .PCIM_wlast(cl_sh_pcim_wlast_vhdl),
        .PCIM_wready(sh_cl_pcim_wready),
        .PCIM_wstrb(cl_sh_pcim_wstrb_vhdl),
        .PCIM_wvalid(cl_sh_pcim_wvalid_vhdl),
        .vled(cl_sh_status_vled),
        .vdip(sh_cl_status_vdip),
        .glcount0(sh_cl_glcount0),
        .glcount1(sh_cl_glcount1),
        
        .clk(clk),
        .rst_n(sync_rst_n));


`ifdef DMA_PCIS
  assign cl_sh_dma_pcis_awready      =   cl_sh_dma_pcis_awready_vhdl;
  assign cl_sh_dma_pcis_wready       =   cl_sh_dma_pcis_wready_vhdl;
  assign cl_sh_dma_pcis_bid[5:0]     =   cl_sh_dma_pcis_bid_vhdl;
  assign cl_sh_dma_pcis_bresp[1:0]   =   cl_sh_dma_pcis_bresp_vhdl;
  assign cl_sh_dma_pcis_bvalid       =   cl_sh_dma_pcis_bvalid_vhdl;
  assign cl_sh_dma_pcis_arready      =   cl_sh_dma_pcis_arready_vhdl;
  assign cl_sh_dma_pcis_rid          =   cl_sh_dma_pcis_rid_vhdl;
  assign cl_sh_dma_pcis_rdata        =   cl_sh_dma_pcis_rdata_vhdl;
  assign cl_sh_dma_pcis_rresp        =   cl_sh_dma_pcis_rresp_vhdl;
  assign cl_sh_dma_pcis_rlast        =   cl_sh_dma_pcis_rlast_vhdl;
  assign cl_sh_dma_pcis_rvalid       =   cl_sh_dma_pcis_rvalid_vhdl;
`endif

`ifdef AXIL_OCL
  assign ocl_sh_awready     =   ocl_sh_awready_vhdl;
  assign ocl_sh_wready      =   ocl_sh_wready_vhdl;
  assign ocl_sh_bvalid      =   ocl_sh_bvalid_vhdl;
  assign ocl_sh_bresp       =   ocl_sh_bresp_vhdl;
  assign ocl_sh_arready     =   ocl_sh_arready_vhdl;
  assign ocl_sh_rvalid      =   ocl_sh_rvalid_vhdl;
  assign ocl_sh_rdata       =   ocl_sh_rdata_vhdl;
  assign ocl_sh_rresp       =   ocl_sh_rresp_vhdl;
`endif

`ifdef AXIL_USR
  assign bar1_sh_awready             =   bar1_sh_awready_vhdl;
  assign bar1_sh_wready              =   bar1_sh_wready_vhdl;
  assign bar1_sh_bvalid              =   bar1_sh_bvalid_vhdl;
  assign bar1_sh_bresp               =   bar1_sh_bresp_vhdl;
  assign bar1_sh_arready             =   bar1_sh_arready_vhdl;
  assign bar1_sh_rvalid              =   bar1_sh_rvalid_vhdl;
  assign bar1_sh_rdata               =   bar1_sh_rdata_vhdl;
  assign bar1_sh_rresp               =   bar1_sh_rresp_vhdl;
`endif

`ifdef AXIL_SDA
  assign cl_sda_awready              =   cl_sda_awready_vhdl;
  assign cl_sda_wready               =   cl_sda_wready_vhdl;
  assign cl_sda_bvalid               =   cl_sda_bvalid_vhdl;
  assign cl_sda_bresp                =   cl_sda_bresp_vhdl;
  assign cl_sda_arready              =   cl_sda_arready_vhdl;
  assign cl_sda_rvalid               =   cl_sda_rvalid_vhdl;
  assign cl_sda_rdata                =   cl_sda_rdata_vhdl;
  assign cl_sda_rresp                =   cl_sda_rresp_vhdl;
`endif

`ifdef PCIM
  assign cl_sh_pcim_awid             =  cl_sh_pcim_awid_vhdl;
  assign cl_sh_pcim_awaddr           =  cl_sh_pcim_awaddr_vhdl;
  assign cl_sh_pcim_awlen            =  cl_sh_pcim_awlen_vhdl;
  assign cl_sh_pcim_awsize           =  cl_sh_pcim_awsize_vhdl;
  assign cl_sh_pcim_awuser           =  cl_sh_pcim_awuser_vhdl;
  assign cl_sh_pcim_awvalid          =  cl_sh_pcim_awvalid_vhdl;

  assign cl_sh_pcim_wdata            =  cl_sh_pcim_wdata_vhdl;
  assign cl_sh_pcim_wstrb            =  cl_sh_pcim_wstrb_vhdl;
  assign cl_sh_pcim_wlast            =  cl_sh_pcim_wlast_vhdl;
  assign cl_sh_pcim_wvalid           =  cl_sh_pcim_wvalid_vhdl;

  assign cl_sh_pcim_bready           =  cl_sh_pcim_bready_vhdl;

  assign cl_sh_pcim_arid             =  cl_sh_pcim_arid_vhdl;
  assign cl_sh_pcim_araddr           =  cl_sh_pcim_araddr_vhdl;
  assign cl_sh_pcim_arlen            =  cl_sh_pcim_arlen_vhdl;
  assign cl_sh_pcim_arsize           =  cl_sh_pcim_arsize_vhdl;
  assign cl_sh_pcim_aruser           =  cl_sh_pcim_aruser_vhdl;
  assign cl_sh_pcim_arvalid          =  cl_sh_pcim_arvalid_vhdl;

  assign cl_sh_pcim_rready           =  cl_sh_pcim_rready_vhdl;
`endif

   
`ifdef DDR4_SH
   assign cl_sh_ddr_awid = cl_sh_ddr_awid_vhdl;
   assign cl_sh_ddr_awaddr = cl_sh_ddr_awaddr_vhdl;
   assign cl_sh_ddr_awlen = cl_sh_ddr_awlen_vhdl;
   assign cl_sh_ddr_awsize = cl_sh_ddr_awsize_vhdl;
   assign cl_sh_ddr_awvalid = cl_sh_ddr_awvalid_vhdl;  
   assign cl_sh_ddr_wid = 16'b0;
   assign cl_sh_ddr_wdata = cl_sh_ddr_wdata_vhdl;
   assign cl_sh_ddr_wstrb = cl_sh_ddr_wstrb_vhdl;
   assign cl_sh_ddr_wlast = cl_sh_ddr_wlast_vhdl;
   assign cl_sh_ddr_wvalid = cl_sh_ddr_wvalid_vhdl;  
   assign cl_sh_ddr_bready = cl_sh_ddr_bready_vhdl;  
   assign cl_sh_ddr_arid = cl_sh_ddr_arid_vhdl;
   assign cl_sh_ddr_araddr = cl_sh_ddr_araddr_vhdl;
   assign cl_sh_ddr_arlen = cl_sh_ddr_arlen_vhdl;
   assign cl_sh_ddr_arsize = cl_sh_ddr_arsize_vhdl;
   assign cl_sh_ddr_arvalid = cl_sh_ddr_arvalid_vhdl;
   assign cl_sh_ddr_rready = cl_sh_ddr_rready_vhdl;
`endif




        
`ifdef DDR4_CL

logic [7:0] sh_ddr_stat_addr_q[2:0];
logic[2:0] sh_ddr_stat_wr_q;
logic[2:0] sh_ddr_stat_rd_q; 
logic[31:0] sh_ddr_stat_wdata_q[2:0];
logic[2:0] ddr_sh_stat_ack_q;
logic[31:0] ddr_sh_stat_rdata_q[2:0];
logic[7:0] ddr_sh_stat_int_q[2:0];


lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT0 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({sh_ddr_stat_wr0, sh_ddr_stat_rd0, sh_ddr_stat_addr0, sh_ddr_stat_wdata0}),
                                               .out_bus({sh_ddr_stat_wr_q[0], sh_ddr_stat_rd_q[0], sh_ddr_stat_addr_q[0], sh_ddr_stat_wdata_q[0]})
                                               );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK0 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({ddr_sh_stat_ack_q[0], ddr_sh_stat_int_q[0], ddr_sh_stat_rdata_q[0]}),
                                               .out_bus({ddr_sh_stat_ack0, ddr_sh_stat_int0, ddr_sh_stat_rdata0})
                                               );


lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT1 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({sh_ddr_stat_wr1, sh_ddr_stat_rd1, sh_ddr_stat_addr1, sh_ddr_stat_wdata1}),
                                               .out_bus({sh_ddr_stat_wr_q[1], sh_ddr_stat_rd_q[1], sh_ddr_stat_addr_q[1], sh_ddr_stat_wdata_q[1]})
                                               );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK1 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({ddr_sh_stat_ack_q[1], ddr_sh_stat_int_q[1], ddr_sh_stat_rdata_q[1]}),
                                               .out_bus({ddr_sh_stat_ack1, ddr_sh_stat_int1, ddr_sh_stat_rdata1})
                                               );

lib_pipe #(.WIDTH(1+1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT2 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({sh_ddr_stat_wr2, sh_ddr_stat_rd2, sh_ddr_stat_addr2, sh_ddr_stat_wdata2}),
                                               .out_bus({sh_ddr_stat_wr_q[2], sh_ddr_stat_rd_q[2], sh_ddr_stat_addr_q[2], sh_ddr_stat_wdata_q[2]})
                                               );


lib_pipe #(.WIDTH(1+8+32), .STAGES(NUM_CFG_STGS_CL_DDR_ATG)) PIPE_DDR_STAT_ACK2 (.clk(clk), .rst_n(sync_rst_n),
                                               .in_bus({ddr_sh_stat_ack_q[2], ddr_sh_stat_int_q[2], ddr_sh_stat_rdata_q[2]}),
                                               .out_bus({ddr_sh_stat_ack2, ddr_sh_stat_int2, ddr_sh_stat_rdata2})
                                               ); 

//convert to 2D 
logic[15:0] cl_sh_ddr_awid_2d[2:0];
logic[63:0] cl_sh_ddr_awaddr_2d[2:0];
logic[7:0] cl_sh_ddr_awlen_2d[2:0];
logic[2:0] cl_sh_ddr_awsize_2d[2:0];
logic cl_sh_ddr_awvalid_2d [2:0];
logic[2:0] sh_cl_ddr_awready_2d;

logic[15:0] cl_sh_ddr_wid_2d[2:0];
logic[511:0] cl_sh_ddr_wdata_2d[2:0];
logic[63:0] cl_sh_ddr_wstrb_2d[2:0];
logic[2:0] cl_sh_ddr_wlast_2d;
logic[2:0] cl_sh_ddr_wvalid_2d;
logic[2:0] sh_cl_ddr_wready_2d;

logic[15:0] sh_cl_ddr_bid_2d[2:0];
logic[1:0] sh_cl_ddr_bresp_2d[2:0];
logic[2:0] sh_cl_ddr_bvalid_2d;
logic[2:0] cl_sh_ddr_bready_2d;

logic[15:0] cl_sh_ddr_arid_2d[2:0];
logic[63:0] cl_sh_ddr_araddr_2d[2:0];
logic[7:0] cl_sh_ddr_arlen_2d[2:0];
logic[2:0] cl_sh_ddr_arsize_2d[2:0];
logic[2:0] cl_sh_ddr_arvalid_2d;
logic[2:0] sh_cl_ddr_arready_2d;

logic[15:0] sh_cl_ddr_rid_2d[2:0];
logic[511:0] sh_cl_ddr_rdata_2d[2:0];
logic[1:0] sh_cl_ddr_rresp_2d[2:0];
logic[2:0] sh_cl_ddr_rlast_2d;
logic[2:0] sh_cl_ddr_rvalid_2d;
logic[2:0] cl_sh_ddr_rready_2d;

assign cl_sh_ddr_awid_2d = '{lcl_cl_sh_ddrd.awid, lcl_cl_sh_ddrb.awid, lcl_cl_sh_ddra.awid};
assign cl_sh_ddr_awaddr_2d = '{lcl_cl_sh_ddrd.awaddr, lcl_cl_sh_ddrb.awaddr, lcl_cl_sh_ddra.awaddr};
assign cl_sh_ddr_awlen_2d = '{lcl_cl_sh_ddrd.awlen, lcl_cl_sh_ddrb.awlen, lcl_cl_sh_ddra.awlen};
assign cl_sh_ddr_awsize_2d = '{lcl_cl_sh_ddrd.awsize, lcl_cl_sh_ddrb.awsize, lcl_cl_sh_ddra.awsize};
assign cl_sh_ddr_awvalid_2d = '{lcl_cl_sh_ddrd.awvalid, lcl_cl_sh_ddrb.awvalid, lcl_cl_sh_ddra.awvalid};
assign {lcl_cl_sh_ddrd.awready, lcl_cl_sh_ddrb.awready, lcl_cl_sh_ddra.awready} = sh_cl_ddr_awready_2d;

assign cl_sh_ddr_wid_2d = '{lcl_cl_sh_ddrd.wid, lcl_cl_sh_ddrb.wid, lcl_cl_sh_ddra.wid};
assign cl_sh_ddr_wdata_2d = '{lcl_cl_sh_ddrd.wdata, lcl_cl_sh_ddrb.wdata, lcl_cl_sh_ddra.wdata};
assign cl_sh_ddr_wstrb_2d = '{lcl_cl_sh_ddrd.wstrb, lcl_cl_sh_ddrb.wstrb, lcl_cl_sh_ddra.wstrb};
assign cl_sh_ddr_wlast_2d = {lcl_cl_sh_ddrd.wlast, lcl_cl_sh_ddrb.wlast, lcl_cl_sh_ddra.wlast};
assign cl_sh_ddr_wvalid_2d = {lcl_cl_sh_ddrd.wvalid, lcl_cl_sh_ddrb.wvalid, lcl_cl_sh_ddra.wvalid};
assign {lcl_cl_sh_ddrd.wready, lcl_cl_sh_ddrb.wready, lcl_cl_sh_ddra.wready} = sh_cl_ddr_wready_2d;

assign {lcl_cl_sh_ddrd.bid, lcl_cl_sh_ddrb.bid, lcl_cl_sh_ddra.bid} = {sh_cl_ddr_bid_2d[2], sh_cl_ddr_bid_2d[1], sh_cl_ddr_bid_2d[0]};
assign {lcl_cl_sh_ddrd.bresp, lcl_cl_sh_ddrb.bresp, lcl_cl_sh_ddra.bresp} = {sh_cl_ddr_bresp_2d[2], sh_cl_ddr_bresp_2d[1], sh_cl_ddr_bresp_2d[0]};
assign {lcl_cl_sh_ddrd.bvalid, lcl_cl_sh_ddrb.bvalid, lcl_cl_sh_ddra.bvalid} = sh_cl_ddr_bvalid_2d;
assign cl_sh_ddr_bready_2d = {lcl_cl_sh_ddrd.bready, lcl_cl_sh_ddrb.bready, lcl_cl_sh_ddra.bready};

assign cl_sh_ddr_arid_2d = '{lcl_cl_sh_ddrd.arid, lcl_cl_sh_ddrb.arid, lcl_cl_sh_ddra.arid};
assign cl_sh_ddr_araddr_2d = '{lcl_cl_sh_ddrd.araddr, lcl_cl_sh_ddrb.araddr, lcl_cl_sh_ddra.araddr};
assign cl_sh_ddr_arlen_2d = '{lcl_cl_sh_ddrd.arlen, lcl_cl_sh_ddrb.arlen, lcl_cl_sh_ddra.arlen};
assign cl_sh_ddr_arsize_2d = '{lcl_cl_sh_ddrd.arsize, lcl_cl_sh_ddrb.arsize, lcl_cl_sh_ddra.arsize};
assign cl_sh_ddr_arvalid_2d = {lcl_cl_sh_ddrd.arvalid, lcl_cl_sh_ddrb.arvalid, lcl_cl_sh_ddra.arvalid};
assign {lcl_cl_sh_ddrd.arready, lcl_cl_sh_ddrb.arready, lcl_cl_sh_ddra.arready} = sh_cl_ddr_arready_2d;

assign {lcl_cl_sh_ddrd.rid, lcl_cl_sh_ddrb.rid, lcl_cl_sh_ddra.rid} = {sh_cl_ddr_rid_2d[2], sh_cl_ddr_rid_2d[1], sh_cl_ddr_rid_2d[0]};
assign {lcl_cl_sh_ddrd.rresp, lcl_cl_sh_ddrb.rresp, lcl_cl_sh_ddra.rresp} = {sh_cl_ddr_rresp_2d[2], sh_cl_ddr_rresp_2d[1], sh_cl_ddr_rresp_2d[0]};
assign {lcl_cl_sh_ddrd.rdata, lcl_cl_sh_ddrb.rdata, lcl_cl_sh_ddra.rdata} = {sh_cl_ddr_rdata_2d[2], sh_cl_ddr_rdata_2d[1], sh_cl_ddr_rdata_2d[0]};
assign {lcl_cl_sh_ddrd.rlast, lcl_cl_sh_ddrb.rlast, lcl_cl_sh_ddra.rlast} = sh_cl_ddr_rlast_2d;
assign {lcl_cl_sh_ddrd.rvalid, lcl_cl_sh_ddrb.rvalid, lcl_cl_sh_ddra.rvalid} = sh_cl_ddr_rvalid_2d;
assign cl_sh_ddr_rready_2d = {lcl_cl_sh_ddrd.rready, lcl_cl_sh_ddrb.rready, lcl_cl_sh_ddra.rready};

logic sh_ddr_sync_rst_n;
lib_pipe #(.WIDTH(1), .STAGES(4)) SH_DDR_SLC_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(sync_rst_n), .out_bus(sh_ddr_sync_rst_n));

sh_ddr #(
         .DDR_A_PRESENT(DDR4_CL_PRESENT),
         .DDR_A_IO(1),
         .DDR_B_PRESENT(DDR4_CL_PRESENT),
         .DDR_D_PRESENT(DDR4_CL_PRESENT)
   ) SH_DDR
   (
   .clk(clk),
   .rst_n(sh_ddr_sync_rst_n),

   .stat_clk(clk),
   .stat_rst_n(sh_ddr_sync_rst_n),


   .CLK_300M_DIMM0_DP(CLK_300M_DIMM0_DP),
   .CLK_300M_DIMM0_DN(CLK_300M_DIMM0_DN),
   .M_A_ACT_N(M_A_ACT_N),
   .M_A_MA(M_A_MA),
   .M_A_BA(M_A_BA),
   .M_A_BG(M_A_BG),
   .M_A_CKE(M_A_CKE),
   .M_A_ODT(M_A_ODT),
   .M_A_CS_N(M_A_CS_N),
   .M_A_CLK_DN(M_A_CLK_DN),
   .M_A_CLK_DP(M_A_CLK_DP),
   .M_A_PAR(M_A_PAR),
   .M_A_DQ(M_A_DQ),
   .M_A_ECC(M_A_ECC),
   .M_A_DQS_DP(M_A_DQS_DP),
   .M_A_DQS_DN(M_A_DQS_DN),
   .cl_RST_DIMM_A_N(cl_RST_DIMM_A_N),
   
   
   .CLK_300M_DIMM1_DP(CLK_300M_DIMM1_DP),
   .CLK_300M_DIMM1_DN(CLK_300M_DIMM1_DN),
   .M_B_ACT_N(M_B_ACT_N),
   .M_B_MA(M_B_MA),
   .M_B_BA(M_B_BA),
   .M_B_BG(M_B_BG),
   .M_B_CKE(M_B_CKE),
   .M_B_ODT(M_B_ODT),
   .M_B_CS_N(M_B_CS_N),
   .M_B_CLK_DN(M_B_CLK_DN),
   .M_B_CLK_DP(M_B_CLK_DP),
   .M_B_PAR(M_B_PAR),
   .M_B_DQ(M_B_DQ),
   .M_B_ECC(M_B_ECC),
   .M_B_DQS_DP(M_B_DQS_DP),
   .M_B_DQS_DN(M_B_DQS_DN),
   .cl_RST_DIMM_B_N(cl_RST_DIMM_B_N),

   .CLK_300M_DIMM3_DP(CLK_300M_DIMM3_DP),
   .CLK_300M_DIMM3_DN(CLK_300M_DIMM3_DN),
   .M_D_ACT_N(M_D_ACT_N),
   .M_D_MA(M_D_MA),
   .M_D_BA(M_D_BA),
   .M_D_BG(M_D_BG),
   .M_D_CKE(M_D_CKE),
   .M_D_ODT(M_D_ODT),
   .M_D_CS_N(M_D_CS_N),
   .M_D_CLK_DN(M_D_CLK_DN),
   .M_D_CLK_DP(M_D_CLK_DP),
   .M_D_PAR(M_D_PAR),
   .M_D_DQ(M_D_DQ),
   .M_D_ECC(M_D_ECC),
   .M_D_DQS_DP(M_D_DQS_DP),
   .M_D_DQS_DN(M_D_DQS_DN),
   .cl_RST_DIMM_D_N(cl_RST_DIMM_D_N),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid(cl_sh_ddr_awid_2d),
   .cl_sh_ddr_awaddr(cl_sh_ddr_awaddr_2d),
   .cl_sh_ddr_awlen(cl_sh_ddr_awlen_2d),
   .cl_sh_ddr_awsize(cl_sh_ddr_awsize_2d),
   .cl_sh_ddr_awvalid(cl_sh_ddr_awvalid_2d),
   .sh_cl_ddr_awready(sh_cl_ddr_awready_2d),

   .cl_sh_ddr_wid(cl_sh_ddr_wid_2d),
   .cl_sh_ddr_wdata(cl_sh_ddr_wdata_2d),
   .cl_sh_ddr_wstrb(cl_sh_ddr_wstrb_2d),
   .cl_sh_ddr_wlast(cl_sh_ddr_wlast_2d),
   .cl_sh_ddr_wvalid(cl_sh_ddr_wvalid_2d),
   .sh_cl_ddr_wready(sh_cl_ddr_wready_2d),

   .sh_cl_ddr_bid(sh_cl_ddr_bid_2d),
   .sh_cl_ddr_bresp(sh_cl_ddr_bresp_2d),
   .sh_cl_ddr_bvalid(sh_cl_ddr_bvalid_2d),
   .cl_sh_ddr_bready(cl_sh_ddr_bready_2d),

   .cl_sh_ddr_arid(cl_sh_ddr_arid_2d),
   .cl_sh_ddr_araddr(cl_sh_ddr_araddr_2d),
   .cl_sh_ddr_arlen(cl_sh_ddr_arlen_2d),
   .cl_sh_ddr_arsize(cl_sh_ddr_arsize_2d),
   .cl_sh_ddr_arvalid(cl_sh_ddr_arvalid_2d),
   .sh_cl_ddr_arready(sh_cl_ddr_arready_2d),

   .sh_cl_ddr_rid(sh_cl_ddr_rid_2d),
   .sh_cl_ddr_rdata(sh_cl_ddr_rdata_2d),
   .sh_cl_ddr_rresp(sh_cl_ddr_rresp_2d),
   .sh_cl_ddr_rlast(sh_cl_ddr_rlast_2d),
   .sh_cl_ddr_rvalid(sh_cl_ddr_rvalid_2d),
   .cl_sh_ddr_rready(cl_sh_ddr_rready_2d),


   .sh_cl_ddr_is_ready(lcl_sh_cl_ddr_is_ready),
   
   .sh_ddr_stat_addr0  (sh_ddr_stat_addr_q[0]) ,
   .sh_ddr_stat_wr0    (sh_ddr_stat_wr_q[0]     ) , 
   .sh_ddr_stat_rd0    (sh_ddr_stat_rd_q[0]     ) , 
   .sh_ddr_stat_wdata0 (sh_ddr_stat_wdata_q[0]  ) , 
   .ddr_sh_stat_ack0   (ddr_sh_stat_ack_q[0]    ) ,
   .ddr_sh_stat_rdata0 (ddr_sh_stat_rdata_q[0]  ),
   .ddr_sh_stat_int0   (ddr_sh_stat_int_q[0]    ),

   .sh_ddr_stat_addr1  (sh_ddr_stat_addr_q[1]) ,
   .sh_ddr_stat_wr1    (sh_ddr_stat_wr_q[1]     ) , 
   .sh_ddr_stat_rd1    (sh_ddr_stat_rd_q[1]     ) , 
   .sh_ddr_stat_wdata1 (sh_ddr_stat_wdata_q[1]  ) , 
   .ddr_sh_stat_ack1   (ddr_sh_stat_ack_q[1]    ) ,
   .ddr_sh_stat_rdata1 (ddr_sh_stat_rdata_q[1]  ),
   .ddr_sh_stat_int1   (ddr_sh_stat_int_q[1]    ),

   .sh_ddr_stat_addr2  (sh_ddr_stat_addr_q[2]) ,
   .sh_ddr_stat_wr2    (sh_ddr_stat_wr_q[2]     ) , 
   .sh_ddr_stat_rd2    (sh_ddr_stat_rd_q[2]     ) , 
   .sh_ddr_stat_wdata2 (sh_ddr_stat_wdata_q[2]  ) , 
   .ddr_sh_stat_ack2   (ddr_sh_stat_ack_q[2]    ) ,
   .ddr_sh_stat_rdata2 (ddr_sh_stat_rdata_q[2]  ),
   .ddr_sh_stat_int2   (ddr_sh_stat_int_q[2]    ) 
   );
`else


//Drive to 0 inputs to VHDL wrapper
//For CL_DDR disabled

   assign lcl_sh_cl_ddr_is_ready = 3'b000;

   assign lcl_cl_sh_ddra.awready = 1'b0;
   assign lcl_cl_sh_ddra.wready  = 1'b0;
   assign lcl_cl_sh_ddra.bid     = 16'b0;
   assign lcl_cl_sh_ddra.bresp   = 2'b0;
   assign lcl_cl_sh_ddra.bvalid  = 3'b0;
   assign lcl_cl_sh_ddra.arready = 1'b0;
   assign lcl_cl_sh_ddra.rid     = 16'b0;
   assign lcl_cl_sh_ddra.rdata   = 512'b0;
   assign lcl_cl_sh_ddra.rresp   = 2'b0;
   assign lcl_cl_sh_ddra.rlast   = 1'b0;
   assign lcl_cl_sh_ddra.rvalid  = 1'b0;

   assign lcl_cl_sh_ddrb.awready = 1'b0;
   assign lcl_cl_sh_ddrb.wready  = 1'b0;
   assign lcl_cl_sh_ddrb.bid     = 16'b0;
   assign lcl_cl_sh_ddrb.bresp   = 2'b0;
   assign lcl_cl_sh_ddrb.bvalid  = 3'b0;
   assign lcl_cl_sh_ddrb.arready = 1'b0;
   assign lcl_cl_sh_ddrb.rid     = 16'b0;
   assign lcl_cl_sh_ddrb.rdata   = 512'b0;
   assign lcl_cl_sh_ddrb.rresp   = 2'b0;
   assign lcl_cl_sh_ddrb.rlast   = 1'b0;
   assign lcl_cl_sh_ddrb.rvalid  = 1'b0;
   
   assign lcl_cl_sh_ddrd.awready = 1'b0;
   assign lcl_cl_sh_ddrd.wready  = 1'b0;
   assign lcl_cl_sh_ddrd.bid     = 16'b0;
   assign lcl_cl_sh_ddrd.bresp   = 2'b0;
   assign lcl_cl_sh_ddrd.bvalid  = 3'b0;
   assign lcl_cl_sh_ddrd.arready = 1'b0;
   assign lcl_cl_sh_ddrd.rid     = 16'b0;
   assign lcl_cl_sh_ddrd.rdata   = 512'b0;
   assign lcl_cl_sh_ddrd.rresp   = 2'b0;
   assign lcl_cl_sh_ddrd.rlast   = 1'b0;
   assign lcl_cl_sh_ddrd.rvalid  = 1'b0;
        

`endif        




//-------------------------------------------
// Tie-Off Global Signals
//-------------------------------------------
`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  


  assign cl_sh_status0[31:0] =  32'h0000_0FF0;
  assign cl_sh_status1[31:0] = `CL_VERSION;

`ifndef DISABLE_CHIPSCOPE_DEBUG

 //Always added no matter the flow 
 cl_debug_bridge CL_DEBUG_BRIDGE (
      .clk(clk_main_a0),
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
`endif  

endmodule
