// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module cl_dram_dma #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

(
   `include "cl_ports.vh"

);
  
   localparam DDR_A_PRESENT = 1;
   localparam DDR_B_PRESENT = 1;
   localparam DDR_D_PRESENT = 1;
   
   localparam NUM_CFG_STGS_CL_DDR_ATG = 4;
   localparam NUM_CFG_STGS_SH_DDR_ATG = 4;
   localparam NUM_CFG_STGS_PCIE_ATG = 4;
   localparam NUM_CFG_STGS_XDCFG = 4;
   localparam NUM_CFG_STGS_XDMA = 4;
   
`ifdef SIM
   localparam DDR_SCRB_MAX_ADDR = 64'h1FFF;
`else   
   localparam DDR_SCRB_MAX_ADDR = 64'h3FFFFFFFF; //16GB 
`endif
   localparam DDR_SCRB_BURST_LEN_MINUS1 = 15;

`ifdef NO_CL_TST_SCRUBBER
   localparam NO_SCRB_INST = 1;
`else
   localparam NO_SCRB_INST = 0;
`endif   

//---------------------------- 
// Internal signals
//---------------------------- 
axi_bus_t lcl_cl_sh_ddr0();
axi_bus_t lcl_cl_sh_ddr1();
axi_bus_t lcl_cl_sh_ddr2();

axi_bus_t sh_cl_dma_pcis_q();

cfg_bus_t pcim_tst_cfg_bus();
cfg_bus_t ddr0_tst_cfg_bus();
cfg_bus_t ddr1_tst_cfg_bus();
cfg_bus_t ddr2_tst_cfg_bus();
cfg_bus_t ddr3_tst_cfg_bus();
cfg_bus_t int_tst_cfg_bus();

scrb_bus_t ddr0_scrb_bus();
scrb_bus_t ddr1_scrb_bus();
scrb_bus_t ddr2_scrb_bus();
scrb_bus_t ddr3_scrb_bus();

scrb_bus_t hmc0_scrb_bus();
scrb_bus_t hmc1_scrb_bus();
logic [1:0] hmc_link_up_pipe;

logic clk;
logic pipe_rst_n;
logic pre_sync_rst_n;
logic sync_rst_n;
logic sh_cl_flr_assert_q;

logic [3:0] all_ddr_scrb_done;
logic [3:0] all_ddr_is_ready;
logic [2:0] lcl_sh_cl_ddr_is_ready;

logic dbg_scrb_en;
logic [2:0] dbg_scrb_mem_sel;

//---------------------------- 
// End Internal signals
//----------------------------

assign clk = clk_main_a0;
assign cl_sh_ddr_wid = 0;

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

//FLR response 

always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
   begin
      sh_cl_flr_assert_q <= 0;
      cl_sh_flr_done <= 0;
   end
   else
   begin
      sh_cl_flr_assert_q <= sh_cl_flr_assert;
      cl_sh_flr_done <= sh_cl_flr_assert_q && !cl_sh_flr_done;
   end

///////////////////////////////////////////////////////////////////////
///////////////// Scrubber enable and status //////////////////////////
///////////////////////////////////////////////////////////////////////

// Bit 31: Debug enable (for cl_sh_id0 and cl_sh_id1)
// Bit 30:28: Debug Scrb memory select
   
// Bit 5 : HMC1 Scrub enable
// Bit 4 : HMC0 Scrub enable
// Bit 3 : DDR3 Scrub enable
// Bit 2 : DDR2 Scrub enable
// Bit 1 : DDR1 Scrub enable
// Bit 0 : DDR0 Scrub enable
logic [31:0] sh_cl_ctl0_q;
always_ff @(posedge clk or negedge sync_rst_n)
  if (!sync_rst_n)
    sh_cl_ctl0_q <= 32'd0;
  else
    sh_cl_ctl0_q <= sh_cl_ctl0;

assign ddr0_scrb_bus.enable = sh_cl_ctl0_q[0];
assign ddr1_scrb_bus.enable = sh_cl_ctl0_q[1];
assign ddr3_scrb_bus.enable = sh_cl_ctl0_q[2];
assign ddr2_scrb_bus.enable = sh_cl_ctl0_q[3];

assign hmc0_scrb_bus.enable = sh_cl_ctl0_q[4];
assign hmc1_scrb_bus.enable = sh_cl_ctl0_q[5];

assign dbg_scrb_en = sh_cl_ctl0_q[31];
assign dbg_scrb_mem_sel[2:0] = sh_cl_ctl0_q[30:28];

`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  

wire[31:0] id0 = 32'h1d50_6789; 
wire[31:0] id1 = 32'h1d51_fedc; 
   
always_ff @(posedge clk)
    cl_sh_status0 <= dbg_scrb_en ? {1'b0, ddr2_scrb_bus.state, 
                                    1'b0, ddr3_scrb_bus.state, 
                                    1'b0, ddr1_scrb_bus.state, 
                                    1'b0, ddr0_scrb_bus.state,
                                    4'd0, hmc1_scrb_bus.done, hmc0_scrb_bus.done, hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready} :
                        {20'ha111_1, hmc1_scrb_bus.done, hmc0_scrb_bus.done, hmc_link_up_pipe[1:0], all_ddr_scrb_done, all_ddr_is_ready};
assign cl_sh_status1 = `CL_VERSION;


always_ff @(posedge clk)
    cl_sh_id0 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? ddr2_scrb_bus.addr[31:0] :
                                dbg_scrb_mem_sel == 3'd2 ? ddr3_scrb_bus.addr[31:0] :
                                dbg_scrb_mem_sel == 3'd1 ? ddr1_scrb_bus.addr[31:0] : ddr0_scrb_bus.addr[31:0]) :
                                id0; 
always_ff @(posedge clk)
    cl_sh_id1 <= dbg_scrb_en ? (dbg_scrb_mem_sel == 3'd3 ? ddr2_scrb_bus.addr[63:32] :
                                dbg_scrb_mem_sel == 3'd2 ? ddr3_scrb_bus.addr[63:32] :
                                dbg_scrb_mem_sel == 3'd1 ? ddr1_scrb_bus.addr[63:32] : ddr0_scrb_bus.addr[63:32]) :
                                id1;

logic sh_cl_ddr_is_ready_q;
always_ff @(posedge clk or negedge sync_rst_n)
  if (!sync_rst_n)
  begin
    sh_cl_ddr_is_ready_q <= 1'b0;
  end
  else
  begin
    sh_cl_ddr_is_ready_q <= sh_cl_ddr_is_ready;
  end  

assign all_ddr_is_ready = {lcl_sh_cl_ddr_is_ready[2], sh_cl_ddr_is_ready_q, lcl_sh_cl_ddr_is_ready[1:0]};

assign all_ddr_scrb_done = {ddr2_scrb_bus.done, ddr3_scrb_bus.done, ddr1_scrb_bus.done, ddr0_scrb_bus.done};


///////////////////////////////////////////////////////////////////////
///////////////// Scrubber enable and status //////////////////////////
///////////////////////////////////////////////////////////////////////
 

cl_dma_pcis_slv #(.SCRB_BURST_LEN_MINUS1(DDR_SCRB_BURST_LEN_MINUS1),
                    .SCRB_MAX_ADDR(DDR_SCRB_MAX_ADDR),
                    .NO_SCRB_INST(NO_SCRB_INST)) CL_DMA_PCIS_SLV (
    .aclk(clk),
    .aresetn(sync_rst_n),

    .ddr0_tst_cfg_bus(ddr0_tst_cfg_bus),
    .ddr1_tst_cfg_bus(ddr1_tst_cfg_bus),
    .ddr2_tst_cfg_bus(ddr2_tst_cfg_bus),
    .ddr3_tst_cfg_bus(ddr3_tst_cfg_bus),

    .ddr0_scrb_bus(ddr0_scrb_bus),
    .ddr1_scrb_bus(ddr1_scrb_bus),
    .ddr2_scrb_bus(ddr2_scrb_bus),
    .ddr3_scrb_bus(ddr3_scrb_bus),

    .sh_cl_dma_pcis_awid(sh_cl_dma_pcis_awid),
    .sh_cl_dma_pcis_awaddr(sh_cl_dma_pcis_awaddr),
    .sh_cl_dma_pcis_awlen(sh_cl_dma_pcis_awlen),
    .sh_cl_dma_pcis_awsize(sh_cl_dma_pcis_awsize),
    .sh_cl_dma_pcis_awvalid(sh_cl_dma_pcis_awvalid),
    .cl_sh_dma_pcis_awready(cl_sh_dma_pcis_awready),

    .sh_cl_dma_pcis_wdata(sh_cl_dma_pcis_wdata),
    .sh_cl_dma_pcis_wstrb(sh_cl_dma_pcis_wstrb),
    .sh_cl_dma_pcis_wlast(sh_cl_dma_pcis_wlast),
    .sh_cl_dma_pcis_wvalid(sh_cl_dma_pcis_wvalid),
    .cl_sh_dma_pcis_wready(cl_sh_dma_pcis_wready),

    .cl_sh_dma_pcis_bid(cl_sh_dma_pcis_bid),
    .cl_sh_dma_pcis_bresp(cl_sh_dma_pcis_bresp),
    .cl_sh_dma_pcis_bvalid(cl_sh_dma_pcis_bvalid),
    .sh_cl_dma_pcis_bready(sh_cl_dma_pcis_bready),

    .sh_cl_dma_pcis_arid(sh_cl_dma_pcis_arid),
    .sh_cl_dma_pcis_araddr(sh_cl_dma_pcis_araddr),
    .sh_cl_dma_pcis_arlen(sh_cl_dma_pcis_arlen),
    .sh_cl_dma_pcis_arsize(sh_cl_dma_pcis_arsize),
    .sh_cl_dma_pcis_arvalid(sh_cl_dma_pcis_arvalid),
    .cl_sh_dma_pcis_arready(cl_sh_dma_pcis_arready),

    .cl_sh_dma_pcis_rid(cl_sh_dma_pcis_rid),
    .cl_sh_dma_pcis_rdata(cl_sh_dma_pcis_rdata),
    .cl_sh_dma_pcis_rresp(cl_sh_dma_pcis_rresp),
    .cl_sh_dma_pcis_rlast(cl_sh_dma_pcis_rlast),
    .cl_sh_dma_pcis_rvalid(cl_sh_dma_pcis_rvalid),
    .sh_cl_dma_pcis_rready(sh_cl_dma_pcis_rready),

    

    .lcl_cl_sh_ddr0(lcl_cl_sh_ddr0),
    .lcl_cl_sh_ddr1(lcl_cl_sh_ddr1),
    .lcl_cl_sh_ddr2(lcl_cl_sh_ddr2),

    .sh_cl_dma_pcis_q(sh_cl_dma_pcis_q),

    .cl_sh_ddr_awid     (cl_sh_ddr_awid),   
    .cl_sh_ddr_awaddr   (cl_sh_ddr_awaddr), 
    .cl_sh_ddr_awlen    (cl_sh_ddr_awlen),
    .cl_sh_ddr_awsize   (cl_sh_ddr_awsize), 
    .cl_sh_ddr_awvalid  (cl_sh_ddr_awvalid),
    .sh_cl_ddr_awready  (sh_cl_ddr_awready),

    .cl_sh_ddr_wid      (cl_sh_ddr_wid), 
    .cl_sh_ddr_wdata    (cl_sh_ddr_wdata),  
    .cl_sh_ddr_wstrb    (cl_sh_ddr_wstrb),  
    .cl_sh_ddr_wlast    (cl_sh_ddr_wlast),  
    .cl_sh_ddr_wvalid   (cl_sh_ddr_wvalid), 
    .sh_cl_ddr_wready   (sh_cl_ddr_wready), 

    .sh_cl_ddr_bid      (sh_cl_ddr_bid),    
    .sh_cl_ddr_bresp    (sh_cl_ddr_bresp),  
    .sh_cl_ddr_bvalid   (sh_cl_ddr_bvalid), 
    .cl_sh_ddr_bready   (cl_sh_ddr_bready), 

    .cl_sh_ddr_arid     (cl_sh_ddr_arid),   
    .cl_sh_ddr_araddr   (cl_sh_ddr_araddr), 
    .cl_sh_ddr_arlen    (cl_sh_ddr_arlen),
    .cl_sh_ddr_arsize   (cl_sh_ddr_arsize),  
    .cl_sh_ddr_arvalid  (cl_sh_ddr_arvalid),
    .sh_cl_ddr_arready  (sh_cl_ddr_arready),

    .sh_cl_ddr_rid      (sh_cl_ddr_rid),    
    .sh_cl_ddr_rdata    (sh_cl_ddr_rdata),  
    .sh_cl_ddr_rresp    (sh_cl_ddr_rresp),  
    .sh_cl_ddr_rlast    (sh_cl_ddr_rlast),  
    .sh_cl_ddr_rvalid   (sh_cl_ddr_rvalid), 
    .cl_sh_ddr_rready   (cl_sh_ddr_rready)
  );


cl_pcim_mstr CL_PCIM_MSTR (

     .aclk(clk),
     .aresetn(sync_rst_n),

     .cfg_bus(pcim_tst_cfg_bus),

     .cl_sh_pcim_awid     (cl_sh_pcim_awid),   
     .cl_sh_pcim_awaddr   (cl_sh_pcim_awaddr), 
     .cl_sh_pcim_awlen    (cl_sh_pcim_awlen),
     .cl_sh_pcim_awsize   (cl_sh_pcim_awsize), 
     .cl_sh_pcim_awvalid  (cl_sh_pcim_awvalid),
     .sh_cl_pcim_awready  (sh_cl_pcim_awready),
     .cl_sh_pcim_wdata    (cl_sh_pcim_wdata),  
     .cl_sh_pcim_wstrb    (cl_sh_pcim_wstrb),  
     .cl_sh_pcim_wlast    (cl_sh_pcim_wlast),  
     .cl_sh_pcim_wvalid   (cl_sh_pcim_wvalid), 
     .sh_cl_pcim_wready   (sh_cl_pcim_wready), 
     .sh_cl_pcim_bid      (sh_cl_pcim_bid),    
     .sh_cl_pcim_bresp    (sh_cl_pcim_bresp),  
     .sh_cl_pcim_bvalid   (sh_cl_pcim_bvalid), 
     .cl_sh_pcim_bready   (cl_sh_pcim_bready), 
     .cl_sh_pcim_arid     (cl_sh_pcim_arid),   
     .cl_sh_pcim_araddr   (cl_sh_pcim_araddr), 
     .cl_sh_pcim_arlen    (cl_sh_pcim_arlen),  
     .cl_sh_pcim_arsize   (cl_sh_pcim_arsize),
     .cl_sh_pcim_arvalid  (cl_sh_pcim_arvalid),
     .sh_cl_pcim_arready  (sh_cl_pcim_arready),
     .sh_cl_pcim_rid      (sh_cl_pcim_rid),    
     .sh_cl_pcim_rdata    (sh_cl_pcim_rdata),  
     .sh_cl_pcim_rresp    (sh_cl_pcim_rresp),  
     .sh_cl_pcim_rlast    (sh_cl_pcim_rlast),  
     .sh_cl_pcim_rvalid   (sh_cl_pcim_rvalid), 
     .cl_sh_pcim_rready   (cl_sh_pcim_rready)
);

cl_ocl_slv CL_OCL_SLV (

   .clk(clk),
   .sync_rst_n(sync_rst_n),

   .sh_cl_flr_assert_q(sh_cl_flr_assert_q),

   .sh_ocl_awaddr  (sh_ocl_awaddr),
   .sh_ocl_awvalid (sh_ocl_awvalid),
   .ocl_sh_awready (ocl_sh_awready),
   .sh_ocl_wdata   (sh_ocl_wdata),
   .sh_ocl_wstrb   (sh_ocl_wstrb),
   .sh_ocl_wvalid  (sh_ocl_wvalid),
   .ocl_sh_wready  (ocl_sh_wready),
   .ocl_sh_bresp   (ocl_sh_bresp),
   .ocl_sh_bvalid  (ocl_sh_bvalid),
   .sh_ocl_bready  (sh_ocl_bready),
   .sh_ocl_araddr  (sh_ocl_araddr),
   .sh_ocl_arvalid (sh_ocl_arvalid),
   .ocl_sh_arready (ocl_sh_arready),
   .ocl_sh_rdata   (ocl_sh_rdata),
   .ocl_sh_rresp   (ocl_sh_rresp),
   .ocl_sh_rvalid  (ocl_sh_rvalid),
   .sh_ocl_rready  (sh_ocl_rready),

   .pcim_tst_cfg_bus(pcim_tst_cfg_bus),
   .ddr0_tst_cfg_bus(ddr0_tst_cfg_bus),
   .ddr1_tst_cfg_bus(ddr1_tst_cfg_bus),
   .ddr2_tst_cfg_bus(ddr2_tst_cfg_bus),
   .ddr3_tst_cfg_bus(ddr3_tst_cfg_bus),
   .int_tst_cfg_bus(int_tst_cfg_bus)

);



//----------------------------------------- 
// DDR controller instantiation   
//-----------------------------------------
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
 
sh_ddr #(
         .DDR_A_PRESENT(DDR_A_PRESENT),
         .DDR_A_IO(1),
         .DDR_B_PRESENT(DDR_B_PRESENT),
         .DDR_D_PRESENT(DDR_D_PRESENT)
   ) SH_DDR
   (
   .clk(clk),
   .rst_n(sync_rst_n),

   .stat_clk(clk),
   .stat_rst_n(sync_rst_n),


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
   .RST_DIMM_A_N(RST_DIMM_A_N),
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
   .RST_DIMM_B_N(RST_DIMM_B_N),
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
   .RST_DIMM_D_N(RST_DIMM_D_N),
   .M_D_PAR(M_D_PAR),
   .M_D_DQ(M_D_DQ),
   .M_D_ECC(M_D_ECC),
   .M_D_DQS_DP(M_D_DQS_DP),
   .M_D_DQS_DN(M_D_DQS_DN),
   .cl_RST_DIMM_D_N(cl_RST_DIMM_D_N),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid({lcl_cl_sh_ddr2.awid, lcl_cl_sh_ddr1.awid, lcl_cl_sh_ddr0.awid}),
   .cl_sh_ddr_awaddr({lcl_cl_sh_ddr2.awaddr, lcl_cl_sh_ddr1.awaddr, lcl_cl_sh_ddr0.awaddr}),
   .cl_sh_ddr_awlen({lcl_cl_sh_ddr2.awlen, lcl_cl_sh_ddr1.awlen, lcl_cl_sh_ddr0.awlen}),
   .cl_sh_ddr_awvalid({lcl_cl_sh_ddr2.awvalid, lcl_cl_sh_ddr1.awvalid, lcl_cl_sh_ddr0.awvalid}),
   .sh_cl_ddr_awready({lcl_cl_sh_ddr2.awready, lcl_cl_sh_ddr1.awready, lcl_cl_sh_ddr0.awready}),

   .cl_sh_ddr_wid({lcl_cl_sh_ddr2.wid, lcl_cl_sh_ddr1.wid, lcl_cl_sh_ddr0.wid}),
   .cl_sh_ddr_wdata({lcl_cl_sh_ddr2.wdata, lcl_cl_sh_ddr1.wdata, lcl_cl_sh_ddr0.wdata}),
   .cl_sh_ddr_wstrb({lcl_cl_sh_ddr2.wstrb, lcl_cl_sh_ddr1.wstrb, lcl_cl_sh_ddr0.wstrb}),
   .cl_sh_ddr_wlast({lcl_cl_sh_ddr2.wlast, lcl_cl_sh_ddr1.wlast, lcl_cl_sh_ddr0.wlast}),
   .cl_sh_ddr_wvalid({lcl_cl_sh_ddr2.wvalid, lcl_cl_sh_ddr1.wvalid, lcl_cl_sh_ddr0.wvalid}),
   .sh_cl_ddr_wready({lcl_cl_sh_ddr2.wready, lcl_cl_sh_ddr1.wready, lcl_cl_sh_ddr0.wready}),

   .sh_cl_ddr_bid({lcl_cl_sh_ddr2.bid, lcl_cl_sh_ddr1.bid, lcl_cl_sh_ddr0.bid}),
   .sh_cl_ddr_bresp({lcl_cl_sh_ddr2.bresp, lcl_cl_sh_ddr1.bresp, lcl_cl_sh_ddr0.bresp}),
   .sh_cl_ddr_bvalid({lcl_cl_sh_ddr2.bvalid, lcl_cl_sh_ddr1.bvalid, lcl_cl_sh_ddr0.bvalid}),
   .cl_sh_ddr_bready({lcl_cl_sh_ddr2.bready, lcl_cl_sh_ddr1.bready, lcl_cl_sh_ddr0.bready}),

   .cl_sh_ddr_arid({lcl_cl_sh_ddr2.arid, lcl_cl_sh_ddr1.arid, lcl_cl_sh_ddr0.arid}),
   .cl_sh_ddr_araddr({lcl_cl_sh_ddr2.araddr, lcl_cl_sh_ddr1.araddr, lcl_cl_sh_ddr0.araddr}),
   .cl_sh_ddr_arlen({lcl_cl_sh_ddr2.arlen, lcl_cl_sh_ddr1.arlen, lcl_cl_sh_ddr0.arlen}),
   .cl_sh_ddr_arvalid({lcl_cl_sh_ddr2.arvalid, lcl_cl_sh_ddr1.arvalid, lcl_cl_sh_ddr0.arvalid}),
   .sh_cl_ddr_arready({lcl_cl_sh_ddr2.arready, lcl_cl_sh_ddr1.arready, lcl_cl_sh_ddr0.arready}),

   .sh_cl_ddr_rid({lcl_cl_sh_ddr2.rid, lcl_cl_sh_ddr1.rid, lcl_cl_sh_ddr0.rid}),
   .sh_cl_ddr_rdata({lcl_cl_sh_ddr2.rdata, lcl_cl_sh_ddr1.rdata, lcl_cl_sh_ddr0.rdata}),
   .sh_cl_ddr_rresp({lcl_cl_sh_ddr2.rresp, lcl_cl_sh_ddr1.rresp, lcl_cl_sh_ddr0.rresp}),
   .sh_cl_ddr_rlast({lcl_cl_sh_ddr2.rlast, lcl_cl_sh_ddr1.rlast, lcl_cl_sh_ddr0.rlast}),
   .sh_cl_ddr_rvalid({lcl_cl_sh_ddr2.rvalid, lcl_cl_sh_ddr1.rvalid, lcl_cl_sh_ddr0.rvalid}),
   .cl_sh_ddr_rready({lcl_cl_sh_ddr2.rready, lcl_cl_sh_ddr1.rready, lcl_cl_sh_ddr0.rready}),

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


cl_int_slv CL_INT_TST 
(
  .clk                 (clk),
  .rst_n               (sync_rst_n),

  .cfg_bus             (int_tst_cfg_bus),

  .cl_sh_apppf_irq_req (cl_sh_apppf_irq_req),
  .sh_cl_apppf_irq_ack (sh_cl_apppf_irq_ack)
       
);

cl_sda_slv CL_SDA_SLV (

  .aclk(clk),
  .aresetn(sync_rst_n),
  
  .sda_cl_awvalid(sda_cl_awvalid), 
  .sda_cl_awaddr(sda_cl_awaddr),
  .cl_sda_awready(cl_sda_awready),
      
  .sda_cl_wvalid(sda_cl_wvalid),
  .sda_cl_wdata(sda_cl_wdata),
  .sda_cl_wstrb(sda_cl_wstrb),
  .cl_sda_wready(cl_sda_wready),
     
  .cl_sda_bvalid(cl_sda_bvalid), 
  .cl_sda_bresp(cl_sda_bresp),
  .sda_cl_bready(sda_cl_bready),
                 
  .sda_cl_arvalid(sda_cl_arvalid),
  .sda_cl_araddr(sda_cl_araddr),
  .cl_sda_arready(cl_sda_arready),
                    
  .cl_sda_rvalid(cl_sda_rvalid),
  .cl_sda_rdata(cl_sda_rdata),
  .cl_sda_rresp(cl_sda_rresp),        
  .sda_cl_rready(sda_cl_rready)
);

`ifndef DISABLE_CHIPSCOPE_DEBUG

cl_ila CL_ILA (

   .aclk(aclk),

   .drck(drck),
   .shift(shift),
   .tdi(tdi),
   .update(update),
   .sel(sel),
   .tdo(tdo),
   .tms(tms),
   .tck(tck),
   .runtest(runtest),
   .reset(reset),
   .capture(capture),
   .bscanid(bscanid),
 
   .sh_cl_dma_pcis_q(sh_cl_dma_pcis_q),
   .lcl_cl_sh_ddr0(lcl_cl_sh_ddr0)

);


cl_vio CL_VIO (

   .clk_extra_a1(clk_extra_a1)

);

`endif //  `ifndef DISABLE_CHIPSCOPE_DEBUG


endmodule   
