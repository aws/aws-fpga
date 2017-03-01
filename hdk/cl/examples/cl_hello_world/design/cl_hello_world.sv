// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

module cl_hello_world #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

(
   `include "cl_ports.vh" // Fixed port definition

);
  
   localparam NUM_CFG_STGS_INT_TST = 4;
   localparam NUM_CFG_STGS_HMC_ATG = 4;
   localparam NUM_CFG_STGS_CL_DDR_ATG = 4;
   localparam NUM_CFG_STGS_SH_DDR_ATG = 4;
   localparam NUM_CFG_STGS_PCIE_ATG = 4;
   localparam NUM_CFG_STGS_AURORA_ATG = 4;
   localparam NUM_CFG_STGS_XDCFG = 4;
   localparam NUM_CFG_STGS_XDMA = 4;
   
`ifdef SIM
   localparam DDR_SCRB_MAX_ADDR = 64'h1FFF;
   localparam HMC_SCRB_MAX_ADDR = 64'h7FF;
`else   
   localparam DDR_SCRB_MAX_ADDR = 64'h3FFFFFFFF; //16GB 
   localparam HMC_SCRB_MAX_ADDR = 64'h7FFFFFFF;  // 2GB
`endif
   localparam DDR_SCRB_BURST_LEN_MINUS1 = 15;
   localparam HMC_SCRB_BURST_LEN_MINUS1 = 3;

//-------------------------------------------------
// Signals to Tie-off AXI interfaces to sh_ddr module
//-------------------------------------------------
  logic         tie_zero[2:0];
  logic [ 15:0] tie_zero_id[2:0];
  logic [ 63:0] tie_zero_addr[2:0];
  logic [  7:0] tie_zero_len[2:0];
  logic [511:0] tie_zero_data[2:0];
  logic [ 63:0] tie_zero_strb[2:0];
  logic [  7:0] tie_zero_stat_addr[2:0];
  logic [ 31:0] tie_zero_stat_data[2:0];

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------
logic pre_sync_rst_n;
logic sync_rst_n;
   
always_ff @(negedge rst_main_n or posedge clk_extra_a1)
   if (!rst_main_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end

   logic extra_a1_rst_n;
   sync #(.WIDTH(1)) sync_extra_a1_rst (.clk(clk_extra_a1), .rst_n(rst_main_n), .in(1'b1), .sync_out(extra_a1_rst_n));

//-------------------------------------------------
// PCIe Slave AXI (SH to CL) Timing Flops
//-------------------------------------------------
   logic [4:0]                 sh_cl_dma_pcis_awid_q;
   logic [63:0]                sh_cl_dma_pcis_awaddr_q;
   logic                       sh_cl_dma_pcis_awvalid_q;
   logic                       cl_sh_dma_pcis_awready_q;

   logic [511:0]               sh_cl_dma_pcis_wdata_q;
   logic [63:0]                sh_cl_dma_pcis_wstrb_q;
   logic                       sh_cl_dma_pcis_wvalid_q;
   logic                       cl_sh_dma_pcis_wready_q;

   logic [4:0]                 cl_sh_dma_pcis_bid_q;
   logic [1:0]                 cl_sh_dma_pcis_bresp_q;
   logic                       cl_sh_dma_pcis_bvalid_q;
   logic                       sh_cl_dma_pcis_bready_q;

   logic [4:0]                 sh_cl_dma_pcis_arid_q;
   logic [63:0]                sh_cl_dma_pcis_araddr_q;
   logic                       sh_cl_dma_pcis_arvalid_q;
   logic                       cl_sh_dma_pcis_arready_q;

   logic [511:0]               cl_sh_dma_pcis_rdata_q;
   logic [4:0]                 cl_sh_dma_pcis_rid_q;
   logic [1:0]                 cl_sh_dma_pcis_rresp_q;
   logic                       cl_sh_dma_pcis_rlast_q;
   logic                       cl_sh_dma_pcis_rvalid_q;
   logic                       sh_cl_dma_pcis_rready_q;

 // AXI-Lite Register Slice for signals between CL and SH
   axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(64), .DATA_WIDTH(512), .ID_WIDTH(5), .A_USER_WIDTH(1), .FIFO_DEPTH(3), .CCF(1) ) PCI_AXL_REG_SLC (
  //.aclk          (clk_extra_a1),
  //.aresetn       (sync_rst_n),
  //.sync_rst_n    (1'b1),

    .aclk          (clk_main_a0), // 250 MHz
    .aresetn       (rst_main_n),
    .sync_rst_n    (rst_main_n),
    .rd_aclk       (clk_extra_a1), // 125 MHz
    .rd_sync_rst_n (extra_a1_rst_n),



    .s_axi_awid    (sh_cl_dma_pcis_awid),
    .s_axi_awaddr  (sh_cl_dma_pcis_awaddr),
    .s_axi_awlen   (8'd0),                                            
    .s_axi_awvalid (sh_cl_dma_pcis_awvalid),
    .s_axi_awuser  (),
    .s_axi_awready (cl_sh_dma_pcis_awready),
    .s_axi_wdata   (sh_cl_dma_pcis_wdata),
    .s_axi_wstrb   (sh_cl_dma_pcis_wstrb),
    .s_axi_wlast   (1'd0),
    .s_axi_wuser   (),
    .s_axi_wvalid  (sh_cl_dma_pcis_wvalid),
    .s_axi_wready  (cl_sh_dma_pcis_wready),
    .s_axi_bid     (cl_sh_dma_pcis_bid),
    .s_axi_bresp   (cl_sh_dma_pcis_bresp),
    .s_axi_bvalid  (cl_sh_dma_pcis_bvalid),
    .s_axi_buser   (),
    .s_axi_bready  (sh_cl_dma_pcis_bready),
    .s_axi_arid    (sh_cl_dma_pcis_arid),
    .s_axi_araddr  (sh_cl_dma_pcis_araddr),
    .s_axi_arlen   (8'd0), 
    .s_axi_arvalid (sh_cl_dma_pcis_arvalid),
    .s_axi_aruser  (1'd0),
    .s_axi_arready (cl_sh_dma_pcis_arready),
    .s_axi_rid     (cl_sh_dma_pcis_rid),
    .s_axi_rdata   (cl_sh_dma_pcis_rdata),
    .s_axi_rresp   (cl_sh_dma_pcis_rresp),
    .s_axi_rlast   (cl_sh_dma_pcis_rlast),
    .s_axi_ruser   (),
    .s_axi_rvalid  (cl_sh_dma_pcis_rvalid),
    .s_axi_rready  (sh_cl_dma_pcis_rready), 
    .m_axi_awid    (sh_cl_dma_pcis_awid_q),
    .m_axi_awaddr  (sh_cl_dma_pcis_awaddr_q), 
    .m_axi_awlen   (),
    .m_axi_awvalid (sh_cl_dma_pcis_awvalid_q),
    .m_axi_awuser  (),
    .m_axi_awready (cl_sh_dma_pcis_awready_q),
    .m_axi_wdata   (sh_cl_dma_pcis_wdata_q),  
    .m_axi_wstrb   (sh_cl_dma_pcis_wstrb_q),
    .m_axi_wvalid  (sh_cl_dma_pcis_wvalid_q), 
    .m_axi_wlast   (),
    .m_axi_wuser   (),
    .m_axi_wready  (cl_sh_dma_pcis_wready_q), 
    .m_axi_bresp   (cl_sh_dma_pcis_bresp_q),  
    .m_axi_bvalid  (cl_sh_dma_pcis_bvalid_q), 
    .m_axi_bid     (cl_sh_dma_pcis_bid_q),
    .m_axi_buser   (),
    .m_axi_bready  (sh_cl_dma_pcis_bready_q), 
    .m_axi_arid    (sh_cl_dma_pcis_arid_q), 
    .m_axi_araddr  (sh_cl_dma_pcis_araddr_q), 
    .m_axi_arlen   (), 
    .m_axi_aruser  (), 
    .m_axi_arvalid (sh_cl_dma_pcis_arvalid_q),
    .m_axi_arready (cl_sh_dma_pcis_arready_q),
    .m_axi_rid     (cl_sh_dma_pcis_rid_q),  
    .m_axi_rdata   (cl_sh_dma_pcis_rdata_q),  
    .m_axi_rresp   (cl_sh_dma_pcis_rresp_q),  
    .m_axi_rlast   (cl_sh_dma_pcis_rlast_q),  
    .m_axi_ruser   (1'b0),
    .m_axi_rvalid  (cl_sh_dma_pcis_rvalid_q), 
    .m_axi_rready  (sh_cl_dma_pcis_rready_q)
   );

//-------------------------------------------------
// Slave state machine (accesses from PCIe)
//-------------------------------------------------
typedef enum logic[2:0] {
   SLV_IDLE = 0,
   SLV_WR_ADDR = 1,
   SLV_CYC = 2,
   SLV_RESP = 3
   } slv_state_t;

slv_state_t slv_state, slv_state_nxt;

logic        slv_arb_wr;          // Arbitration winner (write/read)
logic        slv_cyc_wr;          // Cycle is write
logic[31:0]  slv_mx_addr;         // Mux address
logic        slv_mx_rsp_ready;    // Mux the response ready
             
logic        slv_wr_req;          // Write request
             
logic        slv_cyc_done;        // Cycle is done
             
logic[31:0]  slv_rdata;           // Latch rdata
             
logic[31:0]  slv_tst_addr;
logic[31:0]  slv_tst_wdata;
logic        slv_tst_wr;
logic        slv_tst_rd;
logic        slv_mx_req_valid;
             
logic        tst_slv_ack;
logic[31:0]  tst_slv_rdata ;
             
logic        slv_did_req;         // Once cycle request, latch that did the request

logic [63:0] slv_req_rd_addr;
logic [63:0] slv_req_wr_addr;
logic [4:0]  slv_req_rd_id;
logic [4:0]  slv_req_wr_id;
   
//Write request valid when both address is valid
assign slv_wr_req = sh_cl_dma_pcis_awvalid_q;

assign slv_mx_rsp_ready = (slv_cyc_wr)? sh_cl_dma_pcis_bready_q: sh_cl_dma_pcis_rready_q;

assign slv_mx_req_valid = (slv_cyc_wr)?   sh_cl_dma_pcis_wvalid_q:
                                          1'b1;
//Fixed write hi-pri
assign slv_arb_wr = slv_wr_req;

always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
  if (!extra_a1_rst_n)
    {slv_req_rd_addr, slv_req_wr_addr} <= 128'd0;
  else if ((slv_state == SLV_IDLE) && (sh_cl_dma_pcis_arvalid_q || sh_cl_dma_pcis_awvalid_q))
    {slv_req_rd_addr, slv_req_wr_addr} <= {sh_cl_dma_pcis_araddr_q, sh_cl_dma_pcis_awaddr_q};
   
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
  if (!extra_a1_rst_n)
    {slv_req_rd_id, slv_req_wr_id} <= 0;
  else if ((slv_state == SLV_IDLE) && (sh_cl_dma_pcis_arvalid_q || sh_cl_dma_pcis_awvalid_q))
    {slv_req_rd_id, slv_req_wr_id} <= {sh_cl_dma_pcis_arid_q, sh_cl_dma_pcis_awid_q};
   
//Mux address
assign slv_mx_addr = (slv_cyc_wr)? slv_req_wr_addr : slv_req_rd_addr;
   
//Latch the winner
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
      slv_cyc_wr <= 0;
   else if (slv_state==SLV_IDLE)
      slv_cyc_wr <= slv_arb_wr;

//State machine
always_comb
begin
   slv_state_nxt = slv_state;
   case (slv_state)

      SLV_IDLE:
      begin
         if (slv_wr_req)
            slv_state_nxt = SLV_WR_ADDR;
         else if (sh_cl_dma_pcis_arvalid_q)
            slv_state_nxt = SLV_CYC;
         else
            slv_state_nxt = SLV_IDLE;
      end

      SLV_WR_ADDR:
      begin
         slv_state_nxt = SLV_CYC;
      end

      SLV_CYC:
      begin
         if (slv_cyc_done)
            slv_state_nxt = SLV_RESP;
         else
            slv_state_nxt = SLV_CYC;
      end

      SLV_RESP:
      begin
         if (slv_mx_rsp_ready)
            slv_state_nxt = SLV_IDLE;
         else
            slv_state_nxt = SLV_RESP;
      end

   endcase
end

//State machine flops
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
      slv_state <= SLV_IDLE;
   else
      slv_state <= slv_state_nxt;


//Cycle to sub-blocks for register access
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
   begin
      slv_tst_addr  <= '{default:'0};
      slv_tst_wdata <= '{default:'0};
   end
   else
   begin
      slv_tst_addr  <= slv_mx_addr;
      slv_tst_wdata <= sh_cl_dma_pcis_wdata_q >> (32 * slv_req_wr_addr[5:2]);
   end

//Test are 1 clock pulses (because want to support clock crossing)
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
   begin
      slv_did_req <= 0;
   end
   else if (slv_state==SLV_IDLE)
   begin
      slv_did_req <= 0;
   end
   else if (|slv_tst_wr || |slv_tst_rd)
   begin
      slv_did_req <= 1;
   end

//Flop this for timing
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
   begin
      slv_tst_wr <= 0;
      slv_tst_rd <= 0;
   end
   else
   begin
      slv_tst_wr <= ((slv_state==SLV_CYC) & slv_mx_req_valid & slv_cyc_wr & !slv_did_req);
      slv_tst_rd <= ((slv_state==SLV_CYC) & slv_mx_req_valid & !slv_cyc_wr & !slv_did_req);
   end

assign slv_cyc_done = tst_slv_ack;

//Latch the return data
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
      slv_rdata <= 0;
   else if (slv_cyc_done)
      slv_rdata <= tst_slv_rdata;

//Ready back to AXI for request
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
   begin
      cl_sh_dma_pcis_awready_q <= 0;
      cl_sh_dma_pcis_wready_q <= 0;
      cl_sh_dma_pcis_arready_q <= 0;
   end
   else
   begin
      cl_sh_dma_pcis_awready_q <= (slv_state_nxt==SLV_WR_ADDR);
      cl_sh_dma_pcis_wready_q <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && slv_cyc_wr;
      cl_sh_dma_pcis_arready_q <= ((slv_state==SLV_CYC) && (slv_state_nxt!=SLV_CYC)) && ~slv_cyc_wr;
   end

//Response back to AXI
assign cl_sh_dma_pcis_bid_q = slv_req_wr_id;
assign cl_sh_dma_pcis_bresp_q = 2'b0;
assign cl_sh_dma_pcis_bvalid_q = (slv_state==SLV_RESP) && slv_cyc_wr;

assign cl_sh_dma_pcis_rid_q = slv_req_rd_id;
assign cl_sh_dma_pcis_rdata_q = slv_rdata << (32 * slv_req_rd_addr[5:2]);
assign cl_sh_dma_pcis_rresp_q = 2'b00;
assign cl_sh_dma_pcis_rvalid_q = (slv_state==SLV_RESP) && !slv_cyc_wr;
assign cl_sh_dma_pcis_rlast_q = 1'b1;         //Always 1 DW

//assign cl_sh_dma_pcis_bresp[1]  = 2'h0;
//assign cl_sh_dma_pcis_bvalid = 1'h0;

//assign cl_sh_dma_pcis_rdata  = 512'h0;
//assign cl_sh_dma_pcis_rresp  = 2'h0;
//assign cl_sh_dma_pcis_rvalid = 1'h0;

// Config Register Access
//---------------------------------------------

// Offset         Register
// ------         ---------------------------
// 0x0            Hello World Register
// 0x4            Virtual DIP & LED Register

//Commands are single cycle pulse, stretch here

logic        cfg_wr_stretch;
logic        cfg_rd_stretch;
logic [7:0]  cfg_addr_q;
logic [31:0] cfg_wdata_q;
logic [31:0] hello_world_q;
//logic [31:0] virtual_dip_led_q;

always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
   begin
      cfg_wr_stretch <= 0;
      cfg_rd_stretch <= 0;
      cfg_addr_q <= 0;
      cfg_wdata_q <= 0;
   end
   else
   begin
      cfg_wr_stretch <= slv_tst_wr || (cfg_wr_stretch && !tst_slv_ack);
      cfg_rd_stretch <= slv_tst_rd || (cfg_rd_stretch && !tst_slv_ack);
      if (slv_tst_wr||slv_tst_rd)
      begin
         cfg_addr_q[7:0]   <= slv_tst_addr[7:0];
         cfg_wdata_q[31:0] <= slv_tst_wdata[31:0];
      end
   end

// Readback mux
//---------------------------------------------
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
      tst_slv_rdata <= 0;
   else
      case (cfg_addr_q)
         8'h0:       tst_slv_rdata <= {hello_world_q[7:0],   hello_world_q[15:8],
                                       hello_world_q[23:16], hello_world_q[31:24]};

         default:    tst_slv_rdata <= 32'hffffffff;
      endcase

//Ack for cycle
always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n)
      tst_slv_ack <= 0;
   else
      tst_slv_ack <= ((cfg_wr_stretch||cfg_rd_stretch) && !tst_slv_ack);

//-------------------------------------------------
// Hello World Register
//-------------------------------------------------
// The register resides at offset 0x00. When read it
// returns the byte-flipped value.

always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
   if (!extra_a1_rst_n) begin                    // Reset
      hello_world_q[31:0] <= 32'h0000_0000;
   end
   else if (cfg_wr_stretch & (cfg_addr_q == 8'h0)) begin  // Cfg Write to offset 0x00
      hello_world_q[31:0] <= cfg_wdata_q[31:0];
   end
   else begin                                // Hold Value
      hello_world_q[31:0] <= hello_world_q[31:0];
   end

//-------------------------------------------------
// Virtual DIP & LED Register
//-------------------------------------------------
// The register resides at offset 0x04.

//logic [31:0] virtual_dip_led_q;

// The register is divided into:
// 1. Bits 31-16: 16 write-able bits that represent DIP switches and
// 2. Bits 15- 0: 16 read-only bits that represent virtual LEDs

//always_ff @(negedge extra_a1_rst_n or posedge clk_extra_a1)
//   if (!extra_a1_rst_n) begin                    // Reset
//      virtual_dip_led_q[31:0] <= 32'h0000_0000;
//   end
//   else if (cfg_wr_stretch & (cfg_addr_q == 8'h4)) begin  // Cfg Write to offset 0x04
//      // Only DIP switches (bits 31-16) are write-able
//      virtual_dip_led_q[31:0] <= {cfg_wdata_q[31:16],virtual_dip_led_q[15:0]};
//   end
//   else begin                                // Hold Value
//      virtual_dip_led_q[31:0] <= virtual_dip_led_q[31:0];
//   end


//----------------------------------------- 
// DDR controller instantiation   
//----------------------------------------- 
// Although we are not using the DDR controllers in this cl_hello_world
// design, it must be instantiated in order to prevent build errors related to
// DDR pin constraints.

// Only the DDR pins are connected. The AXI and stats interfaces are tied-off.

sh_ddr #(.DDR_A_PRESENT(0),
         .DDR_B_PRESENT(0),
         .DDR_D_PRESENT(0)) SH_DDR
   (
   .clk(clk_extra_a1),
   .rst_n(extra_a1_rst_n),
   .stat_clk(clk_extra_a1),
   .stat_rst_n(clk_extra_a1),

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
   .cl_RST_DIMM_A_N(),
   
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
   .cl_RST_DIMM_B_N(),

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
   .cl_RST_DIMM_D_N(),

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   .cl_sh_ddr_awid     (tie_zero_id),
   .cl_sh_ddr_awaddr   (tie_zero_addr),
   .cl_sh_ddr_awlen    (tie_zero_len),
   .cl_sh_ddr_awvalid  (tie_zero),
   .sh_cl_ddr_awready  (),

   .cl_sh_ddr_wid      (tie_zero_id),
   .cl_sh_ddr_wdata    (tie_zero_data),
   .cl_sh_ddr_wstrb    (tie_zero_strb),
   .cl_sh_ddr_wlast    (3'b0),
   .cl_sh_ddr_wvalid   (3'b0),
   .sh_cl_ddr_wready   (),

   .sh_cl_ddr_bid      (),
   .sh_cl_ddr_bresp    (),
   .sh_cl_ddr_bvalid   (),
   .cl_sh_ddr_bready   (3'b0),

   .cl_sh_ddr_arid     (tie_zero_id),
   .cl_sh_ddr_araddr   (tie_zero_addr),
   .cl_sh_ddr_arlen    (tie_zero_len),
   .cl_sh_ddr_arvalid  (3'b0),
   .sh_cl_ddr_arready  (),

   .sh_cl_ddr_rid      (),
   .sh_cl_ddr_rdata    (),
   .sh_cl_ddr_rresp    (),
   .sh_cl_ddr_rlast    (),
   .sh_cl_ddr_rvalid   (),
   .cl_sh_ddr_rready   (3'b0),

   .sh_cl_ddr_is_ready (),

   .sh_ddr_stat_addr   (tie_zero_stat_addr),
   .sh_ddr_stat_wr     (3'b0), 
   .sh_ddr_stat_rd     (3'b0), 
   .sh_ddr_stat_wdata  (tie_zero_stat_data),
   .ddr_sh_stat_ack    (),
   .ddr_sh_stat_rdata  (),
   .ddr_sh_stat_int    ()
   );

//-------------------------------------------
// Tie-Off Global Signals
//-------------------------------------------
`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  

   assign cl_sh_flr_done        = 1'b0;
   assign cl_sh_id0[31:0]       = 32'h1d50_678A;
   assign cl_sh_id1[31:0]       = 32'h1d51_fedD;
   assign cl_sh_status0[31:0]   = 32'h0000_0000;
   assign cl_sh_status1[31:0]   = `CL_VERSION;

//------------------------------------
// Tie-Off Unused AXI Interfaces
//------------------------------------

   // PCIe Interface from CL to SH
   assign cl_sh_pcim_awid    =   5'b0;
   assign cl_sh_pcim_awaddr  =  64'b0;
   assign cl_sh_pcim_awlen   =   8'b0;
   assign cl_sh_pcim_awuser  =  19'b0;
   assign cl_sh_pcim_awvalid =   1'b0;
                                   
   assign cl_sh_pcim_wdata   = 512'b0;
   assign cl_sh_pcim_wstrb   =  64'b0;
   assign cl_sh_pcim_wlast   =   1'b0;
   assign cl_sh_pcim_wvalid  =   1'b0;
                                    
   assign cl_sh_pcim_bready  =   1'b0;
                                    
   assign cl_sh_pcim_arid    =   5'b0;
   assign cl_sh_pcim_araddr  =  64'b0;
   assign cl_sh_pcim_arlen   =   8'b0;
   assign cl_sh_pcim_aruser  =  19'b0;
   assign cl_sh_pcim_arvalid =   1'b0;
                                    
   assign cl_sh_pcim_rready  =   1'b0;

   // DDRC Interface from CL to SH
   assign ddr_sh_stat_ack[2:0]  =   3'b111; // Needed in order not to hang the interface
   assign ddr_sh_stat_rdata[2]  =  32'b0;
   assign ddr_sh_stat_rdata[1]  =  32'b0;
   assign ddr_sh_stat_rdata[0]  =  32'b0;
   assign ddr_sh_stat_int[2]    =   8'b0;
   assign ddr_sh_stat_int[1]    =   8'b0;
   assign ddr_sh_stat_int[0]    =   8'b0;
                                   
   assign cl_sh_ddr_awid        =   6'b0;
   assign cl_sh_ddr_awaddr      =  64'b0;
   assign cl_sh_ddr_awlen       =   8'b0;
   assign cl_sh_ddr_awvalid     =   1'b0;
                                
   assign cl_sh_ddr_wid         =   6'b0;
   assign cl_sh_ddr_wdata       = 512'b0;
   assign cl_sh_ddr_wstrb       =  64'b0;
   assign cl_sh_ddr_wlast       =   1'b0;
   assign cl_sh_ddr_wvalid      =   1'b0;
                                
   assign cl_sh_ddr_bready      =   1'b0;
                                
   assign cl_sh_ddr_arid        =   6'b0;
   assign cl_sh_ddr_araddr      =  64'b0;
   assign cl_sh_ddr_arlen       =   8'b0;
   assign cl_sh_ddr_arvalid     =   1'b0;
                                
   assign cl_sh_ddr_rready      =   1'b0;

  // Tie-off AXI interfaces to sh_ddr module
  assign tie_zero[2]      = 1'b0;
  assign tie_zero[1]      = 1'b0;
  assign tie_zero[0]      = 1'b0;
                          
  assign tie_zero_id[2]   = 16'b0;
  assign tie_zero_id[1]   = 16'b0;
  assign tie_zero_id[0]   = 16'b0;

  assign tie_zero_addr[2] = 64'b0;
  assign tie_zero_addr[1] = 64'b0;
  assign tie_zero_addr[0] = 64'b0;

  assign tie_zero_len[2]  = 8'b0;
  assign tie_zero_len[1]  = 8'b0;
  assign tie_zero_len[0]  = 8'b0;

  assign tie_zero_data[2] = 512'b0;
  assign tie_zero_data[1] = 512'b0;
  assign tie_zero_data[0] = 512'b0;

  assign tie_zero_strb[2] = 64'b0;
  assign tie_zero_strb[1] = 64'b0;
  assign tie_zero_strb[0] = 64'b0;

//------------------------------------
// Tie-Off HMC Interfaces
//------------------------------------

   assign hmc_iic_scl_o            =  1'b0;
   assign hmc_iic_scl_t            =  1'b0;
   assign hmc_iic_sda_o            =  1'b0;
   assign hmc_iic_sda_t            =  1'b0;

   assign hmc_sh_stat_ack          =  1'b0;
   assign hmc_sh_stat_rdata[31:0]  = 32'b0;

   assign hmc_sh_stat_int[7:0]     =  8'b0;

//------------------------------------
// Tie-Off Aurora Interfaces
//------------------------------------
   assign aurora_sh_stat_ack   =  1'b0;
   assign aurora_sh_stat_rdata = 32'b0;
   assign aurora_sh_stat_int   =  8'b0;

endmodule





