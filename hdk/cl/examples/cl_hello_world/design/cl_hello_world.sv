//---------------------------------------------------------------------------------------
// Amazon FGPA Hardware Development Kit
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
//---------------------------------------------------------------------------------------

module cl_hello_world #(parameter NUM_PCIE=1, parameter NUM_DDR=4, parameter NUM_HMC=4, parameter NUM_GTY = 4) 

(
   `include "cl_ports.vh" // Fixed port definition

);

   `include "cl_common_defines.vh" // CL Defines

// // Value to return for PCIS access to unimplemented register address 
// parameter  UNIMPLEMENTED_REG_VALUE = 32'hdeaddead;

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
// Array Signals to Tie-off AXI interfaces to sh_ddr module
//-------------------------------------------------
  logic         tie_zero[2:0];
  logic [ 15:0] tie_zero_id[2:0];
  logic [ 63:0] tie_zero_addr[2:0];
  logic [  7:0] tie_zero_len[2:0];
  logic [511:0] tie_zero_data[2:0];
  logic [ 63:0] tie_zero_strb[2:0];

//-------------------------------------------------
// Wires
//-------------------------------------------------
  logic        arvalid_q;
  logic [31:0] araddr_q;
  logic [31:0] hello_world_q_byte_swapped;
  logic [15:0] vled_q        = 32'b0;
  logic [31:0] hello_world_q = 32'b0;

//-------------------------------------------------
// ID Values (cl_hello_world_defines.vh)
//-------------------------------------------------
  assign cl_sh_id0[31:0] = `CL_SH_ID0;
  assign cl_sh_id1[31:0] = `CL_SH_ID1;

//-------------------------------------------------
// Reset Synchronization
//-------------------------------------------------
logic pre_sync_rst_n;
logic rst_main_n_sync;

always_ff @(negedge rst_main_n or posedge clk_main_a0)
   if (!rst_main_n)
   begin
      pre_sync_rst_n  <= 0;
      rst_main_n_sync <= 0;
   end
   else
   begin
      pre_sync_rst_n  <= 1;
      rst_main_n_sync <= pre_sync_rst_n;
   end

//-------------------------------------------------
// PCIe OCL AXI-L (SH to CL) Timing Flops
//-------------------------------------------------

  // Write address                                                                                                              
  logic        sh_ocl_awvalid_q;
  logic [31:0] sh_ocl_awaddr_q;
  logic        ocl_sh_awready_q;
                                                                                                                              
  // Write data                                                                                                                
  logic        sh_ocl_wvalid_q;
  logic [31:0] sh_ocl_wdata_q;
  logic [ 3:0] sh_ocl_wstrb_q;
  logic        ocl_sh_wready_q;
                                                                                                                              
  // Write response                                                                                                            
  logic        ocl_sh_bvalid_q;
  logic [ 1:0] ocl_sh_bresp_q;
  logic        sh_ocl_bready_q;
                                                                                                                              
  // Read address                                                                                                              
  logic        sh_ocl_arvalid_q;
  logic [31:0] sh_ocl_araddr_q;
  logic        ocl_sh_arready_q;
                                                                                                                              
  // Read data/response                                                                                                        
  logic        ocl_sh_rvalid_q;
  logic [31:0] ocl_sh_rdata_q;
  logic [ 1:0] ocl_sh_rresp_q;
  logic        sh_ocl_rready_q;

  axi4_flop_fifo #(.IN_FIFO(1), .ADDR_WIDTH(32), .DATA_WIDTH(32), .ID_WIDTH(1), .A_USER_WIDTH(1), .FIFO_DEPTH(3)) AXIL_OCL_REG_SLC (
   .aclk          (clk_main_a0),
   .aresetn       (rst_main_n_sync),
   .sync_rst_n    (rst_main_n_sync),
   .s_axi_awid    (1'b0),
   .s_axi_awaddr  (sh_ocl_awaddr),
   .s_axi_awlen   (8'h00),
   .s_axi_awvalid (sh_ocl_awvalid),
   .s_axi_awuser  (1'b0),
   .s_axi_awready (ocl_sh_awready),
   .s_axi_wdata   (sh_ocl_wdata),
   .s_axi_wstrb   (sh_ocl_wstrb),
   .s_axi_wlast   (1'b0),
   .s_axi_wuser   (1'b0),
   .s_axi_wvalid  (sh_ocl_wvalid),
   .s_axi_wready  (ocl_sh_wready),
   .s_axi_bid     (),
   .s_axi_bresp   (ocl_sh_bresp),
   .s_axi_bvalid  (ocl_sh_bvalid),
   .s_axi_buser   (),
   .s_axi_bready  (sh_ocl_bready),
   .s_axi_arid    (1'h0),
   .s_axi_araddr  (sh_ocl_araddr),
   .s_axi_arlen   (8'h0),
   .s_axi_arvalid (sh_ocl_arvalid),
   .s_axi_aruser  (1'd0),
   .s_axi_arready (ocl_sh_arready),
   .s_axi_rid     (),
   .s_axi_rdata   (ocl_sh_rdata),
   .s_axi_rresp   (ocl_sh_rresp),
   .s_axi_rlast   (),
   .s_axi_ruser   (),
   .s_axi_rvalid  (ocl_sh_rvalid),
   .s_axi_rready  (sh_ocl_rready),
   .m_axi_awid    (),
   .m_axi_awaddr  (sh_ocl_awaddr_q),
   .m_axi_awlen   (),
   .m_axi_awvalid (sh_ocl_awvalid_q),
   .m_axi_awuser  (),
   .m_axi_awready (ocl_sh_awready_q),
   .m_axi_wdata   (sh_ocl_wdata_q),
   .m_axi_wstrb   (sh_ocl_wstrb_q),
   .m_axi_wvalid  (sh_ocl_wvalid_q),
   .m_axi_wlast   (),
   .m_axi_wuser   (),
   .m_axi_wready  (ocl_sh_wready_q),
   .m_axi_bresp   (ocl_sh_bresp_q),
   .m_axi_bvalid  (ocl_sh_bvalid_q),
   .m_axi_bid     (),
   .m_axi_buser   (1'b0),
   .m_axi_bready  (sh_ocl_bready_q),
   .m_axi_arid    (),
   .m_axi_araddr  (sh_ocl_araddr_q),
   .m_axi_arlen   (),
   .m_axi_aruser  (),
   .m_axi_arvalid (sh_ocl_arvalid_q),
   .m_axi_arready (ocl_sh_arready_q),
   .m_axi_rid     (),
   .m_axi_rdata   (ocl_sh_rdata_q),
   .m_axi_rresp   (ocl_sh_rresp_q),
   .m_axi_rlast   (),
   .m_axi_ruser   (1'b0),
   .m_axi_rvalid  (ocl_sh_rvalid_q),
   .m_axi_rready  (sh_ocl_rready_q)
  );

//-------------------------------------------------
// PCIe OCL AXI-L Slave Accesses (accesses from PCIe)
//-------------------------------------------------
// Only supports single-beat accesses.

   logic        awvalid;
   logic [31:0] awaddr;
   logic        wvalid;
   logic [31:0] wdata;
   logic [3:0]  wstrb;
   logic        bready;
   logic        arvalid;
   logic [31:0] araddr;
   logic        rready;

   logic        awready;
   logic        wready;
   logic        bvalid;
   logic [1:0]  bresp;
   logic        arready;
   logic        rvalid;
   logic [31:0] rdata;
   logic [1:0]  rresp;

   // Inputs
   assign awvalid         = sh_ocl_awvalid_q;
   assign awaddr[31:0]    = sh_ocl_awaddr_q;
   assign wvalid          = sh_ocl_wvalid_q;
   assign wdata[31:0]     = sh_ocl_wdata_q;
   assign wstrb[3:0]      = sh_ocl_wstrb_q;
   assign bready          = sh_ocl_bready_q;
   assign arvalid         = sh_ocl_arvalid_q;
   assign araddr[31:0]    = sh_ocl_araddr_q;
   assign rready          = sh_ocl_rready_q;

   // Outputs
   assign ocl_sh_awready_q = awready;
   assign ocl_sh_wready_q  = wready;
   assign ocl_sh_bvalid_q  = bvalid;
   assign ocl_sh_bresp_q   = bresp[1:0];
   assign ocl_sh_arready_q = arready;
   assign ocl_sh_rvalid_q  = rvalid;
   assign ocl_sh_rdata_q   = rdata;
   assign ocl_sh_rresp_q   = rresp[1:0];

// Write Request
logic        wr_active;
logic [31:0] wr_addr;

always_ff @(posedge clk_main_a0)
  if (!rst_main_n_sync) begin
     wr_active <= 0;
     wr_addr   <= 0;
  end
  else begin
     wr_active <=  wr_active && bvalid  && bready ? 1'b0     :
                  ~wr_active && awvalid           ? 1'b1     :
                                                    wr_active;
     wr_addr <= awvalid && ~wr_active ? awaddr : wr_addr     ;
  end

assign awready = ~wr_active;
assign wready  =  wr_active && wvalid;

// Write Response
always_ff @(posedge clk_main_a0)
  if (!rst_main_n_sync) 
    bvalid <= 0;
  else
    bvalid <=  bvalid &&  bready           ? 1'b0  : 
                         ~bvalid && wready ? 1'b1  :
                                             bvalid;
assign bresp = 0;

// Read Request
always_ff @(posedge clk_main_a0)
   if (!rst_main_n_sync) begin
      arvalid_q <= 0;
      araddr_q  <= 0;
   end
   else begin
      arvalid_q <= arvalid;
      araddr_q  <= arvalid ? araddr : araddr_q;
   end

assign arready = !arvalid_q && !rvalid;

// Read Response
always_ff @(posedge clk_main_a0)
   if (!rst_main_n_sync)
   begin
      rvalid <= 0;
      rdata  <= 0;
      rresp  <= 0;
   end
   else if (rvalid && rready)
   begin
      rvalid <= 0;
      rdata  <= 0;
      rresp  <= 0;
   end
   else if (arvalid_q) 
   begin
      rvalid <= 1;
      rdata  <= (araddr_q == `HELLO_WORLD_REG_ADDR) ? hello_world_q_byte_swapped[31:0]:
                (araddr_q == `VLED_REG_ADDR       ) ? {16'b0,vled_q[15:0]            }:
                                                      `UNIMPLEMENTED_REG_VALUE        ;
      rresp  <= 0;
   end

//-------------------------------------------------
// Hello World Register
//-------------------------------------------------
// The register resides at offset 0x00. When read it
// returns the byte-flipped value.

always_ff @(posedge clk_main_a0)
   if (!rst_main_n_sync) begin                    // Reset
      hello_world_q[31:0] <= 32'h0000_0000;
   end
   else if (wready & (wr_addr == `HELLO_WORLD_REG_ADDR)) begin  // Cfg Write to offset 0x00
      hello_world_q[31:0] <= wdata[31:0];
   end
   else begin                                // Hold Value
      hello_world_q[31:0] <= hello_world_q[31:0];
   end

assign hello_world_q_byte_swapped[31:0] = {hello_world_q[7:0],   hello_world_q[15:8],
                                           hello_world_q[23:16], hello_world_q[31:24]};

//-------------------------------------------------
// Virtual LED Register
//-------------------------------------------------
// The Virtual LED register resides at offset 0x04.

// The register contains 16 read-only bits corresponding to 16 LED's.
// For this example, the virtual LED register shadows the hello_world
// register.

always_ff @(posedge clk_main_a0)
   if (!rst_main_n_sync) begin                    // Reset
      vled_q[15:0] <= 16'h0000;
   end
   else begin
      vled_q[15:0] <= hello_world_q[15:0];
   end

// The Virtual LED outputs will be masked with the Virtual DIP switches.
assign cl_sh_status_vled[15:0] = vled_q[15:0] & sh_cl_status_vdip[15:0];

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
   .clk(clk_main_a0),
   .rst_n(rst_main_n_sync),
   .stat_clk(clk_main_a0),
   .stat_rst_n(clk_main_a0),

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

   .sh_ddr_stat_addr0   (8'h00),
   .sh_ddr_stat_wr0     (1'b0), 
   .sh_ddr_stat_rd0     (1'b0), 
   .sh_ddr_stat_wdata0  (32'b0),
   .ddr_sh_stat_ack0   (),
   .ddr_sh_stat_rdata0 (),
   .ddr_sh_stat_int0   (),
   .sh_ddr_stat_addr1   (8'h00),
   .sh_ddr_stat_wr1     (1'b0), 
   .sh_ddr_stat_rd1     (1'b0), 
   .sh_ddr_stat_wdata1  (32'b0),
   .ddr_sh_stat_ack1   (),
   .ddr_sh_stat_rdata1 (),
   .ddr_sh_stat_int1   (),
   .sh_ddr_stat_addr2   (8'h00),
   .sh_ddr_stat_wr2     (1'b0), 
   .sh_ddr_stat_rd2     (1'b0), 
   .sh_ddr_stat_wdata2  (32'b0),
   .ddr_sh_stat_ack2   (),
   .ddr_sh_stat_rdata2 (),
   .ddr_sh_stat_int2   ()
   );

//-------------------------------------------
// Tie-Off Global Signals
//-------------------------------------------
`ifndef CL_VERSION
   `define CL_VERSION 32'hee_ee_ee_00
`endif  

  assign cl_sh_flr_done      =   1'b0;
  assign cl_sh_status0[31:0] =  32'h0000_0FF0;
  assign cl_sh_status1[31:0] = `CL_VERSION;

//------------------------------------
// Tie-Off Unused Interfaces
//------------------------------------

  // PCIe Master (pcim) Interface from CL to SH
  assign cl_sh_pcim_awid             =  16'b0;
  assign cl_sh_pcim_awaddr           =  64'b0;
  assign cl_sh_pcim_awlen            =   8'b0;
  assign cl_sh_pcim_awsize           =   3'h0;
  assign cl_sh_pcim_awuser           =  19'b0;
  assign cl_sh_pcim_awvalid          =   1'b0;

  assign cl_sh_pcim_wdata            = 512'b0;
  assign cl_sh_pcim_wstrb            =  64'b0;
  assign cl_sh_pcim_wlast            =   1'b0;
  assign cl_sh_pcim_wvalid           =   1'b0;

  assign cl_sh_pcim_bready           =   1'b0;

  assign cl_sh_pcim_arid             =  16'b0;
  assign cl_sh_pcim_araddr           =  64'b0;
  assign cl_sh_pcim_arlen            =   8'b0;
  assign cl_sh_pcim_arsize           =   3'h0;
  assign cl_sh_pcim_aruser           =  19'b0;
  assign cl_sh_pcim_arvalid          =   1'b0;

  assign cl_sh_pcim_rready           =   1'b0;

  // PCIe Slave (pcis) Interface from SH to CL
  assign cl_sh_dma_pcis_awready      =   1'b0;

  assign cl_sh_dma_pcis_wready       =   1'b0;

  assign cl_sh_dma_pcis_bid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_bresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_bvalid       =   1'b0;

  assign cl_sh_dma_pcis_arready      =   1'b0;

  assign cl_sh_dma_pcis_rid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_rdata[511:0] = 512'b0;
  assign cl_sh_dma_pcis_rresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_rlast        =   1'b0;
  assign cl_sh_dma_pcis_rvalid       =   1'b0;

  // PCIe Slave (sda) Interface from SH to CL
  assign cl_sda_awready              =   1'b0;

  assign cl_sda_wready               =   1'b0;

  assign cl_sda_bvalid               =   1'b0;
  assign cl_sda_bresp[1:0]           =   2'b0;

  assign cl_sda_arready              =   1'b0;

  assign cl_sda_rvalid               =   1'b0;
  assign cl_sda_rdata[31:0]          =  32'b0;
  assign cl_sda_rresp[1:0]           =   2'b0;

  // PCIe Slave (bar1) Interface from SH to CL
  assign bar1_sh_awready             =   1'b0;

  assign bar1_sh_wready              =   1'b0;

  assign bar1_sh_bvalid              =   1'b0;
  assign bar1_sh_bresp[1:0]          =   2'b0;

  assign bar1_sh_arready             =   1'b0;

  assign bar1_sh_rvalid              =   1'b0;
  assign bar1_sh_rdata[31:0]         =  32'b0;
  assign bar1_sh_rresp[1:0]          =   2'b0;

  // DDRC Interface from CL to SH
  assign ddr_sh_stat_ack0   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata0 =  32'b0;
  assign ddr_sh_stat_int0   =   8'b0;

  assign ddr_sh_stat_ack1   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata1 =  32'b0;
  assign ddr_sh_stat_int1   =   8'b0;

  assign ddr_sh_stat_ack2   =   1'b1; // Needed in order not to hang the interface
  assign ddr_sh_stat_rdata2 =  32'b0;
  assign ddr_sh_stat_int2   =   8'b0;

  assign cl_sh_ddr_awid     =  16'b0;
  assign cl_sh_ddr_awaddr   =  64'b0;
  assign cl_sh_ddr_awlen    =   8'b0;
  assign cl_sh_ddr_awsize   =   3'b0;
  assign cl_sh_ddr_awvalid  =   1'b0;

  assign cl_sh_ddr_wid      =  16'b0;
  assign cl_sh_ddr_wdata    = 512'b0;
  assign cl_sh_ddr_wstrb    =  64'b0;
  assign cl_sh_ddr_wlast    =   1'b0;
  assign cl_sh_ddr_wvalid   =   1'b0;

  assign cl_sh_ddr_bready   =   1'b0;

  assign cl_sh_ddr_arid     =  16'b0;
  assign cl_sh_ddr_araddr   =  64'b0;
  assign cl_sh_ddr_arlen    =   8'b0;
  assign cl_sh_ddr_arsize   =   3'b0;
  assign cl_sh_ddr_arvalid  =   1'b0;

  assign cl_sh_ddr_rready   =   1'b0;

  // Tie-off AXI interfaces to sh_ddr module
  assign tie_zero[2]        =   1'b0;
  assign tie_zero[1]        =   1'b0;
  assign tie_zero[0]        =   1'b0;

  assign tie_zero_id[2]     =  16'b0;
  assign tie_zero_id[1]     =  16'b0;
  assign tie_zero_id[0]     =  16'b0;

  assign tie_zero_addr[2]   =  64'b0;
  assign tie_zero_addr[1]   =  64'b0;
  assign tie_zero_addr[0]   =  64'b0;

  assign tie_zero_len[2]    =   8'b0;
  assign tie_zero_len[1]    =   8'b0;
  assign tie_zero_len[0]    =   8'b0;

  assign tie_zero_data[2]   = 512'b0;
  assign tie_zero_data[1]   = 512'b0;
  assign tie_zero_data[0]   = 512'b0;

  assign tie_zero_strb[2]   =  64'b0;
  assign tie_zero_strb[1]   =  64'b0;
  assign tie_zero_strb[0]   =  64'b0;

//------------------------------------
// Tie-Off Interrupts
//------------------------------------
  assign cl_sh_apppf_irq_req = 16'b0;

//------------------------------------
// Tie-Off HMC Interfaces
//------------------------------------
  assign hmc_iic_scl_o           =  1'b0;
  assign hmc_iic_scl_t           =  1'b0;
  assign hmc_iic_sda_o           =  1'b0;
  assign hmc_iic_sda_t           =  1'b0;

  assign hmc_sh_stat_ack         =  1'b0;
  assign hmc_sh_stat_rdata[31:0] = 32'b0;

  assign hmc_sh_stat_int[7:0]    =  8'b0;

//------------------------------------
// Tie-Off Aurora Interfaces
//------------------------------------
  assign aurora_sh_stat_ack   =  1'b0;
  assign aurora_sh_stat_rdata = 32'b0;
  assign aurora_sh_stat_int   =  8'b0;

endmodule





