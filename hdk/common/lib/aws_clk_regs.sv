///////////////////////////////////////////////////////////////////////////////////
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
///////////////////////////////////////////////////////////////////////////////////
// Module
// -------
// AWS_CLK_REGS
//
// Description
// -----------
// * Houses all the Control/Status Regs for AWS_CLK_GEN design
//
///////////////////////////////////////////////////////////////////////////////////

module aws_clk_regs
  #(
    parameter CLK_GRP_A_EN = 1,
    parameter CLK_GRP_B_EN = 1,
    parameter CLK_GRP_C_EN = 1,
    parameter CLK_HBM_EN   = 1,
    parameter MAX_NUM_CLKS = 10  //Max number of clocks supported
    )
   (
    input  logic         i_clk,
    input  logic         i_rst_n,

    input  logic [31:0]  s_axil_awaddr,
    input  logic         s_axil_awvalid,
    output logic         s_axil_awready,
    input  logic [31:0]  s_axil_wdata,
    input  logic [3:0]   s_axil_wstrb,
    input  logic         s_axil_wvalid,
    output logic         s_axil_wready,
    output logic [1:0]   s_axil_bresp,
    output logic         s_axil_bvalid,
    input  logic         s_axil_bready,
    input  logic [31:0]  s_axil_araddr,
    input  logic         s_axil_arvalid,
    output logic         s_axil_arready,
    output logic [31:0]  s_axil_rdata,
    output logic [1:0]   s_axil_rresp,
    output logic         s_axil_rvalid,
    input  logic         s_axil_rready,

    input  logic         i_mmcm_a_lock,
    input  logic         i_mmcm_b_lock,
    input  logic         i_mmcm_c_lock,
    input  logic         i_mmcm_hbm_lock,

    output logic         o_glbl_rst         = '0,
    output logic         o_cl_rst_hbm_axi_n = '0,
    output logic         o_cl_rst_hbm_ref_n = '0,
    output logic         o_cl_rst_c1_n      = '0,
    output logic         o_cl_rst_c0_n      = '0,
    output logic         o_cl_rst_b1_n      = '0,
    output logic         o_cl_rst_b0_n      = '0,
    output logic         o_cl_rst_a3_n      = '0,
    output logic         o_cl_rst_a2_n      = '0,
    output logic         o_cl_rst_a1_n      = '0,
    output logic         o_cl_rst_main_n    = '0
    );

   //===================================================================
   // AXI-L to CFG convert
   //===================================================================
   axil_bus_t s_axil_bus();
   cfg_bus_t  cfg_bus();

   always_comb begin //{
      s_axil_bus.awaddr   = s_axil_awaddr;
      s_axil_bus.awvalid  = s_axil_awvalid;
      s_axil_awready      = s_axil_bus.awready;

      s_axil_bus.wdata    = s_axil_wdata;
      s_axil_bus.wstrb    = s_axil_wstrb;
      s_axil_bus.wvalid   = s_axil_wvalid;
      s_axil_wready       = s_axil_bus.wready;

      s_axil_bresp        = s_axil_bus.bresp;
      s_axil_bvalid       = s_axil_bus.bvalid;
      s_axil_bus.bready   = s_axil_bready;

      s_axil_bus.araddr   = s_axil_araddr;
      s_axil_bus.arvalid  = s_axil_arvalid;
      s_axil_arready      = s_axil_bus.arready;

      s_axil_rdata        = s_axil_bus.rdata;
      s_axil_rresp        = s_axil_bus.rresp;
      s_axil_rvalid       = s_axil_bus.rvalid;
      s_axil_bus.rready   = s_axil_rready;
   end //}

   // AXIL to CFG convertor
   axil_to_cfg_cnv
     #(
       .ADDR_WIDTH (32),
       .DATA_WIDTH (32)
       )
   AXIL_TO_CFG_CNV_I
     (
      .clk         (i_clk      ),
      .rst_n       (i_rst_n    ),
      .s_axil_bus  (s_axil_bus ),
      .m_cfg_bus   (cfg_bus    ),
      .o_fsm_busy  (           )
      );

   //===================================================================
   // CFG WR/RD reqs
   //===================================================================
   logic [7:0]  cfg_addr_q = '0;
   logic        cfg_wr_q = '0;
   logic        cfg_rd_q = '0;
   logic        cfg_wr_pulse_q = '0;
   logic        cfg_rd_pulse_q = '0;
   logic [31:0] cfg_rdata_q = '0;
   logic [31:0] cfg_wdata_q = '0;

   always_ff @(posedge i_clk)
     if (!i_rst_n) begin //{
        cfg_wr_q <= '0;
        cfg_rd_q <= '0;
     end //}
     else begin //{
        cfg_wr_q       <= cfg_bus.wr;
        cfg_rd_q       <= cfg_bus.rd;
        cfg_addr_q     <= cfg_bus.addr[0+:$bits(cfg_addr_q)];
        cfg_wdata_q    <= cfg_bus.wdata;
        cfg_wr_pulse_q <= ~cfg_wr_q & cfg_bus.wr;
        cfg_rd_pulse_q <= ~cfg_rd_q & cfg_bus.rd;
     end //}

   always_ff @(posedge i_clk)
     if (!i_rst_n)
       cfg_bus.ack <= '0;
     else
       cfg_bus.ack <= cfg_wr_pulse_q | cfg_rd_pulse_q;

   assign cfg_bus.rdata = cfg_rdata_q;

   //===================================================================
   // CSRs
   //===================================================================
   localparam ID_REG             = 8'h00;
   localparam VER_REG            = 8'h04;
   localparam BUILD_REG          = 8'h08;
   localparam CLKS_AVAIL_REG     = 8'h0C;
   localparam G_RST_REG          = 8'h10;
   localparam SYS_RST_REG        = 8'h14;
   localparam DIS_RST_MAIN_REG   = 8'h18;
   localparam MMCM_LOCK_REG      = 8'h20;
   localparam MMCM_LOCK_ERR_REG  = 8'h24;

   logic [31:0] id_reg            = '0;
   logic [31:0] ver_reg           = '0;
   logic [31:0] build_reg         = '0;
   logic [31:0] clks_avail_reg    = '0;
   logic [31:0] g_rst_reg         = '0;
   logic [31:0] sys_rst_reg       = 32'hFFFF_FFFE;
   logic        dis_rst_main_reg  = '0;
   logic [31:0] mmcm_lock_reg     = '0;
   logic [31:0] mmcm_lock_err_reg = '0;

   //===================================================================
   // Read Datapath
   //===================================================================
   always_ff @(posedge i_clk)
     unique case (cfg_addr_q) //{
       ID_REG            : cfg_rdata_q <= id_reg;
       VER_REG           : cfg_rdata_q <= ver_reg;
       BUILD_REG         : cfg_rdata_q <= build_reg;
       CLKS_AVAIL_REG    : cfg_rdata_q <= clks_avail_reg;
       G_RST_REG         : cfg_rdata_q <= g_rst_reg;
       SYS_RST_REG       : cfg_rdata_q <= sys_rst_reg;
       DIS_RST_MAIN_REG  : cfg_rdata_q <= 32'(dis_rst_main_reg);
       MMCM_LOCK_REG     : cfg_rdata_q <= mmcm_lock_reg;
       MMCM_LOCK_ERR_REG : cfg_rdata_q <= mmcm_lock_err_reg;
       default           : cfg_rdata_q <= 32'hBAAD_DEC0;
     endcase // unique case (cfg_addr_q) }

   always_comb begin //{
      id_reg         = 32'h9048_1D0F;   // AWS unique ID
      ver_reg        = 32'h02_01_00_00; // Arch, Major, Minor, Maintenance version
      build_reg      = 32'h09_23_22_23;
      clks_avail_reg = { 23'd0, //       Reserved
                         1'(CLK_HBM_EN),    // 1 = clk_hbm_axi  available | 0 = clock unavilable
                         1'(CLK_GRP_C_EN),  // 1 = clk_extra_c1 available | 0 = clock unavilable
                         1'(CLK_GRP_C_EN),  // 1 = clk_extra_c0 available | 0 = clock unavilable
                         1'(CLK_GRP_B_EN),  // 1 = clk_extra_b1 available | 0 = clock unavilable
                         1'(CLK_GRP_B_EN),  // 1 = clk_extra_b0 available | 0 = clock unavilable
                         1'(CLK_GRP_A_EN),  // 1 = clk_extra_a3 available | 0 = clock unavilable
                         1'(CLK_GRP_A_EN),  // 1 = clk_extra_a2 available | 0 = clock unavilable
                         1'(CLK_GRP_A_EN),  // 1 = clk_extra_a1 available | 0 = clock unavilable
                         1'b1 };            // 1 = clk_main_a0  available | 0 = clock unavilable
   end //}

   //===================================================================
   // Writes
   //===================================================================
   always_ff @(posedge i_clk) begin //{
      if ((cfg_addr_q == G_RST_REG) && cfg_wr_pulse_q)
       g_rst_reg <= cfg_wdata_q;

      if ((cfg_addr_q == SYS_RST_REG) && cfg_wr_pulse_q)
        sys_rst_reg <= cfg_wdata_q;

      if ((cfg_addr_q == DIS_RST_MAIN_REG) && cfg_wr_pulse_q)
        dis_rst_main_reg <= cfg_wdata_q[0];

      if ((cfg_addr_q == MMCM_LOCK_ERR_REG) && cfg_wr_pulse_q)
        mmcm_lock_err_reg <= mmcm_lock_err_reg & ~cfg_wdata_q; // Write 1 to Clear
   end //}

   //===================================================================
   // Reset Outputs
   //===================================================================
   always_ff @(posedge i_clk)
     o_glbl_rst <= (g_rst_reg == '1);

   logic [31:0] rst_out_n = '0;
   //===================================================================
   // Reset truth table
   // -----------------
   // o_glbl_rst | sys_rst_reg | dis_rst_main_reg | i_rst_n | Output
   // ---------------------------------------------------------------
   //     1      |      X      |        X         |    X    |  0
   //     0      |      1      |        X         |    X    |  0
   //     0      |      0      |        0         |    0    |  0
   //     0      |      0      |        0         |    1    |  1
   //     0      |      0      |        1         |    X    |  1
   //     0      |      0      |        1         |    X    |  1
   //===================================================================
   always_ff @(posedge i_clk)
     for (int gg = 0; gg < MAX_NUM_CLKS; gg++)
       rst_out_n[gg] <= ~o_glbl_rst & ~sys_rst_reg[gg] & (dis_rst_main_reg | i_rst_n);

   always_comb begin : RST_OUT_I //{
      o_cl_rst_hbm_axi_n = rst_out_n[9];
      o_cl_rst_hbm_ref_n = rst_out_n[8];
      o_cl_rst_c1_n      = rst_out_n[7];
      o_cl_rst_c0_n      = rst_out_n[6];
      o_cl_rst_b1_n      = rst_out_n[5];
      o_cl_rst_b0_n      = rst_out_n[4];
      o_cl_rst_a3_n      = rst_out_n[3];
      o_cl_rst_a2_n      = rst_out_n[2];
      o_cl_rst_a1_n      = rst_out_n[1];
      o_cl_rst_main_n    = rst_out_n[0];
   end : RST_OUT_I //}

   //==========================================================================
   // MMCM Lock
   //==========================================================================
   logic [3:0] mmcm_lock_in;
   logic [3:0] mmcm_lock_syncd;

   assign mmcm_lock_in = {i_mmcm_hbm_lock, i_mmcm_c_lock, i_mmcm_b_lock, i_mmcm_a_lock};
   generate //{
      for (genvar jj = 0; jj < $bits(mmcm_lock_in); jj++) begin : MMCM_LOCK_SYNC_I //{
         xpm_cdc_single
                       #(
                         .DEST_SYNC_FF       (2),
                         .INIT_SYNC_FF       (0),
                         .SIM_ASSERT_CHK     (0),
                         .SRC_INPUT_REG      (0)
                         )
         CDC_XPM_SINGLE
                       (
                        .src_clk            (i_clk               ),
                        .src_in             (mmcm_lock_in[jj]    ),
                        .dest_clk           (i_clk               ),
                        .dest_out           (mmcm_lock_syncd[jj] )
                        );
      end : MMCM_LOCK_SYNC_I//}
   endgenerate //}

   //
   // MMCM_LOCK_REG
   //
   always_comb begin //{
      mmcm_lock_reg = '0;
      mmcm_lock_reg[0] = mmcm_lock_syncd[0]; // MMCM-A locked
      mmcm_lock_reg[4] = mmcm_lock_syncd[1]; // MMCM-B locked
      mmcm_lock_reg[6] = mmcm_lock_syncd[2]; // MMCM-C locked
      mmcm_lock_reg[8] = mmcm_lock_syncd[3]; // MMCM-HBM locked
   end //}

endmodule // aws_clk_regs
