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
// AWS_CLK_GEN
//
// Description
// -----------
// * Generate clocks and resets to the CL design
//
///////////////////////////////////////////////////////////////////////////////////

module aws_clk_gen
  #(
    parameter CLK_GRP_A_EN = 1,
    parameter CLK_GRP_B_EN = 1,
    parameter CLK_GRP_C_EN = 1,
    parameter CLK_HBM_EN   = 1
    )
   (
    input  logic         i_clk_main_a0, // clk_main_a0 from AWS Shell
    input  logic         i_rst_main_n,  // rst_main_n from AWS Shell

    input  logic         i_clk_hbm_ref, // clk_hbm_ref 100MHz HBM reference clock from AWS Shell

    // AXIL Control interface in i_clk_main_a0 domain
    input  logic [31:0]  s_axil_ctrl_awaddr,
    input  logic         s_axil_ctrl_awvalid,
    output logic         s_axil_ctrl_awready,
    input  logic [31:0]  s_axil_ctrl_wdata,
    input  logic [3:0]   s_axil_ctrl_wstrb,
    input  logic         s_axil_ctrl_wvalid,
    output logic         s_axil_ctrl_wready,
    output logic [1:0]   s_axil_ctrl_bresp,
    output logic         s_axil_ctrl_bvalid,
    input  logic         s_axil_ctrl_bready,
    input  logic [31:0]  s_axil_ctrl_araddr,
    input  logic         s_axil_ctrl_arvalid,
    output logic         s_axil_ctrl_arready,
    output logic [31:0]  s_axil_ctrl_rdata,
    output logic [1:0]   s_axil_ctrl_rresp,
    output logic         s_axil_ctrl_rvalid,
    input  logic         s_axil_ctrl_rready,

    // Pass through clocks
    output logic         o_clk_hbm_ref, // same as i_clk_hbm_ref 100 MHz
    output logic         o_clk_main_a0, // same as i_clk_main_a0

    // Clock group A:
    output logic         o_clk_extra_a1,
    output logic         o_clk_extra_a2,
    output logic         o_clk_extra_a3,

    // Clock group B:
    output logic         o_clk_extra_b0, // This also ap_clk0 for Vitis
    output logic         o_clk_extra_b1,

    // Clock group C:
    output logic         o_clk_extra_c0, // This also ap_clk1 for Vitis
    output logic         o_clk_extra_c1,

    // HBM Axi clock:
    output logic         o_clk_hbm_axi, // HBM AXI clock (max 450 MHz)

    // Resets
    output logic         o_cl_rst_hbm_axi_n , // reset sync'd to o_clk_hbm_axi
    output logic         o_cl_rst_hbm_ref_n , // reset sync'd to o_clk_hbm_ref
    output logic         o_cl_rst_c1_n      , // reset sync'd to o_clk_extra_c1
    output logic         o_cl_rst_c0_n      , // reset sync'd to o_clk_extra_c0
    output logic         o_cl_rst_b1_n      , // reset sync'd to o_clk_extra_b1
    output logic         o_cl_rst_b0_n      , // reset sync'd to o_clk_extra_b0
    output logic         o_cl_rst_a3_n      , // reset sync'd to o_clk_extra_a3
    output logic         o_cl_rst_a2_n      , // reset sync'd to o_clk_extra_a2
    output logic         o_cl_rst_a1_n      , // reset sync'd to o_clk_extra_a1
    output logic         o_cl_rst_main_n      // CL(user) design should use this as main reset. Sync'd to clk_main_a0.
    );

   //===================================================================
   // local signals/params
   //===================================================================
   localparam            MAX_NUM_CLKS = 10;

   logic                 rst_main_n = '0;
   logic                 rst_hbm_n;
   logic [31:0]          hclk_axil_awaddr;
   logic                 hclk_axil_awvalid;
   logic                 hclk_axil_awready;
   logic [31:0]          hclk_axil_wdata;
   logic [3:0]           hclk_axil_wstrb;
   logic                 hclk_axil_wvalid;
   logic                 hclk_axil_wready;
   logic [1:0]           hclk_axil_bresp;
   logic                 hclk_axil_bvalid;
   logic                 hclk_axil_bready;
   logic [31:0]          hclk_axil_araddr;
   logic                 hclk_axil_arvalid;
   logic                 hclk_axil_arready;
   logic [31:0]          hclk_axil_rdata;
   logic [1:0]           hclk_axil_rresp;
   logic                 hclk_axil_rvalid;
   logic                 hclk_axil_rready;

   // AXIL Structure
   typedef struct        {
      logic [31:0]       awaddr;
      logic              awvalid;
      logic              awready;
      logic [31:0]       wdata;
      logic [3:0]        wstrb;
      logic              wvalid;
      logic              wready;
      logic [1:0]        bresp;
      logic              bvalid;
      logic              bready;
      logic [31:0]       araddr;
      logic              arvalid;
      logic              arready;
      logic [31:0]       rdata;
      logic [1:0]        rresp;
      logic              rvalid;
      logic              rready;
   } st_axil_cctrl;

   st_axil_cctrl base_a_axil;
   st_axil_cctrl base_b_axil;
   st_axil_cctrl base_c_axil;
   st_axil_cctrl base_hbm_axil;
   st_axil_cctrl base_reg_axil;

   logic                    glbl_rst;
   logic [MAX_NUM_CLKS-1:0] cl_rst_n;

   //===================================================================
   // Rest sync
   //===================================================================
   always_ff @(posedge i_clk_main_a0)
     rst_main_n <= i_rst_main_n;

   xpm_cdc_async_rst
     #(
       .DEST_SYNC_FF     (4),
       .INIT_SYNC_FF     (0),
       .RST_ACTIVE_HIGH  (0)
       )
   CDC_ASYNC_HBM_RST_I
     (
      .src_arst         (rst_main_n    ),
      .dest_clk         (i_clk_hbm_ref ),
      .dest_arst        (rst_hbm_n     )
      );

   //===================================================================
   // Convert AXIL interface from clk_main_a0 to i_clk_hbm_ref domain
   //===================================================================
   cl_axi_clock_converter_light AXIL_CLK_CNV_I
     (
      .s_axi_aclk        (i_clk_main_a0           ),
      .s_axi_aresetn     (rst_main_n              ),
      .s_axi_awaddr      (s_axil_ctrl_awaddr      ),
      .s_axi_awprot      (3'd0                    ),
      .s_axi_awvalid     (s_axil_ctrl_awvalid     ),
      .s_axi_awready     (s_axil_ctrl_awready     ),
      .s_axi_wdata       (s_axil_ctrl_wdata       ),
      .s_axi_wstrb       (s_axil_ctrl_wstrb       ),
      .s_axi_wvalid      (s_axil_ctrl_wvalid      ),
      .s_axi_wready      (s_axil_ctrl_wready      ),
      .s_axi_bresp       (s_axil_ctrl_bresp       ),
      .s_axi_bvalid      (s_axil_ctrl_bvalid      ),
      .s_axi_bready      (s_axil_ctrl_bready      ),
      .s_axi_araddr      (s_axil_ctrl_araddr      ),
      .s_axi_arprot      (3'd0                    ),
      .s_axi_arvalid     (s_axil_ctrl_arvalid     ),
      .s_axi_arready     (s_axil_ctrl_arready     ),
      .s_axi_rdata       (s_axil_ctrl_rdata       ),
      .s_axi_rresp       (s_axil_ctrl_rresp       ),
      .s_axi_rvalid      (s_axil_ctrl_rvalid      ),
      .s_axi_rready      (s_axil_ctrl_rready      ),
      .m_axi_aclk        (i_clk_hbm_ref           ),
      .m_axi_aresetn     (rst_hbm_n               ),
      .m_axi_awaddr      (hclk_axil_awaddr        ),
      .m_axi_awprot      (                        ),
      .m_axi_awvalid     (hclk_axil_awvalid       ),
      .m_axi_awready     (hclk_axil_awready       ),
      .m_axi_wdata       (hclk_axil_wdata         ),
      .m_axi_wstrb       (hclk_axil_wstrb         ),
      .m_axi_wvalid      (hclk_axil_wvalid        ),
      .m_axi_wready      (hclk_axil_wready        ),
      .m_axi_bresp       (hclk_axil_bresp         ),
      .m_axi_bvalid      (hclk_axil_bvalid        ),
      .m_axi_bready      (hclk_axil_bready        ),
      .m_axi_araddr      (hclk_axil_araddr        ),
      .m_axi_arprot      (                        ),
      .m_axi_arvalid     (hclk_axil_arvalid       ),
      .m_axi_arready     (hclk_axil_arready       ),
      .m_axi_rdata       (hclk_axil_rdata         ),
      .m_axi_rresp       (hclk_axil_rresp         ),
      .m_axi_rvalid      (hclk_axil_rvalid        ),
      .m_axi_rready      (hclk_axil_rready        )
      );

   //===================================================================
   // AXIL XBAR address range:
   // 0x5_0000 - 0x5_0FFF : BASE_B
   // 0x5_1000 - 0x5_1FFF : BASE_C
   // 0x5_2000 - 0x5_2FFF : BASE_A
   // 0x5_4000 - 0x5_4FFF : BASE_HBM
   // 0x5_8000 - 0x5_8FFF : BASE_REG
   //
   //===================================================================
   cl_clk_axil_xbar AXIL_XBAR_I
     (
      .aclk               (i_clk_hbm_ref          ),
      .aresetn            (rst_hbm_n              ),
      .s_axi_awaddr       (hclk_axil_awaddr       ),
      .s_axi_awprot       (3'd0                   ),
      .s_axi_awvalid      (hclk_axil_awvalid      ),
      .s_axi_awready      (hclk_axil_awready      ),
      .s_axi_wdata        (hclk_axil_wdata        ),
      .s_axi_wstrb        (hclk_axil_wstrb        ),
      .s_axi_wvalid       (hclk_axil_wvalid       ),
      .s_axi_wready       (hclk_axil_wready       ),
      .s_axi_bresp        (hclk_axil_bresp        ),
      .s_axi_bvalid       (hclk_axil_bvalid       ),
      .s_axi_bready       (hclk_axil_bready       ),
      .s_axi_araddr       (hclk_axil_araddr       ),
      .s_axi_arprot       (3'd0                   ),
      .s_axi_arvalid      (hclk_axil_arvalid      ),
      .s_axi_arready      (hclk_axil_arready      ),
      .s_axi_rdata        (hclk_axil_rdata        ),
      .s_axi_rresp        (hclk_axil_rresp        ),
      .s_axi_rvalid       (hclk_axil_rvalid       ),
      .s_axi_rready       (hclk_axil_rready       ),
      .m_axi_awaddr       ({base_reg_axil.awaddr   , base_hbm_axil.awaddr   , base_a_axil.awaddr   , base_c_axil.awaddr   , base_b_axil.awaddr   }),
      .m_axi_awprot       (                                                                                                                       ),
      .m_axi_awvalid      ({base_reg_axil.awvalid  , base_hbm_axil.awvalid  , base_a_axil.awvalid  , base_c_axil.awvalid  , base_b_axil.awvalid  }),
      .m_axi_awready      ({base_reg_axil.awready  , base_hbm_axil.awready  , base_a_axil.awready  , base_c_axil.awready  , base_b_axil.awready  }),
      .m_axi_wdata        ({base_reg_axil.wdata    , base_hbm_axil.wdata    , base_a_axil.wdata    , base_c_axil.wdata    , base_b_axil.wdata    }),
      .m_axi_wstrb        ({base_reg_axil.wstrb    , base_hbm_axil.wstrb    , base_a_axil.wstrb    , base_c_axil.wstrb    , base_b_axil.wstrb    }),
      .m_axi_wvalid       ({base_reg_axil.wvalid   , base_hbm_axil.wvalid   , base_a_axil.wvalid   , base_c_axil.wvalid   , base_b_axil.wvalid   }),
      .m_axi_wready       ({base_reg_axil.wready   , base_hbm_axil.wready   , base_a_axil.wready   , base_c_axil.wready   , base_b_axil.wready   }),
      .m_axi_bresp        ({base_reg_axil.bresp    , base_hbm_axil.bresp    , base_a_axil.bresp    , base_c_axil.bresp    , base_b_axil.bresp    }),
      .m_axi_bvalid       ({base_reg_axil.bvalid   , base_hbm_axil.bvalid   , base_a_axil.bvalid   , base_c_axil.bvalid   , base_b_axil.bvalid   }),
      .m_axi_bready       ({base_reg_axil.bready   , base_hbm_axil.bready   , base_a_axil.bready   , base_c_axil.bready   , base_b_axil.bready   }),
      .m_axi_araddr       ({base_reg_axil.araddr   , base_hbm_axil.araddr   , base_a_axil.araddr   , base_c_axil.araddr   , base_b_axil.araddr   }),
      .m_axi_arprot       (                                                                                                                       ),
      .m_axi_arvalid      ({base_reg_axil.arvalid  , base_hbm_axil.arvalid  , base_a_axil.arvalid  , base_c_axil.arvalid  , base_b_axil.arvalid  }),
      .m_axi_arready      ({base_reg_axil.arready  , base_hbm_axil.arready  , base_a_axil.arready  , base_c_axil.arready  , base_b_axil.arready  }),
      .m_axi_rdata        ({base_reg_axil.rdata    , base_hbm_axil.rdata    , base_a_axil.rdata    , base_c_axil.rdata    , base_b_axil.rdata    }),
      .m_axi_rresp        ({base_reg_axil.rresp    , base_hbm_axil.rresp    , base_a_axil.rresp    , base_c_axil.rresp    , base_b_axil.rresp    }),
      .m_axi_rvalid       ({base_reg_axil.rvalid   , base_hbm_axil.rvalid   , base_a_axil.rvalid   , base_c_axil.rvalid   , base_b_axil.rvalid   }),
      .m_axi_rready       ({base_reg_axil.rready   , base_hbm_axil.rready   , base_a_axil.rready   , base_c_axil.rready   , base_b_axil.rready   })
      );

   //===================================================================
   // Reg Slice for each AXI-Lite interface
   //===================================================================
   st_axil_cctrl base_a_axil_q;
   st_axil_cctrl base_b_axil_q;
   st_axil_cctrl base_c_axil_q;
   st_axil_cctrl base_hbm_axil_q;
   st_axil_cctrl base_reg_axil_q;

   // BASE_A
   cl_axi_register_slice_light SLICE_AXIL_A
     (
      .aclk            (i_clk_hbm_ref           ),
      .aresetn         (rst_hbm_n               ),
      .s_axi_awaddr    (base_a_axil.awaddr      ),
      .s_axi_awvalid   (base_a_axil.awvalid     ),
      .s_axi_awready   (base_a_axil.awready     ),
      .s_axi_wdata     (base_a_axil.wdata       ),
      .s_axi_wstrb     (base_a_axil.wstrb       ),
      .s_axi_wvalid    (base_a_axil.wvalid      ),
      .s_axi_wready    (base_a_axil.wready      ),
      .s_axi_bresp     (base_a_axil.bresp       ),
      .s_axi_bvalid    (base_a_axil.bvalid      ),
      .s_axi_bready    (base_a_axil.bready      ),
      .s_axi_araddr    (base_a_axil.araddr      ),
      .s_axi_arvalid   (base_a_axil.arvalid     ),
      .s_axi_arready   (base_a_axil.arready     ),
      .s_axi_rdata     (base_a_axil.rdata       ),
      .s_axi_rresp     (base_a_axil.rresp       ),
      .s_axi_rvalid    (base_a_axil.rvalid      ),
      .s_axi_rready    (base_a_axil.rready      ),
      .m_axi_awaddr    (base_a_axil_q.awaddr    ),
      .m_axi_awvalid   (base_a_axil_q.awvalid   ),
      .m_axi_awready   (base_a_axil_q.awready   ),
      .m_axi_wdata     (base_a_axil_q.wdata     ),
      .m_axi_wstrb     (base_a_axil_q.wstrb     ),
      .m_axi_wvalid    (base_a_axil_q.wvalid    ),
      .m_axi_wready    (base_a_axil_q.wready    ),
      .m_axi_bresp     (base_a_axil_q.bresp     ),
      .m_axi_bvalid    (base_a_axil_q.bvalid    ),
      .m_axi_bready    (base_a_axil_q.bready    ),
      .m_axi_araddr    (base_a_axil_q.araddr    ),
      .m_axi_arvalid   (base_a_axil_q.arvalid   ),
      .m_axi_arready   (base_a_axil_q.arready   ),
      .m_axi_rdata     (base_a_axil_q.rdata     ),
      .m_axi_rresp     (base_a_axil_q.rresp     ),
      .m_axi_rvalid    (base_a_axil_q.rvalid    ),
      .m_axi_rready    (base_a_axil_q.rready    )
      );

   // BASE_B
   cl_axi_register_slice_light SLICE_AXIL_B
     (
      .aclk            (i_clk_hbm_ref           ),
      .aresetn         (rst_hbm_n               ),
      .s_axi_awaddr    (base_b_axil.awaddr      ),
      .s_axi_awvalid   (base_b_axil.awvalid     ),
      .s_axi_awready   (base_b_axil.awready     ),
      .s_axi_wdata     (base_b_axil.wdata       ),
      .s_axi_wstrb     (base_b_axil.wstrb       ),
      .s_axi_wvalid    (base_b_axil.wvalid      ),
      .s_axi_wready    (base_b_axil.wready      ),
      .s_axi_bresp     (base_b_axil.bresp       ),
      .s_axi_bvalid    (base_b_axil.bvalid      ),
      .s_axi_bready    (base_b_axil.bready      ),
      .s_axi_araddr    (base_b_axil.araddr      ),
      .s_axi_arvalid   (base_b_axil.arvalid     ),
      .s_axi_arready   (base_b_axil.arready     ),
      .s_axi_rdata     (base_b_axil.rdata       ),
      .s_axi_rresp     (base_b_axil.rresp       ),
      .s_axi_rvalid    (base_b_axil.rvalid      ),
      .s_axi_rready    (base_b_axil.rready      ),
      .m_axi_awaddr    (base_b_axil_q.awaddr    ),
      .m_axi_awvalid   (base_b_axil_q.awvalid   ),
      .m_axi_awready   (base_b_axil_q.awready   ),
      .m_axi_wdata     (base_b_axil_q.wdata     ),
      .m_axi_wstrb     (base_b_axil_q.wstrb     ),
      .m_axi_wvalid    (base_b_axil_q.wvalid    ),
      .m_axi_wready    (base_b_axil_q.wready    ),
      .m_axi_bresp     (base_b_axil_q.bresp     ),
      .m_axi_bvalid    (base_b_axil_q.bvalid    ),
      .m_axi_bready    (base_b_axil_q.bready    ),
      .m_axi_araddr    (base_b_axil_q.araddr    ),
      .m_axi_arvalid   (base_b_axil_q.arvalid   ),
      .m_axi_arready   (base_b_axil_q.arready   ),
      .m_axi_rdata     (base_b_axil_q.rdata     ),
      .m_axi_rresp     (base_b_axil_q.rresp     ),
      .m_axi_rvalid    (base_b_axil_q.rvalid    ),
      .m_axi_rready    (base_b_axil_q.rready    )
      );

   // BASE_C
   cl_axi_register_slice_light SLICE_AXIL_C
     (
      .aclk            (i_clk_hbm_ref           ),
      .aresetn         (rst_hbm_n               ),
      .s_axi_awaddr    (base_c_axil.awaddr      ),
      .s_axi_awvalid   (base_c_axil.awvalid     ),
      .s_axi_awready   (base_c_axil.awready     ),
      .s_axi_wdata     (base_c_axil.wdata       ),
      .s_axi_wstrb     (base_c_axil.wstrb       ),
      .s_axi_wvalid    (base_c_axil.wvalid      ),
      .s_axi_wready    (base_c_axil.wready      ),
      .s_axi_bresp     (base_c_axil.bresp       ),
      .s_axi_bvalid    (base_c_axil.bvalid      ),
      .s_axi_bready    (base_c_axil.bready      ),
      .s_axi_araddr    (base_c_axil.araddr      ),
      .s_axi_arvalid   (base_c_axil.arvalid     ),
      .s_axi_arready   (base_c_axil.arready     ),
      .s_axi_rdata     (base_c_axil.rdata       ),
      .s_axi_rresp     (base_c_axil.rresp       ),
      .s_axi_rvalid    (base_c_axil.rvalid      ),
      .s_axi_rready    (base_c_axil.rready      ),
      .m_axi_awaddr    (base_c_axil_q.awaddr    ),
      .m_axi_awvalid   (base_c_axil_q.awvalid   ),
      .m_axi_awready   (base_c_axil_q.awready   ),
      .m_axi_wdata     (base_c_axil_q.wdata     ),
      .m_axi_wstrb     (base_c_axil_q.wstrb     ),
      .m_axi_wvalid    (base_c_axil_q.wvalid    ),
      .m_axi_wready    (base_c_axil_q.wready    ),
      .m_axi_bresp     (base_c_axil_q.bresp     ),
      .m_axi_bvalid    (base_c_axil_q.bvalid    ),
      .m_axi_bready    (base_c_axil_q.bready    ),
      .m_axi_araddr    (base_c_axil_q.araddr    ),
      .m_axi_arvalid   (base_c_axil_q.arvalid   ),
      .m_axi_arready   (base_c_axil_q.arready   ),
      .m_axi_rdata     (base_c_axil_q.rdata     ),
      .m_axi_rresp     (base_c_axil_q.rresp     ),
      .m_axi_rvalid    (base_c_axil_q.rvalid    ),
      .m_axi_rready    (base_c_axil_q.rready    )
      );

   // BASE_HBM
   cl_axi_register_slice_light SLICE_AXIL_HBM
     (
      .aclk            (i_clk_hbm_ref             ),
      .aresetn         (rst_hbm_n                 ),
      .s_axi_awaddr    (base_hbm_axil.awaddr      ),
      .s_axi_awvalid   (base_hbm_axil.awvalid     ),
      .s_axi_awready   (base_hbm_axil.awready     ),
      .s_axi_wdata     (base_hbm_axil.wdata       ),
      .s_axi_wstrb     (base_hbm_axil.wstrb       ),
      .s_axi_wvalid    (base_hbm_axil.wvalid      ),
      .s_axi_wready    (base_hbm_axil.wready      ),
      .s_axi_bresp     (base_hbm_axil.bresp       ),
      .s_axi_bvalid    (base_hbm_axil.bvalid      ),
      .s_axi_bready    (base_hbm_axil.bready      ),
      .s_axi_araddr    (base_hbm_axil.araddr      ),
      .s_axi_arvalid   (base_hbm_axil.arvalid     ),
      .s_axi_arready   (base_hbm_axil.arready     ),
      .s_axi_rdata     (base_hbm_axil.rdata       ),
      .s_axi_rresp     (base_hbm_axil.rresp       ),
      .s_axi_rvalid    (base_hbm_axil.rvalid      ),
      .s_axi_rready    (base_hbm_axil.rready      ),
      .m_axi_awaddr    (base_hbm_axil_q.awaddr    ),
      .m_axi_awvalid   (base_hbm_axil_q.awvalid   ),
      .m_axi_awready   (base_hbm_axil_q.awready   ),
      .m_axi_wdata     (base_hbm_axil_q.wdata     ),
      .m_axi_wstrb     (base_hbm_axil_q.wstrb     ),
      .m_axi_wvalid    (base_hbm_axil_q.wvalid    ),
      .m_axi_wready    (base_hbm_axil_q.wready    ),
      .m_axi_bresp     (base_hbm_axil_q.bresp     ),
      .m_axi_bvalid    (base_hbm_axil_q.bvalid    ),
      .m_axi_bready    (base_hbm_axil_q.bready    ),
      .m_axi_araddr    (base_hbm_axil_q.araddr    ),
      .m_axi_arvalid   (base_hbm_axil_q.arvalid   ),
      .m_axi_arready   (base_hbm_axil_q.arready   ),
      .m_axi_rdata     (base_hbm_axil_q.rdata     ),
      .m_axi_rresp     (base_hbm_axil_q.rresp     ),
      .m_axi_rvalid    (base_hbm_axil_q.rvalid    ),
      .m_axi_rready    (base_hbm_axil_q.rready    )
      );

   // BASE_REG
   cl_axi_register_slice_light SLICE_AXIL_REG
     (
      .aclk            (i_clk_hbm_ref             ),
      .aresetn         (rst_hbm_n                 ),
      .s_axi_awaddr    (base_reg_axil.awaddr      ),
      .s_axi_awvalid   (base_reg_axil.awvalid     ),
      .s_axi_awready   (base_reg_axil.awready     ),
      .s_axi_wdata     (base_reg_axil.wdata       ),
      .s_axi_wstrb     (base_reg_axil.wstrb       ),
      .s_axi_wvalid    (base_reg_axil.wvalid      ),
      .s_axi_wready    (base_reg_axil.wready      ),
      .s_axi_bresp     (base_reg_axil.bresp       ),
      .s_axi_bvalid    (base_reg_axil.bvalid      ),
      .s_axi_bready    (base_reg_axil.bready      ),
      .s_axi_araddr    (base_reg_axil.araddr      ),
      .s_axi_arvalid   (base_reg_axil.arvalid     ),
      .s_axi_arready   (base_reg_axil.arready     ),
      .s_axi_rdata     (base_reg_axil.rdata       ),
      .s_axi_rresp     (base_reg_axil.rresp       ),
      .s_axi_rvalid    (base_reg_axil.rvalid      ),
      .s_axi_rready    (base_reg_axil.rready      ),
      .m_axi_awaddr    (base_reg_axil_q.awaddr    ),
      .m_axi_awvalid   (base_reg_axil_q.awvalid   ),
      .m_axi_awready   (base_reg_axil_q.awready   ),
      .m_axi_wdata     (base_reg_axil_q.wdata     ),
      .m_axi_wstrb     (base_reg_axil_q.wstrb     ),
      .m_axi_wvalid    (base_reg_axil_q.wvalid    ),
      .m_axi_wready    (base_reg_axil_q.wready    ),
      .m_axi_bresp     (base_reg_axil_q.bresp     ),
      .m_axi_bvalid    (base_reg_axil_q.bvalid    ),
      .m_axi_bready    (base_reg_axil_q.bready    ),
      .m_axi_araddr    (base_reg_axil_q.araddr    ),
      .m_axi_arvalid   (base_reg_axil_q.arvalid   ),
      .m_axi_arready   (base_reg_axil_q.arready   ),
      .m_axi_rdata     (base_reg_axil_q.rdata     ),
      .m_axi_rresp     (base_reg_axil_q.rresp     ),
      .m_axi_rvalid    (base_reg_axil_q.rvalid    ),
      .m_axi_rready    (base_reg_axil_q.rready    )
      );

   //===================================================================
   // MMCM_A
   //===================================================================
   logic                 mmcm_a_locked;
   if (CLK_GRP_A_EN) begin : CLK_GRP_A_EN_I //{
      clk_mmcm_a CLK_MMCM_A_I
        (
         .s_axi_aclk       (i_clk_hbm_ref         ),
         .s_axi_aresetn    (rst_hbm_n             ),
         .s_axi_awaddr     (base_a_axil_q.awaddr  ),
         .s_axi_awvalid    (base_a_axil_q.awvalid ),
         .s_axi_awready    (base_a_axil_q.awready ),
         .s_axi_wdata      (base_a_axil_q.wdata   ),
         .s_axi_wstrb      (base_a_axil_q.wstrb   ),
         .s_axi_wvalid     (base_a_axil_q.wvalid  ),
         .s_axi_wready     (base_a_axil_q.wready  ),
         .s_axi_bresp      (base_a_axil_q.bresp   ),
         .s_axi_bvalid     (base_a_axil_q.bvalid  ),
         .s_axi_bready     (base_a_axil_q.bready  ),
         .s_axi_araddr     (base_a_axil_q.araddr  ),
         .s_axi_arvalid    (base_a_axil_q.arvalid ),
         .s_axi_arready    (base_a_axil_q.arready ),
         .s_axi_rdata      (base_a_axil_q.rdata   ),
         .s_axi_rresp      (base_a_axil_q.rresp   ),
         .s_axi_rvalid     (base_a_axil_q.rvalid  ),
         .s_axi_rready     (base_a_axil_q.rready  ),
         .clk_out1         (o_clk_extra_a1        ),
         .clk_out2         (o_clk_extra_a2        ),
         .clk_out3         (o_clk_extra_a3        ),
         .locked           (mmcm_a_locked         ),
         .clk_in1          (i_clk_hbm_ref         )
         );

   end : CLK_GRP_A_EN_I //}
   else begin  : NO_CLK_GRP_A_EN_I //{

      always_comb begin
         base_a_axil_q.awready = '0;
         base_a_axil_q.wready  = '0;
         base_a_axil_q.bresp   = '0;
         base_a_axil_q.bvalid  = '0;
         base_a_axil_q.arready = '0;
         base_a_axil_q.rdata   = '0;
         base_a_axil_q.rresp   = '0;
         base_a_axil_q.rvalid  = '0;
         o_clk_extra_a1        = '0;
         o_clk_extra_a2        = '0;
         o_clk_extra_a3        = '0;
         mmcm_a_locked         = '0;
      end
   end : NO_CLK_GRP_A_EN_I //}

   //===================================================================
   // MMCM_B
   //===================================================================
   logic                 mmcm_b_locked;

   if (CLK_GRP_B_EN) begin : CLK_GRP_B_EN_I //{
      clk_mmcm_b CLK_MMCM_B_I
        (
         .s_axi_aclk       (i_clk_hbm_ref         ),
         .s_axi_aresetn    (rst_hbm_n             ),
         .s_axi_awaddr     (base_b_axil_q.awaddr  ),
         .s_axi_awvalid    (base_b_axil_q.awvalid ),
         .s_axi_awready    (base_b_axil_q.awready ),
         .s_axi_wdata      (base_b_axil_q.wdata   ),
         .s_axi_wstrb      (base_b_axil_q.wstrb   ),
         .s_axi_wvalid     (base_b_axil_q.wvalid  ),
         .s_axi_wready     (base_b_axil_q.wready  ),
         .s_axi_bresp      (base_b_axil_q.bresp   ),
         .s_axi_bvalid     (base_b_axil_q.bvalid  ),
         .s_axi_bready     (base_b_axil_q.bready  ),
         .s_axi_araddr     (base_b_axil_q.araddr  ),
         .s_axi_arvalid    (base_b_axil_q.arvalid ),
         .s_axi_arready    (base_b_axil_q.arready ),
         .s_axi_rdata      (base_b_axil_q.rdata   ),
         .s_axi_rresp      (base_b_axil_q.rresp   ),
         .s_axi_rvalid     (base_b_axil_q.rvalid  ),
         .s_axi_rready     (base_b_axil_q.rready  ),
         .clk_out1         (o_clk_extra_b0        ),
         .clk_out2         (o_clk_extra_b1        ),
         .locked           (mmcm_b_locked         ),
         .clk_in1          (i_clk_hbm_ref         )
         );

   end : CLK_GRP_B_EN_I //}
   else begin  : NO_CLK_GRP_B_EN_I //{

      always_comb begin
         base_b_axil_q.awready = '0;
         base_b_axil_q.wready  = '0;
         base_b_axil_q.bresp   = '0;
         base_b_axil_q.bvalid  = '0;
         base_b_axil_q.arready = '0;
         base_b_axil_q.rdata   = '0;
         base_b_axil_q.rresp   = '0;
         base_b_axil_q.rvalid  = '0;
         o_clk_extra_b0        = '0;
         o_clk_extra_b1        = '0;
         mmcm_b_locked         = '0;
      end
   end : NO_CLK_GRP_B_EN_I //}


   //===================================================================
   // MMCM_C
   //===================================================================
   logic                 mmcm_c_locked;

   if (CLK_GRP_C_EN) begin : CLK_GRP_C_EN_I //{
      clk_mmcm_c CLK_MMCM_C_I
        (
         .s_axi_aclk       (i_clk_hbm_ref         ),
         .s_axi_aresetn    (rst_hbm_n             ),
         .s_axi_awaddr     (base_c_axil_q.awaddr  ),
         .s_axi_awvalid    (base_c_axil_q.awvalid ),
         .s_axi_awready    (base_c_axil_q.awready ),
         .s_axi_wdata      (base_c_axil_q.wdata   ),
         .s_axi_wstrb      (base_c_axil_q.wstrb   ),
         .s_axi_wvalid     (base_c_axil_q.wvalid  ),
         .s_axi_wready     (base_c_axil_q.wready  ),
         .s_axi_bresp      (base_c_axil_q.bresp   ),
         .s_axi_bvalid     (base_c_axil_q.bvalid  ),
         .s_axi_bready     (base_c_axil_q.bready  ),
         .s_axi_araddr     (base_c_axil_q.araddr  ),
         .s_axi_arvalid    (base_c_axil_q.arvalid ),
         .s_axi_arready    (base_c_axil_q.arready ),
         .s_axi_rdata      (base_c_axil_q.rdata   ),
         .s_axi_rresp      (base_c_axil_q.rresp   ),
         .s_axi_rvalid     (base_c_axil_q.rvalid  ),
         .s_axi_rready     (base_c_axil_q.rready  ),
         .clk_out1         (o_clk_extra_c0        ),
         .clk_out2         (o_clk_extra_c1        ),
         .locked           (mmcm_c_locked         ),
         .clk_in1          (i_clk_hbm_ref         )
         );

   end : CLK_GRP_C_EN_I //}
   else begin  : NO_CLK_GRP_C_EN_I //{

      always_comb begin
         base_c_axil_q.awready = '0;
         base_c_axil_q.wready  = '0;
         base_c_axil_q.bresp   = '0;
         base_c_axil_q.bvalid  = '0;
         base_c_axil_q.arready = '0;
         base_c_axil_q.rdata   = '0;
         base_c_axil_q.rresp   = '0;
         base_c_axil_q.rvalid  = '0;
         o_clk_extra_c0        = '0;
         o_clk_extra_c1        = '0;
         mmcm_c_locked         = '0;
      end
   end : NO_CLK_GRP_C_EN_I //}


   //===================================================================
   // MMCM_HBM
   //===================================================================
   logic                 mmcm_hbm_locked;

   if (CLK_HBM_EN) begin : CLK_HBM_EN_I //{
      clk_mmcm_hbm CLK_MMCM_HBM_I
        (
         .s_axi_aclk       (i_clk_hbm_ref           ),
         .s_axi_aresetn    (rst_hbm_n               ),
         .s_axi_awaddr     (base_hbm_axil_q.awaddr  ),
         .s_axi_awvalid    (base_hbm_axil_q.awvalid ),
         .s_axi_awready    (base_hbm_axil_q.awready ),
         .s_axi_wdata      (base_hbm_axil_q.wdata   ),
         .s_axi_wstrb      (base_hbm_axil_q.wstrb   ),
         .s_axi_wvalid     (base_hbm_axil_q.wvalid  ),
         .s_axi_wready     (base_hbm_axil_q.wready  ),
         .s_axi_bresp      (base_hbm_axil_q.bresp   ),
         .s_axi_bvalid     (base_hbm_axil_q.bvalid  ),
         .s_axi_bready     (base_hbm_axil_q.bready  ),
         .s_axi_araddr     (base_hbm_axil_q.araddr  ),
         .s_axi_arvalid    (base_hbm_axil_q.arvalid ),
         .s_axi_arready    (base_hbm_axil_q.arready ),
         .s_axi_rdata      (base_hbm_axil_q.rdata   ),
         .s_axi_rresp      (base_hbm_axil_q.rresp   ),
         .s_axi_rvalid     (base_hbm_axil_q.rvalid  ),
         .s_axi_rready     (base_hbm_axil_q.rready  ),
         .clk_out1         (o_clk_hbm_axi           ),
         .locked           (mmcm_hbm_locked         ),
         .clk_in1          (i_clk_hbm_ref           )
         );

   end : CLK_HBM_EN_I //}
   else begin  : NO_CLK_HBM_EN_I //{

      always_comb begin
         base_hbm_axil_q.awready = '0;
         base_hbm_axil_q.wready  = '0;
         base_hbm_axil_q.bresp   = '0;
         base_hbm_axil_q.bvalid  = '0;
         base_hbm_axil_q.arready = '0;
         base_hbm_axil_q.rdata   = '0;
         base_hbm_axil_q.rresp   = '0;
         base_hbm_axil_q.rvalid  = '0;
         o_clk_hbm_axi           = '0;
         mmcm_hbm_locked         = '0;
      end
   end : NO_CLK_HBM_EN_I //}


   //===================================================================
   // pass-through clocks
   //===================================================================
   assign o_clk_hbm_ref = i_clk_hbm_ref;
   assign o_clk_main_a0 = i_clk_main_a0;

   //===================================================================
   // AWS_REGS
   //===================================================================
   aws_clk_regs
     #(
       .CLK_GRP_A_EN    (CLK_GRP_A_EN),
       .CLK_GRP_B_EN    (CLK_GRP_B_EN),
       .CLK_GRP_C_EN    (CLK_GRP_C_EN),
       .CLK_HBM_EN      (CLK_HBM_EN  ),
       .MAX_NUM_CLKS    (MAX_NUM_CLKS)
       )
   AWS_CLK_REGS_I
     (
      .i_clk              (i_clk_hbm_ref             ),
      .i_rst_n            (rst_hbm_n                 ),
      .s_axil_awaddr      (base_reg_axil_q.awaddr    ),
      .s_axil_awvalid     (base_reg_axil_q.awvalid   ),
      .s_axil_awready     (base_reg_axil_q.awready   ),
      .s_axil_wdata       (base_reg_axil_q.wdata     ),
      .s_axil_wstrb       (base_reg_axil_q.wstrb     ),
      .s_axil_wvalid      (base_reg_axil_q.wvalid    ),
      .s_axil_wready      (base_reg_axil_q.wready    ),
      .s_axil_bresp       (base_reg_axil_q.bresp     ),
      .s_axil_bvalid      (base_reg_axil_q.bvalid    ),
      .s_axil_bready      (base_reg_axil_q.bready    ),
      .s_axil_araddr      (base_reg_axil_q.araddr    ),
      .s_axil_arvalid     (base_reg_axil_q.arvalid   ),
      .s_axil_arready     (base_reg_axil_q.arready   ),
      .s_axil_rdata       (base_reg_axil_q.rdata     ),
      .s_axil_rresp       (base_reg_axil_q.rresp     ),
      .s_axil_rvalid      (base_reg_axil_q.rvalid    ),
      .s_axil_rready      (base_reg_axil_q.rready    ),
      .i_mmcm_a_lock      (mmcm_a_locked             ),
      .i_mmcm_b_lock      (mmcm_b_locked             ),
      .i_mmcm_c_lock      (mmcm_c_locked             ),
      .i_mmcm_hbm_lock    (mmcm_hbm_locked           ),
      .o_glbl_rst         (glbl_rst                  ),
      .o_cl_rst_hbm_axi_n (cl_rst_n[9]               ),
      .o_cl_rst_hbm_ref_n (cl_rst_n[8]               ),
      .o_cl_rst_c1_n      (cl_rst_n[7]               ),
      .o_cl_rst_c0_n      (cl_rst_n[6]               ),
      .o_cl_rst_b1_n      (cl_rst_n[5]               ),
      .o_cl_rst_b0_n      (cl_rst_n[4]               ),
      .o_cl_rst_a3_n      (cl_rst_n[3]               ),
      .o_cl_rst_a2_n      (cl_rst_n[2]               ),
      .o_cl_rst_a1_n      (cl_rst_n[1]               ),
      .o_cl_rst_main_n    (cl_rst_n[0]               )
      );

   //===================================================================
   // AWS Clock Reset synchronizers
   //===================================================================
   logic [MAX_NUM_CLKS-1:0] s_clks;
   logic [MAX_NUM_CLKS-1:0] sync_rst_out_n;

   always_comb begin //{
      s_clks = { o_clk_hbm_axi,
                 o_clk_hbm_ref,
                 o_clk_extra_c1,
                 o_clk_extra_c0,
                 o_clk_extra_b1,
                 o_clk_extra_b0,
                 o_clk_extra_a3,
                 o_clk_extra_a2,
                 o_clk_extra_a1,
                 o_clk_main_a0 };

      // Output reset synchronized to their clock domain.
      {o_cl_rst_hbm_axi_n,
       o_cl_rst_hbm_ref_n,
       o_cl_rst_c1_n,
       o_cl_rst_c0_n,
       o_cl_rst_b1_n,
       o_cl_rst_b0_n,
       o_cl_rst_a3_n,
       o_cl_rst_a2_n,
       o_cl_rst_a1_n,
       o_cl_rst_main_n} = sync_rst_out_n;
   end //}

   // Instantiate synchronizers
   generate //{
      for (genvar gg = 0; gg < MAX_NUM_CLKS; gg++) begin : CDC_RST_OUT //{
         xpm_cdc_async_rst
                       #(
                         .DEST_SYNC_FF     (2),
                         .INIT_SYNC_FF     (0),
                         .RST_ACTIVE_HIGH  (0)
                         )
         CDC_ASYNC_RST_OUT_I
                       (
                        .src_arst    (cl_rst_n[gg]       ),
                        .dest_clk    (s_clks[gg]         ),
                        .dest_arst   (sync_rst_out_n[gg] )
                        );
      end : CDC_RST_OUT //}
   endgenerate //}

endmodule // aws_clk_gen
