// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

// SDE Top Level

module sde #(parameter bit C2H_ONLY = 0,
             parameter bit H2C_ONLY = 0,
             
             parameter H2C_PCIM_MAX_RD_SIZE = 0, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB
             parameter C2H_PCIM_MAX_WR_SIZE = 3, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB

             parameter PCIM_DATA_WIDTH = 512,
             parameter PCIM_ID_WIDTH = 3,
             parameter PCIM_LEN_WIDTH = 8,
             parameter PCIM_ADDR_WIDTH = 64,

             parameter PCIM_NUM_OT_RD = 64,
             
             parameter PCIS_DATA_WIDTH = 512,
             parameter PCIS_ID_WIDTH = 16,
             parameter PCIS_LEN_WIDTH = 8,
             parameter PCIS_ADDR_WIDTH = 64,
             
             parameter bit C2H_DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
             
             parameter C2H_DESC_RAM_DEPTH = 64,
             
             parameter C2H_AXIS_DATA_WIDTH = 512,
             parameter C2H_USER_BIT_WIDTH = C2H_DESC_TYPE ? 1 : 64,
             
             parameter C2H_BUF_DEPTH = 512,
             
             parameter bit H2C_DESC_TYPE = 0,
             parameter H2C_DESC_RAM_DEPTH = 64,
             
             parameter H2C_AXIS_DATA_WIDTH = 512,
             parameter H2C_USER_BIT_WIDTH = H2C_DESC_TYPE ? 1 : 64,
             
             parameter H2C_BUF_DEPTH = 512,
             
             parameter H2C_PKT_SIZE_BYTES = 64,
             
             
             parameter C2H_PCIM_DM_AWID = 0,   // This is the AWID used for write accesses from C2H Data Mover
             parameter C2H_PCIM_WB_AWID = 1,   // This is the AWID used for write accesses from C2H Write Back Block
             parameter H2C_PCIM_WB_AWID = 2,   // This is the AWID used for write accesses from H2C Write Back Block
             
             parameter C2H_PCIM_DESC_ARID = 0, // This is the ARID used for read access from the C2H Desc Block
             parameter H2C_PCIM_DESC_ARID = 1, // This is the ARID used for read access from the H2C Desc Block
             parameter H2C_PCIM_DM_ARID = 2    // This is the ARID used for write accesses from H2C Data Mover
             )
  (
    input                                       clk,
    input                                       rst_n,
   
   // PCIS Interface
    input [PCIS_ID_WIDTH-1:0]                   pcis_awid,
    input [PCIS_ADDR_WIDTH-1:0]                 pcis_awaddr,
    input [PCIS_LEN_WIDTH-1:0]                  pcis_awlen,
    input [2:0]                                 pcis_awsize,
    input                                       pcis_awvalid,
    output logic                                pcis_awready,
    input [PCIS_DATA_WIDTH-1:0]                 pcis_wdata,
    input [(PCIS_DATA_WIDTH>>3)-1:0]            pcis_wstrb,
    input                                       pcis_wlast,
    input                                       pcis_wvalid,
    output logic                                pcis_wready,
    output logic [PCIS_ID_WIDTH-1:0]            pcis_bid,
    output logic [1:0]                          pcis_bresp,
    output logic                                pcis_bvalid,
    input                                       pcis_bready,
    input [PCIS_ID_WIDTH-1:0]                   pcis_arid,
    input [PCIS_ADDR_WIDTH-1:0]                 pcis_araddr,
    input [PCIS_LEN_WIDTH-1:0]                  pcis_arlen,
    input [2:0]                                 pcis_arsize,
    input                                       pcis_arvalid,
    output logic                                pcis_arready,
    output logic [PCIS_ID_WIDTH-1:0]            pcis_rid,
    output logic [PCIS_DATA_WIDTH-1:0]          pcis_rdata,
    output logic [1:0]                          pcis_rresp,
    output logic                                pcis_rlast,
    output logic                                pcis_rvalid,
    input                                       pcis_rready,
   
   // PCIM Interface
    output logic                                pcim_awvalid,
    output logic [PCIM_ID_WIDTH-1:0]            pcim_awid,
    output logic [PCIM_ADDR_WIDTH-1:0]          pcim_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]           pcim_awlen,
    output logic [2:0]                          pcim_awsize,
    input                                       pcim_awready,
    output logic                                pcim_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]          pcim_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0]     pcim_wstrb,
    output logic                                pcim_wlast,
    input                                       pcim_wready,
    input logic                                 pcim_bvalid,
    input logic [PCIM_ID_WIDTH-1:0]             pcim_bid,
    input logic [1:0]                           pcim_bresp,
    output logic                                pcim_bready,
    output logic                                pcim_arvalid,
    output logic [PCIM_ID_WIDTH-1:0]            pcim_arid,
    output logic [PCIM_ADDR_WIDTH-1:0]          pcim_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]           pcim_arlen,
    output logic [2:0]                          pcim_arsize,
    input                                       pcim_arready,
    input                                       pcim_rvalid,
    input [PCIM_ID_WIDTH-1:0]                   pcim_rid,
    input [PCIM_DATA_WIDTH-1:0]                 pcim_rdata,
    input [1:0]                                 pcim_rresp,
    input                                       pcim_rlast,
    output logic                                pcim_rready,

    // C2H AXI-Stream Interface
    input                                       c2h_axis_valid,
    input [C2H_AXIS_DATA_WIDTH-1:0]             c2h_axis_data,
    input [(C2H_AXIS_DATA_WIDTH>>3)-1:0]        c2h_axis_keep,
    input [C2H_USER_BIT_WIDTH-1:0]              c2h_axis_user,
    input                                       c2h_axis_last,
    output logic                                c2h_axis_ready,
    
   // H2C AXI-Stream Interface
    output logic                                h2c_axis_valid,
    output logic [H2C_AXIS_DATA_WIDTH-1:0]      h2c_axis_data,
    output logic [(H2C_AXIS_DATA_WIDTH>>3)-1:0] h2c_axis_keep,
    output logic [H2C_USER_BIT_WIDTH-1:0]       h2c_axis_user,
    output logic                                h2c_axis_last,
    input                                       h2c_axis_ready

   );

   localparam C2H_DESC_WIDTH = 128;
   localparam H2C_DESC_WIDTH = H2C_DESC_TYPE ? 128 : 256;
   localparam H2C_PKT_WIDTH = H2C_PKT_SIZE_BYTES*8;

   logic                                        sync_rst_n;
   logic                                        c2h_sync_rst_n;
   logic                                        h2c_sync_rst_n;
   logic                                        pm_sync_rst_n;
   
   logic                                        c2h_ps_desc_wr_req;
   logic [C2H_DESC_WIDTH-1:0]                   c2h_ps_desc_wdata;
   logic                                        c2h_ps_desc_ack;
   
   logic                                        h2c_ps_desc_wr_req;
   logic [H2C_DESC_WIDTH-1:0]                   h2c_ps_desc_wdata;
   logic                                        h2c_ps_desc_ack;
   
   logic                                        h2c_ps_pkt_wr_req;
   logic [H2C_PKT_WIDTH-1:0]                    h2c_ps_pkt_wdata;
   logic                                        h2c_ps_pkt_ack;
   
   logic                                        pm_ps_cfg_wr_req;
   logic                                        pm_ps_cfg_rd_req;
   logic [15:0]                                 pm_ps_cfg_addr;
   logic [31:0]                                 pm_ps_cfg_wdata;
   logic                                        pm_ps_cfg_ack;
   logic [31:0]                                 pm_ps_cfg_rdata;
   
   logic                                        c2h_ps_cfg_wr_req;
   logic                                        c2h_ps_cfg_rd_req;
   logic [15:0]                                 c2h_ps_cfg_addr;
   logic [31:0]                                 c2h_ps_cfg_wdata;
   logic                                        c2h_ps_cfg_ack;
   logic [31:0]                                 c2h_ps_cfg_rdata;
   
   logic                                        c2h_desc_ooo_error;
   logic                                        c2h_desc_unalin_error;

   logic                                        h2c_ps_cfg_wr_req;
   logic                                        h2c_ps_cfg_rd_req;
   logic [15:0]                                 h2c_ps_cfg_addr;
   logic [31:0]                                 h2c_ps_cfg_wdata;
   logic                                        h2c_ps_cfg_ack;
   logic [31:0]                                 h2c_ps_cfg_rdata;

   logic                                        h2c_desc_ooo_error;
   logic                                        h2c_desc_unalin_error;

   logic                                        c2h_desc_pm_arvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  c2h_desc_pm_araddr;
   logic [PCIM_LEN_WIDTH-1:0]                   c2h_desc_pm_arlen;
   logic                                        c2h_pm_desc_arready;

   logic                                        c2h_pm_desc_rvalid;
   logic [1:0]                                  c2h_pm_desc_rresp;
   logic [PCIM_DATA_WIDTH-1:0]                  c2h_pm_desc_rdata;
   logic                                        c2h_pm_desc_rlast;
   logic                                        c2h_desc_pm_rready;

   logic                                        c2h_dm_pm_awvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  c2h_dm_pm_awaddr;
   logic [PCIM_LEN_WIDTH-1:0]                   c2h_dm_pm_awlen;
   logic [PCIM_ID_WIDTH-1:0]                    c2h_dm_pm_awid;
   logic                                        c2h_pm_dm_awready;
   
   logic                                        c2h_dm_pm_wvalid;
   logic [PCIM_DATA_WIDTH-1:0]                  c2h_dm_pm_wdata;
   logic [(PCIM_DATA_WIDTH>>3)-1:0]             c2h_dm_pm_wstrb;
   logic                                        c2h_dm_pm_wlast;
   logic                                        c2h_pm_dm_wready;

   logic                                        c2h_pm_dm_bvalid;
   logic [1:0]                                  c2h_pm_dm_bresp;
   logic                                        c2h_dm_pm_bready;

   logic                                        c2h_wb_pm_awvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  c2h_wb_pm_awaddr;
   logic [PCIM_LEN_WIDTH-1:0]                   c2h_wb_pm_awlen;
   logic [PCIM_ID_WIDTH-1:0]                    c2h_wb_pm_awid;
   logic                                        c2h_pm_wb_awready;
   
   logic                                        c2h_wb_pm_wvalid;
   logic [PCIM_DATA_WIDTH-1:0]                  c2h_wb_pm_wdata;
   logic [(PCIM_DATA_WIDTH>>3)-1:0]             c2h_wb_pm_wstrb;
   logic                                        c2h_wb_pm_wlast;
   logic                                        c2h_pm_wb_wready;

   logic                                        c2h_pm_wb_bvalid;
   logic [1:0]                                  c2h_pm_wb_bresp;
   logic                                        c2h_wb_pm_bready;

   logic                                        h2c_desc_pm_arvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  h2c_desc_pm_araddr;
   logic [PCIM_LEN_WIDTH-1:0]                   h2c_desc_pm_arlen;
   logic                                        h2c_pm_desc_arready;

   logic                                        h2c_pm_desc_rvalid;
   logic [1:0]                                  h2c_pm_desc_rresp;
   logic [PCIM_DATA_WIDTH-1:0]                  h2c_pm_desc_rdata;
   logic                                        h2c_pm_desc_rlast;
   logic                                        h2c_desc_pm_rready;
   
   logic                                        h2c_dm_pm_arvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  h2c_dm_pm_araddr;
   logic [PCIM_LEN_WIDTH-1:0]                   h2c_dm_pm_arlen;
   logic [PCIM_ID_WIDTH-1:0]                    h2c_dm_pm_arid;
   logic                                        h2c_pm_dm_arready;

   logic                                        h2c_pm_dm_rvalid;
   logic [1:0]                                  h2c_pm_dm_rresp;
   logic [PCIM_DATA_WIDTH-1:0]                  h2c_pm_dm_rdata;
   logic                                        h2c_pm_dm_rlast;
   logic                                        h2c_dm_pm_rready;

   logic                                        h2c_wb_pm_awvalid;
   logic [PCIM_ADDR_WIDTH-1:0]                  h2c_wb_pm_awaddr;
   logic [PCIM_LEN_WIDTH-1:0]                   h2c_wb_pm_awlen;
   logic [PCIM_ID_WIDTH-1:0]                    h2c_wb_pm_awid;
   logic                                        h2c_pm_wb_awready;
   
   logic                                        h2c_wb_pm_wvalid;
   logic [PCIM_DATA_WIDTH-1:0]                  h2c_wb_pm_wdata;
   logic [(PCIM_DATA_WIDTH>>3)-1:0]             h2c_wb_pm_wstrb;
   logic                                        h2c_wb_pm_wlast;
   logic                                        h2c_pm_wb_wready;

   logic                                        h2c_pm_wb_bvalid;
   logic [1:0]                                  h2c_pm_wb_bresp;
   logic                                        h2c_wb_pm_bready;

   // Generate local copy of Reset
   always @(posedge clk)
        sync_rst_n <= rst_n;
   
   // PCIS Interface 
   sde_ps #(.PCIS_DATA_WIDTH (PCIS_DATA_WIDTH),
            .PCIS_ID_WIDTH   (PCIS_ID_WIDTH),
            .PCIS_LEN_WIDTH  (PCIS_LEN_WIDTH),
            .PCIS_ADDR_WIDTH (PCIS_ADDR_WIDTH),

            .C2H_DESC_TYPE   (C2H_DESC_TYPE),
            .C2H_DESC_WIDTH  (C2H_DESC_WIDTH),

            .H2C_DESC_TYPE   (H2C_DESC_TYPE),
            .H2C_PKT_SIZE_BYTES (H2C_PKT_SIZE_BYTES)
            )
   SDE_PCI_SLV
     (.clk                (clk),
      .rst_n              (sync_rst_n),

      .pcis_awid          (pcis_awid   ),
      .pcis_awaddr        (pcis_awaddr ),
      .pcis_awlen         (pcis_awlen  ),
      .pcis_awsize        (pcis_awsize ),
      .pcis_awvalid       (pcis_awvalid),
      .pcis_awready       (pcis_awready),
      .pcis_wdata         (pcis_wdata  ),
      .pcis_wstrb         (pcis_wstrb  ),
      .pcis_wlast         (pcis_wlast  ),
      .pcis_wvalid        (pcis_wvalid ),
      .pcis_wready        (pcis_wready ),
      .pcis_bid           (pcis_bid    ),
      .pcis_bresp         (pcis_bresp  ),
      .pcis_bvalid        (pcis_bvalid ),
      .pcis_bready        (pcis_bready ),
      .pcis_arid          (pcis_arid   ),
      .pcis_araddr        (pcis_araddr ),
      .pcis_arlen         (pcis_arlen  ),
      .pcis_arsize        (pcis_arsize ),
      .pcis_arvalid       (pcis_arvalid),
      .pcis_arready       (pcis_arready),
      .pcis_rid           (pcis_rid    ),
      .pcis_rdata         (pcis_rdata  ),
      .pcis_rresp         (pcis_rresp  ),
      .pcis_rlast         (pcis_rlast  ),
      .pcis_rvalid        (pcis_rvalid ),
      .pcis_rready        (pcis_rready ),

      .c2h_sync_rst_n     (c2h_sync_rst_n),
      .h2c_sync_rst_n     (h2c_sync_rst_n),
      .pm_sync_rst_n      (pm_sync_rst_n ),

      .c2h_ps_desc_wr_req (c2h_ps_desc_wr_req),
      .c2h_ps_desc_wdata  (c2h_ps_desc_wdata ),
      .c2h_ps_desc_ack    (c2h_ps_desc_ack   ),
      
      .h2c_ps_desc_wr_req (h2c_ps_desc_wr_req),
      .h2c_ps_desc_wdata  (h2c_ps_desc_wdata ),
      .h2c_ps_desc_ack    (h2c_ps_desc_ack   ),
      
      .h2c_ps_pkt_wr_req  (h2c_ps_pkt_wr_req),
      .h2c_ps_pkt_wdata   (h2c_ps_pkt_wdata ),
      .h2c_ps_pkt_ack     (h2c_ps_pkt_ack   ),
      
      .pm_ps_cfg_wr_req   (pm_ps_cfg_wr_req),
      .pm_ps_cfg_rd_req   (pm_ps_cfg_rd_req),
      .pm_ps_cfg_addr     (pm_ps_cfg_addr  ),
      .pm_ps_cfg_wdata    (pm_ps_cfg_wdata ),
      .pm_ps_cfg_ack      (pm_ps_cfg_ack   ),
      .pm_ps_cfg_rdata    (pm_ps_cfg_rdata ),
      
      .c2h_ps_cfg_wr_req  (c2h_ps_cfg_wr_req),
      .c2h_ps_cfg_rd_req  (c2h_ps_cfg_rd_req),
      .c2h_ps_cfg_addr    (c2h_ps_cfg_addr  ),
      .c2h_ps_cfg_wdata   (c2h_ps_cfg_wdata ),
      .c2h_ps_cfg_ack     (c2h_ps_cfg_ack   ),
      .c2h_ps_cfg_rdata   (c2h_ps_cfg_rdata ),
      
      .c2h_desc_ooo_error    (c2h_desc_ooo_error),
      .c2h_desc_unalin_error (c2h_desc_unalin_error),

      .h2c_ps_cfg_wr_req  (h2c_ps_cfg_wr_req),
      .h2c_ps_cfg_rd_req  (h2c_ps_cfg_rd_req),
      .h2c_ps_cfg_addr    (h2c_ps_cfg_addr  ),
      .h2c_ps_cfg_wdata   (h2c_ps_cfg_wdata ),
      .h2c_ps_cfg_ack     (h2c_ps_cfg_ack   ),
      .h2c_ps_cfg_rdata   (h2c_ps_cfg_rdata ),

      .h2c_desc_ooo_error    (h2c_desc_ooo_error),
      .h2c_desc_unalin_error (h2c_desc_unalin_error)

      );
   
   // PCIM Interface
   sde_pm #(.PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
            .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
            .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
            .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),

            .C2H_PCIM_DM_AWID (C2H_PCIM_DM_AWID),
            .C2H_PCIM_WB_AWID (C2H_PCIM_WB_AWID),
            .H2C_PCIM_WB_AWID (H2C_PCIM_WB_AWID),
            
            .C2H_PCIM_DESC_ARID(C2H_PCIM_DESC_ARID),
            .H2C_PCIM_DESC_ARID(H2C_PCIM_DESC_ARID),
            .H2C_PCIM_DM_ARID  (H2C_PCIM_DM_ARID  )

           )
   SDE_PCI_MSTR
     (.clk                 (clk),
      .rst_n               (pm_sync_rst_n),
      
      .pm_ps_cfg_wr_req    (pm_ps_cfg_wr_req),
      .pm_ps_cfg_rd_req    (pm_ps_cfg_rd_req),
      .pm_ps_cfg_addr      (pm_ps_cfg_addr  ),
      .pm_ps_cfg_wdata     (pm_ps_cfg_wdata ),
      .pm_ps_cfg_ack       (pm_ps_cfg_ack   ),
      .pm_ps_cfg_rdata     (pm_ps_cfg_rdata ),
      
      .pcim_awvalid        (pcim_awvalid ),
      .pcim_awid           (pcim_awid    ),
      .pcim_awaddr         (pcim_awaddr  ),
      .pcim_awlen          (pcim_awlen   ),
      .pcim_awsize         (pcim_awsize  ),
      .pcim_awready        (pcim_awready ),
      .pcim_wvalid         (pcim_wvalid  ),
      .pcim_wdata          (pcim_wdata   ),
      .pcim_wstrb          (pcim_wstrb   ),
      .pcim_wlast          (pcim_wlast   ),
      .pcim_wready         (pcim_wready  ),
      .pcim_bvalid         (pcim_bvalid  ),
      .pcim_bid            (pcim_bid     ),
      .pcim_bresp          (pcim_bresp   ),
      .pcim_bready         (pcim_bready  ),
      .pcim_arvalid        (pcim_arvalid ),
      .pcim_arid           (pcim_arid    ),
      .pcim_araddr         (pcim_araddr  ),
      .pcim_arlen          (pcim_arlen   ),
      .pcim_arsize         (pcim_arsize  ),
      .pcim_arready        (pcim_arready ),
      .pcim_rvalid         (pcim_rvalid  ),
      .pcim_rid            (pcim_rid     ),
      .pcim_rdata          (pcim_rdata   ),
      .pcim_rresp          (pcim_rresp   ),
      .pcim_rlast          (pcim_rlast   ),
      .pcim_rready         (pcim_rready  ),

      .c2h_desc_pm_arvalid (c2h_desc_pm_arvalid),
      .c2h_desc_pm_araddr  (c2h_desc_pm_araddr ),
      .c2h_desc_pm_arlen   (c2h_desc_pm_arlen  ),
      .c2h_pm_desc_arready (c2h_pm_desc_arready),
      .c2h_pm_desc_rvalid  (c2h_pm_desc_rvalid),
      .c2h_pm_desc_rresp   (c2h_pm_desc_rresp ),
      .c2h_pm_desc_rdata   (c2h_pm_desc_rdata ),
      .c2h_pm_desc_rlast   (c2h_pm_desc_rlast ),
      .c2h_desc_pm_rready  (c2h_desc_pm_rready),

      .c2h_dm_pm_awvalid   (c2h_dm_pm_awvalid),
      .c2h_dm_pm_awaddr    (c2h_dm_pm_awaddr ),
      .c2h_dm_pm_awlen     (c2h_dm_pm_awlen  ),
      .c2h_dm_pm_awid      (c2h_dm_pm_awid   ),
      .c2h_pm_dm_awready   (c2h_pm_dm_awready),
      .c2h_dm_pm_wvalid    (c2h_dm_pm_wvalid ),
      .c2h_dm_pm_wdata     (c2h_dm_pm_wdata  ),
      .c2h_dm_pm_wstrb     (c2h_dm_pm_wstrb  ),
      .c2h_dm_pm_wlast     (c2h_dm_pm_wlast  ),
      .c2h_pm_dm_wready    (c2h_pm_dm_wready ),
      .c2h_pm_dm_bvalid    (c2h_pm_dm_bvalid ),
      .c2h_pm_dm_bresp     (c2h_pm_dm_bresp  ),
      .c2h_dm_pm_bready    (c2h_dm_pm_bready ),

      
      .c2h_wb_pm_awvalid   (c2h_wb_pm_awvalid),
      .c2h_wb_pm_awaddr    (c2h_wb_pm_awaddr ),
      .c2h_wb_pm_awlen     (c2h_wb_pm_awlen  ),
      .c2h_wb_pm_awid      (c2h_wb_pm_awid   ),
      .c2h_pm_wb_awready   (c2h_pm_wb_awready),
      .c2h_wb_pm_wvalid    (c2h_wb_pm_wvalid ),
      .c2h_wb_pm_wdata     (c2h_wb_pm_wdata  ),
      .c2h_wb_pm_wstrb     (c2h_wb_pm_wstrb  ),
      .c2h_wb_pm_wlast     (c2h_wb_pm_wlast  ),
      .c2h_pm_wb_wready    (c2h_pm_wb_wready ),
      .c2h_pm_wb_bvalid    (c2h_pm_wb_bvalid ),
      .c2h_pm_wb_bresp     (c2h_pm_wb_bresp  ),
      .c2h_wb_pm_bready    (c2h_wb_pm_bready ),
      
      .h2c_desc_pm_arvalid (h2c_desc_pm_arvalid),
      .h2c_desc_pm_araddr  (h2c_desc_pm_araddr ),
      .h2c_desc_pm_arlen   (h2c_desc_pm_arlen  ),
      .h2c_pm_desc_arready (h2c_pm_desc_arready),
      .h2c_pm_desc_rvalid  (h2c_pm_desc_rvalid),
      .h2c_pm_desc_rresp   (h2c_pm_desc_rresp ),
      .h2c_pm_desc_rdata   (h2c_pm_desc_rdata ),
      .h2c_pm_desc_rlast   (h2c_pm_desc_rlast ),
      .h2c_desc_pm_rready  (h2c_desc_pm_rready),
      
      .h2c_dm_pm_arvalid   (h2c_dm_pm_arvalid),
      .h2c_dm_pm_araddr    (h2c_dm_pm_araddr ),
      .h2c_dm_pm_arlen     (h2c_dm_pm_arlen  ),
      .h2c_pm_dm_arready   (h2c_pm_dm_arready),
      .h2c_pm_dm_rvalid    (h2c_pm_dm_rvalid),
      .h2c_pm_dm_rresp     (h2c_pm_dm_rresp ),
      .h2c_pm_dm_rdata     (h2c_pm_dm_rdata ),
      .h2c_pm_dm_rlast     (h2c_pm_dm_rlast ),
      .h2c_dm_pm_rready    (h2c_dm_pm_rready),
      
      .h2c_wb_pm_awvalid   (h2c_wb_pm_awvalid),
      .h2c_wb_pm_awaddr    (h2c_wb_pm_awaddr ),
      .h2c_wb_pm_awlen     (h2c_wb_pm_awlen  ),
      .h2c_wb_pm_awid      (h2c_wb_pm_awid   ),
      .h2c_pm_wb_awready   (h2c_pm_wb_awready),
      .h2c_wb_pm_wvalid    (h2c_wb_pm_wvalid ),
      .h2c_wb_pm_wdata     (h2c_wb_pm_wdata  ),
      .h2c_wb_pm_wstrb     (h2c_wb_pm_wstrb  ),
      .h2c_wb_pm_wlast     (h2c_wb_pm_wlast  ),
      .h2c_pm_wb_wready    (h2c_pm_wb_wready ),
      .h2c_pm_wb_bvalid    (h2c_pm_wb_bvalid ),
      .h2c_pm_wb_bresp     (h2c_pm_wb_bresp  ),
      .h2c_wb_pm_bready    (h2c_wb_pm_bready )

      );
   
   // C2H
   if (H2C_ONLY == 0)
     begin
        sde_c2h 
          #(.C2H_DESC_TYPE      (C2H_DESC_TYPE),
            .C2H_DESC_WIDTH     (C2H_DESC_WIDTH),
            
            .C2H_DESC_RAM_DEPTH (C2H_DESC_RAM_DEPTH),
            .C2H_PCIM_DM_AWID   (C2H_PCIM_DM_AWID),
            .C2H_PCIM_WB_AWID   (C2H_PCIM_WB_AWID),
            .C2H_PCIM_DESC_ARID (C2H_PCIM_DESC_ARID),
            
            .C2H_PCIM_MAX_WR_SIZE (C2H_PCIM_MAX_WR_SIZE),

            .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
            .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
            .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
            .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),
           
            .C2H_AXIS_DATA_WIDTH (C2H_AXIS_DATA_WIDTH),
            .C2H_USER_BIT_WIDTH  (C2H_USER_BIT_WIDTH),
            .C2H_BUF_DEPTH       (C2H_BUF_DEPTH)
            )
        SDE_C2H
          (.clk                 (clk),
           .rst_n               (c2h_sync_rst_n),

           .c2h_ps_desc_wr_req  (c2h_ps_desc_wr_req),
           .c2h_ps_desc_wdata   (c2h_ps_desc_wdata ),
           .c2h_ps_desc_ack     (c2h_ps_desc_ack   ),
           
           .c2h_ps_cfg_wr_req   (c2h_ps_cfg_wr_req),
           .c2h_ps_cfg_rd_req   (c2h_ps_cfg_rd_req),
           .c2h_ps_cfg_addr     (c2h_ps_cfg_addr  ),
           .c2h_ps_cfg_wdata    (c2h_ps_cfg_wdata ),
           .c2h_ps_cfg_ack      (c2h_ps_cfg_ack   ),
           .c2h_ps_cfg_rdata    (c2h_ps_cfg_rdata ),
           
           .c2h_desc_ooo_error    (c2h_desc_ooo_error),
           .c2h_desc_unalin_error (c2h_desc_unalin_error),

           .c2h_desc_pm_arvalid (c2h_desc_pm_arvalid),
           .c2h_desc_pm_araddr  (c2h_desc_pm_araddr ),
           .c2h_desc_pm_arlen   (c2h_desc_pm_arlen  ),
           .c2h_pm_desc_arready (c2h_pm_desc_arready),
           .c2h_pm_desc_rvalid  (c2h_pm_desc_rvalid),
           .c2h_pm_desc_rresp   (c2h_pm_desc_rresp ),
           .c2h_pm_desc_rdata   (c2h_pm_desc_rdata ),
           .c2h_pm_desc_rlast   (c2h_pm_desc_rlast ),
           .c2h_desc_pm_rready  (c2h_desc_pm_rready),

           .c2h_dm_pm_awvalid   (c2h_dm_pm_awvalid),
           .c2h_dm_pm_awaddr    (c2h_dm_pm_awaddr ),
           .c2h_dm_pm_awlen     (c2h_dm_pm_awlen  ),
           .c2h_dm_pm_awid      (c2h_dm_pm_awid   ),
           .c2h_pm_dm_awready   (c2h_pm_dm_awready),
           .c2h_dm_pm_wvalid    (c2h_dm_pm_wvalid ),
           .c2h_dm_pm_wdata     (c2h_dm_pm_wdata  ),
           .c2h_dm_pm_wstrb     (c2h_dm_pm_wstrb  ),
           .c2h_dm_pm_wlast     (c2h_dm_pm_wlast  ),
           .c2h_pm_dm_wready    (c2h_pm_dm_wready ),
           .c2h_pm_dm_bvalid    (c2h_pm_dm_bvalid ),
           .c2h_pm_dm_bresp     (c2h_pm_dm_bresp  ),
           .c2h_dm_pm_bready    (c2h_dm_pm_bready ),

           
           .c2h_wb_pm_awvalid   (c2h_wb_pm_awvalid),
           .c2h_wb_pm_awaddr    (c2h_wb_pm_awaddr ),
           .c2h_wb_pm_awlen     (c2h_wb_pm_awlen  ),
           .c2h_wb_pm_awid      (c2h_wb_pm_awid   ),
           .c2h_pm_wb_awready   (c2h_pm_wb_awready),
           .c2h_wb_pm_wvalid    (c2h_wb_pm_wvalid ),
           .c2h_wb_pm_wdata     (c2h_wb_pm_wdata  ),
           .c2h_wb_pm_wstrb     (c2h_wb_pm_wstrb  ),
           .c2h_wb_pm_wlast     (c2h_wb_pm_wlast  ),
           .c2h_pm_wb_wready    (c2h_pm_wb_wready ),
           .c2h_pm_wb_bvalid    (c2h_pm_wb_bvalid ),
           .c2h_pm_wb_bresp     (c2h_pm_wb_bresp  ),
           .c2h_wb_pm_bready    (c2h_wb_pm_bready ),

           .c2h_axis_valid      (c2h_axis_valid ),
           .c2h_axis_data       (c2h_axis_data  ), 
           .c2h_axis_keep       (c2h_axis_keep  ), 
           .c2h_axis_user       (c2h_axis_user  ), 
           .c2h_axis_last       (c2h_axis_last  ),  
           .c2h_axis_ready      (c2h_axis_ready )

           );
     end // if (H2C_ONLY == 0)
   else begin
      assign 
        c2h_ps_desc_ack = 1'b1,
        c2h_ps_cfg_ack = 1'b1,
        c2h_ps_cfg_rdata = 32'd00,
        c2h_desc_pm_arvalid = 1'b0,
        c2h_desc_pm_rready = 1'b1,
        c2h_dm_pm_awvalid = 1'b0,
        c2h_dm_pm_wvalid = 1'b0,
        c2h_dm_pm_bready = 1'b1,
        c2h_axis_ready = 1'b0;
   end // else: !if(H2C_ONLY == 0)
   
   // H2C
   if (C2H_ONLY == 0) begin
      sde_h2c 
        #(.H2C_DESC_TYPE      (H2C_DESC_TYPE),
          .H2C_DESC_RAM_DEPTH (H2C_DESC_RAM_DEPTH),
          .H2C_PCIM_DM_ARID   (H2C_PCIM_DM_ARID),
          .H2C_PCIM_WB_AWID   (H2C_PCIM_WB_AWID),
          .H2C_PCIM_DESC_ARID (H2C_PCIM_DESC_ARID),

          .PCIM_NUM_OT_RD  (PCIM_NUM_OT_RD  ),
          .H2C_PCIM_MAX_RD_SIZE (H2C_PCIM_MAX_RD_SIZE),
          
          .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
          .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
          .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
          .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),
         
          .H2C_AXIS_DATA_WIDTH (H2C_AXIS_DATA_WIDTH),
          .H2C_USER_BIT_WIDTH  (H2C_USER_BIT_WIDTH),
          .H2C_BUF_DEPTH       (H2C_BUF_DEPTH)
          )
      SDE_H2C
        (.clk                 (clk),
         .rst_n               (h2c_sync_rst_n),

         .h2c_ps_desc_wr_req  (h2c_ps_desc_wr_req),
         .h2c_ps_desc_wdata   (h2c_ps_desc_wdata ),
         .h2c_ps_desc_ack     (h2c_ps_desc_ack   ),
         
         .h2c_ps_cfg_wr_req   (h2c_ps_cfg_wr_req),
         .h2c_ps_cfg_rd_req   (h2c_ps_cfg_rd_req),
         .h2c_ps_cfg_addr     (h2c_ps_cfg_addr  ),
         .h2c_ps_cfg_wdata    (h2c_ps_cfg_wdata ),
         .h2c_ps_cfg_ack      (h2c_ps_cfg_ack   ),
         .h2c_ps_cfg_rdata    (h2c_ps_cfg_rdata ),
         
         .h2c_desc_ooo_error    (h2c_desc_ooo_error),
         .h2c_desc_unalin_error (h2c_desc_unalin_error),

         .h2c_desc_pm_arvalid (h2c_desc_pm_arvalid),
         .h2c_desc_pm_araddr  (h2c_desc_pm_araddr ),
         .h2c_desc_pm_arlen   (h2c_desc_pm_arlen  ),
         .h2c_pm_desc_arready (h2c_pm_desc_arready),
         .h2c_pm_desc_rvalid  (h2c_pm_desc_rvalid),
         .h2c_pm_desc_rresp   (h2c_pm_desc_rresp ),
         .h2c_pm_desc_rdata   (h2c_pm_desc_rdata ),
         .h2c_pm_desc_rlast   (h2c_pm_desc_rlast ),
         .h2c_desc_pm_rready  (h2c_desc_pm_rready),

         .h2c_dm_pm_arvalid   (h2c_dm_pm_arvalid),
         .h2c_dm_pm_araddr    (h2c_dm_pm_araddr ),
         .h2c_dm_pm_arlen     (h2c_dm_pm_arlen  ),
         .h2c_dm_pm_arid      (h2c_dm_pm_arid   ),
         .h2c_pm_dm_arready   (h2c_pm_dm_arready),
         .h2c_pm_dm_rvalid    (h2c_pm_dm_rvalid ),
         .h2c_pm_dm_rresp     (h2c_pm_dm_rresp  ),
         .h2c_pm_dm_rdata     (h2c_pm_dm_rdata  ),
         .h2c_pm_dm_rlast     (h2c_pm_dm_rlast  ),
         .h2c_dm_pm_rready    (h2c_dm_pm_rready ),
         
         .h2c_wb_pm_awvalid   (h2c_wb_pm_awvalid),
         .h2c_wb_pm_awaddr    (h2c_wb_pm_awaddr ),
         .h2c_wb_pm_awlen     (h2c_wb_pm_awlen  ),
         .h2c_wb_pm_awid      (h2c_wb_pm_awid   ),
         .h2c_pm_wb_awready   (h2c_pm_wb_awready),
         .h2c_wb_pm_wvalid    (h2c_wb_pm_wvalid ),
         .h2c_wb_pm_wdata     (h2c_wb_pm_wdata  ),
         .h2c_wb_pm_wstrb     (h2c_wb_pm_wstrb  ),
         .h2c_wb_pm_wlast     (h2c_wb_pm_wlast  ),
         .h2c_pm_wb_wready    (h2c_pm_wb_wready ),
         .h2c_pm_wb_bvalid    (h2c_pm_wb_bvalid ),
         .h2c_pm_wb_bresp     (h2c_pm_wb_bresp  ),
         .h2c_wb_pm_bready    (h2c_wb_pm_bready ),

         .h2c_axis_valid      (h2c_axis_valid),
         .h2c_axis_data       (h2c_axis_data ), 
         .h2c_axis_keep       (h2c_axis_keep ), 
         .h2c_axis_user       (h2c_axis_user ), 
         .h2c_axis_last       (h2c_axis_last ), 
         .h2c_axis_ready      (h2c_axis_ready)

         );
   end // if (C2H_ONLY == 0)
   else begin
      assign 
        h2c_ps_desc_ack = 1'b1,
        h2c_ps_cfg_ack = 1'b1,
        h2c_ps_cfg_rdata = 32'd0,
        h2c_desc_pm_arvalid = 1'b0,
        h2c_desc_pm_rready = 1'b1,
        h2c_dm_pm_arvalid = 1'b0,
        h2c_dm_pm_rready = 1'b1,
        h2c_axis_valid = 1'b0;
   end // else: !if(C2H_ONLY == 0)
   
`ifndef NO_SDE_DEBUG_ILA

//    ila_axi4_wrapper #(.AXI_DATA_WIDTH(32)) PCIS_AXI4_ILA
//      (.aclk         (clk),
//       .trig_disable (1'b0),
//       .ila_awid     (pcis_awid   ),
//       .ila_awaddr   (pcis_awaddr ),
//       .ila_awvalid  (pcis_awvalid),
//       .ila_awready  (pcis_awready),
//       .ila_awlen    (pcis_awlen  ),
//       .ila_awsize   (pcis_awsize ),
//       .ila_wvalid   (pcis_wvalid ),
//       .ila_wready   (pcis_wready ),
//       .ila_wdata    (pcis_wdata  ),
//       .ila_wstrb    (pcis_wstrb  ),
//       .ila_wlast    (pcis_wlast  ),
//       .ila_bid      (pcis_bid    ),
//       .ila_bvalid   (pcis_bvalid ),
//       .ila_bready   (pcis_bready ),
//       .ila_bresp    (pcis_bresp  ),
//       .ila_arid     (pcis_arid   ),
//       .ila_araddr   (pcis_araddr ),
//       .ila_arvalid  (pcis_arvalid),
//       .ila_arready  (pcis_arready),
//       .ila_arlen    (pcis_arlen  ),
//       .ila_arsize   (pcis_arsize ),
//       .ila_rid      (pcis_rid    ),
//       .ila_rvalid   (pcis_rvalid ),
//       .ila_rready   (pcis_rready ),
//       .ila_rdata    (pcis_rdata  ),
//       .ila_rresp    (pcis_rresp  ),
//       .ila_rlast    (pcis_rlast  )
//       );
// 
//    ila_axi4_wrapper #(.AXI_DATA_WIDTH(32)) PCIM_AXI4_ILA
//      (.aclk         (clk),
//       .trig_disable (1'b0),
//       .ila_awid     (pcim_awid   ),
//       .ila_awaddr   (pcim_awaddr ),
//       .ila_awvalid  (pcim_awvalid),
//       .ila_awready  (pcim_awready),
//       .ila_awlen    (pcim_awlen  ),
//       .ila_awsize   (pcim_awsize ),
//       .ila_wvalid   (pcim_wvalid ),
//       .ila_wready   (pcim_wready ),
//       .ila_wdata    (pcim_wdata  ),
//       .ila_wstrb    (pcim_wstrb  ),
//       .ila_wlast    (pcim_wlast  ),
//       .ila_bid      (pcim_bid    ),
//       .ila_bvalid   (pcim_bvalid ),
//       .ila_bready   (pcim_bready ),
//       .ila_bresp    (pcim_bresp  ),
//       .ila_arid     (pcim_arid   ),
//       .ila_araddr   (pcim_araddr ),
//       .ila_arvalid  (pcim_arvalid),
//       .ila_arready  (pcim_arready),
//       .ila_arlen    (pcim_arlen  ),
//       .ila_arsize   (pcim_arsize ),
//       .ila_rid      (pcim_rid    ),
//       .ila_rvalid   (pcim_rvalid ),
//       .ila_rready   (pcim_rready ),
//       .ila_rdata    (pcim_rdata  ),
//       .ila_rresp    (pcim_rresp  ),
//       .ila_rlast    (pcim_rlast  )
//       );   

   ila_axis C2H_AXIS_ILA
     (.clk (clk),
      .probe0 (c2h_axis_valid),
      .probe1 (c2h_axis_last),
      .probe2 (c2h_axis_keep),
      .probe3 (c2h_axis_data),
      .probe4 (c2h_axis_user),
      .probe5 (c2h_axis_ready)
      );
   
   ila_axis H2C_AXIS_ILA
     (.clk (clk),
      .probe0 (h2c_axis_valid),
      .probe1 (h2c_axis_last),
      .probe2 (h2c_axis_keep),
      .probe3 (h2c_axis_data),
      .probe4 (h2c_axis_user),
      .probe5 (h2c_axis_ready)
      );
   
`endif //  `ifndef NO_SDE_DEBUG_ILA
   
   
      
endmodule // sde

   

   
