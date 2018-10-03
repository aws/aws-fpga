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


// C2H Top level

module sde_c2h #(parameter bit C2H_DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
                 parameter C2H_DESC_WIDTH = 128,
                 
                 parameter C2H_DESC_RAM_DEPTH = 64,
                 
                 parameter C2H_PCIM_DM_AWID = 0, // This is the AWID used for write accesses from Data Mover
                 parameter C2H_PCIM_WB_AWID = 1, // This is the AWID used for write accesses from Write Back Block
                 parameter C2H_PCIM_DESC_ARID = 2, // This is the ARID used for read access from the C2H Desc Block

                 parameter C2H_PCIM_MAX_WR_SIZE = 3, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB

                 parameter PCIM_DATA_WIDTH = 512,
                 parameter PCIM_ID_WIDTH = 3,
                 parameter PCIM_LEN_WIDTH = 8,
                 parameter PCIM_ADDR_WIDTH = 64,

                 parameter C2H_AXIS_DATA_WIDTH = 512,
                 parameter C2H_USER_BIT_WIDTH = C2H_DESC_TYPE ? 1 : 64,
                 
                 parameter C2H_BUF_DEPTH = 512

                 )

   (

    input                                   clk,
    input                                   rst_n,

    // PCIS to C2H Descriptor
    input                                   c2h_ps_desc_wr_req,
    input [C2H_DESC_WIDTH-1:0]              c2h_ps_desc_wdata,
    output logic                            c2h_ps_desc_ack,
    
    // PCIS to C2H CSR
    input                                   c2h_ps_cfg_wr_req,
    input                                   c2h_ps_cfg_rd_req,
    input [15:0]                            c2h_ps_cfg_addr,
    input [31:0]                            c2h_ps_cfg_wdata,
    output logic                            c2h_ps_cfg_ack,
    output logic [31:0]                     c2h_ps_cfg_rdata,

    input                                   c2h_desc_ooo_error,
    input                                   c2h_desc_unalin_error,

     // C2H Descriptor to PCIM Interface
     // Read Address to PCIM
    output logic                            c2h_desc_pm_arvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      c2h_desc_pm_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]       c2h_desc_pm_arlen,
    input                                   c2h_pm_desc_arready,

    // Read Data from PCIM
    input                                   c2h_pm_desc_rvalid,
    input [1:0]                             c2h_pm_desc_rresp,
    input [PCIM_DATA_WIDTH-1:0]             c2h_pm_desc_rdata,
    input                                   c2h_pm_desc_rlast,
    output logic                            c2h_desc_pm_rready,

     // C2H Data Mover to PCIM Interface
     // Write Address to PCIM
    output logic                            c2h_dm_pm_awvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      c2h_dm_pm_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]       c2h_dm_pm_awlen,
    output logic [PCIM_ID_WIDTH-1:0]        c2h_dm_pm_awid,
    input                                   c2h_pm_dm_awready,
    
     // Write Data to PCIM
    output logic                            c2h_dm_pm_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]      c2h_dm_pm_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] c2h_dm_pm_wstrb,
    output logic                            c2h_dm_pm_wlast,
    input                                   c2h_pm_dm_wready,

     // Bresp from PCIM
    input                                   c2h_pm_dm_bvalid,
    input [1:0]                             c2h_pm_dm_bresp,
    output logic                            c2h_dm_pm_bready,

     // C2H Write-Back Block to PCIM Interface
     // Write Address to PCIM
    output logic                            c2h_wb_pm_awvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      c2h_wb_pm_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]       c2h_wb_pm_awlen,
    output logic [PCIM_ID_WIDTH-1:0]        c2h_wb_pm_awid,
    input                                   c2h_pm_wb_awready,
    
    // Write Data to PCIM
    output logic                            c2h_wb_pm_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]      c2h_wb_pm_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] c2h_wb_pm_wstrb,
    output logic                            c2h_wb_pm_wlast,
    input                                   c2h_pm_wb_wready,

    // Bresp from PCIM
    input                                   c2h_pm_wb_bvalid,
    input [1:0]                             c2h_pm_wb_bresp,
    output logic                            c2h_wb_pm_bready,

    // C2H AXI-Stream Interface
    input                                   c2h_axis_valid,
    input [C2H_AXIS_DATA_WIDTH-1:0]         c2h_axis_data,
    input [(C2H_AXIS_DATA_WIDTH>>3)-1:0]    c2h_axis_keep,
    input [C2H_USER_BIT_WIDTH-1:0]          c2h_axis_user,
    input                                   c2h_axis_last,
    output logic                            c2h_axis_ready    

    );

   localparam PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3);
   localparam BUF_ADDR_RAM_IDX_WIDTH = $clog2(C2H_BUF_DEPTH);
   localparam BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH;
   localparam BUF_AUX_WIDTH = BUF_ADDR_WIDTH + C2H_USER_BIT_WIDTH;
   

   // Signals
   logic                                    desc_dm_empty;
   logic                                    dm_desc_pop;
   sde_pkg::comm_desc_t desc_dm_desc;
   logic                                    desc_dm_desc_valid;

   logic                                    dm_desc_cnt_inc;
   
   // Descriptor to Write Back Block
   logic                                    desc_wb_limit_req;
   logic [31:0]                             desc_wb_limit;
   logic                                    desc_wb_cnt_req;
   logic [31:0]                             desc_wb_cnt;

   logic                                    dm_wb_md_req;
   sde_pkg::c2h_reg_wb_t                    dm_wb_md;
   logic                                    wb_dm_md_grant;
   
   // Data Mover to Buffer 
   logic                                    buf_dm_aux_valid;
   logic [BUF_AUX_WIDTH-1:0]                buf_dm_aux_data;
   logic                                    dm_buf_aux_pop;
   
   logic [BUF_ADDR_WIDTH-1:0]               dm_buf_rd_byte_addr;

   logic [BUF_ADDR_WIDTH:0]                 buf_dm_num_bytes; // Difference in pointers + plus num of bytes in last beat
   
   logic                                    dm_buf_rd;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]       dm_buf_addr;
   logic [PCIM_DATA_WIDTH-1:0]              buf_dm_data;

   logic                                    axis_buf_valid;
   logic [PCIM_DATA_WIDTH-1:0]              axis_buf_data;
   logic [(PCIM_DATA_WIDTH>>3)-1:0]         axis_buf_keep;
   logic [C2H_USER_BIT_WIDTH-1:0]           axis_buf_user;
   logic                                    axis_buf_last;
   logic                                    buf_axis_ready;
    
   logic                                    axis_wb_pkt_cnt_req;
   logic [31:0]                             axis_wb_pkt_cnt;

   // Cfg block signals
   logic                                    cfg_desc_clr_desc_cnt;
   logic                                    cfg_desc_clr_cdt_limit;
   logic                                    cfg_desc_clr_cdt_consumed;

   logic [31:0]                             desc_cfg_cdt_consumed;
   logic [31:0]                             desc_cfg_cdt_limit;
   logic [31:0]                             desc_cfg_desc_cnt;
   logic [15:0]                             desc_cfg_wr_ptr;
   logic [15:0]                             desc_cfg_rd_ptr;

   logic                                    cfg_desc_ram_wr_req;
   logic                                    cfg_desc_ram_rd_req;
   logic [15:0]                             cfg_desc_ram_addr  ;
   logic [C2H_DESC_WIDTH-1:0]               cfg_desc_ram_wdata ;
   logic                                    desc_cfg_ram_ack   ;
   logic [C2H_DESC_WIDTH-1:0]               desc_cfg_ram_rdata ;
      
   logic                                    dm_cfg_bresp_err;
   logic                                    dm_cfg_desc_len_err;
   
   logic                                    cfg_wb_desc_cdt_en;
   logic                                    cfg_wb_desc_cnt_en;
   logic                                    cfg_wb_pkt_cnt_en;
   logic                                    cfg_wb_md_ptr_en;
   logic [47:0]                             cfg_wb_status_addr;
   logic [47:0]                             cfg_wb_md_ring_addr;
   logic [31:0]                             cfg_wb_md_ring_size;
   logic [15:0]                             cfg_wb_md_rd_ptr;
   logic [15:0]                             wb_cfg_md_wr_ptr;
   logic                                    cfg_wb_clr_wr_ptr;
   
   logic                                    cfg_wb_desc_error; 
   logic                                    cfg_wb_dm_error  ; 
   logic                                    cfg_wb_wb_error  ;
   logic [31:0]                             wb_cfg_status_dw ;
   
   logic                                    cfg_desc_cdt_wc_en;
   logic                                    cfg_desc_cnt_wc_en;
   logic                                    cfg_pkt_cnt_wc_en;
   logic                                    cfg_md_wr_ptr_wc_en;
   logic [19:0]                             cfg_wc_tick_cnt;
   logic [3:0]                              cfg_wc_to_cnt;
   logic [5:0]                              cfg_wc_cnt_minus1;
         
   logic                                    cfg_axis_clr_pkt_cnt;
   logic [31:0]                             axis_cfg_pkt_cnt;
  
   logic                                    dm_num_beats_err;

   logic                                    desc_cfg_oflow;
   logic                                    desc_cfg_uflow;
   logic                                    desc_cfg_full ;
   logic                                    desc_cfg_empty;

   logic                                    wb_cfg_md_bresp_err ;
   logic                                    wb_cfg_sts_bresp_err;
   
   logic                                    buf_cfg_buf_oflow;
   logic                                    buf_cfg_buf_uflow;
   logic                                    buf_cfg_buf_full;
   logic                                    buf_cfg_buf_empty;
   logic [15:0]                             buf_cfg_buf_wr_ptr ;
   logic [15:0]                             buf_cfg_buf_rd_addr;
   logic                                    buf_cfg_aux_fifo_oflow;
   logic                                    buf_cfg_aux_fifo_uflow;
   logic                                    buf_cfg_aux_fifo_full ; 
   logic                                    buf_cfg_aux_fifo_empty;
   logic [15:0]                             buf_cfg_aux_ram_wr_ptr;
   logic [15:0]                             buf_cfg_aux_ram_rd_ptr; 
   logic [15:0]                             buf_cfg_num_bytes;
   logic [31:0]                             buf_cfg_in_pkt_cnt;
   logic [31:0]                             buf_cfg_out_pkt_cnt;
   logic                                    cfg_buf_clr_in_pkt_cnt;
   logic                                    cfg_buf_clr_out_pkt_cnt;
   
   // Generate local copy of Reset
   logic                                    sync_rst_n;
   always @(posedge clk)
     if (!rst_n) 
       sync_rst_n <= 0;
     else
       sync_rst_n <= rst_n;
   
   // C2H CSR Block
   sde_c2h_cfg #(
       .DESC_TYPE       (C2H_DESC_TYPE),
       .DESC_RAM_DEPTH  (C2H_DESC_RAM_DEPTH),
       .DESC_WIDTH      (C2H_DESC_WIDTH)
       )
   SDE_C2H_CFG
     (.clk                (clk),
      .rst_n              (sync_rst_n),
      
      .c2h_ps_cfg_wr_req  (c2h_ps_cfg_wr_req),
      .c2h_ps_cfg_rd_req  (c2h_ps_cfg_rd_req),
      .c2h_ps_cfg_addr    (c2h_ps_cfg_addr  ),
      .c2h_ps_cfg_wdata   (c2h_ps_cfg_wdata ),
      .c2h_ps_cfg_ack     (c2h_ps_cfg_ack   ),
      .c2h_ps_cfg_rdata   (c2h_ps_cfg_rdata ),

      .desc_ooo_error        (c2h_desc_ooo_error),
      .desc_unalin_error     (c2h_desc_unalin_error),

      .cfg_desc_clr_desc_cnt     (cfg_desc_clr_desc_cnt    ),
      .cfg_desc_clr_cdt_limit    (cfg_desc_clr_cdt_limit   ),
      .cfg_desc_clr_cdt_consumed (cfg_desc_clr_cdt_consumed),
      
      .desc_cfg_cdt_consumed (desc_cfg_cdt_consumed),
      .desc_cfg_cdt_limit    (desc_cfg_cdt_limit   ),
      .desc_cfg_desc_cnt     (desc_cfg_desc_cnt    ),
      .desc_cfg_wr_ptr       (desc_cfg_wr_ptr      ),
      .desc_cfg_rd_ptr       (desc_cfg_rd_ptr      ),
      
      .cfg_desc_ram_wr_req   (cfg_desc_ram_wr_req),
      .cfg_desc_ram_rd_req   (cfg_desc_ram_rd_req),
      .cfg_desc_ram_addr     (cfg_desc_ram_addr  ),
      .cfg_desc_ram_wdata    (cfg_desc_ram_wdata ),
      .desc_cfg_ram_ack      (desc_cfg_ram_ack   ),
      .desc_cfg_ram_rdata    (desc_cfg_ram_rdata ),
      
      .desc_cfg_oflow        (desc_cfg_oflow),
      .desc_cfg_uflow        (desc_cfg_uflow),
      .desc_cfg_full         (desc_cfg_full ),
      .desc_cfg_empty        (desc_cfg_empty),

      .dm_cfg_bresp_err      (dm_cfg_bresp_err),
      .dm_cfg_desc_len_err   (dm_cfg_desc_len_err),

      .cfg_wb_desc_cdt_en    (cfg_wb_desc_cdt_en ),
      .cfg_wb_desc_cnt_en    (cfg_wb_desc_cnt_en ),
      .cfg_wb_pkt_cnt_en     (cfg_wb_pkt_cnt_en  ),
      .cfg_wb_md_ptr_en      (cfg_wb_md_ptr_en   ),
      .cfg_wb_status_addr    (cfg_wb_status_addr ),
      .cfg_wb_md_ring_addr   (cfg_wb_md_ring_addr),
      .cfg_wb_md_ring_size   (cfg_wb_md_ring_size),
      .cfg_wb_md_rd_ptr      (cfg_wb_md_rd_ptr   ),
      .wb_cfg_md_wr_ptr      (wb_cfg_md_wr_ptr   ),
      .cfg_wb_clr_wr_ptr     (cfg_wb_clr_wr_ptr  ),
      
      .cfg_desc_cdt_wc_en    (cfg_desc_cdt_wc_en ),
      .cfg_desc_cnt_wc_en    (cfg_desc_cnt_wc_en ),
      .cfg_pkt_cnt_wc_en     (cfg_pkt_cnt_wc_en  ),
      .cfg_md_wr_ptr_wc_en   (cfg_md_wr_ptr_wc_en),
      .cfg_wc_tick_cnt       (cfg_wc_tick_cnt    ),
      .cfg_wc_to_cnt         (cfg_wc_to_cnt      ),
      .cfg_wc_cnt_minus1     (cfg_wc_cnt_minus1  ),

      .wb_cfg_md_bresp_err   (wb_cfg_md_bresp_err),
      .wb_cfg_sts_bresp_err  (wb_cfg_sts_bresp_err), 

      .cfg_wb_desc_error     (cfg_wb_desc_error), 
      .cfg_wb_dm_error       (cfg_wb_dm_error  ), 
      .cfg_wb_wb_error       (cfg_wb_wb_error  ),
      .wb_cfg_status_dw      (wb_cfg_status_dw ),
      
      .buf_cfg_buf_oflow       (buf_cfg_buf_oflow      ),
      .buf_cfg_buf_uflow       (buf_cfg_buf_uflow      ),
      .buf_cfg_buf_full        (buf_cfg_buf_full       ),
      .buf_cfg_buf_empty       (buf_cfg_buf_empty      ),
      .buf_cfg_buf_wr_ptr      (buf_cfg_buf_wr_ptr     ),
      .buf_cfg_buf_rd_addr     (buf_cfg_buf_rd_addr    ),
      .buf_cfg_aux_fifo_oflow  (buf_cfg_aux_fifo_oflow ),
      .buf_cfg_aux_fifo_uflow  (buf_cfg_aux_fifo_uflow ),
      .buf_cfg_aux_fifo_full   (buf_cfg_aux_fifo_full  ), 
      .buf_cfg_aux_fifo_empty  (buf_cfg_aux_fifo_empty ),
      .buf_cfg_aux_ram_wr_ptr  (buf_cfg_aux_ram_wr_ptr ),
      .buf_cfg_aux_ram_rd_ptr  (buf_cfg_aux_ram_rd_ptr ), 
      .buf_cfg_num_bytes       (buf_cfg_num_bytes      ),
      .buf_cfg_in_pkt_cnt      (buf_cfg_in_pkt_cnt     ),
      .buf_cfg_out_pkt_cnt     (buf_cfg_out_pkt_cnt    ),
      .cfg_buf_clr_in_pkt_cnt  (cfg_buf_clr_in_pkt_cnt ),
      .cfg_buf_clr_out_pkt_cnt (cfg_buf_clr_out_pkt_cnt),
         
      .cfg_axis_clr_pkt_cnt  (cfg_axis_clr_pkt_cnt),
      .axis_cfg_pkt_cnt      (axis_cfg_pkt_cnt    )

      );
      

   // C2H Descriptor
   sde_desc 
     #(.H2C_N_C2H       (0),
       
       .DESC_TYPE       (C2H_DESC_TYPE),
       .DESC_WIDTH      (C2H_DESC_WIDTH), 
       .DESC_RAM_DEPTH  (C2H_DESC_RAM_DEPTH),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),

       .PCIM_DESC_ARID  (C2H_PCIM_DESC_ARID)
       ) 
   SDE_C2H_DESC 
     (.clk                (clk),
      .rst_n              (sync_rst_n),
      
      .ps_desc_wr_req     (c2h_ps_desc_wr_req),
      .ps_desc_wdata      (c2h_ps_desc_wdata),
      .ps_desc_ack        (c2h_ps_desc_ack),
      
      .cfg_desc_ram_wr_req       (cfg_desc_ram_wr_req),
      .cfg_desc_ram_rd_req       (cfg_desc_ram_rd_req),
      .cfg_desc_ram_addr         (cfg_desc_ram_addr  ),
      .cfg_desc_ram_wdata        (cfg_desc_ram_wdata ),
      .desc_cfg_ram_ack          (desc_cfg_ram_ack   ),
      .desc_cfg_ram_rdata        (desc_cfg_ram_rdata ),
      
      .cfg_desc_clr_desc_cnt     (cfg_desc_clr_desc_cnt    ),
      .cfg_desc_clr_cdt_limit    (cfg_desc_clr_cdt_limit   ),
      .cfg_desc_clr_cdt_consumed (cfg_desc_clr_cdt_consumed),
      
      .desc_cfg_cdt_consumed (desc_cfg_cdt_consumed),
      .desc_cfg_cdt_limit    (desc_cfg_cdt_limit   ),
      .desc_cfg_desc_cnt     (desc_cfg_desc_cnt    ),
      .desc_cfg_wr_ptr       (desc_cfg_wr_ptr      ),
      .desc_cfg_rd_ptr       (desc_cfg_rd_ptr      ),

      .desc_cfg_oflow        (desc_cfg_oflow),
      .desc_cfg_uflow        (desc_cfg_uflow),
      .desc_cfg_full         (desc_cfg_full ),
      .desc_cfg_empty        (desc_cfg_empty),

      .desc_dm_empty      (desc_dm_empty),
      .dm_desc_pop        (dm_desc_pop),
      .desc_dm_desc       (desc_dm_desc),
      .desc_dm_desc_valid (desc_dm_desc_valid),

      .dm_desc_cnt_inc    (dm_desc_cnt_inc),
      
      .desc_wb_limit_req  (desc_wb_limit_req), 
      .desc_wb_limit      (desc_wb_limit),
      .desc_wb_cnt_req    (desc_wb_cnt_req),
      .desc_wb_cnt        (desc_wb_cnt),

      .desc_pm_arvalid    (c2h_desc_pm_arvalid),
      .desc_pm_araddr     (c2h_desc_pm_araddr ),
      .desc_pm_arlen      (c2h_desc_pm_arlen  ),
      .pm_desc_arready    (c2h_pm_desc_arready),
      
      .pm_desc_rvalid     (c2h_pm_desc_rvalid),
      .pm_desc_rresp      (c2h_pm_desc_rresp ),
      .pm_desc_rdata      (c2h_pm_desc_rdata ),
      .pm_desc_rlast      (c2h_pm_desc_rlast ),
      .desc_pm_rready     (c2h_desc_pm_rready)

      );
   
   // C2H Data Mover
   sde_c2h_data 
     #(.DESC_TYPE       (C2H_DESC_TYPE),
       
       .PCIM_DM_AWID    (C2H_PCIM_DM_AWID),
       
       .PCIM_MAX_WR_SIZE (C2H_PCIM_MAX_WR_SIZE),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),
       
       .BUF_DEPTH       (C2H_BUF_DEPTH),
       
       .USER_BIT_WIDTH  (C2H_USER_BIT_WIDTH)
       )
   SDE_C2H_DATA 
     (.clk                   (clk),
      .rst_n                (sync_rst_n),

      // TODO CSRs
      .dm_cfg_bresp_err     (dm_cfg_bresp_err),
      .dm_cfg_desc_len_err  (dm_cfg_desc_len_err),
      .dm_num_beats_err     (dm_num_beats_err),
      
      .desc_dm_empty        (desc_dm_empty),
      .dm_desc_pop          (dm_desc_pop),
      .desc_dm_desc         (desc_dm_desc),
      .desc_dm_desc_valid   (desc_dm_desc_valid),

      .dm_desc_cnt_inc      (dm_desc_cnt_inc),
      
      .dm_pm_awvalid        (c2h_dm_pm_awvalid),
      .dm_pm_awaddr         (c2h_dm_pm_awaddr ),
      .dm_pm_awlen          (c2h_dm_pm_awlen  ),
      .dm_pm_awid           (c2h_dm_pm_awid   ),
      .pm_dm_awready        (c2h_pm_dm_awready),
      .dm_pm_wvalid         (c2h_dm_pm_wvalid ),
      .dm_pm_wdata          (c2h_dm_pm_wdata  ),
      .dm_pm_wstrb          (c2h_dm_pm_wstrb  ),
      .dm_pm_wlast          (c2h_dm_pm_wlast  ),
      .pm_dm_wready         (c2h_pm_dm_wready ),
      .pm_dm_bvalid         (c2h_pm_dm_bvalid ),
      .pm_dm_bresp          (c2h_pm_dm_bresp  ),
      .dm_pm_bready         (c2h_dm_pm_bready ),

      .dm_wb_md_req         (dm_wb_md_req),
      .dm_wb_md             (dm_wb_md),
      .wb_dm_md_grant       (wb_dm_md_grant),

      .buf_dm_aux_valid     (buf_dm_aux_valid),
      .buf_dm_aux_data      (buf_dm_aux_data),
      .dm_buf_aux_pop       (dm_buf_aux_pop),

      .dm_buf_rd_byte_addr  (dm_buf_rd_byte_addr),
      .buf_dm_num_bytes     (buf_dm_num_bytes),

      .dm_buf_rd            (dm_buf_rd),
      .dm_buf_addr          (dm_buf_addr),
      .buf_dm_data          (buf_dm_data)
      );
      
   // C2H Write-Back
   sde_wb
     #(.H2C_N_C2H       (0),
       .DESC_TYPE       (C2H_DESC_TYPE),

       .DESC_RAM_DEPTH  (C2H_DESC_RAM_DEPTH),
       .PCIM_WB_AWID    (C2H_PCIM_WB_AWID),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH )
       )
   SDE_C2H_WB
     (.clk                   (clk),
      .rst_n                 (sync_rst_n),

      .cfg_wb_desc_cdt_en    (cfg_wb_desc_cdt_en),
      .cfg_wb_desc_cnt_en    (cfg_wb_desc_cnt_en),
      .cfg_wb_pkt_cnt_en     (cfg_wb_pkt_cnt_en ),
      .cfg_wb_md_ptr_en      (cfg_wb_md_ptr_en  ),
      .cfg_wb_status_addr    (cfg_wb_status_addr),
      .cfg_wb_md_ring_addr   (cfg_wb_md_ring_addr),
      .cfg_wb_md_ring_size   (cfg_wb_md_ring_size),
      .cfg_wb_md_rd_ptr      (cfg_wb_md_rd_ptr   ),
      .wb_cfg_md_wr_ptr      (wb_cfg_md_wr_ptr   ),
      .cfg_wb_clr_wr_ptr     (cfg_wb_clr_wr_ptr  ),
      
      .cfg_desc_cdt_wc_en    (cfg_desc_cdt_wc_en ),
      .cfg_desc_cnt_wc_en    (cfg_desc_cnt_wc_en ),
      .cfg_pkt_cnt_wc_en     (cfg_pkt_cnt_wc_en  ),
      .cfg_md_wr_ptr_wc_en   (cfg_md_wr_ptr_wc_en),
      .cfg_wc_tick_cnt       (cfg_wc_tick_cnt    ),
      .cfg_wc_to_cnt         (cfg_wc_to_cnt      ),
      .cfg_wc_cnt_minus1     (cfg_wc_cnt_minus1  ),
         
      .cfg_wb_desc_error     (cfg_wb_desc_error), 
      .cfg_wb_dm_error       (cfg_wb_dm_error  ), 
      .cfg_wb_wb_error       (cfg_wb_wb_error  ),
      .wb_cfg_status_dw      (wb_cfg_status_dw ),

      .wb_cfg_md_bresp_err   (wb_cfg_md_bresp_err),
      .wb_cfg_sts_bresp_err  (wb_cfg_sts_bresp_err), 

      .cfg_desc_clr_desc_cnt  (cfg_desc_clr_desc_cnt ),
      .cfg_desc_clr_cdt_limit (cfg_desc_clr_cdt_limit),
      .cfg_axis_clr_pkt_cnt   (cfg_axis_clr_pkt_cnt),
      
      .desc_wb_limit_req     (desc_wb_limit_req), 
      .desc_wb_limit         (desc_wb_limit),

      .desc_wb_cnt_req       (desc_wb_cnt_req),
      .desc_wb_cnt           (desc_wb_cnt),

      .dm_wb_md_req          (dm_wb_md_req),
      .dm_wb_md              (dm_wb_md),
      .wb_dm_md_grant        (wb_dm_md_grant),

      .axis_wb_pkt_cnt_req   (axis_wb_pkt_cnt_req),
      .axis_wb_pkt_cnt       (axis_wb_pkt_cnt),
      
      .wb_pm_awvalid         (c2h_wb_pm_awvalid),
      .wb_pm_awaddr          (c2h_wb_pm_awaddr ),
      .wb_pm_awlen           (c2h_wb_pm_awlen  ),
      .wb_pm_awid            (c2h_wb_pm_awid   ),
      .pm_wb_awready         (c2h_pm_wb_awready),
      .wb_pm_wvalid          (c2h_wb_pm_wvalid ),
      .wb_pm_wdata           (c2h_wb_pm_wdata  ),
      .wb_pm_wstrb           (c2h_wb_pm_wstrb  ),
      .wb_pm_wlast           (c2h_wb_pm_wlast  ),
      .pm_wb_wready          (c2h_pm_wb_wready ),
      .pm_wb_bvalid          (c2h_pm_wb_bvalid ),
      .pm_wb_bresp           (c2h_pm_wb_bresp  ),
      .wb_pm_bready          (c2h_wb_pm_bready )

      );
       
   // C2H Buffer
   sde_c2h_buf
     #(.DESC_TYPE       (C2H_DESC_TYPE),

       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       
       .BUF_DEPTH       (C2H_BUF_DEPTH),
       .USER_BIT_WIDTH  (C2H_USER_BIT_WIDTH)

       )
   SDE_C2H_BUF
     (.clk                 (clk),
      .rst_n               (sync_rst_n),

      // CSRs
      .buf_cfg_buf_oflow       (buf_cfg_buf_oflow      ),
      .buf_cfg_buf_uflow       (buf_cfg_buf_uflow      ),
      .buf_cfg_buf_full        (buf_cfg_buf_full       ),
      .buf_cfg_buf_empty       (buf_cfg_buf_empty      ),
      .buf_cfg_buf_wr_ptr      (buf_cfg_buf_wr_ptr     ),
      .buf_cfg_buf_rd_addr     (buf_cfg_buf_rd_addr    ),
      .buf_cfg_aux_fifo_oflow  (buf_cfg_aux_fifo_oflow ),
      .buf_cfg_aux_fifo_uflow  (buf_cfg_aux_fifo_uflow ),
      .buf_cfg_aux_fifo_full   (buf_cfg_aux_fifo_full  ), 
      .buf_cfg_aux_fifo_empty  (buf_cfg_aux_fifo_empty ),
      .buf_cfg_aux_ram_wr_ptr  (buf_cfg_aux_ram_wr_ptr ),
      .buf_cfg_aux_ram_rd_ptr  (buf_cfg_aux_ram_rd_ptr ), 
      .buf_cfg_num_bytes       (buf_cfg_num_bytes      ),
      .buf_cfg_in_pkt_cnt      (buf_cfg_in_pkt_cnt     ),
      .buf_cfg_out_pkt_cnt     (buf_cfg_out_pkt_cnt    ),
      .cfg_buf_clr_in_pkt_cnt  (cfg_buf_clr_in_pkt_cnt ),
      .cfg_buf_clr_out_pkt_cnt (cfg_buf_clr_out_pkt_cnt),
               
      .axis_buf_valid      (axis_buf_valid ), 
      .axis_buf_data       (axis_buf_data  ),  
      .axis_buf_keep       (axis_buf_keep  ),  
      .axis_buf_user       (axis_buf_user  ),  
      .axis_buf_last       (axis_buf_last  ),   
      .buf_axis_ready      (buf_axis_ready ),

      .buf_dm_aux_valid    (buf_dm_aux_valid),
      .buf_dm_aux_data     (buf_dm_aux_data),
      .dm_buf_aux_pop      (dm_buf_aux_pop),

      .dm_buf_rd_byte_addr (dm_buf_rd_byte_addr),
      .buf_dm_num_bytes    (buf_dm_num_bytes),

      .dm_buf_rd           (dm_buf_rd),
      .dm_buf_addr         (dm_buf_addr),
      .buf_dm_data         (buf_dm_data)
      );
      
   // C2H AXI-Stream Interface
   sde_c2h_axis
     #(.DESC_TYPE       (C2H_DESC_TYPE),

       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),

       .AXIS_DATA_WIDTH (C2H_AXIS_DATA_WIDTH),
       .USER_BIT_WIDTH  (C2H_USER_BIT_WIDTH)
       )
   SDE_C2H_AXIS
     (.clk                 (clk),
      .rst_n               (sync_rst_n),
                           
      .cfg_axis_clr_pkt_cnt (cfg_axis_clr_pkt_cnt),
      .axis_cfg_pkt_cnt     (axis_cfg_pkt_cnt),
                 
      .c2h_axis_valid      (c2h_axis_valid ),
      .c2h_axis_data       (c2h_axis_data  ), 
      .c2h_axis_keep       (c2h_axis_keep  ), 
      .c2h_axis_user       (c2h_axis_user  ), 
      .c2h_axis_last       (c2h_axis_last  ),  
      .c2h_axis_ready      (c2h_axis_ready ),
                           
      .axis_buf_valid      (axis_buf_valid ), 
      .axis_buf_data       (axis_buf_data  ),  
      .axis_buf_keep       (axis_buf_keep  ),  
      .axis_buf_user       (axis_buf_user  ),  
      .axis_buf_last       (axis_buf_last  ),   
      .buf_axis_ready      (buf_axis_ready ),

      .axis_wb_pkt_cnt_req (axis_wb_pkt_cnt_req),
      .axis_wb_pkt_cnt     (axis_wb_pkt_cnt)
      
      );
   

endmodule // sde_c2h




    
    
