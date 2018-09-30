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

// H2C Top Level

module sde_h2c #(parameter bit H2C_DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
                 parameter H2C_DESC_WIDTH = H2C_DESC_TYPE ? 128 : 256,
                 
                 parameter H2C_DESC_RAM_DEPTH = 64,
                 
                 parameter H2C_PCIM_DM_ARID = 0,   // This is the ARID used for write accesses from Data Mover
                 parameter H2C_PCIM_WB_AWID = 1,   // This is the AWID used for write accesses from Write Back Block
                 parameter H2C_PCIM_DESC_ARID = 2, // This is the ARID used for read access from the H2C Desc Block

                 parameter PCIM_NUM_OT_RD = 32,    // Number of outstanding PCIM reads
                 
                 parameter H2C_PCIM_MAX_RD_SIZE = 0, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB

                 parameter PCIM_DATA_WIDTH = 512,
                 parameter PCIM_ID_WIDTH = 3,
                 parameter PCIM_LEN_WIDTH = 8,
                 parameter PCIM_ADDR_WIDTH = 64,

                 parameter H2C_AXIS_DATA_WIDTH = 512,
                 parameter H2C_USER_BIT_WIDTH = H2C_DESC_TYPE ? 1 : 64,
                 
                 parameter H2C_BUF_DEPTH = 512,
                 parameter H2C_BUF_AUX_DEPTH = 64

                 )
   (
    input                                   clk,
    input                                   rst_n,

    // PCIS to H2C Descriptor
    input                                   h2c_ps_desc_wr_req,
    input [H2C_DESC_WIDTH-1:0]              h2c_ps_desc_wdata,
    output logic                            h2c_ps_desc_ack,
    
    // PCIS to H2C CSR
    input                                   h2c_ps_cfg_wr_req,
    input                                   h2c_ps_cfg_rd_req,
    input [15:0]                            h2c_ps_cfg_addr,
    input [31:0]                            h2c_ps_cfg_wdata,
    output logic                            h2c_ps_cfg_ack,
    output logic [31:0]                     h2c_ps_cfg_rdata,

    input                                   h2c_desc_ooo_error,
    input                                   h2c_desc_unalin_error,

     // H2C Descriptor to PCIM Interface
     // Read Address to PCIM
    output logic                            h2c_desc_pm_arvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      h2c_desc_pm_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]       h2c_desc_pm_arlen,
    input                                   h2c_pm_desc_arready,

    // Read Data from PCIM
    input                                   h2c_pm_desc_rvalid,
    input [1:0]                             h2c_pm_desc_rresp,
    input [PCIM_DATA_WIDTH-1:0]             h2c_pm_desc_rdata,
    input                                   h2c_pm_desc_rlast,
    output logic                            h2c_desc_pm_rready,

     // H2C Data Mover to PCIM Interface
     // Read Address to PCIM
    output logic                            h2c_dm_pm_arvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      h2c_dm_pm_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]       h2c_dm_pm_arlen,
    output logic [PCIM_ID_WIDTH-1:0]        h2c_dm_pm_arid,
    input                                   h2c_pm_dm_arready,
    
     // Read Data to PCIM
    input                                   h2c_pm_dm_rvalid,
    input [1:0]                             h2c_pm_dm_rresp,
    input [PCIM_DATA_WIDTH-1:0]             h2c_pm_dm_rdata,
    input                                   h2c_pm_dm_rlast,
    output logic                            h2c_dm_pm_rready,

     // H2C Write-Back Block to PCIM Interface
     // Write Address to PCIM
    output logic                            h2c_wb_pm_awvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      h2c_wb_pm_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]       h2c_wb_pm_awlen,
    output logic [PCIM_ID_WIDTH-1:0]        h2c_wb_pm_awid,
    input                                   h2c_pm_wb_awready,
    
    // Write Data to PCIM
    output logic                            h2c_wb_pm_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]      h2c_wb_pm_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] h2c_wb_pm_wstrb,
    output logic                            h2c_wb_pm_wlast,
    input                                   h2c_pm_wb_wready,

    // Bresp from PCIM
    input                                   h2c_pm_wb_bvalid,
    input [1:0]                             h2c_pm_wb_bresp,
    output logic                            h2c_wb_pm_bready,

    // H2C AXI-Stream Interface
    output logic                            h2c_axis_valid,
    output logic [PCIM_DATA_WIDTH-1:0]      h2c_axis_data,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] h2c_axis_keep,
    output logic [H2C_USER_BIT_WIDTH-1:0]   h2c_axis_user,
    output logic                            h2c_axis_last,
    input                                   h2c_axis_ready

    );

   localparam PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3);
   localparam BUF_ADDR_RAM_IDX_WIDTH = $clog2(H2C_BUF_DEPTH);
   localparam BUF_AUX_RAM_ADDR_WIDTH = $clog2(H2C_BUF_AUX_DEPTH);
   localparam BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH;
   
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

   // Data Mover to Buffer 
//   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]       dm_buf_wr_ptr;
   logic [BUF_ADDR_WIDTH-1:0]               dm_buf_wr_byte_addr;
   logic                                    dm_buf_wr_ptr_msb;
   logic [BUF_ADDR_WIDTH:0]                 buf_dm_num_bytes; // Difference in pointers + plus num of bytes in last beat

   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]       dm_buf_aux_wr_ptr;
   logic                                    dm_buf_aux_wr_ptr_msb;
   logic                                    buf_dm_aux_full;
   
   logic                                    dm_buf_wr  ;
   logic [PCIM_DATA_WIDTH-1:0]              dm_buf_data;
   logic                                    dm_buf_eop ;
   logic [H2C_USER_BIT_WIDTH-1:0]           dm_buf_user;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0]     dm_buf_num_bytes_minus1;

   logic                                    buf_axis_valid;
   logic [PCIM_DATA_WIDTH-1:0]              buf_axis_data;
   logic [(PCIM_DATA_WIDTH>>3)-1:0]         buf_axis_keep;
   logic [H2C_USER_BIT_WIDTH-1:0]           buf_axis_user;
   logic                                    buf_axis_last;
   logic                                    axis_buf_ready;
    
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
   logic [H2C_DESC_WIDTH-1:0]               cfg_desc_ram_wdata ;
   logic                                    desc_cfg_ram_ack   ;
   logic [H2C_DESC_WIDTH-1:0]               desc_cfg_ram_rdata ;

   logic                                    dm_cfg_rresp_err;
   logic                                    dm_cfg_desc_len_err;
   
   logic                                    cfg_wb_desc_cdt_en;
   logic                                    cfg_wb_desc_cnt_en;
   logic                                    cfg_wb_pkt_cnt_en;
   logic [47:0]                             cfg_wb_status_addr;
   
   logic                                    cfg_wb_desc_error; 
   logic                                    cfg_wb_dm_error  ; 
   logic                                    cfg_wb_wb_error  ;
   logic [31:0]                             wb_cfg_status_dw ;
   
   logic                                    cfg_desc_cdt_wc_en;
   logic                                    cfg_desc_cnt_wc_en;
   logic                                    cfg_pkt_cnt_wc_en;
   logic [19:0]                             cfg_wc_tick_cnt;
   logic [3:0]                              cfg_wc_to_cnt;
   logic [5:0]                              cfg_wc_cnt_minus1;

   logic                                    cfg_axis_clr_pkt_cnt;
   logic [31:0]                             axis_cfg_pkt_cnt;
  
   logic                                    desc_cfg_oflow;
   logic                                    desc_cfg_uflow;
   logic                                    desc_cfg_full ;
   logic                                    desc_cfg_empty;

   logic                                    wb_cfg_sts_bresp_err;

   logic                                    buf_cfg_buf_oflow;
   logic                                    buf_cfg_buf_uflow;
   logic                                    buf_cfg_buf_full;
   logic                                    buf_cfg_buf_empty;
   logic [15:0]                             buf_cfg_buf_wr_ptr ;
   logic [15:0]                             buf_cfg_buf_rd_ptr;
   logic                                    buf_cfg_aux_fifo_oflow;
   logic                                    buf_cfg_aux_fifo_uflow;
   logic                                    buf_cfg_aux_fifo_full ; 
   logic                                    buf_cfg_aux_fifo_empty;
   logic [15:0]                             buf_cfg_aux_ram_wr_ptr;
   logic [15:0]                             buf_cfg_aux_ram_rd_ptr; 
   logic [15:0]                             buf_cfg_dm_wr_ptr;
   logic [15:0]                             buf_cfg_dm_aux_wr_ptr;
   logic [15:0]                             buf_cfg_num_free_slots;
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
   
   // H2C CSR Block
   sde_h2c_cfg #(
       .DESC_TYPE       (H2C_DESC_TYPE),
       .DESC_RAM_DEPTH  (H2C_DESC_RAM_DEPTH),
       .DESC_WIDTH      (H2C_DESC_WIDTH)
       )
   SDE_H2C_CFG
     (.clk                (clk),
      .rst_n              (sync_rst_n),
      
      .h2c_ps_cfg_wr_req  (h2c_ps_cfg_wr_req),
      .h2c_ps_cfg_rd_req  (h2c_ps_cfg_rd_req),
      .h2c_ps_cfg_addr    (h2c_ps_cfg_addr  ),
      .h2c_ps_cfg_wdata   (h2c_ps_cfg_wdata ),
      .h2c_ps_cfg_ack     (h2c_ps_cfg_ack   ),
      .h2c_ps_cfg_rdata   (h2c_ps_cfg_rdata ),

      .desc_ooo_error        (h2c_desc_ooo_error),
      .desc_unalin_error     (h2c_desc_unalin_error),

      .cfg_desc_clr_desc_cnt     (cfg_desc_clr_desc_cnt    ),
      .cfg_desc_clr_cdt_limit    (cfg_desc_clr_cdt_limit   ),
      .cfg_desc_clr_cdt_consumed (cfg_desc_clr_cdt_consumed),
      
      .desc_cfg_cdt_consumed (desc_cfg_cdt_consumed),
      .desc_cfg_cdt_limit    (desc_cfg_cdt_limit   ),
      .desc_cfg_desc_cnt     (desc_cfg_desc_cnt    ),
      .desc_cfg_wr_ptr       (desc_cfg_wr_ptr      ),
      .desc_cfg_rd_ptr       (desc_cfg_rd_ptr      ),
      
      .cfg_desc_ram_wr_req       (cfg_desc_ram_wr_req),
      .cfg_desc_ram_rd_req       (cfg_desc_ram_rd_req),
      .cfg_desc_ram_addr         (cfg_desc_ram_addr  ),
      .cfg_desc_ram_wdata        (cfg_desc_ram_wdata ),
      .desc_cfg_ram_ack          (desc_cfg_ram_ack   ),
      .desc_cfg_ram_rdata        (desc_cfg_ram_rdata ),
      
      .desc_cfg_oflow        (desc_cfg_oflow),
      .desc_cfg_uflow        (desc_cfg_uflow),
      .desc_cfg_full         (desc_cfg_full ),
      .desc_cfg_empty        (desc_cfg_empty),

      .dm_cfg_rresp_err      (dm_cfg_rresp_err),
      .dm_cfg_desc_len_err   (dm_cfg_desc_len_err),
      
      .cfg_wb_desc_cdt_en    (cfg_wb_desc_cdt_en  ),
      .cfg_wb_desc_cnt_en    (cfg_wb_desc_cnt_en  ),
      .cfg_wb_pkt_cnt_en     (cfg_wb_pkt_cnt_en   ),
      .cfg_wb_status_addr    (cfg_wb_status_addr  ),
      
      .cfg_desc_cdt_wc_en    (cfg_desc_cdt_wc_en ),
      .cfg_desc_cnt_wc_en    (cfg_desc_cnt_wc_en ),
      .cfg_pkt_cnt_wc_en     (cfg_pkt_cnt_wc_en  ),
      .cfg_wc_tick_cnt       (cfg_wc_tick_cnt    ),
      .cfg_wc_to_cnt         (cfg_wc_to_cnt      ),
      .cfg_wc_cnt_minus1     (cfg_wc_cnt_minus1  ),

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
      .buf_cfg_buf_rd_ptr      (buf_cfg_buf_rd_ptr     ),
      .buf_cfg_aux_fifo_oflow  (buf_cfg_aux_fifo_oflow ),
      .buf_cfg_aux_fifo_uflow  (buf_cfg_aux_fifo_uflow ),
      .buf_cfg_aux_fifo_full   (buf_cfg_aux_fifo_full  ), 
      .buf_cfg_aux_fifo_empty  (buf_cfg_aux_fifo_empty ),
      .buf_cfg_aux_ram_wr_ptr  (buf_cfg_aux_ram_wr_ptr ),
      .buf_cfg_aux_ram_rd_ptr  (buf_cfg_aux_ram_rd_ptr ), 
      .buf_cfg_dm_wr_ptr       (buf_cfg_dm_wr_ptr      ),
      .buf_cfg_dm_aux_wr_ptr   (buf_cfg_dm_aux_wr_ptr  ),
      .buf_cfg_num_free_slots  (buf_cfg_num_free_slots ),
      .buf_cfg_in_pkt_cnt      (buf_cfg_in_pkt_cnt     ),
      .buf_cfg_out_pkt_cnt     (buf_cfg_out_pkt_cnt    ),
      .cfg_buf_clr_in_pkt_cnt  (cfg_buf_clr_in_pkt_cnt ),
      .cfg_buf_clr_out_pkt_cnt (cfg_buf_clr_out_pkt_cnt),

      .cfg_axis_clr_pkt_cnt  (cfg_axis_clr_pkt_cnt),
      .axis_cfg_pkt_cnt      (axis_cfg_pkt_cnt    )

      );
      
      
   // H2C Descriptor
   sde_desc 
     #(.H2C_N_C2H       (1),
       
       .DESC_TYPE       (H2C_DESC_TYPE),
       .DESC_RAM_DEPTH  (H2C_DESC_RAM_DEPTH),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),

       .PCIM_DESC_ARID  (H2C_PCIM_DESC_ARID)
       ) 
   SDE_H2C_DESC 
     (.clk                (clk),
      .rst_n              (sync_rst_n),
      
      .ps_desc_wr_req     (h2c_ps_desc_wr_req),
      .ps_desc_wdata      (h2c_ps_desc_wdata),
      .ps_desc_ack        (h2c_ps_desc_ack),
      
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

      .desc_pm_arvalid    (h2c_desc_pm_arvalid),
      .desc_pm_araddr     (h2c_desc_pm_araddr ),
      .desc_pm_arlen      (h2c_desc_pm_arlen  ),
      .pm_desc_arready    (h2c_pm_desc_arready),
      
      .pm_desc_rvalid     (h2c_pm_desc_rvalid),
      .pm_desc_rresp      (h2c_pm_desc_rresp ),
      .pm_desc_rdata      (h2c_pm_desc_rdata ),
      .pm_desc_rlast      (h2c_pm_desc_rlast ),
      .desc_pm_rready     (h2c_desc_pm_rready)

      );
   
   // H2C Data Mover
   sde_h2c_data 
     #(.DESC_TYPE       (H2C_DESC_TYPE),

       .PCIM_NUM_OT_RD  (PCIM_NUM_OT_RD),
       .PCIM_DM_ARID    (H2C_PCIM_DM_ARID),

       .PCIM_MAX_RD_SIZE (H2C_PCIM_MAX_RD_SIZE),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH ),
       
       .BUF_DEPTH       (H2C_BUF_DEPTH),
       .BUF_AUX_DEPTH   (H2C_BUF_AUX_DEPTH),

       .USER_BIT_WIDTH  (H2C_USER_BIT_WIDTH)
       )
   SDE_H2C_DATA 
     (.clk                     (clk),
      .rst_n                   (sync_rst_n),

      // TODO - CSRs 
      .dm_cfg_rresp_err        (dm_cfg_rresp_err),
      .dm_cfg_desc_len_err     (dm_cfg_desc_len_err),
      
      .desc_dm_empty           (desc_dm_empty),
      .dm_desc_pop             (dm_desc_pop),
      .desc_dm_desc            (desc_dm_desc),
      .desc_dm_desc_valid      (desc_dm_desc_valid),

      .dm_desc_cnt_inc         (dm_desc_cnt_inc),
      
      .dm_pm_arvalid           (h2c_dm_pm_arvalid),
      .dm_pm_araddr            (h2c_dm_pm_araddr ),
      .dm_pm_arlen             (h2c_dm_pm_arlen  ),
      .dm_pm_arid              (h2c_dm_pm_arid   ),
      .pm_dm_arready           (h2c_pm_dm_arready),
      .pm_dm_rvalid            (h2c_pm_dm_rvalid),
      .pm_dm_rresp             (h2c_pm_dm_rresp ),
      .pm_dm_rdata             (h2c_pm_dm_rdata ),
      .pm_dm_rlast             (h2c_pm_dm_rlast ),
      .dm_pm_rready            (h2c_dm_pm_rready),
      
//      .dm_buf_wr_ptr           (dm_buf_wr_ptr),
      .dm_buf_wr_byte_addr     (dm_buf_wr_byte_addr),
      .dm_buf_wr_ptr_msb       (dm_buf_wr_ptr_msb),
      .buf_dm_num_bytes        (buf_dm_num_bytes),
      
      .dm_buf_aux_wr_ptr       (dm_buf_aux_wr_ptr),
      .dm_buf_aux_wr_ptr_msb   (dm_buf_aux_wr_ptr_msb),
      .buf_dm_aux_full         (buf_dm_aux_full),
      
      .dm_buf_wr               (dm_buf_wr  ),
      .dm_buf_data             (dm_buf_data),
      .dm_buf_eop              (dm_buf_eop ),
      .dm_buf_user             (dm_buf_user),
      .dm_buf_num_bytes_minus1 (dm_buf_num_bytes_minus1)

      );

   // H2C Write-Back
   sde_wb
     #(.H2C_N_C2H       (1),
       .DESC_TYPE       (H2C_DESC_TYPE),

       .DESC_RAM_DEPTH  (H2C_DESC_RAM_DEPTH),
       .PCIM_WB_AWID    (H2C_PCIM_WB_AWID),
       
       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       .PCIM_ID_WIDTH   (PCIM_ID_WIDTH   ),
       .PCIM_LEN_WIDTH  (PCIM_LEN_WIDTH  ),
       .PCIM_ADDR_WIDTH (PCIM_ADDR_WIDTH )
       )
   SDE_H2C_WB
     (.clk                   (clk),
      .rst_n                 (sync_rst_n),

      .cfg_wb_desc_cdt_en    (cfg_wb_desc_cdt_en),
      .cfg_wb_desc_cnt_en    (cfg_wb_desc_cnt_en),
      .cfg_wb_pkt_cnt_en     (cfg_wb_pkt_cnt_en),
      .cfg_wb_md_ptr_en      (1'b0),
      .cfg_wb_status_addr    (cfg_wb_status_addr),
      
      .cfg_desc_clr_desc_cnt  (cfg_desc_clr_desc_cnt ),
      .cfg_desc_clr_cdt_limit (cfg_desc_clr_cdt_limit),
      .cfg_axis_clr_pkt_cnt   (cfg_axis_clr_pkt_cnt),
      
      .cfg_desc_cdt_wc_en    (cfg_desc_cdt_wc_en ),
      .cfg_desc_cnt_wc_en    (cfg_desc_cnt_wc_en ),
      .cfg_pkt_cnt_wc_en     (cfg_pkt_cnt_wc_en  ),
      .cfg_md_wr_ptr_wc_en   (1'b0),
      .cfg_wc_tick_cnt       (cfg_wc_tick_cnt    ),
      .cfg_wc_to_cnt         (cfg_wc_to_cnt      ),
      .cfg_wc_cnt_minus1     (cfg_wc_cnt_minus1  ),
         
      .wb_cfg_md_bresp_err   (),
      .wb_cfg_sts_bresp_err  (wb_cfg_sts_bresp_err), 

      .cfg_wb_desc_error     (cfg_wb_desc_error), 
      .cfg_wb_dm_error       (cfg_wb_dm_error  ), 
      .cfg_wb_wb_error       (cfg_wb_wb_error  ),
      .wb_cfg_status_dw      (wb_cfg_status_dw ),

      .desc_wb_limit_req     (desc_wb_limit_req), 
      .desc_wb_limit         (desc_wb_limit),

      .desc_wb_cnt_req       (desc_wb_cnt_req),
      .desc_wb_cnt           (desc_wb_cnt),

      .dm_wb_md_req          (1'b0),
      .dm_wb_md              (),
      .wb_dm_md_grant        (),

      .axis_wb_pkt_cnt_req   (axis_wb_pkt_cnt_req),
      .axis_wb_pkt_cnt       (axis_wb_pkt_cnt),
      
      .wb_pm_awvalid         (h2c_wb_pm_awvalid),
      .wb_pm_awaddr          (h2c_wb_pm_awaddr ),
      .wb_pm_awlen           (h2c_wb_pm_awlen  ),
      .wb_pm_awid            (h2c_wb_pm_awid   ),
      .pm_wb_awready         (h2c_pm_wb_awready),
      .wb_pm_wvalid          (h2c_wb_pm_wvalid ),
      .wb_pm_wdata           (h2c_wb_pm_wdata  ),
      .wb_pm_wstrb           (h2c_wb_pm_wstrb  ),
      .wb_pm_wlast           (h2c_wb_pm_wlast  ),
      .pm_wb_wready          (h2c_pm_wb_wready ),
      .pm_wb_bvalid          (h2c_pm_wb_bvalid ),
      .pm_wb_bresp           (h2c_pm_wb_bresp  ),
      .wb_pm_bready          (h2c_wb_pm_bready )

      );
       
   // H2C Buffer
   sde_h2c_buf
     #(.DESC_TYPE       (H2C_DESC_TYPE),

       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),
       
       .BUF_DEPTH       (H2C_BUF_DEPTH),
       .BUF_AUX_DEPTH   (H2C_BUF_AUX_DEPTH),
       
       .USER_BIT_WIDTH  (H2C_USER_BIT_WIDTH)

       )
   SDE_H2C_BUF
     (.clk                     (clk),
      .rst_n                   (sync_rst_n),

      .buf_cfg_buf_oflow       (buf_cfg_buf_oflow      ),
      .buf_cfg_buf_uflow       (buf_cfg_buf_uflow      ),
      .buf_cfg_buf_full        (buf_cfg_buf_full       ),
      .buf_cfg_buf_empty       (buf_cfg_buf_empty      ),
      .buf_cfg_buf_wr_ptr      (buf_cfg_buf_wr_ptr     ),
      .buf_cfg_buf_rd_ptr      (buf_cfg_buf_rd_ptr     ),
      .buf_cfg_aux_fifo_oflow  (buf_cfg_aux_fifo_oflow ),
      .buf_cfg_aux_fifo_uflow  (buf_cfg_aux_fifo_uflow ),
      .buf_cfg_aux_fifo_full   (buf_cfg_aux_fifo_full  ), 
      .buf_cfg_aux_fifo_empty  (buf_cfg_aux_fifo_empty ),
      .buf_cfg_aux_ram_wr_ptr  (buf_cfg_aux_ram_wr_ptr ),
      .buf_cfg_aux_ram_rd_ptr  (buf_cfg_aux_ram_rd_ptr ), 
      .buf_cfg_dm_wr_ptr       (buf_cfg_dm_wr_ptr      ),
      .buf_cfg_dm_aux_wr_ptr   (buf_cfg_dm_aux_wr_ptr  ),
      .buf_cfg_num_free_slots  (buf_cfg_num_free_slots ),
      .buf_cfg_in_pkt_cnt      (buf_cfg_in_pkt_cnt     ),
      .buf_cfg_out_pkt_cnt     (buf_cfg_out_pkt_cnt    ),
      .cfg_buf_clr_in_pkt_cnt  (cfg_buf_clr_in_pkt_cnt ),
      .cfg_buf_clr_out_pkt_cnt (cfg_buf_clr_out_pkt_cnt),
         
      .buf_axis_valid          (buf_axis_valid ), 
      .buf_axis_data           (buf_axis_data  ),  
      .buf_axis_keep           (buf_axis_keep  ),  
      .buf_axis_user           (buf_axis_user  ),  
      .buf_axis_last           (buf_axis_last  ),   
      .axis_buf_ready          (axis_buf_ready ),

//      .dm_buf_wr_ptr           (dm_buf_wr_ptr),
      .dm_buf_wr_byte_addr     (dm_buf_wr_byte_addr),
      .dm_buf_wr_ptr_msb       (dm_buf_wr_ptr_msb),
      .buf_dm_num_bytes        (buf_dm_num_bytes),

      .dm_buf_aux_wr_ptr       (dm_buf_aux_wr_ptr),
      .dm_buf_aux_wr_ptr_msb   (dm_buf_aux_wr_ptr_msb),
      .buf_dm_aux_full         (buf_dm_aux_full),

      .dm_buf_wr               (dm_buf_wr  ),
      .dm_buf_data             (dm_buf_data),
      .dm_buf_eop              (dm_buf_eop ),
      .dm_buf_user             (dm_buf_user),
      .dm_buf_num_bytes_minus1 (dm_buf_num_bytes_minus1)

      );
   
   
   // H2C AXI-Stream Interface
   sde_h2c_axis
     #(.DESC_TYPE       (H2C_DESC_TYPE),

       .PCIM_DATA_WIDTH (PCIM_DATA_WIDTH ),

       .AXIS_DATA_WIDTH (H2C_AXIS_DATA_WIDTH),
       .USER_BIT_WIDTH  (H2C_USER_BIT_WIDTH)
       )
   SDE_H2C_AXIS
     (.clk                 (clk),
      .rst_n               (sync_rst_n),

      // TODO - CSRs
      .cfg_axis_clr_pkt_cnt (cfg_axis_clr_pkt_cnt),
      .axis_cfg_pkt_cnt     (axis_cfg_pkt_cnt),
                 
      .h2c_axis_valid      (h2c_axis_valid ),
      .h2c_axis_data       (h2c_axis_data  ), 
      .h2c_axis_keep       (h2c_axis_keep  ), 
      .h2c_axis_user       (h2c_axis_user  ), 
      .h2c_axis_last       (h2c_axis_last  ),  
      .h2c_axis_ready      (h2c_axis_ready ),
      
      .buf_axis_valid      (buf_axis_valid ), 
      .buf_axis_data       (buf_axis_data  ),  
      .buf_axis_keep       (buf_axis_keep  ),  
      .buf_axis_user       (buf_axis_user  ),  
      .buf_axis_last       (buf_axis_last  ),   
      .axis_buf_ready      (axis_buf_ready ),

      .axis_wb_pkt_cnt_req (axis_wb_pkt_cnt_req),
      .axis_wb_pkt_cnt     (axis_wb_pkt_cnt)

      );


endmodule // sde_h2c
