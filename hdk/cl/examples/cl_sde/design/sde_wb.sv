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

// Write Back

module sde_wb #(parameter bit H2C_N_C2H = 0,  // 0 - C2H, 1 - H2C
                parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
                parameter PCIM_WB_AWID = 1, // This is the ID used for write accesses from Write Back Block

                parameter DESC_RAM_DEPTH = 64,
                
                parameter PCIM_DATA_WIDTH = 512,
                parameter PCIM_ID_WIDTH = 3,
                parameter PCIM_LEN_WIDTH = 8,
                parameter PCIM_ADDR_WIDTH = 64,
                parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),

                // These are internal FIFOs - Dont change unless absolutely required
                parameter WB_BRESP_TRK_FIFO_DEPTH = 32
                )

   (
    input                                   clk,
    input                                   rst_n,

    // CSR to Write-Back
    input                                   cfg_wb_desc_cdt_en,
    input                                   cfg_wb_desc_cnt_en,
    input                                   cfg_wb_pkt_cnt_en,
    input                                   cfg_wb_md_ptr_en,
    input [47:0]                            cfg_wb_status_addr,
    input [47:0]                            cfg_wb_md_ring_addr,
    input [31:0]                            cfg_wb_md_ring_size,
    input [15:0]                            cfg_wb_md_rd_ptr,
    output logic [15:0]                     wb_cfg_md_wr_ptr,
    input                                   cfg_wb_clr_wr_ptr,

    input                                   cfg_wb_desc_error, 
    input                                   cfg_wb_dm_error, 
    input                                   cfg_wb_wb_error,
    output logic [31:0]                     wb_cfg_status_dw,
    
    input                                   cfg_desc_clr_cdt_limit,
    input                                   cfg_desc_clr_desc_cnt,
    input                                   cfg_axis_clr_pkt_cnt,

    input                                   cfg_desc_cdt_wc_en,
    input                                   cfg_desc_cnt_wc_en,
    input                                   cfg_pkt_cnt_wc_en,
    input                                   cfg_md_wr_ptr_wc_en,
    input [19:0]                            cfg_wc_tick_cnt,
    input [3:0]                             cfg_wc_to_cnt,
    input [5:0]                             cfg_wc_cnt_minus1,
         
    output logic                            wb_cfg_md_bresp_err,
    output logic                            wb_cfg_sts_bresp_err,
    
    output logic [63:0]                     wb_cfg_bresp_err_addr,
    
    // Desc to Write-Back
    input                                   desc_wb_limit_req,
    input [31:0]                            desc_wb_limit,

    input                                   desc_wb_cnt_req,
    input [31:0]                            desc_wb_cnt,

    // AXIS to Write-Back
    input                                   axis_wb_pkt_cnt_req,
    input [31:0]                            axis_wb_pkt_cnt,
    
    // Data Mover to Write-Block Request
    input                                   dm_wb_md_req,
    input                                   sde_pkg::c2h_reg_wb_t dm_wb_md, // Used for C2H Only
    output                                  wb_dm_md_grant,

     // Write Address to PCIM
    output logic                            wb_pm_awvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]      wb_pm_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]       wb_pm_awlen,
    output logic [PCIM_ID_WIDTH-1:0]        wb_pm_awid,
    input                                   pm_wb_awready,
    
    // Write Data to PCIM
    output logic                            wb_pm_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]      wb_pm_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] wb_pm_wstrb,
    output logic                            wb_pm_wlast,
    input                                   pm_wb_wready,

    // Bresp from PCIM
    input                                   pm_wb_bvalid,
    input [1:0]                             pm_wb_bresp,
    output logic                            wb_pm_bready

    );

   localparam PCIM_DATA_WIDTH_BYTES = PCIM_DATA_WIDTH >> 3;
   localparam WB_MD_WIDTH = DESC_TYPE ? 64 : 128;
   localparam WB_MD_NUM_WR_BEATS = (WB_MD_WIDTH + PCIM_DATA_WIDTH - 1) / PCIM_DATA_WIDTH;
   localparam WB_MD_WIDTH_BYTES = WB_MD_WIDTH >> 3;
   localparam WB_MD_WIDTH_BYTES_LOG2 = $clog2(WB_MD_WIDTH_BYTES);
   localparam NUM_REQUESTER = (H2C_N_C2H == 1) ? 1 : 2;
   localparam REQUESTER_WIDTH = 1;

   localparam WB_STATUS_NUM_BYTES = H2C_N_C2H ? (4*4) : (5*4); // 5 DWs for C2H, 4 DWs for H2C

   localparam MD_PTR_WIDTH = 16; // This dictates the maximum buffer size for Write-Back Metadata
                                 // For example, 
                                 // With MD_PTR_WIDTH = 16, the maximum number of metadata entries = 65536. 
                                 // for regular type write-back metadata (16B), maximum WB buffer size = 16B * 65536 = 1MB
                                 // for compact type write-back metadata (8B) , maximum WB buffer size = 8B * 65536 = 512KB

   localparam WDATA_TO_SEND_WIDTH = WB_STATUS_NUM_BYTES*8 > WB_MD_WIDTH ? WB_STATUS_NUM_BYTES*8 : WB_MD_WIDTH;
   localparam WSTRB_TO_SEND_WIDTH = WDATA_TO_SEND_WIDTH >> 3;
                                   
   typedef enum logic [REQUESTER_WIDTH-1:0] 
                {
                 WB_STATUS = 0,
                 WB_METADATA = 1
                 } requester_t;

   logic        dm_wb_md_req_pend;
   logic        status_dw_req_pend;
   logic        desc_cdt_req_pend;
   logic        desc_cnt_req_pend;
   logic        pkt_cnt_req_pend;
   logic        md_wr_ptr_req_pend;
   logic        md_wr_ptr_req;

   logic        start_new_req;
   
   logic        bresp_prealloc_avail;
   logic        wr_done;
   logic        do_arb;
   logic [REQUESTER_WIDTH-1:0] requester_arb_out;
   logic [NUM_REQUESTER-1:0]   requester_arb_in;
   logic                       accept_new_wb_req;
   logic                       new_wb_req;
   logic                       addr_active;
   requester_t req_winner;
   logic                       status_req_qual;
   logic                       req_qual;
//    logic                       desc_cdt_req_qual;
//    logic                       desc_cnt_req_qual;
//    logic                       pkt_cnt_req_qual;
//    logic                       md_wr_ptr_req_qual;
   logic                       md_req_qual;
//   logic                       send_pm_addr_req;
   logic                       addr_done;
   logic [63:0]                addr_pipe_write_addr;
   logic [7:0]                 addr_pipe_num_bytes;
   logic [7:0]                 addr_pipe_num_bytes_adj;
   logic [7:0]                 addr_pipe_num_beats_minus1;
   logic                       wr_active;
   logic                       wr_active_q;
   logic                       wr_active_re;
   logic                       wr_active_re_q;
//   logic                       send_pm_wr_req;
   logic [31:0]                desc_wb_limit_q;
   logic [31:0]                desc_wb_cnt_q;
   logic [31:0]                axis_wb_pkt_cnt_q;
   logic [MD_PTR_WIDTH-1:0]    md_wr_ptr_q;
   logic [31:0]                desc_wb_limit_sent;
   logic [31:0]                desc_wb_cnt_sent;
   logic [31:0]                axis_wb_pkt_cnt_sent;
   logic [MD_PTR_WIDTH-1:0]    md_wr_ptr_sent;
   sde_pkg::c2h_comp_wb_t dm_wb_md_comp;
   logic [7:0]                 wr_pipe_num_beats_minus1;
   logic [63:0]                wr_pipe_addr;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] wr_pipe_lwr_addr;
   logic [12:0]                         wb_wr_max_bytes;
   logic [7:0]                          wb_wr_num_bytes_total;
   logic [12:0]                         wb_wr_num_bytes_remain;
   logic [12:0]                         wb_wr_num_bytes_to_send;
   logic [WSTRB_TO_SEND_WIDTH-1:0]      wb_wr_strb_to_send;
   logic [WB_MD_WIDTH-1:0]              wb_wr_md;
   logic [WDATA_TO_SEND_WIDTH-1:0]      wb_wr_data_to_send;
   logic [7:0]                          wb_wr_idx;
   logic [7:0]                          wb_wr_num_bytes_sent;

   logic                                status_req_pend;

   logic [31:0]                         num_md_in_ring;
   logic [MD_PTR_WIDTH:0]               md_wr_ptr_next_inc;
   logic [MD_PTR_WIDTH:0]               md_wr_ptr_next_inc_rovr;
   logic [MD_PTR_WIDTH-1:0]             md_wr_ptr_next;
   logic [MD_PTR_WIDTH-1:0]             md_wr_ptr;
   logic [MD_PTR_WIDTH:0]               md_wr_ptr_plus1;
   logic [MD_PTR_WIDTH:0]               md_wr_ptr_plus1_rovr;
   logic                                md_ring_full;
   logic [63:0]                         md_wr_addr;
   
   logic [31:0] status_dw;
   logic [31:0] status_dw_q;
   logic [31:0] status_dw_sent;

   // Status DW Definition
   // 0 - Descriptor Error
   // 1 - Data Mover Error
   // 2 - Write Back Error 
   assign status_dw = {cfg_wb_wb_error, cfg_wb_dm_error, cfg_wb_desc_error};
   assign wb_cfg_status_dw = status_dw;
   
   if (~H2C_N_C2H) begin
      
      always @(posedge clk)
        if (!rst_n) 
          num_md_in_ring <= 0;
        else
          num_md_in_ring <= cfg_wb_md_ring_size >> WB_MD_WIDTH_BYTES_LOG2;
   
   assign md_wr_ptr_next_inc = md_wr_ptr + 1;
   assign md_wr_ptr_next_inc_rovr = md_wr_ptr_next_inc - num_md_in_ring;
   assign md_wr_ptr_next = md_wr_ptr_next_inc >= num_md_in_ring ? md_wr_ptr_next_inc_rovr : md_wr_ptr_next_inc;
   
   //    assign md_wr_ptr_next_plus1 = md_wr_ptr_next + 1;
   //    assign md_wr_ptr_next_plus1_rovr = md_wr_ptr_next_plus1 >= num_md_in_ring ? 0 : md_wr_ptr_next_plus1;
   
   
   // Move write pointer
   always @(posedge clk)
     if (!rst_n) begin
        md_wr_ptr <= 0;
        md_wr_ptr_req <= 0;
        
        //        md_ring_full <= 0;
     end
     else begin
        md_wr_ptr <= cfg_wb_clr_wr_ptr ? 0 : 
                     wr_done & (req_winner == WB_METADATA) ? md_wr_ptr_next : md_wr_ptr;
        md_wr_ptr_req <= wr_done & (req_winner == WB_METADATA);
        
        //        md_ring_full <= wr_done & (req_winner == WB_METADATA) ? (md_wr_ptr_next_plus1_rovr == cfg_wb_md_rd_ptr) : 
        //                        (md_wr_ptr_plus1 >= num_md_in_ring);
     end // else: !if(!rst_n)
   
   assign wb_cfg_md_wr_ptr = md_wr_ptr;
   
   // assign md_wr_addr = (md_wr_ptr << $clog2(WB_MD_WIDTH_BYTES)) + cfg_wb_md_ring_addr;
   assign md_wr_addr[WB_MD_WIDTH_BYTES_LOG2-1:0] = cfg_wb_md_ring_addr[WB_MD_WIDTH_BYTES_LOG2-1:0];
   assign md_wr_addr[47:WB_MD_WIDTH_BYTES_LOG2] = md_wr_ptr + cfg_wb_md_ring_addr[47:WB_MD_WIDTH_BYTES_LOG2];
   assign md_wr_addr[63:48] = 16'd0;
   
   
   assign md_wr_ptr_plus1 = md_wr_ptr + 1;
   assign md_wr_ptr_plus1_rovr = (md_wr_ptr_plus1 >= num_md_in_ring) ? 0 : md_wr_ptr_plus1;
   assign md_ring_full = (md_wr_ptr_plus1_rovr == cfg_wb_md_rd_ptr);

end // if (~H2C_N_C2H)
   
   else begin
      assign num_md_in_ring = 0;
      assign md_wr_ptr = 0;
      assign md_wr_ptr_req = 0;
      assign wb_cfg_md_wr_ptr = 0;
      assign md_wr_addr = 0;
      assign md_ring_full = 0;
   end // else: !if(~H2C_N_C2H)

   logic [19:0] wc_to_tick_cnt;

   logic [3:0] cfg_desc_cdt_wc_to_cnt;
   logic [3:0] cfg_desc_cnt_wc_to_cnt;
   logic [3:0] cfg_pkt_cnt_wc_to_cnt;
   logic [3:0] cfg_md_wr_ptr_wc_to_cnt;
   logic [6:0] cfg_desc_cdt_wc_cnt_m1;
   logic [6:0] cfg_desc_cnt_wc_cnt_m1;
   logic [6:0] cfg_pkt_cnt_wc_cnt_m1;
   logic [6:0] cfg_md_wr_ptr_wc_cnt_m1;

   logic [6:0] desc_cdt_req_wc_cnt;
   logic [6:0] desc_cnt_req_wc_cnt;
   logic [6:0] pkt_cnt_req_wc_cnt;
   logic [6:0] md_wr_ptr_req_wc_cnt;

   logic [3:0] desc_cdt_req_wc_to_cnt;
   logic [3:0] desc_cnt_req_wc_to_cnt;
   logic [3:0] pkt_cnt_req_wc_to_cnt;
   logic [3:0] md_wr_ptr_req_wc_to_cnt;

   logic       desc_wb_limit_wc_req  ;
   logic       desc_wb_cnt_wc_req    ;
   logic       axis_wb_pkt_cnt_wc_req;
   logic       md_wr_ptr_wc_req  ;

   logic [31:0] desc_wb_limit_diff;
   logic [31:0] desc_wb_cnt_diff;
   logic [31:0] axis_wb_pkt_cnt_diff;
   logic [MD_PTR_WIDTH-1:0] md_wr_ptr_diff;
    
   assign cfg_desc_cdt_wc_to_cnt  = cfg_desc_cdt_wc_en  ? cfg_wc_to_cnt : 0;
   assign cfg_desc_cnt_wc_to_cnt  = cfg_desc_cnt_wc_en  ? cfg_wc_to_cnt : 0;
   assign cfg_pkt_cnt_wc_to_cnt   = cfg_pkt_cnt_wc_en   ? cfg_wc_to_cnt : 0;
   assign cfg_md_wr_ptr_wc_to_cnt = cfg_md_wr_ptr_wc_en ? cfg_wc_to_cnt : 0;

   assign cfg_desc_cdt_wc_cnt_m1  = cfg_desc_cdt_wc_en  ? cfg_wc_cnt_minus1 : 0;
   assign cfg_desc_cnt_wc_cnt_m1  = cfg_desc_cnt_wc_en  ? cfg_wc_cnt_minus1 : 0;
   assign cfg_pkt_cnt_wc_cnt_m1   = cfg_pkt_cnt_wc_en   ? cfg_wc_cnt_minus1 : 0;
   assign cfg_md_wr_ptr_wc_cnt_m1 = cfg_md_wr_ptr_wc_en ? cfg_wc_cnt_minus1 : 0;
                            
   assign desc_wb_limit_diff = (desc_wb_limit - desc_wb_limit_q);
   assign desc_wb_cnt_diff = desc_wb_cnt - desc_wb_cnt_q;
   assign axis_wb_pkt_cnt_diff = axis_wb_pkt_cnt - axis_wb_pkt_cnt_q;
   assign md_wr_ptr_diff = (md_wr_ptr >= md_wr_ptr_q) ? md_wr_ptr - md_wr_ptr_q : 
                           md_wr_ptr_q - md_wr_ptr;
   
   always @(posedge clk)
     if (!rst_n) begin
        wc_to_tick_cnt <= 0;
        
        desc_cdt_req_wc_cnt <= 0;
        desc_cnt_req_wc_cnt <= 0;
        pkt_cnt_req_wc_cnt <= 0;
        md_wr_ptr_req_wc_cnt <= 0;

        desc_cdt_req_wc_to_cnt <= 0;
        desc_cnt_req_wc_to_cnt <= 0;
        pkt_cnt_req_wc_to_cnt <= 0;
        md_wr_ptr_req_wc_to_cnt <= 0;
     end
     else begin
        wc_to_tick_cnt <= (wc_to_tick_cnt == 0) ? cfg_wc_tick_cnt : wc_to_tick_cnt - 1;
        
        desc_cdt_req_wc_cnt <= desc_wb_limit_diff;
        
        desc_cnt_req_wc_cnt <= desc_wb_cnt_diff;
        
        pkt_cnt_req_wc_cnt <= axis_wb_pkt_cnt_diff;
        
        md_wr_ptr_req_wc_cnt <= md_wr_ptr_diff;

        desc_cdt_req_wc_to_cnt <= desc_wb_limit_wc_req ? 0 :
                                  (desc_cdt_req_wc_cnt > 0) & (wc_to_tick_cnt == 0) & (desc_cdt_req_wc_to_cnt < 4'hF) ? desc_cdt_req_wc_to_cnt + 1 :
                                  desc_cdt_req_wc_to_cnt;
        
        desc_cnt_req_wc_to_cnt <= desc_wb_cnt_wc_req ? 0 :
                                  (desc_cnt_req_wc_cnt > 0) & (wc_to_tick_cnt == 0) & (desc_cnt_req_wc_to_cnt < 4'hF) ? desc_cnt_req_wc_to_cnt + 1 :
                                  desc_cnt_req_wc_to_cnt;

        pkt_cnt_req_wc_to_cnt <= axis_wb_pkt_cnt_wc_req ? 0 :
                                 (pkt_cnt_req_wc_cnt > 0) & (wc_to_tick_cnt == 0) & (pkt_cnt_req_wc_to_cnt < 4'hF) ? pkt_cnt_req_wc_to_cnt + 1 :
                                 pkt_cnt_req_wc_to_cnt;
        
        md_wr_ptr_req_wc_to_cnt <= md_wr_ptr_wc_req ? 0 : 
                                   (md_wr_ptr_req_wc_cnt > 0) & (wc_to_tick_cnt == 0) & (md_wr_ptr_req_wc_to_cnt < 4'hF) ? md_wr_ptr_req_wc_to_cnt + 1 :
                                   md_wr_ptr_req_wc_to_cnt;
        
     end // else: !if(!rst_n)

   assign desc_wb_limit_wc_req   = ((desc_cdt_req_wc_to_cnt  >= cfg_wc_to_cnt) || (desc_cdt_req_wc_cnt  > cfg_desc_cdt_wc_cnt_m1 ))  & (desc_cdt_req_wc_cnt  > 0);
   assign desc_wb_cnt_wc_req     = ((desc_cnt_req_wc_to_cnt  >= cfg_wc_to_cnt) || (desc_cnt_req_wc_cnt  > cfg_desc_cnt_wc_cnt_m1 ))  & (desc_cnt_req_wc_cnt  > 0);
   assign axis_wb_pkt_cnt_wc_req = ((pkt_cnt_req_wc_to_cnt   >= cfg_wc_to_cnt) || (pkt_cnt_req_wc_cnt   > cfg_pkt_cnt_wc_cnt_m1  ))  & (pkt_cnt_req_wc_cnt   > 0);
   assign md_wr_ptr_wc_req       = ((md_wr_ptr_req_wc_to_cnt >= cfg_wc_to_cnt) || (md_wr_ptr_req_wc_cnt > cfg_md_wr_ptr_wc_cnt_m1))  & (md_wr_ptr_req_wc_cnt > 0);
   
   // Request Pending 
   always @(posedge clk)
     if (!rst_n) begin
        dm_wb_md_req_pend <= 0;
        status_dw_req_pend <= 0;
        desc_cdt_req_pend <= 0;
        desc_cnt_req_pend <= 0;
        pkt_cnt_req_pend <= 0;
        md_wr_ptr_req_pend <= 0;
     end
     else begin
        dm_wb_md_req_pend <= wr_done & (req_winner == WB_METADATA) ? 1'b0 : 
                             dm_wb_md_req & ~(md_ring_full & cfg_wb_md_ptr_en) ? 1'b1 : dm_wb_md_req_pend;
        status_dw_req_pend <= wr_done & (req_winner == WB_STATUS) ? 1'b0 :
                              (status_dw_sent != status_dw) ? 1'b1 :
                              status_dw_req_pend;
        desc_cdt_req_pend <= wr_done & (req_winner == WB_STATUS) ? 1'b0 : 
                             desc_wb_limit_wc_req & cfg_wb_desc_cdt_en & (desc_wb_limit_sent != desc_wb_limit) ? 1'b1 : 
                             desc_cdt_req_pend;
        desc_cnt_req_pend <= wr_done & (req_winner == WB_STATUS) ? 1'b0 : 
                             desc_wb_cnt_wc_req & cfg_wb_desc_cnt_en & (desc_wb_cnt_sent != desc_wb_cnt) ? 1'b1 : 
                             desc_cnt_req_pend;
        pkt_cnt_req_pend <= wr_done & (req_winner == WB_STATUS) ? 1'b0 : 
                            axis_wb_pkt_cnt_wc_req & cfg_wb_pkt_cnt_en & (axis_wb_pkt_cnt_sent != axis_wb_pkt_cnt) ? 1'b1 : 
                            pkt_cnt_req_pend;
        md_wr_ptr_req_pend <= wr_done & (req_winner == WB_STATUS) ? 1'b0 : 
                              md_wr_ptr_wc_req & cfg_wb_md_ptr_en & (md_wr_ptr_sent != md_wr_ptr) ? 1'b1 : 
                              md_wr_ptr_req_pend;
     end // else: !if(!rst_n)

   assign status_req_pend = pkt_cnt_req_pend || desc_cnt_req_pend || desc_cdt_req_pend || status_dw_req_pend || md_wr_ptr_req_pend;

   if (H2C_N_C2H) begin
      assign requester_arb_out = 0;
   end
   else begin
      // Arbitrate between 2 requests
      // Round Robin arbiter
      assign requester_arb_in = {dm_wb_md_req_pend, status_req_pend};
      
      rr_arb #(.WINNER_WIDTH(REQUESTER_WIDTH),
               .REQ_WIDTH (NUM_REQUESTER),
               .DO_ARB_IS_CHANGE_STATE(1)) REQUESTER_RR_ARB (.clk     (clk),
                                                             .rst_n   (rst_n),
                                                             .req     (requester_arb_in),
                                                             .do_arb  (do_arb),
                                                             .winner  (requester_arb_out)
                                                             );
   end // else: !if(H2C_N_C2H)
      
   assign accept_new_wb_req = ~start_new_req & ~wr_active & ~addr_active & bresp_prealloc_avail;

   assign new_wb_req = dm_wb_md_req_pend || status_req_pend;
   
   assign do_arb = ~addr_active & start_new_req;
   
   always @(posedge clk)
     if (!rst_n) begin
        start_new_req <= 0;
        addr_active <= 0;
        req_winner <= requester_t'(0);

//        status_req_qual <= 0;
        
//        md_req_qual <= 0;
     end
     else begin
        start_new_req <= accept_new_wb_req  & new_wb_req;
        
        addr_active <= addr_active & addr_done ? 1'b0 : 
                       start_new_req ? 1'b1 :
                       addr_active;
        
        req_winner <= start_new_req ? requester_t'(requester_arb_out) : req_winner;

//         status_req_qual <= start_new_req ? ((desc_cdt_req_pend & (desc_wb_limit_sent != desc_wb_limit)) ||
//                                             (desc_cnt_req_pend & (desc_wb_cnt_sent   != desc_wb_cnt)  ) ||
//                                             (pkt_cnt_req_pend  & (axis_wb_pkt_cnt_sent != axis_wb_pkt_cnt)) ||
//                                             (md_wr_ptr_req_pend & (md_wr_ptr_sent != md_wr_ptr))) : 
//                            status_req_qual;

//        md_req_qual <= start_new_req ? (dm_wb_md_req_pend & ~(md_ring_full & cfg_wb_md_ptr_en)) : md_req_qual;
     end // else: !if(!rst_n)

   assign status_req_qual = 1;
   
   assign md_req_qual = 1;
   
   assign req_qual = (req_winner == WB_STATUS) ? status_req_qual : md_req_qual;
   
   assign addr_done = addr_active & (~req_qual || (wb_pm_awvalid && pm_wb_awready));
   
   assign addr_pipe_write_addr = (req_winner == WB_STATUS) ? cfg_wb_status_addr : md_wr_addr;

   assign addr_pipe_num_bytes = (req_winner == WB_METADATA) ? WB_MD_WIDTH_BYTES : WB_STATUS_NUM_BYTES;
   assign addr_pipe_num_bytes_adj = addr_pipe_num_bytes + addr_pipe_write_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0];
   assign addr_pipe_num_beats_minus1 = (|addr_pipe_num_bytes_adj[0 +: PCIM_ADDR_BYTE_IDX_WIDTH]) ? (addr_pipe_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) : 
                                       (addr_pipe_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) - 1;
   
   always @(posedge clk) 
     if (!rst_n) begin
        wb_pm_awvalid <= 0;
        wb_pm_awaddr <= '{default:'0};
        wb_pm_awlen <= '{default:'0};
        wb_pm_awid <= '{default:'0};
     end
     else begin
        wb_pm_awvalid <= wb_pm_awvalid & pm_wb_awready ? 1'b0 :
                         addr_active & req_qual ? 1'b1 :
                         wb_pm_awvalid;
        wb_pm_awaddr <= addr_active & req_qual ? addr_pipe_write_addr : wb_pm_awaddr;
        wb_pm_awlen <= addr_active & req_qual ? addr_pipe_num_beats_minus1 : wb_pm_awlen;
        wb_pm_awid <= PCIM_WB_AWID;
     end // else: !if(!rst_n)
   
   // Write Pipe
   // Decide if data has to be sent
   // Latch new data to send
   // Send data
   always @(posedge clk)
     if (!rst_n) begin
        wr_active <= 0;
//        req_winner <= 0;
        wr_active_q <= 0;
        wr_active_re_q <= 0;
     end
     else begin
        wr_active <= wr_active & wr_done ? 1'b0 : 
                     start_new_req ? 1'b1 :
                     wr_active;
        
//        req_winner <= start_new_req ? 0 :
//                     req_winner;

        wr_active_q <= wr_active;
        wr_active_re_q <= wr_active_re;
     end // else: !if(!rst_n)

   assign wr_active_re = wr_active & ~wr_active_q;
   
   // Write Data FSM
   // WR_IDLE 
   // WR_GET_DATA
   // WR_REQ
   typedef enum logic [1:0] {WR_IDLE = 0,
                             WR_GET_DATA = 1,
                             WR_REQ = 2} wr_state_t;
   wr_state_t wr_state, wr_state_next;
   always @(posedge clk)
     if (!rst_n) 
        wr_state <= WR_IDLE;
     else
       wr_state <= wr_state_next;

   always_comb begin
      wr_state_next = wr_state;
      case (wr_state)
        WR_IDLE :
          if (wr_active & req_qual) 
            wr_state_next = WR_REQ ;      // WR_GET_DATA;
          else
            wr_state_next = WR_IDLE;

        WR_GET_DATA:
          wr_state_next = WR_REQ;

        WR_REQ:
          if (wb_pm_wvalid && wb_pm_wlast && pm_wb_wready)
            wr_state_next = WR_IDLE;
          else
            wr_state_next = WR_REQ;

      endcase // case (wr_state)
   end // always_comb

   // Data to send
   always @(posedge clk) 
     if (!rst_n) begin
        status_dw_q <= 0;
        desc_wb_limit_q <= DESC_RAM_DEPTH;
        desc_wb_cnt_q <= 0;
        axis_wb_pkt_cnt_q <= 0;
        md_wr_ptr_q <= 0;
        
//        desc_wb_limit_sent <= 0;
//        desc_wb_cnt_sent <= 0;
//        axis_wb_pkt_cnt_sent <= 0;
     end
     else begin
        status_dw_q <= (req_winner == WB_STATUS) & wr_active_re & req_qual ? status_dw :
                       status_dw_q;
        desc_wb_limit_q <= cfg_desc_clr_cdt_limit ? 0 : 
                           (req_winner == WB_STATUS) & wr_active_re & req_qual ? desc_wb_limit :
                           desc_wb_limit_q;
        desc_wb_cnt_q <= cfg_desc_clr_desc_cnt ? 0 : 
                         (req_winner == WB_STATUS) & wr_active_re & req_qual ? desc_wb_cnt :
                         desc_wb_cnt_q;
        axis_wb_pkt_cnt_q <= cfg_axis_clr_pkt_cnt ? 0 : 
                             (req_winner == WB_STATUS) & wr_active_re & req_qual ? axis_wb_pkt_cnt :
                             axis_wb_pkt_cnt_q;
        md_wr_ptr_q <= cfg_wb_clr_wr_ptr ? 0 : 
                       (req_winner == WB_STATUS) & wr_active_re & req_qual ? md_wr_ptr : md_wr_ptr_q;
        
//        desc_wb_limit_sent <= (req_winner == WB_STATUS) & (wr_state == WR_REQ) & wr_done ? desc_wb_limit_q :
//                           desc_wb_limit_sent;
//        desc_wb_cnt_sent <= (req_winner == WB_STATUS) & (wr_state == WR_REQ) & wr_done ? desc_wb_cnt_q :
//                         desc_wb_cnt_sent;
//        axis_wb_pkt_cnt_sent <= (req_winner == WB_STATUS) & (wr_state == WR_REQ) & wr_done ? axis_wb_pkt_cnt_q :
//                             axis_wb_pkt_cnt_sent;
     end // else: !if(!rst_n)

   assign status_dw_sent = status_dw_q;
   assign desc_wb_limit_sent = desc_wb_limit_q;
   assign desc_wb_cnt_sent = desc_wb_cnt_q;
   assign axis_wb_pkt_cnt_sent = axis_wb_pkt_cnt_q;
   assign md_wr_ptr_sent = md_wr_ptr_q;
   
   always_comb begin
      dm_wb_md_comp = sde_pkg::c2h_conv_wb_reg2comp(dm_wb_md);
   end

//    assign wr_pipe_num_bytes = (req_winner == WB_METADATA) ? WB_MD_WIDTH_BYTES : 4;
//    assign wr_pipe_num_bytes_adj = wr_pipe_num_bytes + wr_pipe_lwr_addr;
//    assign wr_pipe_num_beats_minus1 = (|wr_pipe_num_bytes_adj[0 +: PCIM_WR_BYTE_IDX_WIDTH]) ? (wr_pipe_num_bytes_adj >> PCIM_WR_BYTE_IDX_WIDTH) : 
//                                      (wr_pipe_num_bytes_adj >> PCIM_WR_BYTE_IDX_WIDTH) - 1;
   assign wr_pipe_num_beats_minus1 = addr_pipe_num_beats_minus1;
   
//    assign wr_pipe_addr = (req_winner == WB_STATUS) ? cfg_wb_status_addr : dm_wb_md_addr;
   assign wr_pipe_addr = addr_pipe_write_addr;
   
   assign wr_pipe_lwr_addr = wr_pipe_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   
   assign wb_wr_max_bytes = wr_active_re_q  & req_qual ? (PCIM_DATA_WIDTH_BYTES) - wr_pipe_lwr_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] : 
                            PCIM_DATA_WIDTH_BYTES;

   assign wb_wr_num_bytes_total = (req_winner == WB_METADATA) ? WB_MD_WIDTH_BYTES : WB_STATUS_NUM_BYTES;

   assign wb_wr_num_bytes_remain = wb_wr_num_bytes_total - wb_wr_num_bytes_sent;
   
   assign wb_wr_num_bytes_to_send = wb_wr_num_bytes_remain < wb_wr_max_bytes ? wb_wr_num_bytes_remain : wb_wr_max_bytes;

//    always_comb begin
//       wb_wr_strb_to_send = '{default:'0};
//       for (int byte_idx = 0; byte_idx < PCIM_DATA_WIDTH_BYTES; byte_idx++) begin
//          if (byte_idx < wb_wr_num_bytes_to_send)
//            wb_wr_strb_to_send[byte_idx] = 1;
//       end
//    end

   if (DESC_TYPE) 
     assign wb_wr_md = dm_wb_md_comp;
   else
     assign wb_wr_md = dm_wb_md;

   assign wb_wr_data_to_send = (req_winner == WB_STATUS) ? {md_wr_ptr_q, axis_wb_pkt_cnt_q, desc_wb_cnt_q, desc_wb_limit_q, status_dw_q} : wb_wr_md;

   assign wb_wr_strb_to_send = (req_winner == WB_STATUS) ? {WB_STATUS_NUM_BYTES{1'b1}} : {WB_MD_WIDTH_BYTES{1'b1}};
   
   always @(posedge clk)
     if (!rst_n) begin
        wb_wr_idx <= 0;
        wb_wr_num_bytes_sent <= 0;
        
        wb_pm_wvalid <= 0;
        wb_pm_wdata <= '{default:'0};
        wb_pm_wstrb <= '{default:'0};
        wb_pm_wlast <= 0;
     end
     else begin
        wb_wr_idx <= wr_active_re_q & req_qual ? 0 : 
                     wb_pm_wvalid & pm_wb_wready ? wb_wr_idx + 1 :
                     wb_wr_idx;

        wb_wr_num_bytes_sent <= wr_active_re_q  & req_qual ? wb_wr_num_bytes_to_send :
                                wb_pm_wvalid & wb_pm_wlast & pm_wb_wready ? 0 : 
                                wb_pm_wvalid & pm_wb_wready ? wb_wr_num_bytes_sent + wb_wr_num_bytes_to_send :
                                wb_wr_num_bytes_sent;
                                
        wb_pm_wvalid <= wb_pm_wvalid & pm_wb_wready & (wb_wr_idx >= wr_pipe_num_beats_minus1) ? 1'b0 :
                        wr_active_re_q  & req_qual ? 1'b1 :
                        wb_pm_wvalid;

        wb_pm_wdata <= wr_active_re_q & req_qual ? wb_wr_data_to_send << ({wr_pipe_lwr_addr, 3'd0}) : 
                       wb_pm_wvalid & pm_wb_wready ? wb_wr_data_to_send >> ({wb_wr_num_bytes_sent, 3'd0}) :
                       wb_pm_wdata;

        wb_pm_wstrb <= wr_active_re_q & req_qual ? wb_wr_strb_to_send << wr_pipe_lwr_addr :
                       wb_pm_wvalid & pm_wb_wready ? wb_wr_strb_to_send  >> wb_wr_num_bytes_sent : 
                       wb_pm_wstrb;
        
        
        wb_pm_wlast <= wr_active_re_q & req_qual ? (wr_pipe_num_beats_minus1 == 0) :
                       wb_pm_wvalid & pm_wb_wready ? (wb_wr_idx >= (wr_pipe_num_beats_minus1 - 1)) : 
                       wb_pm_wlast;

     end // else: !if(!rst_n)
   
   assign wr_done = wr_active & (~req_qual || (wb_pm_wvalid && wb_pm_wlast && pm_wb_wready));

   assign wb_dm_md_grant = wr_done & (req_winner == WB_METADATA);
   
   // BRESP track FIFO
   // Need room for 2 BRESP 
   localparam WB_BRESP_TRK_FIFO_DEPTH_MINUS1 = WB_BRESP_TRK_FIFO_DEPTH - 1;
   localparam WB_BRESP_TRK_FIFO_WIDTH = REQUESTER_WIDTH + PCIM_ADDR_WIDTH;

   logic wb_bresp_trk_ff_push;
   logic [WB_BRESP_TRK_FIFO_WIDTH-1:0] wb_bresp_trk_ff_push_data;
   logic wb_bresp_trk_ff_pop;
   logic [WB_BRESP_TRK_FIFO_WIDTH-1:0] wb_bresp_trk_ff_pop_data;
   logic                               wb_bresp_trk_ff_valid;
   logic                               wb_bresp_trk_ff_full;
   logic [REQUESTER_WIDTH-1:0]         wb_bresp_trk_ff_pop_requester;
   logic [PCIM_ADDR_WIDTH-1:0]         wb_bresp_trk_ff_pop_addr;
   
   flop_fifo_in #(.WIDTH(WB_BRESP_TRK_FIFO_WIDTH),
                  .DEPTH(WB_BRESP_TRK_FIFO_DEPTH)
                  ) WB_BRESP_TRK_FIFO (.clk         (clk),
                                       .rst_n       (1'b1),
                                       .sync_rst_n  (rst_n),
                                       .cfg_watermark (WB_BRESP_TRK_FIFO_DEPTH_MINUS1),
                                       .push        (wb_bresp_trk_ff_push),
                                       .push_data   (wb_bresp_trk_ff_push_data),
                                       .pop         (wb_bresp_trk_ff_pop),
                                       .pop_data    (wb_bresp_trk_ff_pop_data),
                                       .half_full   (),
                                       .watermark   (wb_bresp_trk_ff_full),
                                       .data_valid  (wb_bresp_trk_ff_valid)
                                       );

   assign wb_bresp_trk_ff_push = wr_active & wr_done & req_qual & ~wb_bresp_trk_ff_full;
   assign wb_bresp_trk_ff_push_data = {req_winner, wr_pipe_addr};
   
   assign wb_bresp_trk_ff_pop = wb_bresp_trk_ff_valid & pm_wb_bvalid;
   assign {wb_bresp_trk_ff_pop_requester, wb_bresp_trk_ff_pop_addr} = wb_bresp_trk_ff_pop_data;

   // Pre-allocate bresp
   logic bresp_prealloc_avail_cnt_inc;
   logic bresp_prealloc_avail_cnt_dec;
   logic [7:0] bresp_prealloc_avail_cnt;
   
   assign bresp_prealloc_avail_cnt_dec = start_new_req;
   assign bresp_prealloc_avail_cnt_inc = wb_bresp_trk_ff_pop;
   
   always @(posedge clk)
     if (!rst_n)
       bresp_prealloc_avail_cnt <= WB_BRESP_TRK_FIFO_DEPTH;
     else
       bresp_prealloc_avail_cnt <= bresp_prealloc_avail_cnt_inc & ~bresp_prealloc_avail_cnt_dec ? bresp_prealloc_avail_cnt + 1 : 
                                   ~bresp_prealloc_avail_cnt_inc & bresp_prealloc_avail_cnt_dec ? bresp_prealloc_avail_cnt - 1 : 
                                   bresp_prealloc_avail_cnt;

   assign bresp_prealloc_avail = (bresp_prealloc_avail_cnt > 0);

   // In config block: 4 error counters - One for each type of error
   // 1 address to latch the first error bresp
   always @(posedge clk)
     if (!rst_n) begin
        wb_cfg_md_bresp_err <= 0;
        wb_cfg_sts_bresp_err <= 0;
     end
     else begin
        wb_cfg_md_bresp_err  <= wb_bresp_trk_ff_pop & (wb_bresp_trk_ff_pop_requester == WB_METADATA) & (pm_wb_bresp != 2'd0);
        wb_cfg_sts_bresp_err <= wb_bresp_trk_ff_pop & (wb_bresp_trk_ff_pop_requester == WB_STATUS) & (pm_wb_bresp != 2'd0);
     end // else: !if(!rst_n)
   
   assign wb_pm_bready = 1;
   
//Simulation checks
//synopsys translate_off
   logic [6:0] cfg_wc_cnt;
   logic       wr_done_q;
   
   assign cfg_wc_cnt = cfg_wc_cnt_minus1 + 1;
   
   always @(posedge clk)
     if (rst_n) begin
        wr_done_q <= wr_done;
        
        if (cfg_desc_cdt_wc_en & (desc_wb_limit_q != 32'h0) & ~wr_done_q & ~desc_cdt_req_pend)
          assert (desc_wb_limit - desc_wb_limit_q <= (cfg_wc_cnt * 2)) else begin
             $display("%m: *** ERROR ***: Desc Limit Write Coalesce Error. desc_wb_limit = 0x%x, desc_wb_limit_q = 0x%x, cfg_wc_cnt = 0x%x. @ %0t", desc_wb_limit, desc_wb_limit_q, cfg_wc_cnt, $time);
             $finish;
          end
        
        if (cfg_wb_desc_cnt_en & cfg_desc_cnt_wc_en & ~wr_done_q & ~desc_cnt_req_pend)
          assert (desc_wb_cnt - desc_wb_cnt_q <= (cfg_wc_cnt * 2)) else begin
             $display("%m: *** ERROR ***: Desc Cnt Write Coalesce Error. desc_wb_cnt = 0x%x, desc_wb_cnt_q = 0x%x, cfg_wc_cnt = 0x%x. @ %0t", desc_wb_cnt, desc_wb_cnt_q, cfg_wc_cnt, $time);
             $finish;
          end
        
        if (cfg_wb_pkt_cnt_en & cfg_pkt_cnt_wc_en & ~wr_done_q & ~pkt_cnt_req_pend)
          assert (axis_wb_pkt_cnt - axis_wb_pkt_cnt_q <= (cfg_wc_cnt * 2)) else begin
             $display("%m: *** ERROR ***: AXIS Pkt Count Write Coalesce Error. axis_wb_pkt_cnt = 0x%x, axis_wb_pkt_cnt_q = 0x%x, cfg_wc_cnt = 0x%x. @ %0t", axis_wb_pkt_cnt, axis_wb_pkt_cnt_q, cfg_wc_cnt, $time);
             $finish;
          end
        
        if (cfg_md_wr_ptr_wc_en && (md_wr_ptr >= md_wr_ptr_q) & ~wr_done_q & ~md_wr_ptr_req_pend)
          assert (md_wr_ptr - md_wr_ptr_q <= (cfg_wc_cnt * 2)) else begin
             $display("%m: *** ERROR ***: Desc Limit Write Coalesce Error. md_wr_ptr = 0x%x, md_wr_ptr_q = 0x%x, cfg_wc_cnt = 0x%x. @ %0t", md_wr_ptr, md_wr_ptr_q, cfg_wc_cnt, $time);
             $finish;
          end
        
     end // if (rst_n)
   
//synopsys translate_on

 `ifndef NO_SDE_DEBUG_ILA
 
   ila_sde_wb SDE_WB_ILA
     (      
            .clk(clk),
      
            // 0 - 7
            .probe0(desc_wb_limit_req),
            .probe1(desc_wb_limit),
            .probe2(desc_wb_cnt_req),
            .probe3(desc_wb_cnt),
            .probe4(axis_wb_pkt_cnt_req),
            .probe5(axis_wb_pkt_cnt),
            .probe6(dm_wb_md_req),
            .probe7(wb_dm_md_grant),
      
            // 8 - 15                                              
            .probe8(wb_pm_awvalid),
            .probe9(wb_pm_awaddr),
            .probe10(pm_wb_awready),
            .probe11(wb_pm_wvalid),
            .probe12(wb_pm_wdata[63:32]),
            .probe13(pm_wb_wready),
            .probe14(dm_wb_md_req_pend),
            .probe15(desc_cdt_req_pend),

            // 16- 23
            .probe16(desc_cnt_req_pend),
            .probe17(pkt_cnt_req_pend),
            .probe18(md_wr_ptr_req_pend),
            .probe19(md_wr_ptr_req),
            .probe20(wr_done),
            .probe21(new_wb_req),
            .probe22(addr_active),
            .probe23(status_req_qual),

            // 24-31
            .probe24(req_qual),
            .probe25(addr_done),
            .probe26(wr_active),
            .probe27(desc_wb_limit_q),
            .probe28(desc_wb_cnt_q),
            .probe29(axis_wb_pkt_cnt_q),
            .probe30(md_wr_ptr_q),
            .probe31(status_req_pend),

            // 32-39
            .probe32(md_wr_ptr),
            .probe33(md_ring_full),
            .probe34(md_wr_addr),
            .probe35(cfg_wc_to_cnt),
            .probe36(cfg_wc_cnt_m1),
            .probe37(desc_cdt_req_wc_cnt),
            .probe38(desc_cnt_req_wc_cnt),
            .probe39(pkt_cnt_req_wc_cnt),
      
            // 40-47
            .probe40(md_wr_ptr_req_wc_cnt),
            .probe41(desc_cdt_req_wc_to_cnt),
            .probe42(desc_cnt_req_wc_to_cnt),
            .probe43(pkt_cnt_req_wc_to_cnt),
            .probe44(md_wr_ptr_req_wc_to_cnt),
            .probe45(desc_wb_limit_wc_req  ),
            .probe46(desc_wb_cnt_wc_req    ),
            .probe47(axis_wb_pkt_cnt_wc_req),
      
            // 48-55
            .probe48(md_wr_ptr_wc_req  )

            );
   
 `endif //  `ifndef NO_SDE_DEBUG_ILA
   
              


   
endmodule // sde_wb
