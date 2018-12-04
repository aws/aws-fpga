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

// C2H Data Mover

module sde_c2h_data #(parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact

                      parameter PCIM_DM_AWID = 0, // This is the ID used for write accesses from Data Mover

                      parameter PCIM_MAX_WR_SIZE = 3, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB

                      parameter PCIM_DATA_WIDTH = 512,
                      parameter PCIM_ID_WIDTH = 3,
                      parameter PCIM_LEN_WIDTH = 8,
                      parameter PCIM_ADDR_WIDTH = 64,
                      parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),

                      parameter BUF_DEPTH = 512,
                      parameter BUF_ADDR_RAM_IDX_WIDTH = $clog2(BUF_DEPTH),
                      parameter BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH,

                      parameter USER_BIT_WIDTH = DESC_TYPE ? 1 : 64,
                      parameter BUF_AUX_WIDTH = BUF_ADDR_WIDTH + USER_BIT_WIDTH,

                      // These are internal FIFOs - Dont change unless absolutely required
                      parameter DP_DATA_OUTPUT_FIFO_DEPTH = 4,
                      parameter DP_WB_FIFO_DEPTH = 32,
                      parameter DP_DATA_BRESP_FIFO_DEPTH = 32

                      )
   (
    input                                     clk,
    input                                     rst_n,

    // CSR to Data Mover
    // TODO
    output logic                              dm_cfg_bresp_err,
    output logic                              dm_cfg_desc_len_err,

    output logic                              dm_num_beats_err,
    // Desc to Data Mover
    input                                     desc_dm_empty,
    output logic                              dm_desc_pop,
    input                                     sde_pkg::comm_desc_t desc_dm_desc,
    input                                     desc_dm_desc_valid,
    output logic                              dm_desc_cnt_inc,

    // Data Mover to PCIM Interface

    // Write Address to PCIM
    output logic                              dm_pm_awvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]        dm_pm_awaddr,
    output logic [PCIM_LEN_WIDTH-1:0]         dm_pm_awlen,
    output logic [PCIM_ID_WIDTH-1:0]          dm_pm_awid,
    input                                     pm_dm_awready,

    // Write Data to PCIM
    output logic                              dm_pm_wvalid,
    output logic [PCIM_DATA_WIDTH-1:0]        dm_pm_wdata,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0]   dm_pm_wstrb,
    output logic                              dm_pm_wlast,
    input                                     pm_dm_wready,

    // Bresp from PCIM
    input                                     pm_dm_bvalid,
    input [1:0]                               pm_dm_bresp,
    output logic                              dm_pm_bready,

    // Data Mover to Write-Back Block - Write Back data
    output logic                              dm_wb_md_req,
    output                                    sde_pkg::c2h_reg_wb_t dm_wb_md,
    input                                     wb_dm_md_grant,

    // Data Mover to Buffer
    input                                     buf_dm_aux_valid,
    input [BUF_AUX_WIDTH-1:0]                 buf_dm_aux_data,
    output logic                              dm_buf_aux_pop,

    output logic [BUF_ADDR_WIDTH-1:0]         dm_buf_rd_byte_addr,

    input [BUF_ADDR_WIDTH:0]                  buf_dm_num_bytes, // Difference in pointers + plus num of bytes in last beat

    output logic                              dm_buf_rd,
    output logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] dm_buf_addr,
    input [PCIM_DATA_WIDTH-1:0]               buf_dm_data

    );

   localparam PCIM_DATA_WIDTH_BYTES = PCIM_DATA_WIDTH >> 3;
   localparam BUF_SIZE_BYTES = BUF_DEPTH * (PCIM_DATA_WIDTH>>3);
   localparam BUF_DEPTH_MINUS1 = BUF_DEPTH - 1;

   localparam PCIM_MAX_WR_SIZE_BYTES_USER = PCIM_MAX_WR_SIZE == 0 ? 512 :
                                            PCIM_MAX_WR_SIZE == 1 ? 1024 :
                                            PCIM_MAX_WR_SIZE == 2 ? 2048 : 4096;
   
   localparam PCIM_MAX_WR_SIZE_BYTES_DATA_WIDTH = PCIM_DATA_WIDTH_BYTES == 64 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES == 32 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES == 16 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES ==  8 ? 2048 :
                                                  PCIM_DATA_WIDTH_BYTES ==  4 ? 1024 :
                                                  PCIM_DATA_WIDTH_BYTES ==  2 ?  512 : 256;
   
   localparam PCIM_MAX_WR_SIZE_BYTES = PCIM_MAX_WR_SIZE_BYTES_DATA_WIDTH > PCIM_MAX_WR_SIZE_BYTES_USER ? PCIM_MAX_WR_SIZE_BYTES_USER : PCIM_MAX_WR_SIZE_BYTES_DATA_WIDTH;
   
   // Request FSM
   typedef enum logic [2:0] {REQ_IDLE         = 0,
                             REQ_GET_DESC     = 1,
                             REQ_WAIT_DATA    = 2,
                             REQ_ADDR         = 3,
                             REQ_DATA         = 4,
                             REQ_WAIT_CALC    = 5
                             } req_state_t;

   sde_pkg::c2h_if_desc_t curr_desc;

   req_state_t req_state, req_state_next;
   logic        data_desc_done;
   logic        data_desc_done_w_eop;
   logic        curr_txn_data_avail;
   logic [63:0] curr_desc_dest_addr;
   logic [31:0] curr_desc_len;
   logic [31:0] curr_desc_num_txns;
   logic [31:0] curr_desc_num_bytes;
   logic [12:0] curr_txn_max_bytes;
   logic [BUF_ADDR_WIDTH-1:0] curr_buf_byte_rd_addr;
   logic [BUF_ADDR_WIDTH:0]   curr_buf_byte_rd_addr_plus_txn_num_bytes;
   logic [BUF_ADDR_WIDTH:0]   curr_buf_byte_rd_addr_plus_txn_num_bytes_rovr;
   logic [BUF_ADDR_WIDTH-1:0] curr_buf_byte_rd_addr_next;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] curr_buf_ram_rd_addr_next;
   logic [63:0]                       curr_txn_dest_addr;
   logic [12:0]               curr_txn_num_bytes;
   logic [12:0]               curr_txn_min_num_bytes;
   logic [12:0]               curr_txn_min_num_bytes_adj;
   logic [PCIM_LEN_WIDTH-1:0] curr_txn_awlen;
   logic                      curr_txn_awlen_2_extra_beats;
   logic                      curr_txn_awlen_1_extra_beat;
   logic                      curr_txn_addr_complete;

   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_a_minus_r_d;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_r_minus_a_d;
   logic                              curr_txn_case1_a_gt_r_d;
   logic                              curr_txn_case2_r_gt_a_d;
   logic                              curr_txn_case3_a_eq_r_d;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_a_r_diff_d;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_num_bytes_fi;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_num_bytes_fo;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_a_r_diff;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_dw_minus_a_r_diff;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_num_bytes_sav;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] curr_txn_num_bytes_dw_minus_sav;
   logic                              curr_txn_case1_a_gt_r;
   logic                              curr_txn_case2_r_gt_a;
   logic                              curr_txn_case3_a_eq_r;

   logic                      data_tx_done;
   logic                      data_rd_addr_update;
   logic [BUF_ADDR_WIDTH-1:0] data_rd_addr;

   logic dp_wb_ff_full;
   logic bresp_prealloc_avail;
   
   logic [BUF_ADDR_WIDTH:0] buf_dm_num_bytes_q;
   logic                    buf_dm_aux_valid_q;
   logic [BUF_AUX_WIDTH-1:0] buf_dm_aux_data_q ;

   // Flop things coming from the buffer
   always @(posedge clk)
     if (!rst_n) begin
        buf_dm_num_bytes_q <= '{default:'0};
        buf_dm_aux_valid_q <= 0;
        buf_dm_aux_data_q <= '{default:'0};
     end
     else begin
        buf_dm_num_bytes_q <= buf_dm_num_bytes;
        buf_dm_aux_valid_q <= buf_dm_aux_valid;
        buf_dm_aux_data_q <= buf_dm_aux_data;
     end
   // REQ FSM
   always @(posedge clk)
     if (!rst_n)
        req_state <= REQ_IDLE;
     else
       req_state <= req_state_next;

   // IDLE -> GET_DESC when desc_dm_desc_valid is true.
   // GET_DESC -> WAIT_DATA immediately. Here flop the required bits
   // ADDR : Send awaddr, awlen, awid - wait until Grant - Also start data fetch from RAM
   // DATA : Wait until data transfer is done

   always_comb
     begin
        req_state_next <= req_state;
        case (req_state)
          REQ_IDLE :
            if (desc_dm_desc_valid)
              req_state_next <= REQ_WAIT_DATA; // REQ_GET_DESC;
            else
              req_state_next <= REQ_IDLE;

//          REQ_GET_DESC:
//            req_state_next <= REQ_WAIT_DATA;

          REQ_WAIT_DATA:
            if (curr_txn_data_avail & ~dp_wb_ff_full & bresp_prealloc_avail)
              req_state_next <= REQ_ADDR;
            else
              req_state_next <= REQ_WAIT_DATA;

          REQ_ADDR:
            if (dm_pm_awvalid & pm_dm_awready)
              req_state_next <= REQ_DATA;
            else
              req_state_next <= REQ_ADDR;

          REQ_DATA:
            if (data_tx_done && data_desc_done)
              req_state_next <= REQ_IDLE;
            else if (data_tx_done)
              req_state_next <= REQ_WAIT_CALC;
            else
              req_state_next <= REQ_DATA;

          REQ_WAIT_CALC:
            // Only required to be in this state when servicing multiple packets per descriptor
            // Need to wait 1 clock for the buf_dm_num_bytes to get updated after the end of REQ_DATA phase
            req_state_next <= REQ_WAIT_DATA;

          default:
            req_state_next <= req_state;

        endcase // case (req_state)
     end // always_comb

   // Pop data from descriptor
   assign dm_desc_pop = (req_state == REQ_IDLE) && desc_dm_desc_valid;

   sde_pkg::c2h_if_desc_t desc_dm_desc_in;
   assign desc_dm_desc_in = sde_pkg::c2h_cnv_desc_comm2if(desc_dm_desc);

   logic [63:0] curr_desc_dest_addr_d;
   logic [12:0] curr_desc_max_minus_dest_addr;
   assign curr_desc_dest_addr_d = ((req_state == REQ_IDLE) && desc_dm_desc_valid) ? desc_dm_desc_in.dest_addr :
                                  ((req_state == REQ_DATA) && data_tx_done) ? curr_desc_dest_addr + curr_txn_num_bytes : curr_desc_dest_addr;

   // Save the descriptor and descriptor related stuff
   always @(posedge clk)
     if (!rst_n) begin
        curr_desc <= '{default:'0};
        curr_desc_dest_addr <= '{default:'0};
        curr_desc_max_minus_dest_addr <= '{default:'0};
        curr_desc_len <= '{default:'0};
        curr_desc_num_txns <= 0;
        curr_desc_num_bytes <= 0;
     end
     else begin

        // Save the descriptor
       if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
         curr_desc <= desc_dm_desc_in;
       else
         curr_desc <= curr_desc;

        // Physical Addr and Increment after every Txn
        //Optimize// if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
        //Optimize//   curr_desc_dest_addr <= desc_dm_desc_in.dest_addr;
        //Optimize// else if ((req_state == REQ_DATA) && data_tx_done)
        //Optimize//   curr_desc_dest_addr <= curr_desc_dest_addr + curr_txn_num_bytes;
        //Optimize// else
        //Optimize//   curr_desc_dest_addr <= curr_desc_dest_addr;
        curr_desc_dest_addr <= curr_desc_dest_addr_d;
        // curr_desc_max_minus_dest_addr <=  13'h1000 - curr_desc_dest_addr_d[11:0];
        curr_desc_max_minus_dest_addr <= (PCIM_MAX_WR_SIZE_BYTES == 4096) ? 13'h1000 - curr_desc_dest_addr_d[11:0] : 
                                         (PCIM_MAX_WR_SIZE_BYTES == 2048) ? 13'h0800 - curr_desc_dest_addr_d[10:0] : 
                                         (PCIM_MAX_WR_SIZE_BYTES == 1024) ? 13'h0400 - curr_desc_dest_addr_d[ 9:0] : 
                                         (PCIM_MAX_WR_SIZE_BYTES ==  512) ? 13'h0200 - curr_desc_dest_addr_d[ 8:0] : 13'h0100 - curr_desc_dest_addr_d[ 7:0];
        
        // Length and Decrement after every Txn
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_len <= desc_dm_desc_in.len;
        else if ((req_state == REQ_DATA) && data_tx_done)
          curr_desc_len <= curr_desc_len - curr_txn_num_bytes;
        else
          curr_desc_len <= curr_desc_len;

        // Number of txns for every descriptor
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_num_txns <= 0;
        else if ((req_state == REQ_DATA) && data_tx_done)
          curr_desc_num_txns <= curr_desc_num_txns + 1;
        else
          curr_desc_num_txns <= curr_desc_num_txns;

        // Total number of bytes sent
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_num_bytes <= 0;
        else if ((req_state == REQ_DATA) && data_tx_done)
          curr_desc_num_bytes <= curr_desc_num_bytes + curr_txn_num_bytes;
        else
          curr_desc_num_bytes <= curr_desc_num_bytes;

     end // else: !if(!rst_n)

   // Max Number of bytes
   assign curr_txn_max_bytes = curr_desc_max_minus_dest_addr; // 16'h1000 - curr_desc_dest_addr[11:0];

   // Data Available
   logic [12:0] curr_txn_num_bytes_required;
   assign curr_txn_num_bytes_required = (curr_desc_len[31:13] != 0) ? curr_txn_max_bytes :
                                        (curr_desc_len[12:0] > curr_txn_max_bytes[12:0]) ? curr_txn_max_bytes : curr_desc_len;
   //Optimize// assign curr_txn_data_avail = buf_dm_aux_valid_q || (buf_dm_num_bytes_q_ext >= min_bytes_2 (curr_desc_len, curr_txn_max_bytes_ext));

   assign curr_buf_byte_rd_addr_plus_txn_num_bytes = curr_buf_byte_rd_addr + curr_txn_num_bytes;
   assign curr_buf_byte_rd_addr_plus_txn_num_bytes_rovr = curr_buf_byte_rd_addr_plus_txn_num_bytes - BUF_SIZE_BYTES;

   assign curr_buf_byte_rd_addr_next = curr_buf_byte_rd_addr_plus_txn_num_bytes >= BUF_SIZE_BYTES ? curr_buf_byte_rd_addr_plus_txn_num_bytes_rovr : curr_buf_byte_rd_addr_plus_txn_num_bytes;

   assign curr_buf_ram_rd_addr_next = (curr_buf_byte_rd_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] == ({PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}})) ? curr_buf_byte_rd_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] :
                                      curr_buf_byte_rd_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] == BUF_DEPTH_MINUS1 ? ({BUF_ADDR_RAM_IDX_WIDTH{1'b0}}) :
                                      curr_buf_byte_rd_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] + 1;

//Optimize//   assign curr_txn_min_num_bytes =  min_bytes_3 (curr_desc_len, curr_txn_max_bytes_ext, buf_dm_num_bytes_q_ext);
   if (BUF_ADDR_WIDTH > 12) begin
      logic [BUF_ADDR_WIDTH:0] curr_txn_num_bytes_required_ext;
      assign curr_txn_num_bytes_required_ext = curr_txn_num_bytes_required;
      assign curr_txn_min_num_bytes = curr_txn_num_bytes_required_ext > buf_dm_num_bytes_q ? buf_dm_num_bytes_q : curr_txn_num_bytes_required;
      assign curr_txn_data_avail = buf_dm_aux_valid_q || (buf_dm_num_bytes_q >= curr_txn_num_bytes_required_ext);
   end
   else begin
      logic [12:0]             buf_dm_num_bytes_q_ext;
      assign buf_dm_num_bytes_q_ext = buf_dm_num_bytes_q;
      assign curr_txn_min_num_bytes = curr_txn_num_bytes_required > buf_dm_num_bytes_q_ext ? buf_dm_num_bytes_q : curr_txn_num_bytes_required;
      assign curr_txn_data_avail = buf_dm_aux_valid_q || (buf_dm_num_bytes_q_ext >= curr_txn_num_bytes_required);
   end

   assign curr_txn_min_num_bytes_adj = curr_txn_min_num_bytes + curr_desc_dest_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0];

   assign curr_txn_a_minus_r_d = curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] - curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign curr_txn_r_minus_a_d = curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] - curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign curr_txn_case1_a_gt_r_d = curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] > curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign curr_txn_case2_r_gt_a_d = curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] > curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign curr_txn_case3_a_eq_r_d = curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] == curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign curr_txn_a_r_diff_d = curr_txn_case1_a_gt_r_d ? curr_txn_a_minus_r_d : curr_txn_r_minus_a_d;

   assign curr_txn_awlen_2_extra_beats = (curr_txn_min_num_bytes[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] + curr_desc_dest_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]) > PCIM_DATA_WIDTH_BYTES;
   assign curr_txn_awlen_1_extra_beat = (|curr_txn_min_num_bytes[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] || |curr_desc_dest_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]);

   // Save details to be used by the Txn transfered by the Data Transfer Pipe
   always @(posedge clk)
     if (!rst_n) begin
        curr_buf_byte_rd_addr <=  '{default:'0};
        curr_txn_dest_addr <=  '{default:'0};
        curr_txn_num_bytes <= '{default:'0};
        curr_txn_awlen <= '{default:'0};
        curr_txn_num_bytes_fi <= '{default:'0};
        curr_txn_num_bytes_fo <= '{default:'0};
        curr_txn_a_r_diff <= '{default:'0};
        curr_txn_dw_minus_a_r_diff <= '{default:'0};
        curr_txn_num_bytes_sav <= '{default:'0};
        curr_txn_num_bytes_dw_minus_sav <= '{default:'0};
        curr_txn_case1_a_gt_r <= 0;
        curr_txn_case2_r_gt_a <= 0;
        curr_txn_case3_a_eq_r <= 0;
     end // if (!rst_n)
     else begin
        if ((req_state == REQ_DATA) && data_desc_done_w_eop)
          curr_buf_byte_rd_addr <= {curr_buf_ram_rd_addr_next, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
        else if ((req_state == REQ_DATA) && data_tx_done)
          curr_buf_byte_rd_addr <= curr_buf_byte_rd_addr_next;
        else
          curr_buf_byte_rd_addr <= curr_buf_byte_rd_addr;

        if (req_state == REQ_WAIT_DATA) begin

           // Destination Address
           curr_txn_dest_addr <= curr_desc_dest_addr;

           // Number of bytes per txn
           curr_txn_num_bytes <= curr_txn_min_num_bytes; // min_bytes_3 (curr_desc_len, curr_txn_max_bytes_ext, buf_dm_num_bytes_q_ext);

           // AW Len
           //Optimize// curr_txn_awlen <= (|curr_txn_min_num_bytes_adj[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]) ? (curr_txn_min_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) :
           //Optimize//                   (curr_txn_min_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) - 1;
           curr_txn_awlen <= curr_txn_awlen_2_extra_beats ?  (curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] + 1) :
                             curr_txn_awlen_1_extra_beat  ? curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] :
                             (curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] - 1);

           // Number of Bytes First In (FI = DW - R)
           curr_txn_num_bytes_fi <= (PCIM_DATA_WIDTH_BYTES - curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH]);

           // Number of Bytes First Out (FO = DW - A)
           curr_txn_num_bytes_fo <= (PCIM_DATA_WIDTH_BYTES - curr_desc_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH]);

           // Number of bytes to save
           curr_txn_num_bytes_sav <= curr_txn_case1_a_gt_r_d ? curr_txn_a_minus_r_d : PCIM_DATA_WIDTH_BYTES - curr_txn_r_minus_a_d;

           // Number of bytes to copy from input
           curr_txn_num_bytes_dw_minus_sav <= curr_txn_case1_a_gt_r_d ? PCIM_DATA_WIDTH_BYTES - curr_txn_a_minus_r_d : curr_txn_r_minus_a_d;

           // Diff between Txn Out Addr and Txn In Addr (A_R_DIFF = A>R ? A-R : R-A)
           curr_txn_a_r_diff <= curr_txn_a_r_diff_d;

           // Data Width Minus A_R_DIFF
           curr_txn_dw_minus_a_r_diff <= PCIM_DATA_WIDTH_BYTES - curr_txn_a_r_diff_d;

           // Case 1 : A > R
           curr_txn_case1_a_gt_r <= curr_txn_case1_a_gt_r_d;

           // Case 2 : R > A
           curr_txn_case2_r_gt_a <= curr_txn_case2_r_gt_a_d;

           // Case 3 : R = A
           curr_txn_case3_a_eq_r <= curr_txn_case3_a_eq_r_d;
        end // if (req_state == REQ_WAIT_DATA)

     end // else: !if(!rst_n)

   // Buffer Interface
   logic [BUF_ADDR_WIDTH-1:0] buf_dm_aux_eop_byte_addr;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] buf_dm_aux_eop_num_bytes;
   logic [USER_BIT_WIDTH-1:0]          buf_dm_aux_eop_user;
   assign buf_dm_aux_eop_byte_addr = buf_dm_aux_data_q[0 +: BUF_ADDR_WIDTH];
   assign buf_dm_aux_eop_num_bytes = buf_dm_aux_eop_byte_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] + 1;
   assign buf_dm_aux_eop_user = buf_dm_aux_data_q[BUF_ADDR_WIDTH +: USER_BIT_WIDTH];

   // Read pointer Output to Buffer
   always @(posedge clk)
     if (!rst_n)
       dm_buf_rd_byte_addr <= '{default:'0};
     else begin
        if ((req_state == REQ_DATA) && data_desc_done_w_eop)
          dm_buf_rd_byte_addr <= {curr_buf_ram_rd_addr_next, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
        else if ((req_state == REQ_DATA) && data_tx_done)
          dm_buf_rd_byte_addr <= curr_buf_byte_rd_addr_next;
        else if ((req_state == REQ_DATA) && data_rd_addr_update)
          dm_buf_rd_byte_addr <= data_rd_addr;
        else
          dm_buf_rd_byte_addr <= dm_buf_rd_byte_addr;
     end // else: !if(!rst_n)

   // assign dm_buf_rd_byte_addr = curr_buf_byte_rd_addr;

   // Pop the AUX FIFO
   // Pop when descritor is done and there is an eop at the end of the descriptor
   assign dm_buf_aux_pop = data_desc_done_w_eop;

   // PCIM AW Interface
   assign dm_pm_awvalid = (req_state == REQ_ADDR);
   assign dm_pm_awaddr = curr_desc_dest_addr;
   assign dm_pm_awlen = curr_txn_awlen; //(curr_txn_num_bytes >> PCIM_ADDR_BYTE_IDX_WIDTH) - 1;
   assign dm_pm_awid = PCIM_DM_AWID;

   logic aw_req_done;
   logic aw_req_done_q;
   logic                       dp_stall;

   assign aw_req_done = (req_state == REQ_ADDR) & dm_pm_awvalid & pm_dm_awready;
   always @(posedge clk)
     if (!rst_n)
       aw_req_done_q <= 0;
     else
       aw_req_done_q <= aw_req_done & dp_stall ? 1'b1 :
                    aw_req_done_q & ~dp_stall ? 1'b0 :
                    aw_req_done_q;

   assign curr_txn_addr_complete = aw_req_done || aw_req_done_q;

   // Data Transfer pipe - Will get kicked off when state is ADDR and if data is available
   // Stage 0 - Read - Fetch
   // Stage 1 - RAM Latency - Fetch
   // Stage 2 - RAM Data Read - Fetch
   // Stage 4 - Accumulate
   // Stage 5 - Align Stage

   logic stg0_dp_valid;
   logic [BUF_ADDR_WIDTH:0] stg0_dp_byte_rd_addr_next;
   logic [BUF_ADDR_WIDTH-1:0] stg0_dp_byte_rd_addr;
   logic [BUF_ADDR_WIDTH:0]   stg0_dp_byte_rd_addr_plus_width;
   logic [BUF_ADDR_WIDTH:0]   stg0_dp_byte_rd_addr_plus_width_rovr;
   logic pl0_dp_valid;
   logic [BUF_ADDR_WIDTH-1:0] pl0_dp_byte_rd_addr;

   // Stage 0
   assign stg0_dp_valid = curr_txn_addr_complete ? 1'b1 :
                          (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                          pl0_dp_valid;

   assign stg0_dp_byte_rd_addr_plus_width = pl0_dp_byte_rd_addr + PCIM_DATA_WIDTH_BYTES;
   assign stg0_dp_byte_rd_addr_plus_width_rovr = stg0_dp_byte_rd_addr_plus_width - BUF_SIZE_BYTES;

   assign stg0_dp_byte_rd_addr_next = stg0_dp_byte_rd_addr_plus_width >= BUF_SIZE_BYTES ? stg0_dp_byte_rd_addr_plus_width_rovr : stg0_dp_byte_rd_addr_plus_width;

   assign stg0_dp_byte_rd_addr = (req_state == REQ_IDLE) || (req_state == REQ_GET_DESC) || (req_state == REQ_WAIT_DATA) ? pl0_dp_byte_rd_addr :
                                 curr_txn_addr_complete ? curr_buf_byte_rd_addr : stg0_dp_byte_rd_addr_next;

   // Fetch Pipe
   always @(posedge clk)
     if (!rst_n) begin
        pl0_dp_valid <= 0;
        pl0_dp_byte_rd_addr <= '{default:'0};
     end
     else begin
        pl0_dp_valid <= ~dp_stall ? stg0_dp_valid : pl0_dp_valid;
        pl0_dp_byte_rd_addr <= ~dp_stall ? stg0_dp_byte_rd_addr : pl0_dp_byte_rd_addr;
     end

   // BUF Interface
   assign dm_buf_rd = pl0_dp_valid & ~dp_stall;// & ~prev_txn_ovf_valid;
   assign dm_buf_addr = pl0_dp_byte_rd_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH];

   logic stg1_dp_valid;

   logic pl1_dp_valid;
   logic pl1_dp_rd;
   logic [BUF_ADDR_WIDTH-1:0]  pl1_dp_byte_rd_addr;

   assign stg1_dp_valid = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                          pl0_dp_valid;

   // Stage 1
   // RAM Latency
   always @(posedge clk)
     if (!rst_n) begin
        pl1_dp_valid <= 0;
        pl1_dp_rd <= 0;
        pl1_dp_byte_rd_addr <= '{default:'0};
     end
     else begin
        pl1_dp_valid <= ~dp_stall ? stg1_dp_valid : pl1_dp_valid;
        pl1_dp_rd <= dm_buf_rd && ~data_tx_done;
        pl1_dp_byte_rd_addr <= pl0_dp_byte_rd_addr;
     end // else: !if(!rst_n)

   // Stage 2
   logic stg2_dp_valid;
   logic stg2_dp_ovf;

   logic pl2_dp_valid;
   logic pl2_dp_rd;
   logic [BUF_ADDR_WIDTH-1:0]  pl2_dp_byte_rd_addr;
   logic [PCIM_DATA_WIDTH-1:0] pl2_dp_data;

   logic                       pl2_dp_ovf;
   logic [PCIM_DATA_WIDTH-1:0] pl2_dp_ovf_data;
   logic [BUF_ADDR_WIDTH-1:0]  pl2_dp_ovf_byte_rd_addr;

   assign stg2_dp_valid = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                          (pl1_dp_valid || pl2_dp_ovf);
   assign stg2_dp_ovf = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                        pl1_dp_rd & dp_stall ? 1'b1 :
                        ~dp_stall ? 1'b0 : pl2_dp_ovf;
   // Flop RAM Data
   always @(posedge clk)
     if (!rst_n) begin
        pl2_dp_valid <= 0;
        pl2_dp_rd <= 0;
        pl2_dp_data <= '{default:'0};
        pl2_dp_byte_rd_addr <= '{default:'0};

        pl2_dp_ovf <= 0;
        pl2_dp_ovf_data <= '{default:'0};
        pl2_dp_ovf_byte_rd_addr <= '{default:'0};
     end
     else begin
        pl2_dp_valid <= ~dp_stall ? stg2_dp_valid :
                        pl2_dp_valid;
        pl2_dp_rd  <= ~dp_stall ? (pl2_dp_ovf || pl1_dp_rd) : pl2_dp_rd;
        pl2_dp_data <= ~dp_stall ? (pl2_dp_ovf ? pl2_dp_ovf_data : buf_dm_data) : pl2_dp_data;
        pl2_dp_byte_rd_addr <= ~dp_stall ? (pl2_dp_ovf ? pl2_dp_ovf_byte_rd_addr : pl1_dp_byte_rd_addr) : pl2_dp_byte_rd_addr;

        pl2_dp_ovf <= stg2_dp_ovf;
        pl2_dp_ovf_data <= pl1_dp_rd & dp_stall ? buf_dm_data : pl2_dp_ovf_data;
        pl2_dp_ovf_byte_rd_addr <= pl1_dp_rd & dp_stall ? pl1_dp_byte_rd_addr : pl2_dp_ovf_byte_rd_addr;
     end // else: !if(!rst_n)


   // Stage 3 - Shift Stage and Pre-calculate Stage
   logic stg3_dp_valid_in;
   logic stg3_dp_eop_slice_in;
   logic stg3_dp_first_slice_in;
   logic stg3_dp_first_slice_out;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes_in;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes;
   logic stg3_dp_first;
   logic stg3_dp_last;
   logic stg3_dp_eop;
   logic [15:0] stg3_dp_num_bytes_remain;
   logic stg3_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0] stg3_dp_data;

   logic                       pl3_dp_valid;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl3_dp_num_bytes;
   logic                       pl3_dp_first;
   logic                       pl3_dp_last;
   logic                       pl3_dp_eop;
   logic [PCIM_DATA_WIDTH-1:0] pl3_dp_data;
   logic [15:0]                pl3_dp_num_bytes_remain;

   assign stg3_dp_valid_in = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                             (req_state == REQ_DATA) ? pl2_dp_valid : 1'b0;


   assign stg3_dp_eop_slice_in = pl2_dp_valid &&
                                 (pl2_dp_byte_rd_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH] == buf_dm_aux_eop_byte_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH]) &&
                                 buf_dm_aux_valid_q;

   assign stg3_dp_first_slice_in = ~pl3_dp_valid & pl3_dp_first & pl2_dp_valid;

   assign stg3_dp_num_bytes_in = stg3_dp_first_slice_in & stg3_dp_eop_slice_in ? buf_dm_aux_eop_num_bytes - curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] :
                                 stg3_dp_first_slice_in ? PCIM_DATA_WIDTH_BYTES - curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH] :
                                 stg3_dp_eop_slice_in ? buf_dm_aux_eop_num_bytes : PCIM_DATA_WIDTH_BYTES;

   assign stg3_dp_first = curr_txn_addr_complete ? 1 :
                          pl3_dp_valid & pl3_dp_first ? 1'b0 : pl3_dp_first;

   assign stg3_dp_num_bytes = min_bytes_2(stg3_dp_num_bytes_in, pl3_dp_num_bytes_remain);

   assign stg3_dp_num_bytes_remain = curr_txn_addr_complete ? curr_txn_num_bytes :
                                     pl2_dp_valid ? pl3_dp_num_bytes_remain - stg3_dp_num_bytes :
                                     pl3_dp_num_bytes_remain;

   assign stg3_dp_valid =  stg3_dp_valid_in;

   assign stg3_dp_last = (pl3_dp_num_bytes_remain <= stg3_dp_num_bytes_in);

   assign stg3_dp_eop = stg3_dp_eop_slice_in & (pl3_dp_num_bytes_remain == stg3_dp_num_bytes_in);

   assign stg3_dp_data = stg3_dp_first_slice_in ? pl2_dp_data >> ({curr_buf_byte_rd_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH], 3'b000}) : pl2_dp_data;

   always @(posedge clk)
     if (!rst_n) begin
        pl3_dp_valid <= 0;
        pl3_dp_num_bytes <= 0;
        pl3_dp_first <= 0;
        pl3_dp_last <= 0;
        pl3_dp_eop <= 0;
        pl3_dp_data <= '{default:'0};
        pl3_dp_num_bytes_remain <= 0;
     end // if (!rst_n)
     else begin
        pl3_dp_valid <= ~dp_stall ? stg3_dp_valid : pl3_dp_valid;
        pl3_dp_num_bytes <= ~dp_stall ? stg3_dp_num_bytes : pl3_dp_num_bytes;
        pl3_dp_first <= ~dp_stall ? stg3_dp_first : pl3_dp_first;
        pl3_dp_last <= ~dp_stall ? stg3_dp_last : pl3_dp_last;
        pl3_dp_eop <= ~dp_stall ? stg3_dp_eop : pl3_dp_eop;
        pl3_dp_data <= ~dp_stall ? stg3_dp_data : pl3_dp_data;
        pl3_dp_num_bytes_remain <= ~dp_stall ? stg3_dp_num_bytes_remain : pl3_dp_num_bytes_remain;
     end // else: !if(!rst_n)

   logic stg4_dp_valid;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg4_dp_num_bytes_case1;
   logic stg4_dp_first_case1;
   logic stg4_dp_last_case1;
   logic stg4_dp_eop_case1;
   logic [PCIM_DATA_WIDTH-1:0] stg4_dp_data_case1;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg4_dp_num_bytes_case2;
   logic stg4_dp_first_case2;
   logic stg4_dp_last_case2;
   logic stg4_dp_eop_case2;
   logic [PCIM_DATA_WIDTH-1:0] stg4_dp_data_case2;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg4_dp_num_bytes;
   logic stg4_dp_first;
   logic stg4_dp_last;
   logic stg4_dp_eop;
   logic [PCIM_DATA_WIDTH-1:0] stg4_dp_data;

   // Stage 4 - Accumulate
   logic pl4_dp_valid;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl4_dp_num_bytes;
   logic pl4_dp_first;
   logic pl4_dp_last;
   logic pl4_dp_eop;
   logic [PCIM_DATA_WIDTH-1:0] pl4_dp_data;

   assign stg4_dp_valid = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                          (req_state == REQ_DATA) ? pl3_dp_valid & ~curr_txn_case3_a_eq_r : 1'b0;

   // Case 1 - For all beats - Save (A - R) Bytes from 3
   // Number of Bytes
   assign stg4_dp_num_bytes_case1 = pl3_dp_first & pl3_dp_last ? (pl3_dp_num_bytes - curr_txn_num_bytes_fo) : 
                                    pl3_dp_first ? min_bytes_2(pl3_dp_num_bytes, curr_txn_num_bytes_sav) :
                                    pl3_dp_num_bytes - curr_txn_num_bytes_dw_minus_sav;

   // First
   assign stg4_dp_first_case1 = 1'b0;

   // Last
   assign stg4_dp_last_case1 = pl3_dp_first ? pl3_dp_last & (pl3_dp_num_bytes > curr_txn_num_bytes_fo) :
                               pl3_dp_last & (pl3_dp_num_bytes > curr_txn_num_bytes_dw_minus_sav);

   // EOP
   assign stg4_dp_eop_case1 = pl3_dp_first ? pl3_dp_eop & (pl3_dp_num_bytes > curr_txn_num_bytes_fo) :
                              pl3_dp_eop & (pl3_dp_num_bytes > curr_txn_num_bytes_dw_minus_sav);

   // Data
   assign stg4_dp_data_case1 = pl3_dp_first ? (pl3_dp_data >> {curr_txn_num_bytes_fo, 3'b000}) :
                               (pl3_dp_data >> {curr_txn_num_bytes_dw_minus_sav, 3'b000});

   // Case 2 - 1st Beat - Save Bytes from 3
   //          2nd Beat - Save (DW - (R - A)) Bytes from 3

   // Number of Bytes
   assign stg4_dp_num_bytes_case2 = pl3_dp_first ? pl3_dp_num_bytes : // min_bytes_2(pl3_dp_num_bytes, curr_txn_num_bytes_fi) :
                                    pl3_dp_num_bytes - curr_txn_num_bytes_dw_minus_sav;

   // First
   assign stg4_dp_first_case2 = pl3_dp_first;

   // Last
   assign stg4_dp_last_case2 = pl3_dp_first ? pl3_dp_last :
                               pl3_dp_last & (pl3_dp_num_bytes > curr_txn_num_bytes_dw_minus_sav);

   // EOP
   assign stg4_dp_eop_case2 = pl3_dp_first ? pl3_dp_eop :
                              pl3_dp_eop & (pl3_dp_num_bytes > curr_txn_num_bytes_dw_minus_sav);

   // Data
   assign stg4_dp_data_case2 = pl3_dp_first ? pl3_dp_data :
                               (pl3_dp_data >> {curr_txn_num_bytes_dw_minus_sav, 3'b000});

   assign stg4_dp_num_bytes = curr_txn_case1_a_gt_r ? stg4_dp_num_bytes_case1 : stg4_dp_num_bytes_case2;
   assign stg4_dp_first = curr_txn_case1_a_gt_r ? stg4_dp_first_case1 : stg4_dp_first_case2;
   assign stg4_dp_last = curr_txn_case1_a_gt_r ? stg4_dp_last_case1 : stg4_dp_last_case2;
   assign stg4_dp_eop = curr_txn_case1_a_gt_r ? stg4_dp_eop_case1 : stg4_dp_eop_case2;
   assign stg4_dp_data = curr_txn_case1_a_gt_r ? stg4_dp_data_case1 : stg4_dp_data_case2;

   always @(posedge clk)
     if (!rst_n) begin
        pl4_dp_valid <= 0;
        pl4_dp_num_bytes <= 0;
        pl4_dp_first <= 0;
        pl4_dp_last <= 0;
        pl4_dp_eop <= 0;
        pl4_dp_data <= '{default:'0};
     end // if (!rst_n)
     else begin
        pl4_dp_valid <= ~dp_stall ? stg4_dp_valid : pl4_dp_valid;
        pl4_dp_num_bytes <= ~dp_stall ? stg4_dp_num_bytes : pl4_dp_num_bytes;
        pl4_dp_first <= ~dp_stall ? stg4_dp_first : pl4_dp_first;
        pl4_dp_last <= ~dp_stall ? stg4_dp_last : pl4_dp_last;
        pl4_dp_eop <= ~dp_stall ? stg4_dp_eop : pl4_dp_eop;
        pl4_dp_data <= ~dp_stall ? stg4_dp_data : pl4_dp_data;
     end // else: !if(!rst_n)


   // Stage 5 - Align Stage
   logic stg5_dp_valid_case1;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_comb;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_comb;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case1_first_beat;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case1_other_beats;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case1;
   logic stg5_dp_first_case1;
   logic stg5_dp_last_case1_first_beat;
   logic stg5_dp_last_case1_other_beats;
   logic stg5_dp_last_case1;
   logic stg5_dp_eop_case1_first_beat;
   logic stg5_dp_eop_case1_other_beats;
   logic stg5_dp_eop_case1;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case1_first_beat;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case1_other_beats;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case1;

   logic stg5_dp_valid_case2;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case2_first_beat;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case2_other_beats;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case2;
   logic stg5_dp_first_case2;
   logic stg5_dp_last_case2_first_beat;
   logic stg5_dp_last_case2_other_beats;
   logic stg5_dp_last_case2;
   logic stg5_dp_eop_case2_first_beat;
   logic stg5_dp_eop_case2_other_beats;
   logic stg5_dp_eop_case2;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case2_first_beat;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case2_other_beats;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case2;

   logic stg5_dp_valid_case3;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_case3;
   logic stg5_dp_first_case3;
   logic stg5_dp_last_case3;
   logic stg5_dp_eop_case3;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data_case3;

   logic stg5_dp_valid;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes;
   logic stg5_dp_first;
   logic stg5_dp_last;
   logic stg5_dp_eop;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data;

   logic [PCIM_DATA_WIDTH_BYTES-1:0] stg5_dp_strb_all;
   logic [PCIM_DATA_WIDTH_BYTES-1:0] stg5_dp_strb_first_beat;
   logic [PCIM_DATA_WIDTH_BYTES-1:0] stg5_dp_strb;

   logic [BUF_ADDR_WIDTH-1:0]        stg5_dp_byte_rd_addr;
   logic [BUF_ADDR_WIDTH:0]          stg5_dp_byte_rd_addr_next;
   logic [BUF_ADDR_WIDTH:0]          stg5_dp_byte_rd_addr_rovr;
   logic [7:0]                       stg5_dp_num_beats;

   logic pl5_dp_valid;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl5_dp_num_bytes;
   logic pl5_dp_first;
   logic pl5_dp_last;
   logic pl5_dp_eop;
   logic [PCIM_DATA_WIDTH-1:0] pl5_dp_data;
   logic [PCIM_DATA_WIDTH_BYTES-1:0] pl5_dp_strb;
   logic [BUF_ADDR_WIDTH-1:0]        pl5_dp_byte_rd_addr;
   logic [7:0]                       pl5_dp_num_beats;

   // Combined stg3 and stg4
   always_comb begin
      for (int byte_idx = 0; byte_idx < PCIM_DATA_WIDTH_BYTES; byte_idx++)
        if (byte_idx < pl4_dp_num_bytes)
          stg5_dp_data_comb[byte_idx*8 +: 8] = pl4_dp_data[byte_idx*8 +: 8];
        else
          stg5_dp_data_comb[byte_idx*8 +: 8] = pl3_dp_data[(byte_idx - pl4_dp_num_bytes)*8 +: 8];
   end

   assign stg5_dp_num_bytes_comb = pl3_dp_num_bytes + pl4_dp_num_bytes;

   // Case 1 -

   assign stg5_dp_valid_case1 = pl3_dp_valid;

   // Number of bytes
   assign stg5_dp_num_bytes_case1_first_beat = min_bytes_2(curr_txn_num_bytes_fo, pl3_dp_num_bytes);
   assign stg5_dp_num_bytes_case1_other_beats = pl4_dp_last ? pl4_dp_num_bytes : min_bytes_2(PCIM_DATA_WIDTH_BYTES, stg5_dp_num_bytes_comb);
   assign stg5_dp_num_bytes_case1 = pl3_dp_first ? stg5_dp_num_bytes_case1_first_beat : stg5_dp_num_bytes_case1_other_beats;

   // First
   assign stg5_dp_first_case1 = pl3_dp_first;

   // Last
   assign stg5_dp_last_case1_first_beat = pl3_dp_last & (pl3_dp_num_bytes <= curr_txn_num_bytes_fo);

   assign stg5_dp_last_case1_other_beats = (pl4_dp_last & (pl4_dp_num_bytes <= curr_txn_num_bytes_sav)) ||
                                           (~pl4_dp_last & pl3_dp_last & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));

   assign stg5_dp_last_case1 = pl3_dp_first ? stg5_dp_last_case1_first_beat : stg5_dp_last_case1_other_beats;

   // EOP
   assign stg5_dp_eop_case1_first_beat = pl3_dp_eop & (pl3_dp_num_bytes <= curr_txn_num_bytes_fo);

   assign stg5_dp_eop_case1_other_beats = (pl4_dp_eop & (pl4_dp_num_bytes <= curr_txn_num_bytes_sav)) ||
                                          (~pl4_dp_eop & pl3_dp_eop & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));

   assign stg5_dp_eop_case1 = pl3_dp_first ? stg5_dp_eop_case1_first_beat : stg5_dp_eop_case1_other_beats;


   // First Beat -
   // Copy FO from Stage 3 and Shift
   assign stg5_dp_data_case1_first_beat = pl3_dp_data << {curr_txn_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH], 3'b000};

   // 2nd Beat -
   // Send Combined (Copy a_r_diff from Stage 4, Rest from Stage 3)
   assign stg5_dp_data_case1_other_beats = stg5_dp_data_comb;

   assign stg5_dp_data_case1 = pl3_dp_first ? stg5_dp_data_case1_first_beat : stg5_dp_data_comb;


   // Case 2
   assign stg5_dp_valid_case2 = pl4_dp_valid;

   // Number of Bytes
   assign stg5_dp_num_bytes_case2_first_beat = pl4_dp_last ? pl4_dp_num_bytes : min_bytes_2(stg5_dp_num_bytes_comb, curr_txn_num_bytes_fo);

   assign stg5_dp_num_bytes_case2_other_beats = pl4_dp_last ? pl4_dp_num_bytes :
                                                pl3_dp_last & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav) ? stg5_dp_num_bytes_comb :
                                                min_bytes_2(stg5_dp_num_bytes_comb, PCIM_DATA_WIDTH_BYTES);

   assign stg5_dp_num_bytes_case2 = pl4_dp_first ? stg5_dp_num_bytes_case2_first_beat : stg5_dp_num_bytes_case2_other_beats;

   // First
   assign stg5_dp_first_case2 = pl4_dp_first;

   // Last
   assign stg5_dp_last_case2_first_beat = pl4_dp_last || (~pl4_dp_last & pl3_dp_last & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));
   assign stg5_dp_last_case2_other_beats = pl4_dp_last || (~pl4_dp_last & pl3_dp_last & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));
   assign stg5_dp_last_case2 = pl4_dp_first ? stg5_dp_last_case2_first_beat : stg5_dp_last_case2_other_beats;

   //EOP
   assign stg5_dp_eop_case2_first_beat = pl4_dp_eop || (~pl4_dp_eop & pl3_dp_eop & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));
   assign stg5_dp_eop_case2_other_beats = pl4_dp_eop || (~pl4_dp_eop & pl3_dp_eop & (pl3_dp_num_bytes <= curr_txn_num_bytes_dw_minus_sav));
   assign stg5_dp_eop_case2 = pl4_dp_first ? stg5_dp_eop_case2_first_beat : stg5_dp_eop_case2_other_beats;

   // First Beat -
   // Combine and shift
   assign stg5_dp_data_case2_first_beat = stg5_dp_data_comb << {curr_txn_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH], 3'b000};

   // 2nd Beat -
   // Send Combined (Copy a_r_diff from Stage 4, Rest from Stage 3)
   assign stg5_dp_data_case2_other_beats = stg5_dp_data_comb;

   assign stg5_dp_data_case2 = pl4_dp_first ? stg5_dp_data_case2_first_beat : stg5_dp_data_case2_other_beats;


   // Case 3
   assign stg5_dp_num_bytes_case3 = pl3_dp_num_bytes;
   assign stg5_dp_first_case3 = pl3_dp_first;
   assign stg5_dp_last_case3 = pl3_dp_last;
   assign stg5_dp_eop_case3 = pl3_dp_eop;
   assign stg5_dp_data_case3 = pl3_dp_first ? (pl3_dp_data << {curr_txn_dest_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH], 3'b000}) : pl3_dp_data;
   assign stg5_dp_valid_case3 = pl3_dp_valid;

   assign stg5_dp_valid = (req_state == REQ_DATA) && data_tx_done ? 1'b0 :
                          (req_state == REQ_DATA) ? (curr_txn_case1_a_gt_r ? stg5_dp_valid_case1 :
                                                     curr_txn_case2_r_gt_a ? stg5_dp_valid_case2 : stg5_dp_valid_case3) : 1'b0;
   assign stg5_dp_num_bytes = curr_txn_case1_a_gt_r ? stg5_dp_num_bytes_case1 :
                              curr_txn_case2_r_gt_a ? stg5_dp_num_bytes_case2 : stg5_dp_num_bytes_case3;
   assign stg5_dp_first = curr_txn_case1_a_gt_r ? stg5_dp_first_case1 :
                          curr_txn_case2_r_gt_a ? stg5_dp_first_case2 : stg5_dp_first_case3;
   assign stg5_dp_last = curr_txn_case1_a_gt_r ? stg5_dp_last_case1 :
                         curr_txn_case2_r_gt_a ? stg5_dp_last_case2 : stg5_dp_last_case3;
   assign stg5_dp_eop = curr_txn_case1_a_gt_r ? stg5_dp_eop_case1 :
                        curr_txn_case2_r_gt_a ? stg5_dp_eop_case2 : stg5_dp_eop_case3;
   assign stg5_dp_data = curr_txn_case1_a_gt_r ? stg5_dp_data_case1 :
                         curr_txn_case2_r_gt_a ? stg5_dp_data_case2 : stg5_dp_data_case3;
   // Write Strobe
   always_comb begin
      stg5_dp_strb_all = '{default:'0};
      for (int byte_idx=0; byte_idx < PCIM_DATA_WIDTH_BYTES; byte_idx++) begin
         if (byte_idx < stg5_dp_num_bytes)
           stg5_dp_strb_all[byte_idx] = 1;
      end
   end

   assign stg5_dp_strb_first_beat = stg5_dp_strb_all << curr_txn_dest_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0];

   assign stg5_dp_strb = stg5_dp_first ? stg5_dp_strb_first_beat : stg5_dp_strb_all;

   // Read Byte adress
   assign stg5_dp_byte_rd_addr_next = pl5_dp_byte_rd_addr + stg5_dp_num_bytes;
   assign stg5_dp_byte_rd_addr_rovr = (stg5_dp_byte_rd_addr_next >= BUF_SIZE_BYTES) ? (stg5_dp_byte_rd_addr_next - BUF_SIZE_BYTES) :
                                      stg5_dp_byte_rd_addr_next;
   assign stg5_dp_byte_rd_addr = curr_txn_addr_complete ? curr_buf_byte_rd_addr :
                                 stg5_dp_valid ? stg5_dp_byte_rd_addr_rovr :
                                 pl5_dp_byte_rd_addr;

   // Beats
   assign stg5_dp_num_beats = stg5_dp_valid & stg5_dp_first ? curr_txn_awlen :
                              stg5_dp_valid ? pl5_dp_num_beats - 1 :
                              pl5_dp_num_beats;

   always @(posedge clk)
     if (!rst_n) begin
        pl5_dp_valid <= 0;
        pl5_dp_num_bytes <= 0;
        pl5_dp_first <= 0;
        pl5_dp_last <= 0;
        pl5_dp_eop <= 0;
        pl5_dp_data <= '{default:'0};
        pl5_dp_strb <= '{default:'0};
        pl5_dp_byte_rd_addr <= '{default:'0};
        pl5_dp_num_beats <= '{default:'0};
     end // if (!rst_n)
     else begin
        pl5_dp_valid <= ~dp_stall ? stg5_dp_valid : pl5_dp_valid;
        pl5_dp_num_bytes <= ~dp_stall ? stg5_dp_num_bytes : pl5_dp_num_bytes;
        pl5_dp_first <= ~dp_stall ? stg5_dp_first : pl5_dp_first;
        pl5_dp_last <= ~dp_stall ? stg5_dp_last : pl5_dp_last;
        pl5_dp_eop <= ~dp_stall ? stg5_dp_eop : pl5_dp_eop;
        pl5_dp_data <= ~dp_stall ? stg5_dp_data : pl5_dp_data;
        pl5_dp_strb <= ~dp_stall ? stg5_dp_strb : pl5_dp_strb;
        pl5_dp_byte_rd_addr <= ~dp_stall ? stg5_dp_byte_rd_addr : pl5_dp_byte_rd_addr;
        pl5_dp_num_beats <= ~dp_stall ? stg5_dp_num_beats : pl5_dp_num_beats;
     end // else: !if(!rst_n)



   // Output FIFO
   localparam DP_DATA_OUTPUT_FIFO_DEPTH_MINUS1 = DP_DATA_OUTPUT_FIFO_DEPTH - 1;
   localparam DP_DATA_OUTPUT_FIFO_WIDTH = PCIM_DATA_WIDTH + PCIM_DATA_WIDTH_BYTES + 1;

   logic dp_data_out_ff_push;
   logic dp_data_out_ff_pop;
   logic [DP_DATA_OUTPUT_FIFO_WIDTH-1:0] dp_data_out_ff_pop_data;
   logic dp_data_out_ff_full;
   logic dp_data_out_ff_valid;

   // Output fifo for Write data
   flop_fifo #(.WIDTH(DP_DATA_OUTPUT_FIFO_WIDTH),
               .DEPTH(DP_DATA_OUTPUT_FIFO_DEPTH)
               ) DP_DATA_OUTPUT_FIFO (.clk         (clk),
                                      .rst_n       (1'b1),
                                      .sync_rst_n  (rst_n),
                                      .cfg_watermark (DP_DATA_OUTPUT_FIFO_DEPTH_MINUS1),
                                      .push        (dp_data_out_ff_push),
                                      .push_data   ({pl5_dp_last, pl5_dp_strb, pl5_dp_data}),
                                      .pop         (dp_data_out_ff_pop),
                                      .pop_data    (dp_data_out_ff_pop_data),
                                      .half_full   (),
                                      .watermark   (dp_data_out_ff_full),
                                      .data_valid  (dp_data_out_ff_valid)
                                      );

   // Back-pressure to Data Pipeline
   assign dp_stall = dp_data_out_ff_full;

   assign dp_data_out_ff_push = pl5_dp_valid & ~dp_data_out_ff_full;
   assign dp_data_out_ff_pop = dp_data_out_ff_valid & pm_dm_wready;

   // Output to PCIM interface
   assign {dm_pm_wlast, dm_pm_wstrb, dm_pm_wdata} = dp_data_out_ff_pop_data;
   assign dm_pm_wvalid  = dp_data_out_ff_valid;

   // Output to the FSM
   assign data_rd_addr_update = pl5_dp_valid & ~dp_stall;
   assign data_rd_addr = pl5_dp_byte_rd_addr;

   assign data_tx_done = pl5_dp_valid & ~dp_stall & pl5_dp_last;
   assign data_desc_done = pl5_dp_valid & ~dp_stall & pl5_dp_last & ((curr_desc_len <= curr_txn_num_bytes) || pl5_dp_eop);
   assign data_desc_done_w_eop = pl5_dp_valid & ~dp_stall & pl5_dp_last & pl5_dp_eop;

   // Increment number of completed descriptors
   assign dm_desc_cnt_inc = data_desc_done;

   // Response FIFO - RAM based FT_FIFO
   // Store WB_ADDR (64/48 bit), EOP (1 bit), LEN (32 bit), NUM_BRESP (32 bit)

   localparam DP_WB_FIFO_FIFO_DEPTH_MINUS1 = DP_WB_FIFO_DEPTH - 1;
   localparam DP_WB_FIFO_WIDTH = 1 + 32 + 32 + USER_BIT_WIDTH;

   logic dp_wb_ff_push;
   logic [31:0] dp_wb_ff_push_num_bytes;
   logic [31:0] dp_wb_ff_push_num_bresp_minus1;
   logic [USER_BIT_WIDTH-1:0] dp_wb_ff_push_user;
   logic [DP_WB_FIFO_WIDTH-1:0] dp_wb_ff_push_data;
   logic                        dp_wb_ff_pop;
   logic [DP_WB_FIFO_WIDTH-1:0] dp_wb_ff_pop_data;
   logic                        dp_wb_ff_valid;
   logic [31:0]                 dp_wb_ff_pop_num_bytes;
   logic                        dp_wb_ff_pop_eop;
   logic [31:0]                 dp_wb_ff_pop_num_bresp_minus1;
   logic [USER_BIT_WIDTH-1:0]   dp_wb_ff_pop_user;

   assign dp_wb_ff_push = data_desc_done & ~dp_wb_ff_full;
   assign dp_wb_ff_push_num_bytes = curr_desc_num_bytes + curr_txn_num_bytes;
   assign dp_wb_ff_push_num_bresp_minus1 = curr_desc_num_txns;
   assign dp_wb_ff_push_user = buf_dm_aux_eop_user;
   assign dp_wb_ff_push_data = {pl5_dp_eop, dp_wb_ff_push_num_bytes, dp_wb_ff_push_num_bresp_minus1, dp_wb_ff_push_user};

   ram_fifo_ft #(.WIDTH     (DP_WB_FIFO_WIDTH),
                 .PTR_WIDTH ($clog2(DP_WB_FIFO_DEPTH)),
                 .WATERMARK (DP_WB_FIFO_FIFO_DEPTH_MINUS1),
                 .PIPELINE  (0)
                 ) DP_WB_FIFO (.clk       (clk),
                               .rst_n     (rst_n),
                               .push      (dp_wb_ff_push),
                               .push_data (dp_wb_ff_push_data),
                               .pop       (dp_wb_ff_pop),
                               .pop_data  (dp_wb_ff_pop_data),
                               .valid     (dp_wb_ff_valid),
                               .wmark     (dp_wb_ff_full)
                               );


   assign {dp_wb_ff_pop_eop, dp_wb_ff_pop_num_bytes, dp_wb_ff_pop_num_bresp_minus1, dp_wb_ff_pop_user}  = dp_wb_ff_pop_data;
   assign dp_wb_ff_pop = dm_wb_md_req & wb_dm_md_grant & dp_wb_ff_valid;

   // Response logic
   // BRESP FIFO - Stores BRESP value for each request (Can be 32 deep FIFO)
   localparam DP_DATA_BRESP_FIFO_DEPTH_MINUS1 = DP_DATA_BRESP_FIFO_DEPTH - 1;

   logic                        dp_bresp_ff_push;
   logic                        dp_bresp_ff_pop;
   logic [1:0]                  dp_bresp_ff_pop_data;
   logic                        dp_bresp_ff_full;
   logic                        dp_bresp_ff_valid;
   logic [31:0]                 curr_desc_bresp_cnt;
   logic [31:0]                 curr_desc_bresp_err_cnt;
   logic                        curr_desc_send_to_wb;
   logic                        curr_desc_send_to_wb_q;
   logic                        curr_desc_wb_complete;

   // Flop the BRESP
   flop_fifo_in #(.WIDTH(2),
                  .DEPTH(DP_DATA_BRESP_FIFO_DEPTH)
                  ) DP_DATA_BRESP_FIFO (.clk         (clk),
                                        .rst_n       (1'b1),
                                        .sync_rst_n  (rst_n),
                                        .cfg_watermark (DP_DATA_BRESP_FIFO_DEPTH_MINUS1),
                                        .push        (dp_bresp_ff_push),
                                        .push_data   (pm_dm_bresp),
                                        .pop         (dp_bresp_ff_pop),
                                        .pop_data    (dp_bresp_ff_pop_data),
                                        .half_full   (),
                                        .watermark   (dp_bresp_ff_full),
                                        .data_valid  (dp_bresp_ff_valid)
                                        );
   assign dp_bresp_ff_push = pm_dm_bvalid & ~dp_bresp_ff_full;

   assign dm_pm_bready = ~dp_bresp_ff_full;

   // Keep a count of how many BRESP that have come
   always @(posedge clk)
     if (!rst_n) begin
        curr_desc_bresp_cnt <= 0;
        curr_desc_bresp_err_cnt <= 0;
        curr_desc_send_to_wb_q <= 0;
     end
     else begin
        curr_desc_bresp_cnt <= curr_desc_wb_complete ? 0 :
                               dp_bresp_ff_pop ? curr_desc_bresp_cnt + 1 : curr_desc_bresp_cnt;

        curr_desc_bresp_err_cnt <= curr_desc_wb_complete ? 0 :
                                   dp_bresp_ff_pop & (dp_bresp_ff_pop_data != 2'd0) ? curr_desc_bresp_err_cnt + 1 : curr_desc_bresp_err_cnt;
        curr_desc_send_to_wb_q <= curr_desc_send_to_wb;
     end // else: !if(!rst_n)

   assign curr_desc_send_to_wb = dp_bresp_ff_valid & dp_wb_ff_valid & (curr_desc_bresp_cnt >= dp_wb_ff_pop_num_bresp_minus1);
   assign curr_desc_wb_complete = curr_desc_send_to_wb & curr_desc_send_to_wb_q & dm_wb_md_req & wb_dm_md_grant;
   assign dp_bresp_ff_pop = curr_desc_send_to_wb ? curr_desc_wb_complete : dp_bresp_ff_valid;

   logic [31:0]                     dm_wb_md_len;
   logic                            dm_wb_md_eop;
   logic [USER_BIT_WIDTH-1:0]       dm_wb_md_user;
   logic [31:0]                     dm_wb_md_errcnt;

//FLOPPING    assign dm_wb_md_req = curr_desc_send_to_wb;
//FLOPPING    assign dm_wb_md_eop = dp_wb_ff_pop_eop;
//FLOPPING    assign dm_wb_md_len = dp_wb_ff_pop_num_bytes;
//FLOPPING    assign dm_wb_md_user = dp_wb_ff_pop_user;

   always @(posedge clk)
     if (!rst_n) begin
        dm_wb_md_req <= 0;
        dm_wb_md_eop <= 0;
        dm_wb_md_len <= '{default:'0};
        dm_wb_md_user <= '{default:'0};
        dm_wb_md_errcnt <= 0;
     end
     else begin
        dm_wb_md_req <= dm_wb_md_req & wb_dm_md_grant ? 1'b0 :
                        curr_desc_send_to_wb ? 1'b1 : dm_wb_md_req;
        dm_wb_md_eop <= dp_wb_ff_pop_eop;
        dm_wb_md_len <= dp_wb_ff_pop_num_bytes;
        dm_wb_md_user <= dp_wb_ff_pop_user;
        dm_wb_md_errcnt <= (dp_bresp_ff_pop_data != 2'd0) ? (curr_desc_bresp_err_cnt + 1) : curr_desc_bresp_err_cnt;
     end // else: !if(!rst_n)

   always_comb begin
      dm_wb_md = '{default:'0};
      dm_wb_md.valid = 1;
      dm_wb_md.eop = dm_wb_md_eop;
      dm_wb_md.len = dm_wb_md_len;
      dm_wb_md.user = dm_wb_md_user;
   end

   // Pre-allocate bresp
   logic bresp_prealloc_avail_cnt_inc;
   logic bresp_prealloc_avail_cnt_dec;
   logic [7:0] bresp_prealloc_avail_cnt;
   
   assign bresp_prealloc_avail_cnt_dec = (req_state == REQ_ADDR) & (req_state_next != REQ_ADDR);
   assign bresp_prealloc_avail_cnt_inc = dp_bresp_ff_pop;
   
   always @(posedge clk)
     if (!rst_n)
       bresp_prealloc_avail_cnt <= DP_DATA_BRESP_FIFO_DEPTH;
     else
       bresp_prealloc_avail_cnt <= bresp_prealloc_avail_cnt_inc & ~bresp_prealloc_avail_cnt_dec ? bresp_prealloc_avail_cnt + 1 : 
                                   ~bresp_prealloc_avail_cnt_inc & bresp_prealloc_avail_cnt_dec ? bresp_prealloc_avail_cnt - 1 : 
                                   bresp_prealloc_avail_cnt;

   assign bresp_prealloc_avail = (bresp_prealloc_avail_cnt > 0);

   // Errors
   always @(posedge clk)
     if (!rst_n) begin
        dm_cfg_bresp_err <= 0;
        dm_cfg_desc_len_err <= 0;
     end
     else begin
        dm_cfg_bresp_err <= dp_bresp_ff_valid & dp_bresp_ff_pop & (dp_bresp_ff_pop_data != 2'd0);
        dm_cfg_desc_len_err <= dm_desc_pop & (desc_dm_desc_in.len == 0);
     end // else: !if(!rst_n)


   // Design error
   always @(posedge clk)
     if (!rst_n)
       dm_num_beats_err <= 0;
     else
       dm_num_beats_err <= pl5_dp_valid & ~dp_stall & pl5_dp_last & (pl5_dp_num_beats != 0);

   function logic [31:0] min_bytes_2 (input logic [31:0] inp1, input logic [31:0] inp2);
      min_bytes_2 = inp1 > inp2 ? inp2 : inp1;
   endfunction // min_bytes_2

   function logic [31:0] min_bytes_3 (input logic [31:0] inp1, input logic [31:0] inp2, input logic [31:0] inp3);
      min_bytes_3 = min_bytes_2 (min_bytes_2(inp1, inp2), inp3);
   endfunction // min_bytes_3

 `ifndef NO_SDE_DEBUG_ILA

 ila_sde_c2h_dm SDE_C2H_DM_ILA
   (

    .clk(clk),

    // 0
    .probe0(buf_dm_aux_valid    ),
    .probe1(buf_dm_aux_data     ),
    .probe2(dm_buf_rd_byte_addr ),
    .probe3(buf_dm_num_bytes    ),
    .probe4(dm_buf_rd           ),
    .probe5(dm_buf_addr         ),
    .probe6(req_state           ),
    .probe7(curr_desc_dest_addr ),

    // 8
    .probe8(curr_desc_len           ),
    .probe9(curr_desc_num_txns      ),
    .probe10(curr_desc_num_bytes    ),
    .probe11(curr_txn_data_avail    ),
    .probe12(curr_txn_min_num_bytes ),
    .probe13(curr_buf_byte_rd_addr  ),
    .probe14(curr_txn_dest_addr     ),
    .probe15(curr_txn_num_bytes     ),

    // 16
    .probe16(curr_txn_awlen             ),
    .probe17(curr_txn_num_bytes_fi      ),
    .probe18(curr_txn_num_bytes_fo      ),
    .probe19(curr_txn_a_r_diff          ),
    .probe20(curr_txn_dw_minus_a_r_diff ),
    .probe21(curr_txn_case1_a_gt_r      ),
    .probe22(curr_txn_case2_r_gt_a      ),
    .probe23(curr_txn_case3_a_eq_r      ),

    // 24
    .probe24(data_tx_done         ),
    .probe25(data_desc_done       ),
    .probe26(data_desc_done_w_eop ),
    .probe27(dp_stall             ),
    .probe28(dp_data_out_ff_valid ),
    .probe29(dp_wb_ff_full        ),
    .probe30(dp_wb_ff_valid       ),
    .probe31(dp_bresp_ff_full     ),

    // 32
    .probe32(dp_bresp_ff_valid ),
    .probe33(dm_num_beats_err    ),
    .probe34(pl1_dp_valid        ),
    .probe35(pl1_dp_rd           ),
    .probe36(pl1_dp_byte_rd_addr ),
    .probe37(pl2_dp_valid        ),
    .probe38(pl2_dp_rd           ),
    .probe39(pl2_dp_byte_rd_addr ),

    // 40
    .probe40(pl2_dp_ovf              ),
    .probe41(pl2_dp_ovf_byte_rd_addr ),
    .probe42(pl3_dp_valid            ),
    .probe43(pl3_dp_num_bytes        ),
    .probe44(pl3_dp_first            ),
    .probe45(pl3_dp_last             ),
    .probe46(pl3_dp_eop              ),
    .probe47(pl3_dp_num_bytes_remain ),

    // 48
    .probe48(pl4_dp_valid     ),
    .probe49(pl4_dp_num_bytes ),
    .probe50(pl4_dp_first     ),
    .probe51(pl4_dp_last      ),
    .probe52(pl4_dp_eop       ),
    .probe53(pl5_dp_valid     ),
    .probe54(pl5_dp_num_bytes ),
    .probe55(pl5_dp_first     ),

    // 56
    .probe56(pl5_dp_last         ),
    .probe57(pl5_dp_eop          ),
    .probe58(pl5_dp_byte_rd_addr ),
    .probe59(pl5_dp_num_beats    ),
    .probe60(desc_dm_empty       ),
    .probe61(dm_desc_pop         ),
    .probe62(desc_dm_desc_valid  ),
    .probe63(dm_desc_cnt_inc     )

    );


 `endif //  `ifndef NO_SDE_DEBUG_ILA


`ifndef NO_SIM_CHECK
//Simulation checks
//synopsys translate_off

   always @(posedge clk)
     if (rst_n)
       assert (dm_num_beats_err == 1'b0) else begin
          $display("%m: *** ERROR ***: AXI Write has more beats than expected. @%0t", $time);
          $finish;
       end

//synopsys translate_on
`endif



endmodule // sde_c2h_data

