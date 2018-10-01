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


// H2C Data Mover

module sde_h2c_data #(parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact

                      parameter PCIM_NUM_OT_RD = 32, // Number of outstanding PCIM reads
                      parameter PCIM_DM_ARID = 0,    // This is the ID used for read accesses from Data Mover

                      parameter PCIM_MAX_RD_SIZE = 0, // 0 - 512B, 1 - 1KB, 2 - 2KB, 3 - 4KB
                      
                      parameter PCIM_DATA_WIDTH = 512,
                      parameter PCIM_ID_WIDTH = 3,
                      parameter PCIM_LEN_WIDTH = 8,
                      parameter PCIM_ADDR_WIDTH = 64,
                      parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),
                      
                      parameter BUF_DEPTH = 512,
                      parameter BUF_ADDR_RAM_IDX_WIDTH = $clog2(BUF_DEPTH),
                      parameter BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH,

                      parameter BUF_AUX_DEPTH = 64,
                      parameter BUF_AUX_RAM_ADDR_WIDTH = $clog2(BUF_AUX_DEPTH),

                      parameter USER_BIT_WIDTH = DESC_TYPE ? 1 : 64,

                      // These are internal FIFOs - Dont change unless absolutely required
                      parameter RD_TXN_TRK_FIFO_DEPTH = PCIM_NUM_OT_RD,
                      parameter DP_DATA_OUTPUT_FIFO_DEPTH = 3
                      
                      
                      )
   (
    input                                       clk,
    input                                       rst_n,
    
    // CSR to Data Mover
    //TODO
    output logic                                dm_cfg_rresp_err,
    output logic                                dm_cfg_desc_len_err,
    
    // Desc to Data Mover
    input                                       desc_dm_empty,
    output logic                                dm_desc_pop,
    input                                       sde_pkg::comm_desc_t desc_dm_desc,
    input                                       desc_dm_desc_valid,
    output logic                                dm_desc_cnt_inc,

    // Data Mover to PCIM Interface

    // Read Address to PCIM
    output logic                                dm_pm_arvalid,
    output logic [PCIM_ADDR_WIDTH-1:0]          dm_pm_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]           dm_pm_arlen,
    output logic [PCIM_ID_WIDTH-1:0]            dm_pm_arid,
    input                                       pm_dm_arready,

    // Read Data from PCIM
    input                                       pm_dm_rvalid,
    input [1:0]                                 pm_dm_rresp,
    input [PCIM_DATA_WIDTH-1:0]                 pm_dm_rdata,
    input                                       pm_dm_rlast,
    output logic                                dm_pm_rready,

    // Data Mover to Buffer
//    output logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]   dm_buf_wr_ptr,
    output logic [BUF_ADDR_WIDTH-1:0]           dm_buf_wr_byte_addr,
    output logic                                dm_buf_wr_ptr_msb,
    input [BUF_ADDR_WIDTH:0]                    buf_dm_num_bytes,
    
    output logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]   dm_buf_aux_wr_ptr,
    output logic                                dm_buf_aux_wr_ptr_msb,
    input                                       buf_dm_aux_full,
    
    output logic                                dm_buf_wr,
    output logic [PCIM_DATA_WIDTH-1:0]          dm_buf_data,
    output logic                                dm_buf_eop,
    output logic [USER_BIT_WIDTH-1:0]           dm_buf_user,
    output logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] dm_buf_num_bytes_minus1

    );
   
   localparam PCIM_DATA_WIDTH_BYTES = PCIM_DATA_WIDTH >> 3;
   localparam BUF_SIZE_BYTES = BUF_DEPTH * (PCIM_DATA_WIDTH>>3);
   localparam BUF_DEPTH_MINUS1 = BUF_DEPTH - 1;

   localparam PCIM_MAX_RD_SIZE_BYTES_USER = PCIM_MAX_RD_SIZE == 0 ? 512 :
                                            PCIM_MAX_RD_SIZE == 1 ? 1024 :
                                            PCIM_MAX_RD_SIZE == 2 ? 2048 : 4096;
   
   localparam PCIM_MAX_RD_SIZE_BYTES_DATA_WIDTH = PCIM_DATA_WIDTH_BYTES == 64 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES == 32 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES == 16 ? 4096 :
                                                  PCIM_DATA_WIDTH_BYTES ==  8 ? 2048 :
                                                  PCIM_DATA_WIDTH_BYTES ==  4 ? 1024 :
                                                  PCIM_DATA_WIDTH_BYTES ==  2 ?  512 : 256;
   
   localparam PCIM_MAX_RD_SIZE_BYTES = PCIM_MAX_RD_SIZE_BYTES_DATA_WIDTH > PCIM_MAX_RD_SIZE_BYTES_USER ? PCIM_MAX_RD_SIZE_BYTES_USER : PCIM_MAX_RD_SIZE_BYTES_DATA_WIDTH;
   
                                      
   // Request FSM
   typedef enum logic [2:0] {REQ_IDLE         = 0,
                             REQ_GET_DESC     = 1,
                             REQ_WAIT_DATA    = 2,
                             REQ_ADDR         = 3
                             } req_state_t;

   typedef struct packed {
      logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] txn_src_addr;
      logic desc_spb;
      logic desc_last_txn;
      logic txn_eop;
      logic [12:0] txn_num_bytes;
      logic txn_arlen;
      logic [USER_BIT_WIDTH-1:0] desc_user;
   } rd_txn_trk_t;

   sde_pkg::h2c_if_desc_t curr_desc;

   req_state_t req_state, req_state_next;
   logic        desc_done;
   logic        desc_done_w_eop;
   logic        curr_txn_data_avail;
   logic [63:0] curr_desc_src_addr;
   logic [31:0] curr_desc_len;
   logic [31:0] curr_desc_num_txns;
   logic [31:0] curr_desc_num_bytes;
   logic [12:0] curr_txn_max_bytes;
   logic [BUF_ADDR_WIDTH-1:0] curr_buf_byte_wr_addr;
   logic [BUF_ADDR_WIDTH-1:0] curr_buf_byte_wr_addr_next;
   logic                      curr_buf_byte_wr_addr_msb_next;
   logic [BUF_ADDR_WIDTH:0]   curr_buf_byte_wr_addr_plus_txn_num_bytes;
   logic [BUF_ADDR_WIDTH:0]   curr_buf_byte_wr_addr_plus_txn_num_bytes_rovr;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] curr_buf_ram_wr_addr_next;
   logic                              curr_buf_ram_wr_addr_msb_next;
   logic                              curr_buf_wr_ptr_msb;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0] curr_buf_aux_wr_ptr;
   logic                              curr_buf_aux_wr_ptr_msb;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0] curr_buf_aux_wr_ptr_next;
   logic                              curr_buf_aux_wr_ptr_msb_next;
   logic [63:0]                       curr_txn_src_addr;
   logic [15:0]               curr_txn_num_bytes;
   logic [31:0]               curr_txn_min_num_bytes;
   logic [15:0]               curr_txn_num_bytes_adj;
   logic [PCIM_LEN_WIDTH-1:0] curr_txn_arlen;
   logic                      curr_txn_arlen_2_extra_beats;
   logic                      curr_txn_arlen_1_extra_beat;
   logic                      curr_txn_aux_space_avail;
   logic                      curr_txn_buf_space_avail;
   logic                      curr_txn_space_avail;
   logic                      desc_req_done;
   logic                      rd_txn_trk_ff_full;
   
   logic                      rd_txn_done;
   logic                      data_rx_desc_done;
   logic                      data_rx_done_w_eop;
   
   // REQ FSM
   always @(posedge clk)
     if (!rst_n) 
        req_state <= REQ_IDLE;
     else
       req_state <= req_state_next;
   
   // IDLE -> GET_DESC when desc_dm_desc_valid is true.
   // GET_DESC -> WAIT_DATA immediately. Here flop the required bits
   // ADDR : Send araddr, arlen, arid - wait until Grant - Also start data fetch from RAM
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
            if (curr_txn_space_avail && ~rd_txn_trk_ff_full)
              req_state_next <= REQ_ADDR;
            else
              req_state_next <= REQ_WAIT_DATA;

          REQ_ADDR:
            if (desc_req_done && desc_done)
              req_state_next <= REQ_IDLE;
            else if (desc_req_done)
              req_state_next <= REQ_WAIT_DATA;
            else
              req_state_next <= REQ_ADDR;
          
          default:
            req_state_next <= req_state;

        endcase // case (req_state)
     end // always_comb

   // Pop data from descriptor
   assign dm_desc_pop = (req_state == REQ_IDLE) && desc_dm_desc_valid;

   sde_pkg::h2c_if_desc_t desc_dm_desc_in;
   assign desc_dm_desc_in = sde_pkg::h2c_cnv_desc_comm2if(desc_dm_desc);

   logic [63:0] curr_desc_src_addr_d;
   logic [12:0] curr_desc_max_minus_dest_addr;
   assign curr_desc_src_addr_d = ((req_state == REQ_IDLE) && desc_dm_desc_valid) ? desc_dm_desc_in.src_addr :
                                 desc_req_done ? curr_desc_src_addr + curr_txn_num_bytes : curr_desc_src_addr;
   
   // Save the descriptor and descriptor related stuff
   always @(posedge clk)
     if (!rst_n) begin
        curr_desc <= '{default:'0};
        curr_desc_src_addr <= '{default:'0};
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
        //Optimize//if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
        //Optimize//  curr_desc_src_addr <= desc_dm_desc_in.src_addr;
        //Optimize//else if (desc_req_done)
        //Optimize//  curr_desc_src_addr <= curr_desc_src_addr + curr_txn_num_bytes;
        //Optimize//else
        //Optimize//  curr_desc_src_addr <= curr_desc_src_addr;
        curr_desc_src_addr<= curr_desc_src_addr_d;
        
        // curr_desc_max_minus_dest_addr <= (PCIM_MAX_RD_SIZE == 3) ? 13'h1000 - curr_desc_src_addr_d[11:0] : 
        //                                  (PCIM_MAX_RD_SIZE == 2) ? 13'h0800 - curr_desc_src_addr_d[10:0] : 
        //                                  (PCIM_MAX_RD_SIZE == 1) ? 13'h0400 - curr_desc_src_addr_d[ 9:0] : 13'h0200 - curr_desc_src_addr_d[8:0];
        
        curr_desc_max_minus_dest_addr <= (PCIM_MAX_RD_SIZE_BYTES == 4096) ? 13'h1000 - curr_desc_src_addr_d[11:0] : 
                                         (PCIM_MAX_RD_SIZE_BYTES == 2048) ? 13'h0800 - curr_desc_src_addr_d[10:0] : 
                                         (PCIM_MAX_RD_SIZE_BYTES == 1024) ? 13'h0400 - curr_desc_src_addr_d[ 9:0] : 
                                         (PCIM_MAX_RD_SIZE_BYTES ==  512) ? 13'h0200 - curr_desc_src_addr_d[ 8:0] : 13'h0100 - curr_desc_src_addr_d[ 7:0];
          
        // Length and Decrement after every Txn
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_len <= desc_dm_desc_in.len;
        else if (desc_req_done)
          curr_desc_len <= curr_desc_len - curr_txn_num_bytes;
        else
          curr_desc_len <= curr_desc_len;

        // Number of txns for every descriptor
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_num_txns <= 0;
        else if (desc_req_done)
          curr_desc_num_txns <= curr_desc_num_txns + 1;
        else
          curr_desc_num_txns <= curr_desc_num_txns;

        // Total number of bytes sent
        if ((req_state == REQ_IDLE) && desc_dm_desc_valid)
          curr_desc_num_bytes <= 0;
        else if (desc_req_done)
          curr_desc_num_bytes <= curr_desc_num_bytes + curr_txn_num_bytes;
        else
          curr_desc_num_bytes <= curr_desc_num_bytes;

     end // else: !if(!rst_n)
   
   
   // Max Number of bytes
   // If source is SPB, the maximum bytes is 4K
   //Optimize//assign curr_txn_max_bytes = (PCIM_MAX_RD_SIZE == 3) ? 13'h1000 - curr_desc_src_addr[11:0] : 
   //Optimize//                            (PCIM_MAX_RD_SIZE == 2) ? 13'h0800 - curr_desc_src_addr[10:0] : 
   //Optimize//                            (PCIM_MAX_RD_SIZE == 1) ? 13'h0400 - curr_desc_src_addr[ 9:0] : 13'h0200 - curr_desc_src_addr[8:0];
   assign curr_txn_max_bytes = curr_desc_max_minus_dest_addr;

   // Number of bytes in the transaction 
   //Optimize//assign curr_txn_min_num_bytes =  min_bytes_2 (curr_desc_len, curr_txn_max_bytes);
   assign curr_txn_min_num_bytes = (curr_desc_len[31:13] != 0) ? curr_txn_max_bytes :
                                   (curr_desc_len[12:0] > curr_txn_max_bytes[12:0]) ? curr_txn_max_bytes : curr_desc_len;

   // Space Available in Aux Buffer
   //Optimize//assign curr_txn_aux_space_avail = curr_desc.eop & (curr_desc_len <= curr_txn_min_num_bytes) ? ~buf_dm_aux_full : 1'b1;
   assign curr_txn_aux_space_avail = curr_desc.eop & (curr_desc_len[31:13] == 0) & (curr_desc_len[12:0] <= curr_txn_max_bytes[12:0]) ? ~buf_dm_aux_full : 1'b1;

   // Space Available in Main Buffer
   //Optimize//assign curr_txn_buf_space_avail = (buf_dm_num_bytes >= curr_txn_min_num_bytes);
   if (BUF_ADDR_WIDTH > 12) begin
      logic [BUF_ADDR_WIDTH:0] curr_txn_min_num_bytes_ext;
      assign curr_txn_min_num_bytes_ext = curr_txn_min_num_bytes;
      assign curr_txn_buf_space_avail = (buf_dm_num_bytes >= curr_txn_min_num_bytes_ext);
   end
   else begin
      logic [12:0] buf_dm_num_bytes_ext;
      assign buf_dm_num_bytes_ext = buf_dm_num_bytes;
      assign curr_txn_buf_space_avail = (buf_dm_num_bytes_ext >= curr_txn_min_num_bytes);
   end
   
   // Space Available
   assign curr_txn_space_avail = curr_txn_aux_space_avail & curr_txn_buf_space_avail;

   assign curr_buf_byte_wr_addr_plus_txn_num_bytes = curr_buf_byte_wr_addr + curr_txn_num_bytes;
   assign curr_buf_byte_wr_addr_plus_txn_num_bytes_rovr = curr_buf_byte_wr_addr_plus_txn_num_bytes - BUF_SIZE_BYTES;
   
   assign curr_buf_byte_wr_addr_next = curr_buf_byte_wr_addr_plus_txn_num_bytes >= BUF_SIZE_BYTES ? curr_buf_byte_wr_addr_plus_txn_num_bytes_rovr : curr_buf_byte_wr_addr_plus_txn_num_bytes;

   assign curr_buf_byte_wr_addr_msb_next = curr_buf_byte_wr_addr_plus_txn_num_bytes >= BUF_SIZE_BYTES ? ~curr_buf_wr_ptr_msb : curr_buf_wr_ptr_msb;
   
   assign curr_buf_ram_wr_addr_next = (curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] == ({PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}})) ? curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] : 
                                      curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] == BUF_DEPTH_MINUS1 ? ({BUF_ADDR_RAM_IDX_WIDTH{1'b0}}) : 
                                      curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] + 1;

   assign curr_buf_ram_wr_addr_msb_next = curr_buf_byte_wr_addr_plus_txn_num_bytes >= BUF_SIZE_BYTES ? ~curr_buf_wr_ptr_msb : 
                                          ((curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH  +: BUF_ADDR_RAM_IDX_WIDTH] == BUF_DEPTH_MINUS1) && 
                                           (curr_buf_byte_wr_addr_next[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] != ({PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}))) ? ~curr_buf_wr_ptr_msb : 
                                          curr_buf_wr_ptr_msb;
   
   assign curr_txn_num_bytes_adj = curr_txn_min_num_bytes + curr_desc_src_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0];

   assign curr_buf_aux_wr_ptr_next = (curr_buf_aux_wr_ptr == ({BUF_AUX_RAM_ADDR_WIDTH{1'b1}})) ? 0 : curr_buf_aux_wr_ptr + 1;
   assign curr_buf_aux_wr_ptr_msb_next = (curr_buf_aux_wr_ptr == ({BUF_AUX_RAM_ADDR_WIDTH{1'b1}})) ? ~curr_buf_aux_wr_ptr_msb : curr_buf_aux_wr_ptr_msb;
     
   assign curr_txn_arlen_2_extra_beats = (curr_txn_min_num_bytes[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] + curr_desc_src_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]) > PCIM_DATA_WIDTH_BYTES;
   assign curr_txn_arlen_1_extra_beat = (|curr_txn_min_num_bytes[PCIM_ADDR_BYTE_IDX_WIDTH-1:0] || |curr_desc_src_addr[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]);

   // Save details to be used by the Txn transfered by the Data Transfer Pipe 
   always @(posedge clk)
     if (!rst_n) begin
        curr_buf_byte_wr_addr <=  '{default:'0};
        curr_buf_wr_ptr_msb <= 0;

        curr_buf_aux_wr_ptr <=  '{default:'0};
        curr_buf_aux_wr_ptr_msb <= 0;
        
        curr_txn_src_addr <=  '{default:'0};
        curr_txn_num_bytes <= '{default:'0};
     end
     else begin
        if (desc_done_w_eop)
          curr_buf_byte_wr_addr <= {curr_buf_ram_wr_addr_next, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
        else if (desc_req_done)
          curr_buf_byte_wr_addr <= curr_buf_byte_wr_addr_next;
        else
          curr_buf_byte_wr_addr <= curr_buf_byte_wr_addr;

        if (desc_done_w_eop)
          curr_buf_wr_ptr_msb <= curr_buf_ram_wr_addr_msb_next;
        else if (desc_req_done)
          curr_buf_wr_ptr_msb <= curr_buf_byte_wr_addr_msb_next;
        else
          curr_buf_wr_ptr_msb <= curr_buf_wr_ptr_msb;

        if (desc_done_w_eop)
          curr_buf_aux_wr_ptr <= curr_buf_aux_wr_ptr_next;
        else
          curr_buf_aux_wr_ptr <= curr_buf_aux_wr_ptr;

        if (desc_done_w_eop)
          curr_buf_aux_wr_ptr_msb <= curr_buf_aux_wr_ptr_msb_next;
        else
          curr_buf_aux_wr_ptr_msb <= curr_buf_aux_wr_ptr_msb;

        if ((req_state == REQ_WAIT_DATA)  && ~rd_txn_trk_ff_full)
          curr_txn_src_addr <= curr_desc_src_addr;
        else
          curr_txn_src_addr <= curr_txn_src_addr;
        
        // Number of bytes per txn
        if ((req_state == REQ_WAIT_DATA) && ~rd_txn_trk_ff_full)
          //Optimize// curr_txn_num_bytes <= min_bytes_3 (curr_desc_len, curr_txn_max_bytes, buf_dm_num_bytes);
          curr_txn_num_bytes <= curr_txn_min_num_bytes;
        else
          curr_txn_num_bytes <= curr_txn_num_bytes;

        if ((req_state == REQ_WAIT_DATA) && ~rd_txn_trk_ff_full)
          //Optimize//curr_txn_arlen <= (|curr_txn_num_bytes_adj[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]) ? (curr_txn_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) : 
          //Optimize//                  (curr_txn_num_bytes_adj >> PCIM_ADDR_BYTE_IDX_WIDTH) - 1;
        curr_txn_arlen <= curr_txn_arlen_2_extra_beats ? (curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] + 1) :
                          curr_txn_arlen_1_extra_beat  ? curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] :
                          (curr_txn_min_num_bytes[12:PCIM_ADDR_BYTE_IDX_WIDTH] - 1);
        else
          curr_txn_arlen <= curr_txn_arlen;
        
     end // else: !if(!rst_n)

   // PCIM AR Interface
   assign dm_pm_arvalid = (req_state == REQ_ADDR);
   assign dm_pm_araddr = curr_txn_src_addr;
   assign dm_pm_arlen = curr_txn_arlen; //(curr_txn_num_bytes >> PCIM_ADDR_BYTE_IDX_WIDTH) - 1;
   assign dm_pm_arid = PCIM_DM_ARID;

   // Control Signals to Desc State Machine
   assign desc_req_done = dm_pm_arvalid & pm_dm_arready;
   assign desc_done = desc_req_done & (curr_desc_len <= curr_txn_num_bytes);
   assign desc_done_w_eop = desc_done & curr_desc.eop;

   // Write Address Output to Buffer
//   assign dm_buf_wr_ptr = curr_buf_byte_wr_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH];
   assign dm_buf_wr_byte_addr = curr_buf_byte_wr_addr;
   assign dm_buf_wr_ptr_msb = curr_buf_wr_ptr_msb;

   assign dm_buf_aux_wr_ptr = curr_buf_aux_wr_ptr;
   assign dm_buf_aux_wr_ptr_msb = curr_buf_aux_wr_ptr_msb;
   
   // Read Track FIFO - Used to save AXI TXN Information
   localparam RD_TXN_TRK_FIFO_WIDTH = $bits(rd_txn_trk_t);
   localparam RD_TXN_TRK_FIFO_DEPTH_MINUS1 = RD_TXN_TRK_FIFO_DEPTH - 1;

   logic                             rd_txn_trk_ff_valid;
   logic                             rd_txn_trk_ff_push;
   logic                             rd_txn_trk_ff_pop;
   logic [RD_TXN_TRK_FIFO_WIDTH-1:0] rd_txn_trk_ff_data_out;
   rd_txn_trk_t rd_txn_trk_ff_push_data, rd_txn_trk_ff_pop_data;
   logic [$clog2(RD_TXN_TRK_FIFO_DEPTH) : 0] rd_txn_trk_ff_cnt;
   
   assign rd_txn_trk_ff_push = dm_pm_arvalid & pm_dm_arready;
   assign rd_txn_trk_ff_push_data.txn_src_addr = curr_txn_src_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH];
   assign rd_txn_trk_ff_push_data.desc_spb = curr_desc.spb;
   assign rd_txn_trk_ff_push_data.desc_last_txn = (curr_txn_num_bytes >= curr_desc_len);
   assign rd_txn_trk_ff_push_data.txn_eop = curr_desc.eop && (curr_txn_num_bytes >= curr_desc_len);
   assign rd_txn_trk_ff_push_data.txn_num_bytes = curr_txn_num_bytes[12:0];
   assign rd_txn_trk_ff_push_data.txn_arlen = curr_txn_arlen;
   assign rd_txn_trk_ff_push_data.desc_user = curr_desc.user;
   
   // Read Transaction Track FIFO
   
   ram_fifo_ft #(.WIDTH     (RD_TXN_TRK_FIFO_WIDTH),
                 .PTR_WIDTH ($clog2(RD_TXN_TRK_FIFO_DEPTH)),
                 .WATERMARK (RD_TXN_TRK_FIFO_DEPTH_MINUS1),
                 .PIPELINE (0)
                 ) RD_TXN_TRK_FIFO (.clk       (clk),
                                    .rst_n     (rst_n),
                                    .push      (rd_txn_trk_ff_push),
                                    .push_data (rd_txn_trk_ff_push_data),
                                    .pop       (rd_txn_trk_ff_pop),
                                    .pop_data  (rd_txn_trk_ff_data_out),
                                    .valid     (rd_txn_trk_ff_valid),
                                    .wmark     (rd_txn_trk_ff_full)
                                    );

   
   assign rd_txn_trk_ff_pop = rd_txn_done;
   assign rd_txn_trk_ff_pop_data = rd_txn_trk_ff_data_out;

   always @(posedge clk)
     if (!rst_n)
       rd_txn_trk_ff_cnt <= 0;
     else
       rd_txn_trk_ff_cnt <= (rd_txn_trk_ff_push & ~rd_txn_trk_ff_pop) ? rd_txn_trk_ff_cnt + 1 :
                            (~rd_txn_trk_ff_push & rd_txn_trk_ff_pop) ? rd_txn_trk_ff_cnt - 1 : rd_txn_trk_ff_cnt;

   // TODO: 2 Stages for SPB Read

   // Align Pipe
   logic                         dp_stall;
   logic                         fetch_stall;
   
   // Stage 2 - Mux the SPB Read Pipe or from PCIM
   // TODO: Not supporting SPB now
   logic                         stg2_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0]   stg2_dp_data;
   logic [1:0]                   stg2_dp_resp;
   logic                         stg2_dp_rlast;
   
   logic                         pl2_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0]   pl2_dp_data;
   logic [1:0]                   pl2_dp_resp;
   logic                         pl2_dp_rlast;
   
   assign stg2_dp_valid = pm_dm_rvalid;
   assign stg2_dp_data  = pm_dm_rdata ;
   assign stg2_dp_resp  = pm_dm_rresp ;
   assign stg2_dp_rlast = pm_dm_rlast ;
   assign dm_pm_rready = ~dp_stall;
   
   always @(posedge clk)
     if (!rst_n) begin
        pl2_dp_valid <= 0;
        pl2_dp_data <= 0;
        pl2_dp_resp <= 0;
        pl2_dp_rlast <= 0;
     end
     else begin
        pl2_dp_valid <= ~dp_stall ? stg2_dp_valid : pl2_dp_valid;
        pl2_dp_data  <= ~dp_stall ? stg2_dp_data  : pl2_dp_data ;
        pl2_dp_resp  <= ~dp_stall ? stg2_dp_resp  : pl2_dp_resp ;
        pl2_dp_rlast <= ~dp_stall ? stg2_dp_rlast : pl2_dp_rlast;
     end

   assign rd_txn_done = pl2_dp_valid & ~dp_stall & pl2_dp_rlast;

   // Stage 3 - Compute number of bytes and align first slice
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes_first_slice;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes_last_slice;
   logic stg3_dp_first;
   logic stg3_dp_last;
   logic stg3_dp_eop;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg3_dp_num_bytes_in;
   logic [15:0] stg3_dp_num_bytes_remain;
   logic [PCIM_DATA_WIDTH-1:0]        stg3_dp_data;
   logic                              stg3_dp_valid;
   logic                              stg3_dp_desc_last_txn;
   
   logic                         pl3_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0]   pl3_dp_data;
   logic [1:0]                   pl3_dp_resp;
   logic                         pl3_dp_last;
   logic                         pl3_dp_eop;
   logic [USER_BIT_WIDTH-1:0]    pl3_dp_user;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl3_dp_num_bytes;
   logic [15:0] pl3_dp_num_bytes_remain;
   logic        pl3_dp_desc_last_txn;

   assign stg3_dp_valid = pl2_dp_valid;
   
   assign stg3_dp_num_bytes_first_slice = rd_txn_trk_ff_pop_data.desc_spb ? PCIM_DATA_WIDTH_BYTES: 
                                          PCIM_DATA_WIDTH_BYTES  - (rd_txn_trk_ff_pop_data.txn_src_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH]);
   assign stg3_dp_num_bytes_last_slice = pl3_dp_num_bytes_remain;

   assign stg3_dp_first = pl3_dp_num_bytes_remain == 0;
   
   assign stg3_dp_last = (rd_txn_trk_ff_pop_data.txn_num_bytes <= stg3_dp_num_bytes_first_slice) || (pl3_dp_num_bytes_remain == stg3_dp_num_bytes_in);

   assign stg3_dp_eop = stg3_dp_last & rd_txn_trk_ff_pop_data.txn_eop;
   
   assign stg3_dp_num_bytes = ~stg3_dp_valid ? 0 :
                              stg3_dp_first ? min_bytes_2 (stg3_dp_num_bytes_first_slice, rd_txn_trk_ff_pop_data.txn_num_bytes) : 
                              min_bytes_2(pl3_dp_num_bytes_remain, PCIM_DATA_WIDTH_BYTES);

   assign stg3_dp_num_bytes_in = stg3_dp_first ? min_bytes_2 (stg3_dp_num_bytes_first_slice, rd_txn_trk_ff_pop_data.txn_num_bytes) :
                                 min_bytes_2(pl3_dp_num_bytes_remain, PCIM_DATA_WIDTH_BYTES);
     
   assign stg3_dp_num_bytes_remain =  ~stg3_dp_valid ? pl3_dp_num_bytes_remain : 
                                      stg3_dp_first ? rd_txn_trk_ff_pop_data.txn_num_bytes - stg3_dp_num_bytes_in : 
                                      pl3_dp_num_bytes_remain - stg3_dp_num_bytes_in;
   
   assign stg3_dp_data = stg3_dp_first ? (pl2_dp_data >> ({rd_txn_trk_ff_pop_data.txn_src_addr[0 +: PCIM_ADDR_BYTE_IDX_WIDTH], 3'd0})) : pl2_dp_data;
   
   always @(posedge clk)
     if (!rst_n) begin
        pl3_dp_valid <= 0;
        pl3_dp_data  <= 0;
        pl3_dp_resp  <= 0;
        pl3_dp_last  <= 0;
        pl3_dp_eop   <= 0;
        pl3_dp_user  <= 0;
        pl3_dp_num_bytes <= 0;
        pl3_dp_num_bytes_remain <= 0;
        pl3_dp_desc_last_txn <= 0;
     end
     else begin
        pl3_dp_valid <= ~dp_stall ? stg3_dp_valid : pl3_dp_valid;
        pl3_dp_data  <= ~dp_stall ? stg3_dp_data  : pl3_dp_data ;
        pl3_dp_resp  <= ~dp_stall ? pl2_dp_resp  : pl3_dp_resp ;
        pl3_dp_last  <= ~dp_stall ? stg3_dp_last  : pl3_dp_last ;
        pl3_dp_eop   <= ~dp_stall ? stg3_dp_eop   : pl3_dp_eop  ;
        pl3_dp_user  <= ~dp_stall ? rd_txn_trk_ff_pop_data.desc_user : pl3_dp_user;
        pl3_dp_num_bytes <= ~dp_stall ? stg3_dp_num_bytes : pl3_dp_num_bytes;
        pl3_dp_num_bytes_remain <= ~dp_stall ? stg3_dp_num_bytes_remain : pl3_dp_num_bytes_remain;
        pl3_dp_desc_last_txn <= ~dp_stall ? rd_txn_trk_ff_pop_data.desc_last_txn : pl3_dp_desc_last_txn;
    end

   assign data_rx_desc_done = pl3_dp_valid & ~dp_stall & pl3_dp_last & pl3_dp_desc_last_txn;
   assign data_rx_done_w_eop = pl3_dp_valid & ~dp_stall & pl3_dp_last & pl3_dp_desc_last_txn & pl3_dp_eop;

   // Stage 4 - Accumulate
// _________________________________________________________________________________________________________________________________________________________________
// |   Stage 3  |  Stage 4   |                    Stage 4 Output - Specific Cases               |                    Stage 5 Output - Specific Cases               |
// |------------|------------|------------------------------------------------------------------|------------------------------------------------------------------|
// | Val |  EOP | Val |  EOP |   num_bytes>64        |    num_bytes<64       | num_bytes == 64  |   num_bytes>64        |    num_bytes<64       | num_bytes == 64  |
// | ----|------|-----|------|-----------------------|-----------------------|------------------|-----------------------|-----------------------|------------------|
// |  0  |   x  |  0  |   x  |  Do nothing           |     Do nothing        |   Do nothing     |  Send bubble          |     Send bubble       |   Send bubble    |
// |  0  |   x  |  1  |   0  |  Cannot happen        |     Do nothing        |   Clear          |  Cannot happen        |     Send bubble       |   Send from 4    |
// |  x  |   x  |  1  |   1  |  Copy                 |     Copy              |   Copy           |  Send from 4          |     Send from 4       |   Send from 4    |
// |  1  |   0  |  0  |   x  |  Cannot happen        |     Copy              |   Do nothing     |  Cannot happen        |     Send bubble       |   Send from 3    |
// |  1  |   1  |  0  |   x  |  Cannot happen        |     Do nothing        |   Do nothing     |  Cannot happen        |     Send from 3       |   Send from 3    |
// |  1  |   0  |  1  |   0  |  Save overflow from 3 |     Accumulate into 4 |   Clear          |  Send from 3 & 4      |     Send bubble       |   Send from 3 & 4|
// |  1  |   1  |  1  |   0  |  Save overflow from 3 |     Clear             |   Clear          |  Send from 3 & 4      |     Send from 3 & 4   |   Send from 3 & 4|
// |--------------------------------------------------------------------------------------------|------------------------------------------------------------------|

   logic [PCIM_ADDR_BYTE_IDX_WIDTH+1:0] stg4_dp_num_bytes_comb;
   logic                                stg4_dp_num_bytes_gt_64;
   logic                                stg4_dp_num_bytes_lt_64;
   logic                                stg4_dp_num_bytes_eq_64;
   logic                                stg4_dp_copy;
   logic                                stg4_dp_clear;
   logic                                stg4_dp_accm;
   logic                                stg4_dp_save_ovf;
   logic                                stg4_dp_valid;
   logic [(2*PCIM_DATA_WIDTH)-1:0]      stg4_dp_data_accm_plus_ovf;
   logic [PCIM_DATA_WIDTH-1:0]          stg4_dp_data_accm;
   logic [PCIM_DATA_WIDTH-1:0]          stg4_dp_data_ovf;
   logic [PCIM_DATA_WIDTH-1:0]          stg4_dp_data;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH+1:0] stg4_dp_num_bytes;
   logic                                stg4_dp_eop;
   logic [USER_BIT_WIDTH-1:0]           stg4_dp_user;
   
   logic                         pl4_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0]   pl4_dp_data;
   logic                         pl4_dp_last;
   logic                         pl4_dp_eop;
   logic [USER_BIT_WIDTH-1:0]    pl4_dp_user;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl4_dp_num_bytes;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl4_dp_num_bytes_remain;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] pl4_dp_num_bytes_minus1;
   
   assign stg4_dp_num_bytes_comb = pl3_dp_num_bytes + pl4_dp_num_bytes;
   assign stg4_dp_num_bytes_gt_64 = stg4_dp_num_bytes_comb > PCIM_DATA_WIDTH_BYTES;
   assign stg4_dp_num_bytes_lt_64 = stg4_dp_num_bytes_comb < PCIM_DATA_WIDTH_BYTES;
   assign stg4_dp_num_bytes_eq_64 = stg4_dp_num_bytes_comb == PCIM_DATA_WIDTH_BYTES;

   assign stg4_dp_copy = (pl4_dp_valid & pl4_dp_eop) || 
                         (pl3_dp_valid & ~pl3_dp_eop & ~pl4_dp_valid & stg4_dp_num_bytes_lt_64);
   
   assign stg4_dp_clear = (~pl3_dp_valid & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_eq_64) ||
                          (pl3_dp_valid & ~pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_eq_64) ||
                          (pl3_dp_valid &  pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & (stg4_dp_num_bytes_lt_64 || stg4_dp_num_bytes_eq_64));

   assign stg4_dp_accm = pl3_dp_valid & ~pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_lt_64;

   assign stg4_dp_save_ovf = (pl3_dp_valid & ~pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_gt_64) ||
                             (pl3_dp_valid &  pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_gt_64);

   // Valid 
   assign stg4_dp_valid = stg4_dp_copy ? pl3_dp_valid :
                          stg4_dp_clear ? 1'b0 :
                          stg4_dp_accm || stg4_dp_save_ovf ? 1'b1 :
                          pl4_dp_valid;
   
   // Overflow and Accumulate
   always_comb begin
      stg4_dp_data_accm_plus_ovf = '{default:'0};
      for (int byte_idx = 0; byte_idx < (2*PCIM_DATA_WIDTH_BYTES); byte_idx++)
        if (byte_idx <= pl4_dp_num_bytes_minus1)
          stg4_dp_data_accm_plus_ovf [byte_idx*8 +: 8] = pl4_dp_data[byte_idx*8 +: 8];
        else 
          stg4_dp_data_accm_plus_ovf [byte_idx*8 +: 8] = pl3_dp_data[(byte_idx - pl4_dp_num_bytes)*8 +: 8];
   end

   // Accumulate
   assign stg4_dp_data_accm = stg4_dp_data_accm_plus_ovf[0 +: PCIM_DATA_WIDTH];
   
   // Save Overflow
   assign stg4_dp_data_ovf = stg4_dp_data_accm_plus_ovf[PCIM_DATA_WIDTH +: PCIM_DATA_WIDTH];

   // Data
   assign stg4_dp_data = stg4_dp_copy ? pl3_dp_data : 
                         stg4_dp_accm ? stg4_dp_data_accm :
                         stg4_dp_save_ovf ? stg4_dp_data_ovf : pl4_dp_data;

   // Number of bytes
   assign stg4_dp_num_bytes = stg4_dp_copy ? pl3_dp_num_bytes :
                              stg4_dp_clear ? 0 : 
                              stg4_dp_accm ? stg4_dp_num_bytes_comb : 
                              stg4_dp_save_ovf ? stg4_dp_num_bytes_comb - PCIM_DATA_WIDTH_BYTES : pl4_dp_num_bytes;

   // EOP
   assign stg4_dp_eop = stg4_dp_copy ? pl3_dp_eop :
                        stg4_dp_clear || stg4_dp_accm ? 0 : 
                        stg4_dp_save_ovf ? pl3_dp_eop : pl4_dp_eop;

   // User Bits
   assign stg4_dp_user = stg4_dp_copy || stg4_dp_save_ovf ? pl3_dp_user : pl4_dp_user;
                         
   always @(posedge clk)
     if (!rst_n) begin
        pl4_dp_valid <= 0;
        pl4_dp_data  <= 0;
        pl4_dp_eop   <= 0;
        pl4_dp_user  <= 0;
        pl4_dp_num_bytes <= 0;
        pl4_dp_num_bytes_minus1 <= 0;
     end
     else begin
        pl4_dp_valid <= ~dp_stall ? stg4_dp_valid : pl4_dp_valid;
        pl4_dp_data  <= ~dp_stall ? stg4_dp_data  : pl4_dp_data ;
        pl4_dp_eop   <= ~dp_stall ? stg4_dp_eop   : pl4_dp_eop  ;
        pl4_dp_user  <= ~dp_stall ? stg4_dp_user  : pl4_dp_user ;
        pl4_dp_num_bytes <= ~dp_stall ? stg4_dp_num_bytes : pl4_dp_num_bytes;
        pl4_dp_num_bytes_minus1 <= ~dp_stall ? (stg4_dp_num_bytes - 1) : pl4_dp_num_bytes_minus1;
     end
   
   // Stage 5 - Align
   logic stg5_dp_send_from_3;
   logic stg5_dp_send_from_4;
   logic stg5_dp_send_comb;
   logic stg5_dp_bubble;
   logic stg5_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0] stg5_dp_data;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] stg5_dp_num_bytes_minus1;
   logic                              stg5_dp_eop;
   logic [USER_BIT_WIDTH-1:0]         stg5_dp_user;

   logic                         pl5_dp_valid;
   logic [PCIM_DATA_WIDTH-1:0]   pl5_dp_data;
   logic [1:0]                   pl5_dp_resp;
   logic                         pl5_dp_eop;
   logic [USER_BIT_WIDTH-1:0]    pl5_dp_user;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl5_dp_num_bytes;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH:0] pl5_dp_num_bytes_minus1;
   
   assign stg5_dp_send_from_3 = (pl3_dp_valid & ~pl3_dp_eop & ~pl4_dp_valid & stg4_dp_num_bytes_eq_64) || 
                                (pl3_dp_valid & pl3_dp_eop & ~pl4_dp_valid & (stg4_dp_num_bytes_lt_64 || stg4_dp_num_bytes_eq_64));
   
   assign stg5_dp_send_from_4 = (~pl3_dp_valid & pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_eq_64) || 
                                (pl4_dp_valid & pl4_dp_eop);
   
   assign stg5_dp_send_comb = (pl3_dp_valid & ~pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop & (stg4_dp_num_bytes_gt_64 | stg4_dp_num_bytes_eq_64)) || 
                              (pl3_dp_valid &  pl3_dp_eop & pl4_dp_valid & ~pl4_dp_eop);
   
   assign stg5_dp_bubble = (~pl3_dp_valid & ~pl4_dp_valid) || 
                           (~pl3_dp_valid &  pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_lt_64) || 
                           ( pl3_dp_valid & ~pl3_dp_eop & ~pl4_dp_valid & stg4_dp_num_bytes_lt_64) || 
                           ( pl3_dp_valid & ~pl3_dp_eop &  pl4_dp_valid & ~pl4_dp_eop & stg4_dp_num_bytes_lt_64);

   // Valid
   assign stg5_dp_valid = stg5_dp_send_from_3 ? pl3_dp_valid :
                          stg5_dp_send_from_4 ? pl4_dp_valid :
                          stg5_dp_send_comb ? 1'b1 :
                          stg5_dp_bubble ? 0 : pl5_dp_valid;
   
   // Data
   assign stg5_dp_data = stg5_dp_send_from_3 ? pl3_dp_data :
                         stg5_dp_send_from_4 ? pl4_dp_data :
                         stg5_dp_send_comb ? stg4_dp_data_accm_plus_ovf[0 +: PCIM_DATA_WIDTH] :
                         pl5_dp_data;

   // Number of bytes
   assign stg5_dp_num_bytes = stg5_dp_send_from_3 ? pl3_dp_num_bytes :
                              stg5_dp_send_from_4 ? pl4_dp_num_bytes :
                              stg5_dp_send_comb ? min_bytes_2 (stg4_dp_num_bytes_comb, PCIM_DATA_WIDTH_BYTES) :
                              stg5_dp_bubble ? 0 : 
                              pl5_dp_num_bytes;

   assign stg5_dp_num_bytes_minus1 = stg5_dp_num_bytes - 1;
   

   // EOP
   assign stg5_dp_eop = stg5_dp_send_from_3 ? pl3_dp_eop :
                        stg5_dp_send_from_4 ? pl4_dp_eop :
                        stg5_dp_send_comb   ? pl3_dp_eop & ~stg4_dp_num_bytes_gt_64 : 
                        stg5_dp_bubble ? 0 : pl5_dp_eop;

   // User Bits
   assign stg5_dp_user = stg5_dp_send_from_3 || stg5_dp_send_comb ? pl3_dp_user :
                         stg5_dp_send_from_4 ? pl4_dp_user : pl5_dp_user;

   always @(posedge clk)
     if (!rst_n) begin
        pl5_dp_valid <= 0;
        pl5_dp_data  <= 0;
        pl5_dp_eop   <= 0;
        pl5_dp_user  <= 0;
        pl5_dp_num_bytes <= 0;
        pl5_dp_num_bytes_minus1 <= 0;
     end
     else begin
        pl5_dp_valid <= ~dp_stall ? stg5_dp_valid : pl5_dp_valid;
        pl5_dp_data  <= ~dp_stall ? stg5_dp_data  : pl5_dp_data ;
        pl5_dp_eop   <= ~dp_stall ? stg5_dp_eop   : pl5_dp_eop  ;
        pl5_dp_user  <= ~dp_stall ? stg5_dp_user  : pl5_dp_user ;
        pl5_dp_num_bytes <= ~dp_stall ? stg5_dp_num_bytes : pl5_dp_num_bytes;
        pl5_dp_num_bytes_minus1 <= ~dp_stall ? stg5_dp_num_bytes_minus1 : pl5_dp_num_bytes_minus1;
     end // else: !if(!rst_n)
   
   localparam DP_DATA_OUTPUT_FIFO_DEPTH_MINUS1 = DP_DATA_OUTPUT_FIFO_DEPTH - 1;
   localparam DP_DATA_OUTPUT_FIFO_WIDTH = PCIM_DATA_WIDTH + PCIM_ADDR_BYTE_IDX_WIDTH + USER_BIT_WIDTH + 1;
   
   logic dp_data_out_ff_push;
   logic dp_data_out_ff_pop;
   logic [DP_DATA_OUTPUT_FIFO_WIDTH-1:0] dp_data_out_ff_push_data;
   logic [DP_DATA_OUTPUT_FIFO_WIDTH-1:0] dp_data_out_ff_pop_data;
   logic dp_data_out_ff_full;
   logic dp_data_out_ff_valid;
   logic [$clog2(DP_DATA_OUTPUT_FIFO_DEPTH):0] dp_data_out_ff_cnt;
   
   assign dp_data_out_ff_push = pl5_dp_valid & ~dp_stall;
   assign dp_data_out_ff_push_data = {pl5_dp_data,
                                      pl5_dp_eop,
                                      pl5_dp_user,
                                      pl5_dp_num_bytes_minus1[PCIM_ADDR_BYTE_IDX_WIDTH-1:0]};
   
   // Output fifo for Write Data
   flop_fifo #(.WIDTH(DP_DATA_OUTPUT_FIFO_WIDTH),
               .DEPTH(DP_DATA_OUTPUT_FIFO_DEPTH)
               ) DP_DATA_OUTPUT_FIFO (.clk         (clk),
                                      .rst_n       (1'b1),
                                      .sync_rst_n  (rst_n),
                                      .cfg_watermark (DP_DATA_OUTPUT_FIFO_DEPTH_MINUS1),
                                      .push        (dp_data_out_ff_push),
                                      .push_data   (dp_data_out_ff_push_data),
                                      .pop         (dp_data_out_ff_pop),
                                      .pop_data    (dp_data_out_ff_pop_data),
                                      .half_full   (),
                                      .watermark   (dp_data_out_ff_full),
                                      .data_valid  (dp_data_out_ff_valid)
                                      );
   
   // Back-pressure to Data Pipeline
   assign dp_stall = dp_data_out_ff_full;

   assign dp_data_out_ff_pop = dp_data_out_ff_valid;
   
   assign dm_buf_wr = dp_data_out_ff_valid;
   assign {dm_buf_data,
           dm_buf_eop, 
           dm_buf_user,
           dm_buf_num_bytes_minus1} = dp_data_out_ff_pop_data;

   always @(posedge clk)
     if (!rst_n)
       dp_data_out_ff_cnt <= 0;
     else
       dp_data_out_ff_cnt <= (dp_data_out_ff_push & ~dp_data_out_ff_pop) ? dp_data_out_ff_cnt + 1 :
                             (~dp_data_out_ff_push & dp_data_out_ff_pop) ? dp_data_out_ff_cnt - 1 : dp_data_out_ff_cnt;
   
   // Descriptor data transfer is done
   assign dm_desc_cnt_inc = data_rx_desc_done;
   
   // Error detection
   always @(posedge clk)
     if (!rst_n) begin
        dm_cfg_rresp_err <= 0;
        dm_cfg_desc_len_err <= 0;
     end
     else begin
        dm_cfg_rresp_err <= pl2_dp_valid & (pl2_dp_resp != 2'd0) & pl2_dp_rlast;
        dm_cfg_desc_len_err <= dm_desc_pop & (desc_dm_desc_in.len == 0);
     end
   
   function logic [31:0] min_bytes_2 (input logic [31:0] inp1, input logic [31:0] inp2);
      min_bytes_2 = inp1 > inp2 ? inp2 : inp1;
   endfunction // min_bytes_2

   function logic [31:0] min_bytes_3 (input logic [31:0] inp1, input logic [31:0] inp2, input logic [31:0] inp3);
      min_bytes_3 = min_bytes_2 (min_bytes_2(inp1, inp2), inp3);
   endfunction // min_bytes_3

//Simulation checks
//synopsys translate_off

   logic data_rx_desc_done_q;
   logic data_rx_desc_done_err;
   
   always @(posedge clk)
     if (rst_n) begin
        data_rx_desc_done_q <= 0;
        data_rx_desc_done_err <= 0;
     end
     else begin
        data_rx_desc_done_q <= data_rx_desc_done;
        data_rx_desc_done_err <= data_rx_desc_done_q & data_rx_desc_done;
     end
   
   always @(posedge clk)
     if (rst_n)
       assert (data_rx_desc_done_err != 1'b1) else begin
          $display("%m : *** ERROR ***: data_rx_desc_done_err asserted more than 1 clock.  @%0t", $time);
          $finish;
       end
   
//synopsys translate_on

 `ifndef NO_SDE_DEBUG_ILA
 
   ila_sde_h2c_dm SDE_H2C_DM_ILA 
     (      
      .clk(clk),
      
      // 0 - 7
      .probe0(desc_dm_empty),
      .probe1(dm_desc_pop),
      .probe2(desc_dm_desc_valid),
      .probe3(dm_desc_cnt_inc),
      .probe4(dm_pm_arvalid),
      .probe5(dm_pm_araddr),
      .probe6(dm_pm_arlen),
      .probe7(pm_dm_arready),

      // 8 - 15                                              
      .probe8(pm_dm_rvalid),
      .probe9(pm_dm_rlast),
      .probe10(dm_pm_rready),
//      .probe11(dm_buf_wr_ptr),
      .probe12(dm_buf_wr_ptr_msb),
      .probe13(buf_dm_num_bytes),
      .probe14(dm_buf_aux_wr_ptr),
      .probe15(dm_buf_aux_wr_ptr_msb),

      // 16- 23
      .probe16(buf_dm_aux_full),
      .probe17(dm_buf_wr),
      .probe18(req_state_next),
      .probe19(desc_done),
      .probe20(desc_done_w_eop),
      .probe21(curr_desc_len),
      .probe22(curr_txn_data_avail),
      .probe23(desc_req_done),

      // 24-31
      .probe24(curr_desc_num_txns),
      .probe25(curr_desc_num_bytes),
      .probe26(curr_txn_max_bytes),
      .probe27(curr_txn_min_num_bytes),
      .probe28(curr_txn_num_bytes),
      .probe29(curr_txn_aux_space_avail),
      .probe30(curr_txn_buf_space_avail),
      .probe31(curr_txn_space_avail),

      // 32-39
      .probe32(rd_txn_done),
      .probe33(data_rx_desc_done),
      .probe34(data_rx_done_w_eop),
      .probe35(rd_txn_trk_ff_full),
      .probe36(rd_txn_trk_ff_cnt),
      .probe37(rd_txn_trk_ff_valid),
      .probe38(rd_txn_trk_ff_push),
      .probe39(rd_txn_trk_ff_pop),

      // 40-47
      .probe40(dp_stall),
      .probe41(pl2_dp_valid),
      .probe42(pl3_dp_valid),
      .probe43(pl4_dp_valid),
      .probe44(pl5_dp_valid),
      .probe45(dp_data_out_ff_push),
      .probe46(dp_data_out_ff_pop),
      .probe47(dp_data_out_ff_full),

      // 48-55
      .probe48(dp_data_out_ff_valid),
      .probe49(dp_data_out_ff_cnt)
                            
    );

 `endif //  `ifndef NO_SDE_DEBUG_ILA
   
              
endmodule // sde_h2c_data


    
    
    
