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


module  cl_tst #(parameter DATA_WIDTH=512, parameter NUM_RD_TAG=512) (
   input clk,
   input rst_n,

   input[31:0] cfg_addr,
   input[31:0] cfg_wdata,
   input cfg_wr,
   input cfg_rd,
   output logic tst_cfg_ack,
   output logic[31:0] tst_cfg_rdata = 0,

   output logic atg_enable,

   output logic[8:0] awid,
   output logic[63:0] awaddr,
   output logic[7:0] awlen,
   output logic awvalid,
   output logic[10:0] awuser,
   input awready,

   output logic[8:0] wid,
   output logic[DATA_WIDTH-1:0] wdata = 0,
   output logic[(DATA_WIDTH/8)-1:0] wstrb = 0,
   output logic wlast,
   output logic wvalid,
   input wready,

   input[8:0] bid,
   input[1:0] bresp,
   input bvalid,
   input[17:0] buser,                  //This is specific to HMC, other interfaces should tie to '0'
   output logic bready,

   output logic[8:0] arid,
   output logic[63:0] araddr,
   output logic[7:0] arlen,
   output logic arvalid,
   output logic[10:0] aruser,
   input arready,

   input[8:0] rid,
   input[DATA_WIDTH-1:0] rdata,
   input[1:0] rresp,
   input rlast,
   input rvalid,
   input[17:0] ruser,
   output logic rready
   );

parameter DATA_DW = DATA_WIDTH / 32;

//--------------------------
// Internal signals
//--------------------------
logic wr_inp;
logic rd_inp;
logic rd_resp_pend;
logic[63:0] wr_cyc_count = 0;                       //Total number of cycles
logic[63:0] wr_loop_count = 0;                      //Total number of times through the RAM
logic[63:0] rd_cyc_count = 0;                       //Total number of cycles (read requests)
logic[63:0] rd_loop_count = 0;                      //Total number of times through loop
logic[63:0] rd_resp_count = 0;                      //Total number of responses

logic[63:0] wr_loop_count_wdata = 0;               //Write loop count with write data (used for read/write sync)

logic[127:0] wr_cfg_inst_rdata;
logic[127:0] rd_cfg_inst_rdata;

logic[127:0] wr_cfg_inst_rdata_q = 0;
logic[127:0] rd_cfg_inst_rdata_q = 0;

logic[63:0] rd_cfg_addr_q_ram_data;              //Address
logic[DATA_WIDTH-1:0] rd_cfg_read_ram_data;     //Read latch data
logic[DATA_WIDTH-1:0] rd_cfg_exp_ram_data;      //Expect data
logic rd_cfg_read_ram_ack;

logic[63:0] rd_cfg_addr_q_ram_data_q = 0;             //Address
logic[DATA_WIDTH-1:0] rd_cfg_read_ram_data_q = 0;     //Read latch data
logic[DATA_WIDTH-1:0] rd_cfg_exp_ram_data_q = 0;      //Expect data

logic[31:0] rd_cfg_error_ram_data;              //Error read latch data

logic[7:0] wr_inst_addr = 0;
logic[127:0] inst_wr_rdata;

logic[7:0] rd_inst_addr = 0;
logic[127:0] inst_rd_rdata;
logic[127:0] inst_rd_rdata_q = 0;

logic[4:0] rd_dat_ram_addr = 0;            //Read return data RAM address
logic[4:0] rd_dat_ram_addr_q = 0;

logic[63:0] wr_timer = 0;
logic[63:0] rd_timer = 0;

logic[31:0] bresp_error_count = 0;               //Bresp error count
logic[31:0] rresp_error_count = 0;               //Read respone error count

logic[31:0] bresp_error_first = 0;               //First errored BRESP user[27:0], 2'b00, bresp[1:0]
logic[31:0] rresp_error_first = 0;               //First errored RRESP user[27:0], 2'b00, rresp[1:0]

logic pre_sync_rst_n;
logic sync_rst_n;

typedef enum logic[1:0] {
   WR_IDLE = 0,
   WR_ADDR = 1,
   WR_DAT = 2
   } wr_state_t;

wr_state_t wr_state, wr_state_nxt;

logic[NUM_RD_TAG-1:0] rd_tag_avail = {NUM_RD_TAG{1'b1}};               //Which tags are available

//logic[63:0] wr_addr_rec [31:0];
//logic[5:0] wr_addr_rec_ptr;
//logic wr_addr_rec_single;
//logic[4:0] wr_addr_rec_index;
//logic cfg_rec_sel;
//
//logic[63:0] rd_addr_rec [31:0];
//logic[5:0] rd_addr_rec_ptr;

// End internal signls
//--------------------------------

//Sync reset
always_ff @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end

//-------------------------------------------
// configuration
//-------------------------------------------

//Offset 0x00: 
//             0 - Continuous mode - Keep looping through all the isntructions.
//             1 - Incrementing loop data (every time through loop increment the start data)
//             2 - PRBS mode (else incremeting).  Data will be generated with PRBS.  If not enabled, data will be incrementing per DW
//             3 - Read compare enable.  Do read compare.  Note if this is enabled the address/data in the read instructions must match the write instructinons
//             4 - Sync mode (read/write) -- This makes sure don't issue a read if write hasn't been issued (looking at wr_count/rd_count).  ***Generally should set this if Read Compare Enable.
//             5 - Iteration mode run for a certain number of iterations (see 0xc0)
//             6 - Loop higher address enable (enable shift/mask for higher addresses).  Each time through the loop will increment some upper address bits (see bits 13:8, 21:16)
//             7 - User ID mode - In this mode the USER bits come from the Instruction not from length (PCIe)
//
//             13:8 - Write Address loop shift (in higher address enable, how much to shift the loop count by).  Every time through the loop will increment a counter.  The counter will be logically OR'ed with the address.  This is how much to shift the counter by.
//             21:16 - Read Address loop shift.  Same thing for reads
//             24 - Incrementing ID mode (ID increments rather than first one available
//             25 - Constant data mode (all DW same)
//
//Offset 0x04:
//             15:0 - Read Start -- This is not implemented (not sure we need this)
//             31:0 - Max Write ahead -- This is not implemented (not sure we need this)
//Offset 0x08:
//             0 - Write Go (read back write in progress) - Write this bit to start executing the write instructions.  Reads back '1' while write instructions are in progress. 
//             1 - Read Go (read back write in progress) - Write this bit to start executing the read instructions.  Reads back '1' while read instructions are in progress.
//             2 - Read response pending (read only).  REad only, reads back '1' while read responses are pending.
//Offset 0x0c:
//             0 - Write reset - Doesn't do anything.
//             1 - Read reset - Doesn't do anything.
//Offset 0x10:
//             15:0 - Write Num Inst - Number of write instructions
//             31:16 - Read Num inst - Number of read instructions
//Offset 0x14:
//             3:0 - Max Read outstanding - Max number of read requests to issue (how many simultaneous read requests)
//
// Offset 0x1c: Write Index  - Write instruction Index            
// Offset 0x20: Write address low - Write instruction address
// Offset 0x24: Write address high - Write instruction address
// Offset 0x28: Write data - Write instruction start data.  All other data will be incrementing or PRBS
// Offset 0x2c: Write length/User - Write instruction length (number of data phases.  note there are no partial data phases)
//       7:0 - Length -- this is the number of AXI data phases.   Lower address bits define first data offset
//       15:8 - Last data adj -- Number of DW to adj last data phase (0 means all DW are valid, 1 means all but 1DW valid, etc...)
//       31:16 - User
//
// Offset 0x30: 0 - A value of 1 will drive ATG transactions to DDR. A value of 0 will drive PCIS/XDMA transactions to DDR.
// Offset 0x3c: Read Index - Read instruction index
// Offset 0x40: Read address low - REad instruction address
// Offset 0x44: Read address high - REad instruction address
// Offset 0x48: Read data - Read instruction compare start data.  This should be the same as the Write data if doing compares.  If not doing compares, this is don't care.
// Offset 0x4c: Read length/User - Read Length (number of data phaes.
//       7:0 - Length
//       15:8 - Last data adj - Number of DW to adj last data phase (0 means all DW are valid, 1 means all but 1DW valid, etc...
//       31:16 - User
//
// Offset 0x60: Rd Ram Addr - Read RAM index.  This RAM contains the last 32 data phases.  This is a status RAM to give information on the last 32 received read data
// Offset 0x64: Rd Cycle Addr Low - Read address
// Offset 0x68: Rd Cycle Addr High
// Offset 0x6c: Rd Ram Data - Read Data received
// Offset 0x70: Rd Exp Data - Expected Read data
// Offset 0x74: Rd Ram Write Pointer - Rd RAM write pointer (write pointer - 1 is last location that was written)
//
// Offset 0x80: Write Cyc Count low - Status keeps track of the number of writes performed
// Offset 0x84: Write Cyc Count high
// Offset 0x88: Read Cyc Count low - Status keeps track of the number of reads performed
// Offset 0x8c: Read Cyc Count high
//
//Offset 0x90: write number of loop iterations low - Status number of loops (note this is 1-based)
//Offset 0x94: write number of loop iterations high
//Offset 0x98: read number of loop iterations low
//Offset 0x9c: read number of loop iterations high
//
//Offset 0xa0: Read Resp count low - Number of read responses received
//Offset 0xa4: Read Resp count high
//
//
//Offset 0xb0:    Error status, bit 0 set if got compare error
//             0 - Error
//Offset 0xb4: error addr low    -- Address of error
//Offset 0xb8: error addr high
//Offset 0xbc: error data index  -- Where the error is in the Rd RAM (should be last location)
//
//Offset 0xc0: Write Loop count low - In loop mode number of times loop
//Offset 0xc4: Write Loop count high
//Offset 0xc8: Read Loop count low
//Offset 0xcc: Read Loop count high
//
//Offset 0xd0: Bresp error count
//Offset 0xd4: First errored Bresp value
//    31:4 - User
//    1:0 - resp
//Offset 0xd8: Resp error count
//Offset 0xdc: First errored Rresp value
//    31:4 - User
//    1:0 - resp
//
//Offset 0xf0: Write Timer Low - Status length of time the write state machine was busy (can use to get bandwidth calculation)
//Offset 0xf4: Write Timer high
//Offset 0xf8: Read Timer low - Status length of time the read state machine was busy (can use to get bandwidth calculation)
//Offset 0xfc: Read Timer high


//---------------------------------------------
// Flop R interface for timing
//---------------------------------------------
logic[8:0] rid_q = 0;
logic[DATA_WIDTH-1:0] rdata_q = 0;
logic[1:0] rresp_q = 0;
logic rlast_q = 0;
logic rvalid_q = 0;

always @(posedge clk)
   begin
      rid_q <= rid;
      rdata_q <= rdata;
      rresp_q <= rresp;
      rlast_q <= rlast;
      rvalid_q <= rvalid;
   end

//
//---------------------------------------

logic cfg_rd_cmp_error = 0;
logic[63:0] cfg_rd_cmp_error_address = 0;

logic[15:0] cfg_rd_data_index = 0;

logic cfg_cont_mode = 0;
logic cfg_inc_data_loop_mode = 0;
logic cfg_prbs_mode = 0;
logic cfg_rd_compare_en = 0;
logic cfg_sync_mode = 0;
logic cfg_iter_mode = 0;
logic cfg_loop_addr_mode = 0;
logic cfg_user_mode = 0;
logic[5:0] cfg_wr_loop_addr_shift = 0;
logic[5:0] cfg_rd_loop_addr_shift = 0;
logic cfg_inc_id_mode;
logic cfg_const_data_mode = 0;

logic cfg_atg_enable = 0;
assign atg_enable = cfg_atg_enable;

logic[15:0] cfg_read_start = 0;
logic[15:0] cfg_max_write = 0;

logic[8:0] cfg_max_read_req = (NUM_RD_TAG>32)? 31: NUM_RD_TAG-1;        //Number of tags allowed (0-based)

logic cfg_wr_go;
logic cfg_rd_go;
logic cfg_wr_stop;
logic cfg_rd_stop;

logic cfg_clr_error;

logic cfg_write_reset;
logic cfg_read_reset;

logic[63:0] cfg_write_address = 0;
logic[31:0] cfg_write_data = 0;
logic[7:0] cfg_write_length;
logic[7:0] cfg_write_last_length;
logic[15:0] cfg_write_user;
logic cfg_write_inst_ram_wr;

logic[63:0] cfg_read_address = 0;
logic[31:0] cfg_read_data = 0;
logic[7:0] cfg_read_length;
logic[7:0] cfg_read_last_length;
logic[15:0] cfg_read_user;
logic cfg_read_inst_ram_wr;

logic[4:0] cfg_rd_cmp_error_data_index;

logic[7:0] cfg_wr_inst_index = 0;
logic[7:0] cfg_rd_inst_index = 0;

logic[15:0] cfg_wr_num_inst;
logic[15:0] cfg_rd_num_inst;

logic[63:0] cfg_wr_loop_iter = 0;
logic[63:0] cfg_rd_loop_iter = 0;

logic cfg_wr_stretch;
logic cfg_rd_stretch;

logic[7:0] cfg_addr_q = 0;        //Only care about lower 8-bits of address, upper bits are decoded somewhere else
logic[31:0] cfg_wdata_q = 0;

logic cfg_ram_access;

//Commands are single cycle pulse, stretch here
always @(posedge clk)
   if (!sync_rst_n)
   begin
      cfg_wr_stretch <= 0;
      cfg_rd_stretch <= 0;
   end
   else 
   begin
      cfg_wr_stretch <= cfg_wr || (cfg_wr_stretch && !tst_cfg_ack);
      cfg_rd_stretch <= cfg_rd || (cfg_rd_stretch && !tst_cfg_ack);
      if (cfg_wr||cfg_rd)
      begin
         cfg_addr_q <= cfg_addr[7:0];
         cfg_wdata_q <= cfg_wdata;
      end
   end


always @(posedge clk)
   if (cfg_wr_stretch)
   begin
      if (cfg_addr_q==8'h0)
      begin
         //{cfg_loop_addr_mode, cfg_iter_mode, cfg_sync_mode, cfg_rd_compare_en, cfg_prbs_mode, cfg_inc_data_loop_mode, cfg_cont_mode} <= cfg_wdata_q[7:0];
         {cfg_user_mode, cfg_loop_addr_mode, cfg_iter_mode, cfg_sync_mode, cfg_rd_compare_en} <= cfg_wdata_q[7:3];
         {cfg_inc_data_loop_mode, cfg_cont_mode} <= cfg_wdata_q[1:0];

         cfg_wr_loop_addr_shift <= cfg_wdata_q[13:8];
         cfg_rd_loop_addr_shift <= cfg_wdata_q[21:16];

         //cfg_inc_id_mode <= cfg_wdata_q[24];
         cfg_const_data_mode <= cfg_wdata_q[25];

      end
      else if (cfg_addr_q==8'h4)
      begin
         {cfg_max_write, cfg_read_start} <= cfg_wdata_q;
      end
      else if (cfg_addr_q==8'h10)
      begin
         {cfg_rd_num_inst, cfg_wr_num_inst} <= cfg_wdata_q;
      end
      else if (cfg_addr_q==8'h14)
      begin
         cfg_max_read_req <= (cfg_wdata_q<NUM_RD_TAG)? cfg_wdata_q: NUM_RD_TAG-1;
      end
      else if (cfg_addr_q==8'h20)
         cfg_write_address[31:0] <= cfg_wdata_q;
      else if (cfg_addr_q==8'h24)
         cfg_write_address[63:32] <= cfg_wdata_q;
      else if (cfg_addr_q==8'h28)
         cfg_write_data <= cfg_wdata_q;
      else if (cfg_addr_q==8'h30)
         cfg_atg_enable <= cfg_wdata_q[0];
      else if (cfg_addr_q==8'h40)
         cfg_read_address[31:0] <= cfg_wdata_q;
      else if (cfg_addr_q==8'h44)
         cfg_read_address[63:32] <= cfg_wdata_q;
      else if (cfg_addr_q==8'h48)
         cfg_read_data <= cfg_wdata_q;
      else if (cfg_addr_q==8'h60)
         cfg_rd_data_index <= cfg_wdata_q;
      else if (cfg_addr_q==8'hc0)
         cfg_wr_loop_iter[31:0] <= cfg_wdata_q;
      else if (cfg_addr_q==8'hc4)
         cfg_wr_loop_iter[63:32] <= cfg_wdata_q;
      else if (cfg_addr_q==8'hc8)
         cfg_rd_loop_iter[31:0] <= cfg_wdata_q;
      else if (cfg_addr_q==8'hcc)
         cfg_rd_loop_iter[63:32] <= cfg_wdata_q;
   end

assign cfg_wr_go = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'h8) && cfg_wdata_q[0]) && !wr_inp;
assign cfg_rd_go = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'h8) && cfg_wdata_q[1]) && !rd_inp;

assign cfg_wr_stop = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'h8) && ~cfg_wdata_q[0]);
assign cfg_rd_stop = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'h8) && ~cfg_wdata_q[1]);

assign cfg_write_reset = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hc) && cfg_wdata_q[0]);
assign cfg_read_reset = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hc) && cfg_wdata_q[1]);

assign cfg_write_length = cfg_wdata_q[7:0];
assign cfg_write_last_length = cfg_wdata_q[15:8];
assign cfg_write_user = cfg_wdata_q[31:16];

assign cfg_read_length = cfg_wdata_q[7:0];
assign cfg_read_last_length = cfg_wdata_q[15:8];
assign cfg_read_user = cfg_wdata_q[31:16];

assign cfg_write_inst_ram_wr = (cfg_wr_stretch && (cfg_addr_q==8'h2c));
assign cfg_read_inst_ram_wr = (cfg_wr_stretch && (cfg_addr_q==8'h4c));

assign cfg_clr_error = (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hb0) && cfg_wdata_q[0]);

//Instruction RAM indexes
always @(posedge clk)
   begin
      cfg_wr_inst_index <=    (cfg_wr_stretch && (cfg_addr_q==8'h1c))?     cfg_wdata_q:
                              (cfg_write_inst_ram_wr && tst_cfg_ack)?      cfg_wr_inst_index + 1:
                                                                           cfg_wr_inst_index;

      cfg_rd_inst_index <=    (cfg_wr_stretch && (cfg_addr_q==8'h3c))?     cfg_wdata_q:
                              (cfg_read_inst_ram_wr && tst_cfg_ack)?       cfg_rd_inst_index + 1:
                                                                           cfg_rd_inst_index;
   end

//Readback mux
always @(posedge clk)
begin
      case (cfg_addr_q)
         8'h0:       tst_cfg_rdata <= {6'h0, cfg_const_data_mode, cfg_inc_id_mode, 
                                       2'h0, cfg_rd_loop_addr_shift[5:0], 
                                       2'h0, cfg_wr_loop_addr_shift[5:0], 
                                       cfg_user_mode, cfg_loop_addr_mode, cfg_iter_mode, cfg_sync_mode, cfg_rd_compare_en, cfg_prbs_mode, cfg_inc_data_loop_mode, cfg_cont_mode};
         8'h4:       tst_cfg_rdata <= {cfg_max_write, cfg_read_start};
         8'h8:       tst_cfg_rdata <= {rd_resp_pend, rd_inp, wr_inp};
         8'hc:       tst_cfg_rdata <= {wr_state[1:0], rd_tag_avail[15:0]};
         8'h10:      tst_cfg_rdata <= {cfg_rd_num_inst, cfg_wr_num_inst};
         8'h14:      tst_cfg_rdata <= {cfg_max_read_req};
     
         8'h1c:      tst_cfg_rdata <= cfg_wr_inst_index; 
         8'h20:      tst_cfg_rdata <= wr_cfg_inst_rdata_q;
         8'h24:      tst_cfg_rdata <= wr_cfg_inst_rdata_q >> 32; 
         8'h28:      tst_cfg_rdata <= wr_cfg_inst_rdata_q >> 64; 
         8'h2c:      tst_cfg_rdata <= {wr_cfg_inst_rdata_q[127:96]};

         8'h30:      tst_cfg_rdata <= {31'b0, cfg_atg_enable};

         8'h3c:      tst_cfg_rdata <= cfg_rd_inst_index;
         8'h40:      tst_cfg_rdata <= rd_cfg_inst_rdata_q;
         8'h44:      tst_cfg_rdata <= rd_cfg_inst_rdata_q >> 32; 
         8'h48:      tst_cfg_rdata <= rd_cfg_inst_rdata_q >> 64; 
         8'h4c:      tst_cfg_rdata <= {rd_cfg_inst_rdata_q[127:96]};

         8'h60:      tst_cfg_rdata <= cfg_rd_data_index;
         8'h64:      tst_cfg_rdata <= rd_cfg_addr_q_ram_data_q[31:0];
         8'h68:      tst_cfg_rdata <= rd_cfg_addr_q_ram_data_q[63:32];
         8'h6c:      tst_cfg_rdata <= rd_cfg_read_ram_data_q >> (32 * cfg_rd_data_index[7:0]);
         8'h70:      tst_cfg_rdata <= rd_cfg_exp_ram_data_q >> (32 * cfg_rd_data_index[7:0]);
         8'h74:      tst_cfg_rdata <= rd_dat_ram_addr;

         8'h80:      tst_cfg_rdata <= wr_cyc_count[31:0];
         8'h84:      tst_cfg_rdata <= wr_cyc_count[63:32];
         8'h88:      tst_cfg_rdata <= rd_cyc_count[31:0];
         8'h8c:      tst_cfg_rdata <= rd_cyc_count[63:32];

         8'h90:      tst_cfg_rdata <= wr_loop_count[31:0];
         8'h94:      tst_cfg_rdata <= wr_loop_count[63:32];
         8'h98:      tst_cfg_rdata <= rd_loop_count[31:0];
         8'h9c:      tst_cfg_rdata <= rd_loop_count[63:32];

         8'ha0:      tst_cfg_rdata <= rd_resp_count[31:0];
         8'ha4:      tst_cfg_rdata <= rd_resp_count[63:32];

         8'hb0:      tst_cfg_rdata <= cfg_rd_cmp_error;
         8'hb4:      tst_cfg_rdata <= cfg_rd_cmp_error_address[31:0];
         8'hb8:      tst_cfg_rdata <= cfg_rd_cmp_error_address[63:32];
         8'hbc:      tst_cfg_rdata <= cfg_rd_cmp_error_data_index;             //Where wrote error into RAM

         8'hc0:      tst_cfg_rdata <= cfg_wr_loop_iter[31:0];
         8'hc4:      tst_cfg_rdata <= cfg_wr_loop_iter[63:32];
         8'hc8:      tst_cfg_rdata <= cfg_rd_loop_iter[31:0];
         8'hcc:      tst_cfg_rdata <= cfg_rd_loop_iter[63:32];

         8'hd0:      tst_cfg_rdata <= bresp_error_count;
         8'hd4:      tst_cfg_rdata <= bresp_error_first;
         8'hd8:      tst_cfg_rdata <= rresp_error_count;
         8'hdc:      tst_cfg_rdata <= rresp_error_first;

//         8'he0:      tst_cfg_rdata <= {rd_addr_rec_ptr, 2'h0, wr_addr_rec_ptr, 6'h0, wr_addr_rec_single, cfg_rec_sel, 3'h0, wr_addr_rec_index};
//         8'he4:      tst_cfg_rdata <= (cfg_rec_sel)? rd_addr_rec[wr_addr_rec_index][31:0]: wr_addr_rec[wr_addr_rec_index][31:0];
//         8'he8:      tst_cfg_rdata <= (cfg_rec_sel)? rd_addr_rec[wr_addr_rec_index][63:32]: wr_addr_rec[wr_addr_rec_index][63:32];

         8'hf0:      tst_cfg_rdata <= wr_timer[31:0];
         8'hf4:      tst_cfg_rdata <= wr_timer[63:32];
         8'hf8:      tst_cfg_rdata <= rd_timer[31:0];
         8'hfc:      tst_cfg_rdata <= rd_timer[63:32];

         default:    tst_cfg_rdata <= 32'hffffffff;
      endcase
end

assign cfg_ram_access = (cfg_addr_q==8'h64) || (cfg_addr_q==8'h68) || (cfg_addr_q==8'h6c) || (cfg_addr_q==8'h70);

//Ack for cycle
always_ff @(posedge clk)
   if (!sync_rst_n)
      tst_cfg_ack <= 0;
   else
      tst_cfg_ack <= ((cfg_wr_stretch||cfg_rd_stretch) && !cfg_ram_access && !tst_cfg_ack) ||
                     ((cfg_wr_stretch||cfg_rd_stretch) && cfg_ram_access && rd_cfg_read_ram_ack && !tst_cfg_ack); 

//---------------------------------------
// Inst RAMs
//---------------------------------------

bram_2rw #(.WIDTH(128), .ADDR_WIDTH(8), .DEPTH(256)) WRITE_INST_RAM (
   .clk(clk),
   .wea(cfg_write_inst_ram_wr),
   .ena(1'b1),
   .addra(cfg_wr_inst_index),
   .da({cfg_write_user, cfg_write_last_length, cfg_write_length, cfg_write_data, cfg_write_address}),
   .qa(wr_cfg_inst_rdata),

   .web(1'b0),
   .enb(1'b1),
   .addrb(wr_inst_addr),
   .db(128'h0),
   .qb(inst_wr_rdata)
   );

bram_2rw #(.WIDTH(128), .ADDR_WIDTH(8), .DEPTH(256)) READ_INST_RAM (
   .clk(clk),
   .wea(cfg_read_inst_ram_wr),
   .ena(1'b1),
   .addra(cfg_rd_inst_index),
   .da({cfg_read_user, cfg_read_last_length, cfg_read_length, cfg_read_data, cfg_read_address}),
   .qa(rd_cfg_inst_rdata),

   .web(1'b0),
   .enb(1'b1),
   .addrb(rd_inst_addr),
   .db(128'h0),
   .qb(inst_rd_rdata)
   );

//For timing flop the inst_rd_data before use it
always @(posedge clk)
   inst_rd_rdata_q <= inst_rd_rdata;



//--------------------------------
// Write state machine      
//--------------------------------

logic[7:0] wr_running_length = 0;
logic wr_dat_end;                   //End of data for this instruction (single transfer)
logic wr_inst_done;                 //Done with instructions (end and not continuous mode)

logic[DATA_WIDTH-1:0] wdata_nxt;
logic[(DATA_WIDTH/8)-1:0] wstrb_nxt;

logic wr_stop_pend;

logic[7:0] wr_last_adj = 0;

always_comb
begin
   wr_state_nxt = wr_state;
   case (wr_state)

      WR_IDLE:
      begin
         if (cfg_wr_go)
            wr_state_nxt = WR_ADDR;
         else
            wr_state_nxt = WR_IDLE;
      end

      WR_ADDR:
      begin
         if (awready)
            wr_state_nxt = WR_DAT;
         else  
            wr_state_nxt = WR_ADDR;
      end

      WR_DAT:
      begin
         if (wr_dat_end && wready)
         begin
            if (wr_inst_done || wr_stop_pend)
               wr_state_nxt = WR_IDLE;
            else
               wr_state_nxt = WR_ADDR;
         end
         else
            wr_state_nxt = WR_DAT;
      end

   endcase
end

always_ff @(posedge clk)
   if (!sync_rst_n)
      wr_state <= WR_IDLE;
   else
      wr_state <= wr_state_nxt;

//RAM address
always @( posedge clk)
   if (wr_state==WR_IDLE)
      wr_inst_addr <= 0;
   else if ((wr_state==WR_ADDR) && (wr_state_nxt!=WR_ADDR))
      wr_inst_addr <= (wr_inst_addr==cfg_wr_num_inst)? 0: wr_inst_addr + 1;



//Loop count
always @(posedge clk)
   if (cfg_wr_go)
   begin
//      wr_cyc_count <= 0;
      wr_loop_count <= 0;
   end
   else if ((wr_state==WR_ADDR) && (wr_state_nxt!=WR_ADDR))
   begin
//      wr_cyc_count <= wr_cyc_count + 1;
      if (wr_inst_addr==cfg_wr_num_inst)
         wr_loop_count <= wr_loop_count + 1;
   end

//Increment wr_cyc_count after the Write data for the read/write holdoff
always @(posedge clk)
   if (cfg_wr_go)
      wr_cyc_count <= 0;
   else if ((wr_state==WR_DAT) && (wr_state_nxt!=WR_DAT))
      wr_cyc_count <= wr_cyc_count + 1;

//Timer
always @(posedge clk)
   if (cfg_wr_go)
      wr_timer <= 0;
   else if (wr_inp)
      wr_timer <= wr_timer + 1;


//Stop pending
always_ff @(posedge clk)
   if (!sync_rst_n)
      wr_stop_pend <= 0;
   else
      wr_stop_pend <= (cfg_wr_stop || cfg_rd_cmp_error) || (wr_stop_pend && (wr_state_nxt!=WR_IDLE));

//Instructions done -- When wrap around to 0 is done
assign wr_inst_done =   (cfg_iter_mode)?        ((wr_inst_addr==0) && (wr_loop_count==cfg_wr_loop_iter)):
                        (!cfg_cont_mode)?       (wr_inst_addr==0):
                                                0;

//Address
logic[15:0] user_length_mult;
logic[63:0] wr_loop_addr_adj;                //If in loop addres mode, adjustment to address

//Have to multiply length by number of DW in data width to get total dw_count
assign user_length_mult  = DATA_WIDTH/32;

assign wr_loop_addr_adj = (cfg_loop_addr_mode)? wr_loop_count << cfg_wr_loop_addr_shift: 0;

//FLop this for timing
//assign awid = 0;
////assign awaddr = inst_wr_rdata[63:0] + wr_loop_addr_adj;
//assign awaddr = inst_wr_rdata[63:0] | wr_loop_addr_adj;
//assign awlen = inst_wr_rdata[103:96];
//assign awuser = (cfg_user_mode)? inst_wr_rdata[127:112]: (inst_wr_rdata[103:96]+1) * user_length_mult;

//This is the number of DW to adjust
parameter ADJ_DW_WIDTH =   (DATA_WIDTH==512)?   4:
                        (DATA_WIDTH==256)?   3:
                        (DATA_WIDTH==128)?   2:
                                             1;
//Do adjustment for non-aligned
wire[ADJ_DW_WIDTH-1:0] wr_first_adj = (inst_wr_rdata[63:0] >> 2);

always_ff @( posedge clk)
   if (!sync_rst_n)
   begin
      awid <= 0;
      awaddr <=0 ;
      awlen <= 0;
      awuser <= 0;
   end
   else if (wr_state==WR_ADDR)
   begin
      awid <= 0;
      awaddr <= inst_wr_rdata[63:0] | wr_loop_addr_adj;
      awlen <= inst_wr_rdata[103:96];
      awuser <= (cfg_user_mode)? inst_wr_rdata[127:112]: ((inst_wr_rdata[103:96]+1) * user_length_mult) - wr_first_adj - inst_wr_rdata[104+:ADJ_DW_WIDTH];
   end
   else 
   begin
      awid <= 0;
      awaddr <=0 ;
      awlen <= 0;
      awuser <= 0;
   end

//Latch last length
always @(posedge clk)
   if (wr_state==WR_ADDR)
      wr_last_adj = inst_wr_rdata[111:104];

always_ff @(posedge clk)
   if (!sync_rst_n)
      awvalid <= 0;
   else
      //awvalid <= (wr_state_nxt==WR_ADDR);
      awvalid <= (wr_state==WR_ADDR);

//Data
assign wr_dat_end = (wr_running_length==0);

always @(posedge clk)
   if (wr_state==WR_ADDR)
      wr_running_length <= inst_wr_rdata[103:96];
   else if (wvalid && wready)
      wr_running_length <= wr_running_length - 1;

logic[DATA_WIDTH-1:0] first_wdata = 0;         //Pre-compute this for timing
always @(posedge clk)
   begin
      for (int i=0; i<DATA_DW; i++)
         //FIXME -- Do we want 32-bits here for loopcount, try 8 to help timing         
         //first_wdata[32*i+:32] <=  inst_wr_rdata[95:64] + (wr_loop_count[31:0] & {32{cfg_inc_data_loop_mode}}) + i;
         //first_wdata[32*i+:32] <=  inst_wr_rdata[95:64] + (wr_loop_count[7:0] & {32{cfg_inc_data_loop_mode}}) + i;
         first_wdata[32*i+:32] <=  (cfg_const_data_mode)? inst_wr_rdata[95:64]: inst_wr_rdata[95:64] + i;
   end

//Write data
always_comb
begin
   wdata_nxt = wdata;

   wstrb_nxt = {(DATA_WIDTH/8){1'b1}};

   if (wr_state==WR_ADDR)
      //wdata_nxt[31:0] = inst_wr_rdata[95:64] + (wr_loop_count[31:0] & {32{cfg_inc_data_loop_mode}});
      wdata_nxt = first_wdata;
   else if (wvalid && wready)
   begin
      for (int i=0; i<DATA_DW; i++)
         //wdata_nxt[32*i+:32] = (cfg_prbs_mode)? bit_crc(1'b1, wdata[32*i+:32]): wdata[32*i+:32] + DATA_DW;
         wdata_nxt[32*i+:32] = (cfg_const_data_mode)? wdata[32*i+:32]: wdata[32*i+:32] + DATA_DW;
   end

   if (wr_state==WR_ADDR)
   begin
      //Only have 1 data phase (length is 0)
      if (inst_wr_rdata[103:96]==0)
         wstrb_nxt = ({(DATA_WIDTH/8){1'b1}} << (wr_first_adj*4)) & (~({(DATA_WIDTH/8){1'b1}} << (({ADJ_DW_WIDTH+2{1'b1}} + 1) - (inst_wr_rdata[111:104]*4))));
      else
         wstrb_nxt = {(DATA_WIDTH/8){1'b1}} << (wr_first_adj*4);
   end
   else if ((wr_running_length==1) && wready)
      wstrb_nxt = ~({(DATA_WIDTH/8){1'b1}} << (({ADJ_DW_WIDTH+2{1'b1}} + 1) - (wr_last_adj*4)));      //have to convert from DW to byte
end

always @(posedge clk)
//   if (!sync_rst_n)
//   begin
//      wdata <= 0;
//      wstrb <= 0;
//   end
//   else
   begin
      wdata <= wdata_nxt; 
      wstrb <= wstrb_nxt;
   end


assign wvalid = (wr_state==WR_DAT);
assign wlast = wr_dat_end;
assign wid = 0;
//assign wstrb = {(DATA_WIDTH/8){1'b1}};

assign wr_inp = (wr_state!=WR_IDLE);

//Don't do anything with BRESP
assign bready = 1;

// End Write
//--------------------

//-----------------------------
// Read state machine
//-----------------------------
logic rd_tag_some_avail;                  //Tag is available to allocate
logic[8:0] rd_tag_alloc_winner;           //Allocate winner

logic[511:0] rd_tag_mask = 0;

logic rd_tag_pop;                         //Pop a tag
logic rd_tag_pop_q;                       //One clock delayed to line up with ram read data.  This pushes into request FIFO
logic rd_tag_pop_qq;                      //Two clock delayed to line up with ram read data_q.
logic[8:0] rd_tag_inc_nxt_alloc = 0;      //Next tag to alloc in incrementing mode

logic rd_fifo_full;                       //Read request FIFO is full

logic rd_tag_free;                        //Free a tag

logic[8:0] pre_rd_cur_req_tag;            //Current request tag
logic[8:0] rd_cur_req_tag;                //Line up with pop_qq (pop_qq to flop RAM read data for timing)

//logic[DATA_WIDTH-1:0] rdata_nxt;        //Calculate expected data
logic[DATA_WIDTH-1:0] rd_data_cmp;        //Compare data
logic[DATA_WIDTH-1:0] rd_data_nxt;        //Next phase read data DW0

logic[DATA_WIDTH-1:0] rd_data_mask;

logic[63:0] rd_cyc_addr;
logic[63:0] rd_cyc_addr_q  = 0;

logic[63:0] rd_loop_addr_adj = 0;             //Adjust address based on loop count
logic[63:0] rd_loop_addr_adj_q = 0;

logic[511:0] rd_got_first_phase = 0;          //Got first read phase
//logic[511:0] rd_got_first_phase_q;     
logic rd_got_first_phase_q = 0;     

`define RD_TRK_RAM_WIDTH   8+64+DATA_WIDTH+8+8+1

logic[8:0] rd_trk_ram_wr_addr;
logic[`RD_TRK_RAM_WIDTH-1:0] rd_trk_ram_wr_data;
logic rd_trk_ram_wr;

logic[8:0] rd_trk_ram_rd_addr;
logic[`RD_TRK_RAM_WIDTH-1:0] rd_trk_ram_rd_data;

logic[8:0] rd_md_ram_wr_addr_pre;
logic[(DATA_WIDTH+8)-1:0] rd_md_ram_wr_data_pre;
logic rd_md_ram_wr_pre;

logic[8:0] rd_md_ram_wr_addr = 0;
logic[(DATA_WIDTH+8)-1:0] rd_md_ram_wr_data = 0;
logic rd_md_ram_wr = 0;

logic[8:0] rd_md_ram_rd_addr;
logic[(DATA_WIDTH+8)-1:0] rd_md_ram_rd_data_ram;
logic[(DATA_WIDTH+8)-1:0] rd_md_ram_rd_data;

logic rd_md_ram_col_q_pre = 0;
logic[`RD_TRK_RAM_WIDTH-1:0] rd_md_ram_wr_data_q_pre = 0;

logic rd_md_ram_col_q = 0;
logic[`RD_TRK_RAM_WIDTH-1:0] rd_md_ram_wr_data_q = 0;

typedef struct packed {
   logic[7:0] last_adj;
   logic[63:0] req_addr;
   logic[DATA_WIDTH-1:0] req_data;
   logic[7:0] req_length;
   logic[7:0] running_length;
   logic last_inst;
} rd_trk_t;

//rd_trk_t rd_trk[15:0];                    //Read trackers
rd_trk_t rd_trk_wr;
rd_trk_t rd_trk_rd;

logic rd_stop_pend;  

always @(posedge clk)
   rd_tag_mask <= ~({512{1'b1}} << (cfg_max_read_req+1));

//Stop pending
always_ff @(posedge clk)
   if (!sync_rst_n)
      rd_stop_pend <= 0;
   else
      rd_stop_pend <= (cfg_rd_stop || cfg_rd_cmp_error) || (rd_stop_pend && rd_inp);

wire rd_inst_done =  (cfg_iter_mode)?     ((rd_inst_addr==cfg_rd_num_inst) && ((rd_loop_count+1)==cfg_rd_loop_iter)):
                     (!cfg_cont_mode)?    (rd_inst_addr==cfg_rd_num_inst):
                                          0;

//Read in progress
always_ff @(posedge clk)
   if (!sync_rst_n)
      rd_inp <= 0;
   else if (cfg_rd_go)
      rd_inp <= 1;
   else if (rd_stop_pend || (rd_tag_pop && rd_inst_done))
      rd_inp <= 0;

//For timing, always do inc_id mode.  Think have enough tags where this won't be limiting
assign cfg_inc_id_mode = 1;

//In incrementing mode, increment tag every pop
always @(posedge clk)
   //if (!sync_rst_n)
   //   rd_tag_inc_nxt_alloc <= 0;
   //else if (cfg_read_reset)
   if (cfg_read_reset)
      rd_tag_inc_nxt_alloc <= 0;
   else if (!cfg_inc_id_mode)
      rd_tag_inc_nxt_alloc <= 0;
   else if (rd_tag_pop)
      rd_tag_inc_nxt_alloc <= (rd_tag_inc_nxt_alloc==cfg_max_read_req)? 0: rd_tag_inc_nxt_alloc + 1;

//Tag allocation
logic[8:0] rd_tag_alloc_winner_comb;
always_comb
begin
   rd_tag_alloc_winner_comb = 0; 
  
   //Always do inc_id_mode for timing 
   rd_tag_alloc_winner_comb = rd_tag_inc_nxt_alloc;
   //if (cfg_inc_id_mode)
   //   rd_tag_alloc_winner_comb = rd_tag_inc_nxt_alloc;
   //else
   //begin
   //   for (int i=511; i>=0; i--)
   //      if (rd_tag_avail[i])
   //         rd_tag_alloc_winner_comb = i;
   //end
end

//assign rd_tag_some_avail = (cfg_inc_id_mode)? rd_tag_avail[rd_tag_inc_nxt_alloc]: |rd_tag_avail;

always_ff @(posedge clk)
   if (!sync_rst_n)
   begin
      rd_tag_some_avail <=0 ;
      rd_tag_alloc_winner <= 0;
   end
   else if (rd_tag_pop)
   begin
      rd_tag_some_avail <= 0;
      rd_tag_alloc_winner <= 0;
   end
   else if (!rd_tag_some_avail)
   begin 
      rd_tag_some_avail <= (cfg_inc_id_mode)? rd_tag_avail[rd_tag_inc_nxt_alloc]: |(rd_tag_avail & rd_tag_mask);
      rd_tag_alloc_winner <= rd_tag_alloc_winner_comb;
   end


always @(posedge clk)
   //if (!sync_rst_n)
   //   rd_tag_avail <= {NUM_RD_TAG{1'b1}};
   //else if (cfg_read_reset)
   if (cfg_read_reset)
   begin
      rd_tag_avail <= {NUM_RD_TAG{1'b1}};
   end
   else
   begin
      if (rd_tag_pop)
         rd_tag_avail[rd_tag_alloc_winner] <= 0;
      if (rd_tag_free)
         rd_tag_avail[rid_q] <= 1;
   end

logic rd_cyc_holdoff;

always_ff @(posedge clk)
   if (!sync_rst_n)
      rd_cyc_holdoff <= 0;
   else
      rd_cyc_holdoff <= (rd_cyc_count >= wr_cyc_count);


//If in sync mode, reads cannot pass writes
//wire rd_wr_holdoff = cfg_sync_mode && wr_inp && ((rd_cyc_count+1) >= wr_cyc_count);
wire rd_wr_holdoff = cfg_sync_mode && wr_inp && rd_cyc_holdoff;

//Increment the read instruction 
assign rd_tag_pop = rd_inp && rd_tag_some_avail && !rd_fifo_full && !rd_wr_holdoff;

always @(posedge clk)
   if (!rd_inp)
      rd_inst_addr <= 0;
   else if (rd_tag_pop)
      rd_inst_addr <= (rd_inst_addr==cfg_rd_num_inst)? 0: rd_inst_addr + 1;

always @(posedge clk)
   if (cfg_rd_go)
   begin
      rd_cyc_count <= 0;
      rd_loop_count <= 0;
   end
   else if (rd_tag_pop)
   begin
      rd_cyc_count <= rd_cyc_count + 1;
      if (rd_inst_addr==cfg_rd_num_inst)
         rd_loop_count <= rd_loop_count + 1;
   end

//Timer
always @(posedge clk)
   if (cfg_rd_go)
      rd_timer <= 0;
   else if (rd_inp || rd_resp_pend)
      rd_timer <= rd_timer + 1;

always @( posedge clk)
   if (cfg_rd_go)
   begin
      rd_resp_count <= 0;
   end
   else if (rd_tag_free)
   begin
      rd_resp_count <= rd_resp_count + 1;
   end

always_ff @(posedge clk)
   if (!sync_rst_n)
   begin
      rd_tag_pop_q <= 0;
      rd_tag_pop_qq <= 0;
   end
   else
   begin
      rd_tag_pop_q <= rd_tag_pop;
      rd_tag_pop_qq <= rd_tag_pop_q;
   end

always_ff @(posedge clk)
   if (!sync_rst_n)
   begin
      pre_rd_cur_req_tag <= 0;
      rd_cur_req_tag <= 0;
   end
   else
   begin
      pre_rd_cur_req_tag <= rd_tag_alloc_winner;
      rd_cur_req_tag <= pre_rd_cur_req_tag;
   end

//always_ff @(posedge clk)
//   if (!sync_rst_n)
//      rd_trk <= '{default:'0};
//   else
//   begin
//      if (rd_tag_pop_qq)
//      begin
//         rd_trk[rd_cur_req_tag] <= 0;
//         rd_trk[rd_cur_req_tag].req_addr <= inst_rd_rdata_q[63:0] + rd_loop_addr_adj_q;
//         for (int i=0; i<DATA_DW; i++)
//            rd_trk[rd_cur_req_tag].req_data[32*i+:32] <= inst_rd_rdata_q[95:64] + (rd_loop_count[31:0] & {32{cfg_inc_data_loop_mode}}) + i;
//         rd_trk[rd_cur_req_tag].req_length <= inst_rd_rdata_q[103:96];
//         rd_trk[rd_cur_req_tag].last_inst <= (rd_inst_addr==cfg_rd_num_inst);
//         rd_trk[rd_cur_req_tag].running_length <= 0;
//      end
//
//      if (rvalid_q && rready)
//      begin
//         rd_trk[rid_q].running_length <= rd_trk[rid].running_length + 1;
//         rd_trk[rid_q].req_data <= rd_data_nxt;
//      end
//   end 
//rd_trk_wr.req_data[32*i+:32] = inst_rd_rdata_q[95:64] + (rd_loop_count[7:0] & {32{cfg_inc_data_loop_mode}}) + i;

always_comb
begin
   rd_trk_wr = 0;
   //rd_trk_wr.req_addr = inst_rd_rdata_q[63:0] + rd_loop_addr_adj_q;
   rd_trk_wr.req_addr = inst_rd_rdata_q[63:0] | rd_loop_addr_adj_q;
   for (int i=0; i<DATA_DW; i++)
      rd_trk_wr.req_data[32*i+:32] = (cfg_const_data_mode)? inst_rd_rdata_q[95:64]: inst_rd_rdata_q[95:64] + i;
   rd_trk_wr.req_length = inst_rd_rdata_q[103:96];
   rd_trk_wr.last_inst = (rd_inst_addr==cfg_rd_num_inst);
   rd_trk_wr.running_length = 0;
   rd_trk_wr.last_adj = inst_rd_rdata_q[111:104];
end

assign rd_trk_ram_wr_addr = rd_cur_req_tag;
assign rd_trk_ram_wr = rd_tag_pop_qq;
assign rd_trk_ram_wr_data = rd_trk_wr;

assign rd_md_ram_wr_pre = rvalid_q && rready;

assign rd_md_ram_wr_addr_pre = rid_q;
wire[7:0] rd_md_running_length = rd_trk_rd.running_length + 1;
assign rd_md_ram_wr_data_pre = {rd_md_running_length, rd_data_nxt};

always @(posedge clk)
   begin
      rd_md_ram_wr_addr <= rd_md_ram_wr_addr_pre;
      rd_md_ram_wr <= rd_md_ram_wr_pre;
      rd_md_ram_wr_data <= rd_md_ram_wr_data_pre;
   end   
   

always @(posedge clk)
   begin
      if (rd_tag_pop_qq)
         rd_got_first_phase[rd_cur_req_tag] <= 0;
      if (rvalid & rready)
         rd_got_first_phase[rid] <= 1;

      rd_got_first_phase_q <= rd_got_first_phase[rid];
   end

assign rd_trk_ram_rd_addr = rid;
assign rd_md_ram_rd_addr = rid;

//Assign read track RAM data to a struct for convenience.  If this is not the first data phase then need to
// get Length/Data from MD RAM rather than TRK RAM.
always_comb
begin
   rd_trk_rd = rd_trk_ram_rd_data;
   if (rd_got_first_phase_q)
   begin
      {rd_trk_rd.running_length, rd_trk_rd.req_data} = rd_md_ram_rd_data;
   end
end

logic rvalid_qq = 0;
logic[DATA_WIDTH-1:0] rdata_qq = 0;

always @(posedge clk)
   begin
      rvalid_qq <= rvalid_q;
      rdata_qq <= rdata_q;
   end

assign rd_tag_free = (rvalid_q && rready && rlast_q && (rd_trk_rd.running_length == rd_trk_rd.req_length));

wire[ADJ_DW_WIDTH-1:0] rd_trk_first_adj = (rd_trk_rd.req_addr >> 2);
always_comb
begin
   rd_data_cmp = rd_trk_rd.req_data;

   rd_data_mask = ((rd_trk_rd.running_length==0) && rlast_q)?     ({DATA_WIDTH{1'b1}} << (rd_trk_first_adj*32)) & (~({DATA_WIDTH{1'b1}} << (({ADJ_DW_WIDTH+5{1'b1}} + 1) -  (rd_trk_rd.last_adj[0+:ADJ_DW_WIDTH] * 32)) )):
                  (rd_trk_rd.running_length==0)?                  ({DATA_WIDTH{1'b1}} << (rd_trk_first_adj*32)):
                  (rlast_q)?                                      ~({DATA_WIDTH{1'b1}} << (({ADJ_DW_WIDTH+5{1'b1}} + 1) -  (rd_trk_rd.last_adj[0+:ADJ_DW_WIDTH] * 32)) ):
                                                                  {DATA_WIDTH{1'b1}}; 

   //for (int i=1; i<DATA_DW; i++)
   //begin
   //   rd_data_cmp[(32*i)+:32] = (cfg_prbs_mode)? bit_crc(1'b1, rd_data_cmp[32*(i-1)+:32]): rd_data_cmp[32*(i-1)+:32] + 1;
   //end

   //rd_data_nxt = (cfg_prbs_mode)? bit_crc(1'b1, rd_data_cmp[(DATA_WIDTH-1)-:32]): rd_data_cmp[(DATA_WIDTH-1)-:32] + 1;
   for (int i=0; i<DATA_DW; i++)
      //rd_data_nxt[32*i+:32] = (cfg_prbs_mode)? bit_crc(1'b1, rd_data_cmp[32*i+:32]): rd_data_cmp[32*i+:32] + DATA_DW;
      rd_data_nxt[32*i+:32] = (cfg_const_data_mode)? rd_data_cmp[32*i+:32]: rd_data_cmp[32*i+:32] + DATA_DW;
end

logic[DATA_WIDTH-1:0] rd_data_cmp_q = 0;
logic[DATA_WIDTH-1:0] rd_data_mask_q = 0;

always @(posedge clk)
   begin
      rd_data_cmp_q <= rd_data_cmp;
      rd_data_mask_q <= rd_data_mask;
   end

//tmp variables so can see in waves
logic[31:0] tmp_rdata_qq[(DATA_WIDTH/32)-1:0];
logic[31:0] tmp_rd_data_cmp_q[(DATA_WIDTH/32)-1:0];
logic[31:0] tmp_rd_data_mask_q[(DATA_WIDTH/32)-1:0];

always_comb
begin
   for (int i=0; i<DATA_WIDTH/32; i++)
   begin
      tmp_rdata_qq[i] = rdata_qq >> (32*i);
      tmp_rd_data_cmp_q[i] = rd_data_cmp_q >> (32*i);
      tmp_rd_data_mask_q[i] = rd_data_mask_q >> (32*i);
   end
end

//Do the read compare 
always @(posedge clk)
   if (cfg_clr_error)
   begin
      cfg_rd_cmp_error <= 0;
      cfg_rd_cmp_error_address <= 0;
      cfg_rd_cmp_error_data_index <= 0;
   end
//   else if (cfg_rd_compare_en && rvalid && (rdata!=rd_data_cmp))
   else if (cfg_rd_compare_en && rvalid_qq && ( (rdata_qq&rd_data_mask_q)!=(rd_data_cmp_q&rd_data_mask_q) ) && !cfg_rd_cmp_error)
   begin
      cfg_rd_cmp_error <= 1;
      cfg_rd_cmp_error_address <= rd_cyc_addr_q;
      cfg_rd_cmp_error_data_index <= rd_dat_ram_addr_q;
   end
      
//Do adjustment for non-aligned
wire[ADJ_DW_WIDTH-1:0] rd_req_first_adj = (inst_rd_rdata_q[63:0] >> 2);

//Push the requests into a FIFO, and this FIFO generates the AR requests (pop when ARREADY is asserted)
//Tag, user, length, addr
//wire[9:0] rd_push_len = (inst_rd_rdata_q[103:96]+1) * user_length_mult;
wire[10:0] rd_push_user = (cfg_user_mode)? inst_rd_rdata_q[127:112]: ((inst_rd_rdata_q[103:96]+1) * user_length_mult) - rd_req_first_adj - inst_rd_rdata_q[111:104];


//Need to flop addr adj because pushed on pop_q (rdr_loop_count adjusted on pop)
always @(posedge clk)
   begin
      rd_loop_addr_adj <= (cfg_loop_addr_mode)? rd_loop_count << cfg_rd_loop_addr_shift: 0;
      rd_loop_addr_adj_q <= rd_loop_addr_adj;
   end

wire[63:0] rd_push_addr = inst_rd_rdata_q[63:0] | rd_loop_addr_adj_q;


flop_fifo #(.DEPTH(4), .WIDTH(9+11+8+64)) RD_REQ_FIFO (
   .clk(clk),
   .rst_n(sync_rst_n),
   .sync_rst_n(1'b1),
   .cfg_watermark(2),      //Need full early because of the one clock delay in getting read data could have one outstanding
   .push(rd_tag_pop_qq),
   .push_data({rd_cur_req_tag, rd_push_user, inst_rd_rdata_q[103:96], rd_push_addr}),
   .pop(arvalid & arready),
   
   .pop_data({arid[8:0], aruser, arlen, araddr}),
   .half_full(),
   .watermark(rd_fifo_full),
   .data_valid(arvalid)
   );

//------------------------------
// Read track RAM 

bram_2rw #(.WIDTH(`RD_TRK_RAM_WIDTH), .ADDR_WIDTH(9), .DEPTH(512)) RD_TRK_RAM (
   .clk(clk),
   .wea(rd_trk_ram_wr),
   .ena(1'b1),
   .addra(rd_trk_ram_wr_addr),
   .da(rd_trk_ram_wr_data),
   .qa(),

   .web(1'b0),
   .enb(1'b1),
   .addrb(rd_trk_ram_rd_addr),
   .db({`RD_TRK_RAM_WIDTH{1'b0}}),
   .qb(rd_trk_ram_rd_data)
   );

bram_2rw #(.WIDTH(DATA_WIDTH+8), .ADDR_WIDTH(9), .DEPTH(512)) RD_TRK_MD_RAM (
   .clk(clk),
   .wea(rd_md_ram_wr),
   .ena(1'b1),
   .addra(rd_md_ram_wr_addr),
   .da(rd_md_ram_wr_data),
   .qa(),

   .web(1'b0),
   .enb(1'b1),
   .addrb(rd_md_ram_rd_addr),
   .db({DATA_WIDTH+8{1'b0}}),
   .qb(rd_md_ram_rd_data_ram)
   );

//Collision detection for MD RAM (TRK RAM doesn't need)
always @(posedge clk)
   begin
      rd_md_ram_col_q_pre <= rd_md_ram_wr_pre && (rd_md_ram_wr_addr_pre==rd_md_ram_rd_addr);
      rd_md_ram_wr_data_q_pre <= rd_md_ram_wr_data_pre;

      rd_md_ram_col_q <= rd_md_ram_wr && (rd_md_ram_wr_addr==rd_md_ram_rd_addr);
      rd_md_ram_wr_data_q <= rd_md_ram_wr_data;
   end

assign rd_md_ram_rd_data = (rd_md_ram_col_q_pre)?  rd_md_ram_wr_data_q_pre:
                           (rd_md_ram_col_q)?      rd_md_ram_wr_data_q: 
                                                   rd_md_ram_rd_data_ram;


//-------------------------
// Process read data
//    If compare is enabled, latch every read until get error.  If not enabled, then latch
//    the last read.

logic rd_dat_ram_wr;

assign rready = 1;

assign rd_dat_ram_wr = rvalid_q && !cfg_rd_cmp_error;      //Always write the RAM && (rd_trk[rid_q].last_inst || (cfg_rd_compare_en && !cfg_rd_cmp_error));

always @(posedge clk)
   if (rd_dat_ram_wr)
      rd_dat_ram_addr <= rd_dat_ram_addr + 1;


assign rd_cyc_addr = rd_trk_rd.req_addr + (rd_trk_rd.running_length * DATA_DW * 4);

//Flop these to line up with compare (so can latch for error reporting)
always @(posedge clk)
   begin
      rd_cyc_addr_q <= rd_cyc_addr;
      rd_dat_ram_addr_q <= rd_dat_ram_addr;
   end

bram_2rw #(.WIDTH(64), .ADDR_WIDTH(5), .DEPTH(32)) RD_ADDR_RAM (
   .clk(clk),
   .wea(rd_dat_ram_wr),
   .ena(1'b1),
   .addra(rd_dat_ram_addr),
   .da(rd_cyc_addr),
   .qa(),

   .web(1'b0),
   .enb(1'b1),
   .addrb(cfg_rd_data_index[12:8]),
   .db({64{1'b0}}),
   .qb(rd_cfg_addr_q_ram_data)
   );

bram_2rw #(.WIDTH(DATA_WIDTH), .ADDR_WIDTH(5), .DEPTH(32)) RD_DAT_RAM (
   .clk(clk),
   .wea(rd_dat_ram_wr),
   .ena(1'b1),
   .addra(rd_dat_ram_addr),
   .da(rdata_q),
   .qa(),

   .web(1'b0),
   .enb(1'b1),
   .addrb(cfg_rd_data_index[12:8]),
   .db({DATA_WIDTH{1'b0}}),
   .qb(rd_cfg_read_ram_data)
   );

bram_2rw #(.WIDTH(DATA_WIDTH), .ADDR_WIDTH(5), .DEPTH(32)) RD_EXP_RAM (
   .clk(clk),
   .wea(rd_dat_ram_wr),
   .ena(1'b1),
   .addra(rd_dat_ram_addr),
   .da(rd_data_cmp),
   .qa(),

   .web(1'b0),
   .enb(1'b1),
   .addrb(cfg_rd_data_index[12:8]),
   .db({DATA_WIDTH{1'b0}}),
   .qb(rd_cfg_exp_ram_data)
   );

assign rd_cfg_read_ram_ack = 1;

assign rd_resp_pend = rd_tag_avail!={NUM_RD_TAG{1'b1}};

//Flop all RAM read data
always @(posedge clk)
   begin
      wr_cfg_inst_rdata_q <= wr_cfg_inst_rdata;
      rd_cfg_inst_rdata_q <= rd_cfg_inst_rdata;
      rd_cfg_addr_q_ram_data_q <= rd_cfg_addr_q_ram_data;
      rd_cfg_read_ram_data_q <= rd_cfg_read_ram_data;
      rd_cfg_exp_ram_data_q <= rd_cfg_exp_ram_data;
   end


// End read state machine
//-----------------------------


//BRESP, RRESP error handling

always @(posedge clk)
   begin
      //FIXME -- Add in HMC stuff later
      bresp_error_count <= (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hd0))?  0:
                           //FIXME (bvalid && (|bresp || |buser[21:14]))?                   bresp_error_count + 1:
                           (bvalid && (|bresp))?                                    bresp_error_count + 1:
                                                                                    bresp_error_count;

      bresp_error_first <= (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hd4))?           0:
                            //FIXME (bvalid && (|bresp || |buser[21:14]) && (bresp_error_first==0))?  {buser[17:0], 2'b00, bresp[1:0]}:
                            (bvalid && (|bresp) && (bresp_error_first==0))?                           {buser[17:0], 2'b00, bresp[1:0]}:
                                                                                                      bresp_error_first;

      rresp_error_count <= (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hd8))?  0:
                           //FIXME (rvalid && (|rresp || |ruser[21:14]))?                   rresp_error_count + 1:
                           (rvalid && (|rresp))?                                    rresp_error_count + 1:
                                                                                    rresp_error_count;

      rresp_error_first <= (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'hdc))?           0:
                            //FIXME (rvalid && (|rresp || |ruser[21:14]) && (rresp_error_first==0))? {ruser[17:0], 2'b00, rresp[1:0]}:
                            (rvalid && (|rresp) && (rresp_error_first==0))?                  {ruser[17:0], 2'b00, rresp[1:0]}:
                                                                                             rresp_error_first;
   end

  
////Write addres recording
//always_ff @(posedge clk)
//   if (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'he0) && (cfg_wdata_q[31]))
//   begin 
//      for (int i=0; i<32; i++)
//         wr_addr_rec[i] <= {64{1'b1}};
//      wr_addr_rec_ptr <= 0;
//   end
//   else if (awvalid && awready && ((wr_addr_rec_ptr<32) || ~wr_addr_rec_single))
//   begin
//      wr_addr_rec[wr_addr_rec_ptr[4:0]] <= awaddr;
//      wr_addr_rec_ptr <= wr_addr_rec_ptr + 1;
//   end
//
////Read address recording
//always_ff @(posedge clk)
//   if (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'he0) && (cfg_wdata_q[31]))
//   begin 
//      for (int i=0; i<32; i++)
//         rd_addr_rec[i] <= {64{1'b1}};
//      rd_addr_rec_ptr <= 0;
//   end
//   else if (arvalid && arready && ((rd_addr_rec_ptr<32) || ~wr_addr_rec_single))
//   begin
//      rd_addr_rec[rd_addr_rec_ptr[4:0]] <= araddr;
//      rd_addr_rec_ptr <= rd_addr_rec_ptr + 1;
//   end
//
//always_ff @(negedge sync_rst_n or posedge clk)
//   if (!sync_rst_n)
//   begin
//      wr_addr_rec_index <= 0;
//      wr_addr_rec_single <= 0;
//   end
//   else if (cfg_wr_stretch && tst_cfg_ack && (cfg_addr_q==8'he0))
//   begin
//      wr_addr_rec_index <= cfg_wdata_q[4:0];
//      cfg_rec_sel <= cfg_wdata_q[7];
//      wr_addr_rec_single <= cfg_wdata_q[8];
//   end




function [31:0] bit_crc (input in_bit, input[31:0] in_crc);
logic[31:0] result_crc;
logic tmp_in_xor;
begin
   tmp_in_xor = in_crc[31] ^ in_bit;
   for (int i=0; i<32; i++)
   begin
      case (i)
         0:    result_crc[i] = tmp_in_xor;
         1, 2, 4, 5, 7, 8, 10, 11, 12, 16, 22, 23, 26:      result_crc[i] = in_crc[i-1] ^ tmp_in_xor;
         default: result_crc[i] = in_crc[i-1];
      endcase
   end
   bit_crc = result_crc;
end
endfunction

   
endmodule
