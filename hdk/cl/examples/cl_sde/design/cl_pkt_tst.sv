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

`define CFG_ADDR_TX_CFG        8'h00
`define CFG_ADDR_TX_SEED0      8'h04
`define CFG_ADDR_TX_SEED1      8'h0C
`define CFG_ADDR_TX_MIN_PKTLEN 8'h08
`define CFG_ADDR_TX_MAX_PKTLEN 8'h10
`define CFG_ADDR_TX_PKT_CNT0   8'h14
`define CFG_ADDR_TX_PKT_CNT1   8'h18
`define CFG_ADDR_TICK_CNT      8'h1C
`define CFG_ADDR_TX_TIMER      8'h20
`define CFG_ADDR_TX_NUM_PKTS   8'h24

`define CFG_ADDR_RX_CFG          8'h80
`define CFG_ADDR_RX_DATA0        8'h84
`define CFG_ADDR_RX_DATA1        8'h8C
`define CFG_ADDR_RX_MIN_PKTLEN   8'h88
`define CFG_ADDR_RX_MAX_PKTLEN   8'h90
`define CFG_ADDR_RX_PKT_CNT0     8'h94
`define CFG_ADDR_RX_PKT_CNT1     8'h98
`define CFG_ADDR_RX_ERR_PKT_CNT0 8'h9C
`define CFG_ADDR_RX_ERR_PKT_CNT1 8'hA0
`define CFG_ADDR_RX_ERR_CNT0     8'hA4
`define CFG_ADDR_RX_ERR_CNT1     8'hA8
`define CFG_ADDR_RX_TIMER        8'hAC
`define CFG_ADDR_RX_RAW_PKT_CNT0      8'hB0
`define CFG_ADDR_RX_RAW_PKT_CNT1      8'hB4
`define CFG_ADDR_RX_RAW_DATA_CNT0     8'hB8
`define CFG_ADDR_RX_RAW_DATA_CNT1     8'hBC
`define CFG_ADDR_RX_RAW_ERR_CNT0      8'hC0
`define CFG_ADDR_RX_RAW_ERR_CNT1      8'hC4
`define CFG_ADDR_RX_DBG_RAM_INDEX     8'hC8
`define CFG_ADDR_RX_DBG_RAM_DATA      8'hCC


module cl_pkt_tst #(parameter DATA_WIDTH = 512,  // Should be atleast 32
                    parameter TKEEP_WIDTH = DATA_WIDTH/8,
                    parameter TX_ONLY = 0,
                    parameter RX_ONLY = 0,
		    parameter DBG_RAM_PRESENT = 1
                    )
   (
    input                          clk,
    input                          rst_n,

    input [31:0]                   cfg_addr,
    input [31:0]                   cfg_wdata,
    input                          cfg_wr,
    input                          cfg_rd,
    output logic                   tst_cfg_ack,
    output logic [31:0]            tst_cfg_rdata,

    input                          channel_ready,

    output logic                   axis_tx_tvalid,
    output logic [DATA_WIDTH-1:0]  axis_tx_tdata,
    output logic                   axis_tx_tlast,
    output logic [TKEEP_WIDTH-1:0] axis_tx_tkeep,
    input                          axis_tx_tready,

    input                          axis_rx_tvalid,
    input [DATA_WIDTH-1:0]         axis_rx_tdata,
    input                          axis_rx_tlast,
    input [TKEEP_WIDTH-1:0]        axis_rx_tkeep,
    output logic                   axis_rx_tready

    );

   parameter DATA_DW = DATA_WIDTH / 32;

`ifdef SIM
   // For simulation
   parameter PREAMBLE_PKT_CNT = 32'hF;
   parameter PREAMBLE_TKEEP = {{(TKEEP_WIDTH-4){1'b0}}, {4{1'b1}}};
`else
   parameter PREAMBLE_PKT_CNT = 32'hFF;
   parameter PREAMBLE_TKEEP = {{(TKEEP_WIDTH-8){1'b0}}, {8{1'b1}}};
`endif
   parameter TX_WAIT_CNT = 32'hF;
   parameter RX_LOCK_CNT_MINUS1 = 32'h4;

   typedef enum logic [2:0] {IDLE = 0,
                             PREAMBLE = 1,
                             WAIT = 2,
                             PKT_START = 3,
                             PKT_DATA = 4,
                             PKT_END = 5} pkt_state_t;


   logic        pre_sync_rst_n;
   logic        sync_rst_n;
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

   // Registers

   // Offset 0x00 : Tx CFG, Status
   // 0 - TX Enable (0 - Disable, 1 - Enable) (RW)
   // 1 - TX PRBS Mode (0 - Data Increment, 1 - Data PRBS Enable) (RW)
   // 2 - TX PKT Len Mode (0 - Increment, 1 - Constant) (RW)
   // 3 - TX No Scramble (0 - Scramble, 1 - No Scramble) (RW)
   // 4 - TX No Increment (0 - Increment, 1 - No Increment) (RW)
   // 30:5 - Reserved
   // 31 - Ready (0 - Not Ready, 1 - Ready)

   // Offset 0x04 : TX Seed 0
   // 31:0 - Tx Seed 0 (RW)

   // Offset 0x08 : TX Seed 1
   // 31:0 - Tx Seed 1 (RW)

   // Offset 0x0C : Tx Min Pkt Len
   // 31:0 - Min Pkt Len (RW)

   // Offset 0x10 : Tx Max Pkt Len
   // 31:0 - Max Pkt Len (RW)

   // Offset 0x14 : TX Pkt Count 0
   // 31:0 - Tx Pkt Count 0 (W0C)

   // Offset 0x18 : TX Pkt Count 1
   // 31:0 - Tx Pkt Count 1 (W0C)

   // Offset 0x1C : Tick Count (Clock frequency)
   // 31:0 - Tick Count (RW)

   // Offset 0x20 : TX Timer
   // 31:0 - Tx Timer 0 (W0C) (Seconds since starting)

   // Offset 0x7C-here : Reserved

   // Offset 0x80 : Rx CFG, Status
   // 0 - RX Enable (0 - Disable, 1 - Enable) (RW)
   // 1 - RX PRBS Mode (0 - PRBS Disable, 1 - PRBS Enable) (RW)
   // 2 - RX PKT Len Mode (0 - Increment, 1 - Constant) (RW) - Not Used now
   // 3 - RX No Scramble (0 - Scramble, 1 - No Scramble) (RW)
   // 4 - RX No Increment (0 - Increment, 1 - No Increment) (RW)
   // 7:5 - Reserved
   // 8 - RX Data Check Enable (0 - Disable, 1 - Enable) (RW)
   // 9 - RX Pkt Len Check Disable (0 - Enable, 1 - Disable) (RW) - Not Used now
   // 11:10 - Reserved
   // 12 - RX Loop back Mode (Rx is connected to Tx)
   // 27:13 - Reserved
   // 28 - Rx Packet Length Error (R,W1C) - Not Used now
   // 29 - Rx Lock Timeout Error (R,W1C) - Not Used now
   // 30 - Rx Data Error (R,W1C)
   // 31 - Rx Lock (RO)

   // Offset 0x84 : RX Seed 0 - Not Used now
   // 31:0 - Rx Data 0 (W0C)

   // Offset 0x88 : RX Seed 1 - Not Used now
   // 31:0 - Rx Data 1 (RO)

   // Offset 0x8C : Rx Min Pkt Len - Not Used now
   // 31:0 - Min Pkt Len (RW)

   // Offset 0x90 : Rx Max Pkt Len - Not Used now
   // 31:0 - Max Pkt Len (RW)

   // Offset 0x94 : RX Pkt Count 0
   // 31:0 - Rx Pkt Count 0 (W0C)

   // Offset 0x98 : RX Pkt Count 1
   // 31:0 - Rx Pkt Count 1 (W0C)

   // Offset 0x9C : RX Err Pkt Count 0
   // 31:0 - Rx Err Pkt Count 0 (W0C)

   // Offset 0xA0 : RX Err Pkt Count 1
   // 31:0 - Rx Err Pkt Count 1 (W0C)

   // Offset 0xA4 : RX Err Count 0
   // 31:0 - Rx Err Count 0 (W0C)

   // Offset 0xA8 : RX Err Count 1
   // 31:0 - Rx Err Count 1 (W0C)

   // Offset 0xAC : RX Timer
   // 31:0 - Rx Timer 0 (W0C) (Seconds since first lock)

   // Offset 0xB0 : RX Raw Pkt Count 0
   // 31:0 - Rx Raw Pkt Count 0 (W0C)

   // Offset 0xB4 : RX Raw Pkt Count 1
   // 31:0 - Rx Raw Pkt Count 1 (W0C)

   // Offset 0xB8 : RX Raw Data Count 0
   // 31:0 - Rx Raw Data Count 0 (W0C)

   // Offset 0xBC : RX Raw Data Count 1
   // 31:0 - Rx Raw Data Count 1 (W0C)

   // Offset 0xC0 : RX Raw Err Count 0
   // 31:0 - Rx Raw Err Count 0 (W0C)

   // Offset 0xC4 : RX Raw Err Count 1
   // 31:0 - Rx Raw Err Count 1 (W0C)

   // Offset 0xC8 : RX Debug RAM Index (lower 5 bits - DW Index, next 5 bits - RAM Entry index)
   // 31:0 - Rx Debug RAM Index (RW)

   // Offset 0xCC : RX Debug RAM Data
   // 31:0 - Rx Debug RAM Data (RO)

   // Offset 0xFC-here : Reserved

   logic        cfg_wr_stretch;
   logic        cfg_rd_stretch;

   logic [7:0]  cfg_addr_q;        //Only care about lower 8-bits of address, upper bits are decoded somewhere else
   logic [31:0] cfg_wdata_q;


   //Commands are single cycle pulse, stretch here
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
       begin
          cfg_wr_stretch <= 0;
          cfg_rd_stretch <= 0;
          cfg_addr_q <= 0;
          cfg_wdata_q <= 0;
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

   //Ack for cycle
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
       tst_cfg_ack <= 0;
     else
       tst_cfg_ack <= ((cfg_wr_stretch||cfg_rd_stretch) && !tst_cfg_ack);

   logic cfg_tx_en = 0;
   logic cfg_tx_prbs = 0;
   logic cfg_tx_pktlen_mode= 0;
   logic cfg_tx_no_scramble= 0;
   logic cfg_tx_no_inc= 0;
   logic [31:0] cfg_tx_seed_0= 0;
   logic [31:0] cfg_tx_seed_1= 0;
   logic [31:0] cfg_tx_pktlen_min= 0;
   logic [31:0] cfg_tx_pktlen_max= 0;

   logic[31:0] cfg_tx_num_pkts = 0;
   logic cfg_tx_num_pkts_en = 0;

   logic cfg_rx_en= 0;
   logic cfg_rx_prbs= 0;
   logic cfg_rx_pktlen_mode= 0;
   logic cfg_rx_no_scramble= 0;
   logic cfg_rx_no_inc= 0;
   logic [31:0] cfg_rx_pktlen_min= 0;
   logic [31:0] cfg_rx_pktlen_max= 0;
   logic        cfg_rx_data_chk= 0;
   logic        cfg_rx_pktlen_chk_dis= 0;
   logic        cfg_rx_loopback= 0;

   logic [31:0] cfg_tick_cnt= 0;

   logic cfg_rx_lock_err= 0;
   logic cfg_rx_data_err= 0;
   logic cfg_rx_pktlen_err= 0;

   logic clr_tx_pkt_cnt;
   logic clr_rx_pkt_cnt;
   logic clr_rx_err_pkt_cnt;
   logic clr_rx_err_cnt;
   logic clr_tx_timer;
   logic clr_rx_timer;
   logic clr_rx_raw_pkt_cnt;
   logic clr_rx_raw_data_cnt;
   logic clr_rx_raw_err_cnt;

   logic [31:0] tx_pream_pkt_cnt = 0;
   logic [63:0] tx_pkt_cnt = 0;
   logic        preamble_done;
   logic [31:0] tx_wait_cnt = 0;
   logic        wait_done;
   logic [31:0] next_tx_pktlen;
   logic [31:0] tx_pktlen = 0;
   logic [31:0] tx_slice_idx = 0;
   logic [31:0] next_tx_data_0;
   logic [31:0] tx_data_0 = 0;
   logic [31:0] next_tx_data_1;
   logic [31:0] tx_data_1 = 0;
   logic [TKEEP_WIDTH-1:0] tx_tkeep;

   logic rx_lock = 0;
   logic rx_lock_err;
   logic rx_data_err;
   logic rx_pktlen_err;
   logic [63:0] rx_pkt_cnt = 64'd0;
   logic [63:0] rx_err_pkt_cnt = 64'd0;
   logic [63:0] rx_err_cnt = 64'd0;
   logic [63:0] rx_raw_pkt_cnt = 64'd0;
   logic [63:0] rx_raw_data_cnt = 64'd0;
   logic [63:0] rx_raw_err_cnt = 64'd0;

   logic        rx_tvalid;
   logic [DATA_WIDTH-1:0] rx_tdata;
   logic                  rx_tlast;
   logic [TKEEP_WIDTH-1:0] rx_tkeep;
   logic [31:0]            rx_lock_cnt = 0;

   logic [31:0] next_rx_exp_pktlen;
   logic [31:0] rx_exp_pktlen = 0;
   logic [31:0] rx_slice_idx = 0;
   logic [31:0] next_rx_data_0_in;
   logic [31:0] next_rx_data_0;
   logic [31:0] rx_data_0 = 0;
   logic [31:0] next_rx_data_1_in;
   logic [31:0] next_rx_data_1;
   logic [31:0] rx_data_1 = 0;
   logic [TKEEP_WIDTH-1:0] rx_exp_tkeep;
   logic                   rx_exp_tlast;
   logic [DATA_WIDTH-1:0]  rx_exp_tdata;
   logic [DATA_WIDTH-1:0] rx_exp_tdata_w_mask;
   logic [DATA_WIDTH-1:0] rx_tdata_w_mask;
   logic                  rx_data_mismatch;

   logic [31:0] sec_tick;
   logic [31:0] tx_timer = 0;
   logic        rx_timer_en = 0;
   logic [31:0] rx_timer = 0;
   logic        rx_errored_pkt = 0;

   logic [31:0] cfg_rx_dbg_ram_index = 0;
   logic [31:0] cfg_rx_dbg_ram_rdata = 0;

   logic        clr_last_rx_data_0;
   logic [31:0] last_rx_data_0 = 0;
   logic [31:0] last_rx_data_1 = 0;

   logic                   tx_ff_tvalid;
   logic [DATA_WIDTH-1:0]  tx_ff_tdata;
   logic [TKEEP_WIDTH-1:0] tx_ff_tkeep;
   logic                   tx_ff_tlast;
   logic                   tx_ff_tready;

   logic                   rx_ff_tvalid;
   logic [DATA_WIDTH-1:0]  rx_ff_tdata;
   logic [TKEEP_WIDTH-1:0] rx_ff_tkeep;
   logic                   rx_ff_tlast;
   logic                   rx_ff_tready;

always @(posedge clk)
  if (cfg_wr_stretch) begin
      if (cfg_addr_q==`CFG_ADDR_TX_CFG)
        {cfg_tx_num_pkts_en, cfg_tx_no_inc, cfg_tx_no_scramble, cfg_tx_pktlen_mode, cfg_tx_prbs, cfg_tx_en} <= cfg_wdata_q[5:0];
      else if (cfg_addr_q==`CFG_ADDR_TX_SEED0)
        cfg_tx_seed_0 <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_TX_SEED1)
        cfg_tx_seed_1 <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_TX_MIN_PKTLEN)
        cfg_tx_pktlen_min <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_TX_MAX_PKTLEN)
        cfg_tx_pktlen_max <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_TICK_CNT)
        cfg_tick_cnt <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_TX_NUM_PKTS)
         cfg_tx_num_pkts <= cfg_wdata_q;

      else if (cfg_addr_q==`CFG_ADDR_RX_CFG) begin
         {cfg_rx_no_inc, cfg_rx_no_scramble, cfg_rx_pktlen_mode, cfg_rx_prbs, cfg_rx_en} <= cfg_wdata_q[4:0];
         {cfg_rx_pktlen_chk_dis, cfg_rx_data_chk} <= cfg_wdata_q[9:8];
         cfg_rx_loopback <= cfg_wdata_q[12];
      end // if (cfg_addr_q==8'h80)
      else if (cfg_addr_q==`CFG_ADDR_RX_MIN_PKTLEN)
        cfg_rx_pktlen_min <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_RX_MAX_PKTLEN)
        cfg_rx_pktlen_max <= cfg_wdata_q;
      else if (cfg_addr_q==`CFG_ADDR_RX_DBG_RAM_INDEX)
        cfg_rx_dbg_ram_index <= cfg_wdata_q;
   end // if (cfg_wr_stretch)


always @(posedge clk)
  begin
         cfg_rx_lock_err <= rx_lock_err ? 1'b1 :
                            (cfg_wr_stretch && cfg_wdata_q[29]) ? 1'b0 :
                            cfg_rx_lock_err;
         cfg_rx_data_err <= rx_data_err ? 1'b1 :
                            (cfg_wr_stretch && cfg_wdata_q[30]) ? 1'b0 :
                            cfg_rx_data_err;
         cfg_rx_pktlen_err <= rx_pktlen_err ? 1'b1 :
                              (cfg_wr_stretch && cfg_wdata_q[28]) ? 1'b0 :
                              cfg_rx_pktlen_err;
   end // else: !if(!rst_n)

   assign clr_tx_pkt_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_TX_PKT_CNT0);
   assign clr_tx_timer   = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_TX_TIMER);
   assign clr_rx_pkt_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_PKT_CNT0);
   assign clr_rx_err_pkt_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_ERR_PKT_CNT0);
   assign clr_rx_err_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_ERR_CNT0);
   assign clr_rx_timer   = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_TIMER);
   assign clr_rx_raw_pkt_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_RAW_PKT_CNT0);
   assign clr_rx_raw_data_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_RAW_DATA_CNT0);
   assign clr_rx_raw_err_cnt = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_RAW_ERR_CNT0);
   assign clr_last_rx_data_0 = cfg_wr_stretch && (cfg_wdata_q[31:0] == 32'd0) && (cfg_addr_q == `CFG_ADDR_RX_DATA0);

   //Readback mux
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
       tst_cfg_rdata <= 0;
   else
     case (cfg_addr_q)
       `CFG_ADDR_TX_CFG        :      tst_cfg_rdata <= {channel_ready, 25'd0, cfg_tx_num_pkts_en, cfg_tx_no_inc, cfg_tx_no_scramble, cfg_tx_pktlen_mode, cfg_tx_prbs, cfg_tx_en};
       `CFG_ADDR_TX_SEED0      :      tst_cfg_rdata <= cfg_tx_seed_0;
       `CFG_ADDR_TX_SEED1      :      tst_cfg_rdata <= cfg_tx_seed_1;
       `CFG_ADDR_TX_MIN_PKTLEN :      tst_cfg_rdata <= cfg_tx_pktlen_min;
       `CFG_ADDR_TX_MAX_PKTLEN :      tst_cfg_rdata <= cfg_tx_pktlen_max;
       `CFG_ADDR_TX_PKT_CNT0   :      tst_cfg_rdata <= tx_pkt_cnt[31:0];
       `CFG_ADDR_TX_PKT_CNT1   :      tst_cfg_rdata <= tx_pkt_cnt[63:32];
       `CFG_ADDR_TICK_CNT      :      tst_cfg_rdata <= cfg_tick_cnt[31:0];
       `CFG_ADDR_TX_TIMER      :      tst_cfg_rdata <= tx_timer[31:0];
       `CFG_ADDR_TX_NUM_PKTS   :      tst_cfg_rdata <= cfg_tx_num_pkts;

       `CFG_ADDR_RX_CFG          :    tst_cfg_rdata <= {rx_lock, cfg_rx_data_err, cfg_rx_lock_err, cfg_rx_pktlen_err, 15'd0, cfg_rx_loopback, 2'd0, cfg_rx_pktlen_chk_dis, cfg_rx_data_chk, 3'd0, cfg_rx_no_inc, cfg_rx_no_scramble, cfg_rx_pktlen_mode, cfg_rx_prbs, cfg_rx_en};
       `CFG_ADDR_RX_DATA0        :    tst_cfg_rdata <= last_rx_data_0;
       `CFG_ADDR_RX_DATA1        :    tst_cfg_rdata <= last_rx_data_1;
       `CFG_ADDR_RX_MIN_PKTLEN   :    tst_cfg_rdata <= cfg_rx_pktlen_min;
       `CFG_ADDR_RX_MAX_PKTLEN   :    tst_cfg_rdata <= cfg_rx_pktlen_max;
       `CFG_ADDR_RX_PKT_CNT0     :    tst_cfg_rdata <= rx_pkt_cnt[31:0];
       `CFG_ADDR_RX_PKT_CNT1     :    tst_cfg_rdata <= rx_pkt_cnt[63:32];
       `CFG_ADDR_RX_ERR_PKT_CNT0 :    tst_cfg_rdata <= rx_err_pkt_cnt[31:0];
       `CFG_ADDR_RX_ERR_PKT_CNT1 :    tst_cfg_rdata <= rx_err_pkt_cnt[63:32];
       `CFG_ADDR_RX_ERR_CNT0     :    tst_cfg_rdata <= rx_err_cnt[31:0];
       `CFG_ADDR_RX_ERR_CNT1     :    tst_cfg_rdata <= rx_err_cnt[63:32];
       `CFG_ADDR_RX_TIMER        :    tst_cfg_rdata <= rx_timer[31:0];
       `CFG_ADDR_RX_RAW_PKT_CNT0     :    tst_cfg_rdata <= rx_raw_pkt_cnt[31:0];
       `CFG_ADDR_RX_RAW_PKT_CNT1     :    tst_cfg_rdata <= rx_raw_pkt_cnt[63:32];
       `CFG_ADDR_RX_RAW_DATA_CNT0     :    tst_cfg_rdata <= rx_raw_data_cnt[31:0];
       `CFG_ADDR_RX_RAW_DATA_CNT1     :    tst_cfg_rdata <= rx_raw_data_cnt[63:32];
       `CFG_ADDR_RX_RAW_ERR_CNT0     :    tst_cfg_rdata <= rx_raw_err_cnt[31:0];
       `CFG_ADDR_RX_RAW_ERR_CNT1     :    tst_cfg_rdata <= rx_raw_err_cnt[63:32];
       `CFG_ADDR_RX_DBG_RAM_INDEX    :    tst_cfg_rdata <= cfg_rx_dbg_ram_index;
       `CFG_ADDR_RX_DBG_RAM_DATA     :    tst_cfg_rdata <= cfg_rx_dbg_ram_rdata;
       default:    tst_cfg_rdata <= 32'hdeaddead;
     endcase // case (cfg_addr_q)

   // Second Ticks
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) sec_tick <= 0;
     else if (cfg_wr_stretch && (cfg_addr_q == `CFG_ADDR_TICK_CNT))
       sec_tick <= cfg_wdata_q;
     else if (sec_tick == 0)
       sec_tick <= cfg_tick_cnt;
     else
       sec_tick <= sec_tick - 32'd1;

if (RX_ONLY == 0) begin

   // Tx Pkt FSM
   pkt_state_t tx_pkt_state, next_tx_pkt_state;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) tx_pkt_state <= IDLE;
     else        tx_pkt_state <= cfg_tx_en ? next_tx_pkt_state : IDLE;

   always_comb begin
      case (tx_pkt_state)
        IDLE :
         if (cfg_tx_en && (!cfg_tx_num_pkts_en || (tx_pkt_cnt==0)))
             next_tx_pkt_state = WAIT;
         else
              next_tx_pkt_state = IDLE;
//             next_tx_pkt_state = PREAMBLE;
//
//         PREAMBLE :
//           if (preamble_done)
//             next_tx_pkt_state = WAIT;
//           else
//             next_tx_pkt_state = PREAMBLE;

        WAIT :
          if (wait_done)
            next_tx_pkt_state = PKT_START;
          else
            next_tx_pkt_state = WAIT;

        PKT_START :
          next_tx_pkt_state = PKT_DATA;

        PKT_DATA :
          if ((tx_slice_idx == tx_pktlen - 1) && tx_ff_tready)
            next_tx_pkt_state = PKT_END;
          else
            next_tx_pkt_state = PKT_DATA;

        PKT_END :
         if (cfg_tx_num_pkts_en && (tx_pkt_cnt>=cfg_tx_num_pkts))
            next_tx_pkt_state = IDLE;
         else
            next_tx_pkt_state = PKT_START;

        default :
          next_tx_pkt_state = IDLE;

      endcase // case (tx_pkt_state)
   end // always_comb


   // Pkt Count
   always @(posedge clk)
     if (tx_pkt_state == IDLE)
       tx_pream_pkt_cnt <= 0;
     else if ((tx_pkt_state == PREAMBLE) && tx_ff_tready)
       tx_pream_pkt_cnt <= tx_pream_pkt_cnt + 1;
     else
       tx_pream_pkt_cnt <= tx_pream_pkt_cnt;

   // Preamble Done
   assign preamble_done = (tx_pkt_state == PREAMBLE) && (tx_pream_pkt_cnt >= PREAMBLE_PKT_CNT) & tx_ff_tready;

   // Wait Count
   always @(posedge clk)
     if ((tx_pkt_state == IDLE) && (next_tx_pkt_state == WAIT))
       tx_wait_cnt <= 0;
     else if (tx_pkt_state == WAIT)
       tx_wait_cnt <= tx_wait_cnt + 1;
     else
       tx_wait_cnt <= tx_wait_cnt;

   // Wait done
   assign wait_done = (tx_pkt_state == WAIT) && (tx_wait_cnt >= TX_WAIT_CNT);

   // Pkt Count
   always @(posedge clk)
     if (clr_tx_pkt_cnt)
       tx_pkt_cnt <= 0;
     else if (tx_pkt_state == PKT_END)
       tx_pkt_cnt <= tx_pkt_cnt + 1;
     else
       tx_pkt_cnt <= tx_pkt_cnt;

   // Next Tx Pkt Len
   assign next_tx_pktlen = (tx_pktlen >= cfg_tx_pktlen_max) ? cfg_tx_pktlen_min :
                           cfg_tx_pktlen_mode ? tx_pktlen + 1 : cfg_tx_pktlen_min;

   always @(posedge clk)
     if ((tx_pkt_state == WAIT) && wait_done)
       tx_pktlen <= cfg_tx_pktlen_min;
     else if (tx_pkt_state == PKT_END)
       tx_pktlen <= next_tx_pktlen;
     else
       tx_pktlen <= tx_pktlen;

   // Slice Index
   always @(posedge clk)
     if (tx_pkt_state == PKT_START)
       tx_slice_idx <= 0;
     else if ((tx_pkt_state == PKT_DATA) && tx_ff_tready)
       tx_slice_idx <= tx_slice_idx + 1;
     else
       tx_slice_idx <= tx_slice_idx;

   assign next_tx_data_0 = (cfg_tx_prbs == 0 && cfg_tx_no_inc == 1) ? cfg_tx_seed_0 :
                           (cfg_tx_prbs == 0 && cfg_tx_no_inc == 0) ? tx_data_0 + 1 :
                           crc32(tx_data_0, 1'b1);

   // Data 0
   always @(posedge clk)
     if ((tx_pkt_state == PKT_START) && (tx_pkt_cnt == 0))
         tx_data_0 <= cfg_tx_seed_0;
     else if ((tx_pkt_state == PKT_DATA) && tx_ff_tready)
       tx_data_0 <= next_tx_data_0;
     else
       tx_data_0 <= tx_data_0;

   assign next_tx_data_1 = (cfg_tx_prbs == 0) ? tx_data_1 + 1 :
                           crc32(tx_data_1, 1'b1);
   // Data 1
   always @(posedge clk)
     if ((tx_pkt_state == PKT_START) && (tx_pkt_cnt == 0))
       tx_data_1  <= cfg_tx_seed_1;
     else if ((tx_pkt_state == PKT_DATA) && tx_ff_tready)
       tx_data_1 <= next_tx_data_1;
     else
       tx_data_1 <= tx_data_1;

   // Tx Streaming Interface
   assign tx_ff_tvalid = (tx_pkt_state == PREAMBLE) || (tx_pkt_state == PKT_DATA);

   always_comb begin
      if (tx_pkt_state == PREAMBLE)
        tx_ff_tdata[DATA_WIDTH-1:0]  = {{(DATA_WIDTH-32){1'b0}}, tx_pream_pkt_cnt};
      else begin
          for (int dw_idx = 0; dw_idx < DATA_DW; dw_idx++) begin
             if (cfg_tx_no_scramble == 1)
               tx_ff_tdata[32*dw_idx +: 32]  = {{(DATA_WIDTH-32){1'b0}}, tx_data_0[31:0]};
             else begin
                if (dw_idx % 2 == 0)
                  tx_ff_tdata[32*dw_idx +: 32] = ({tx_data_0[31:0], tx_data_0[31:0]}) >> dw_idx;
                else
                  tx_ff_tdata[32*dw_idx +: 32] = ({tx_data_1[31:0], tx_data_1[31:0]}) >> (dw_idx - 1);
             end

          end // for (int dw_idx = 0; dw_idx < DATA_DW; dw_idx++)


      end // else: !if(tx_pkt_state == PREAMBLE)

   end // always_comb

//   always_comb begin
//          for (int qw_idx = 0; qw_idx < DATA_DW/2; qw_idx++) begin
//             if (cfg_tx_no_scramble == 1)
//               tx_ff_tdata[64*qw_idx +: 64]  = {tx_data_1[31:0], tx_data_0[31:0]};
//             else
//                tx_ff_tdata[64*qw_idx +: 64] = ({tx_data_1[31:0], tx_data_0[31:0], tx_data_1[31:0], tx_data_0[31:0]}) >> qw_idx;
//
//          end // for (int qw_idx = 0; qw_idx < DATA_DW; qw_idx++)
//
//   end // always_comb


   assign tx_ff_tlast = (tx_pkt_state == PREAMBLE) || ((tx_pkt_state == PKT_DATA) && (tx_slice_idx == (tx_pktlen - 1)));

   // TKeep
   assign tx_ff_tkeep = (tx_pkt_state == PREAMBLE) ? PREAMBLE_TKEEP : {TKEEP_WIDTH{1'b1}};

   // Tx Timer
   always @(posedge clk)
     if (clr_tx_timer)
       tx_timer <= 0;
     else if (tx_pkt_state != IDLE && (sec_tick == 0))
       tx_timer <= tx_timer + 32'd1;
     else
       tx_timer <= tx_timer;

   // Output fifo
   axis_flop_fifo #(.DATA_WIDTH(DATA_WIDTH),
                    .KEEP_WIDTH(TKEEP_WIDTH)
                    ) TX_FIFO (.aclk (clk),
                               .aresetn (sync_rst_n),
                               .sync_rst_n (1'b1),

                               .s_axis_valid (tx_ff_tvalid),
                               .s_axis_data  (tx_ff_tdata ),
                               .s_axis_last  (tx_ff_tlast ),
                               .s_axis_keep  (tx_ff_tkeep ),
                               .s_axis_ready (tx_ff_tready),

                               .m_axis_valid (axis_tx_tvalid),
                               .m_axis_data  (axis_tx_tdata ),
                               .m_axis_last  (axis_tx_tlast ),
                               .m_axis_keep  (axis_tx_tkeep ),
                               .m_axis_ready (axis_tx_tready)
                               );

end // if (RX_ONLY == 0)

if (TX_ONLY == 0) begin

   // Input fifo
   axis_flop_fifo #(.IN_FIFO (1),
                    .DATA_WIDTH(DATA_WIDTH),
                    .KEEP_WIDTH(TKEEP_WIDTH)
                    ) RX_FIFO (.aclk (clk),
                               .aresetn (sync_rst_n),
                               .sync_rst_n (1'b1),

                               .s_axis_valid (axis_rx_tvalid),
                               .s_axis_data  (axis_rx_tdata ),
                               .s_axis_last  (axis_rx_tlast ),
                               .s_axis_keep  (axis_rx_tkeep ),
                               .s_axis_ready (axis_rx_tready),

                               .m_axis_valid (rx_ff_tvalid),
                               .m_axis_data  (rx_ff_tdata ),
                               .m_axis_last  (rx_ff_tlast ),
                               .m_axis_keep  (rx_ff_tkeep ),
                               .m_axis_ready (rx_ff_tready)
                               );


   // Flop the Rx inputs
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) begin
        rx_tvalid <= 1'b0;
        rx_tdata <= 0;
        rx_tlast <= 0;
        rx_tkeep <= 0;
     end
     else begin
        rx_tvalid <= cfg_rx_loopback ? axis_tx_tvalid : rx_ff_tvalid;
//        rx_tdata <=  (sec_tick == 5) ? {DATA_WIDTH{1'b1}} : rx_ff_tdata ;
        rx_tdata <=  cfg_rx_loopback ? axis_tx_tdata : rx_ff_tdata ;
        rx_tlast <=  cfg_rx_loopback ? axis_tx_tlast : rx_ff_tlast ;
        rx_tkeep <=  cfg_rx_loopback ? axis_tx_tkeep : rx_ff_tkeep ;
     end // else: !if(!rst_n)

   // Rx_Tready
   assign rx_ff_tready = cfg_rx_en;

   // Rx Pkt FSM
   pkt_state_t rx_pkt_state, next_rx_pkt_state;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) rx_pkt_state <= IDLE;
     else        rx_pkt_state <= cfg_rx_en ? next_rx_pkt_state : IDLE;

   always_comb begin
      case (rx_pkt_state)
        IDLE :
          next_rx_pkt_state = PREAMBLE;

        PREAMBLE :
          if ((rx_lock_cnt[31:0] >= RX_LOCK_CNT_MINUS1) && rx_tvalid && !rx_data_mismatch)
            next_rx_pkt_state = PKT_DATA;
          else
            next_rx_pkt_state = PREAMBLE;

        PKT_DATA :
          if (rx_tvalid && rx_data_mismatch)
            next_rx_pkt_state = PREAMBLE;
          else
            next_rx_pkt_state = PKT_DATA;

        default :
          next_rx_pkt_state = IDLE;

      endcase // case (rx_pkt_state)
   end // always_comb

   // Rx FSM
   always @(posedge clk)
     if (rx_pkt_state == IDLE)
       rx_lock_cnt[31:0] <= 0;
     else if (rx_tvalid) begin
        if (rx_tvalid && rx_data_mismatch)
          rx_lock_cnt[31:0] <= 32'd0;
        else
          rx_lock_cnt[31:0] <= rx_lock_cnt[31:0] + 32'd1;
     end
     else
       rx_lock_cnt[31:0] <= rx_lock_cnt[31:0];

   // Rx lock
   always @(posedge clk)
     if (rx_pkt_state == IDLE)
       rx_lock <= 1'b0;
     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_data_mismatch)
       rx_lock <= 1'b0;
     else if ((rx_pkt_state == PREAMBLE) && (rx_lock_cnt[31:0] >= RX_LOCK_CNT_MINUS1) && rx_tvalid && !rx_data_mismatch)
       rx_lock <= 1'b1;
     else
       rx_lock <= rx_lock;

   // Locked Pkt Count
   always @(posedge clk)
     if (clr_rx_pkt_cnt)
       rx_pkt_cnt <= 0;
     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_tlast)
       rx_pkt_cnt <= rx_pkt_cnt + 1;
     else
       rx_pkt_cnt <= rx_pkt_cnt;

   // Errored Packet
   always @(posedge clk)
     if ((rx_tvalid && rx_tlast && (rx_pkt_state == PKT_DATA)) || (rx_pkt_state == IDLE) || (rx_pkt_state == PREAMBLE))
       rx_errored_pkt <= 0;
     else if (rx_tvalid && (rx_pkt_state == PKT_DATA) && rx_data_mismatch)
       rx_errored_pkt <= 1;
     else
       rx_errored_pkt <= rx_errored_pkt;

   // Error Pkt count
   always @(posedge clk)
     if (clr_rx_err_pkt_cnt)
       rx_err_pkt_cnt <= 0;
     else if (rx_tvalid && rx_tlast && (rx_pkt_state == PKT_DATA) && (rx_errored_pkt || rx_data_mismatch))
       rx_err_pkt_cnt <= rx_err_pkt_cnt + 32'd1;
     else
       rx_err_pkt_cnt <= rx_err_pkt_cnt;

   // Raw Error Count
   always@(posedge clk)
     if (clr_rx_err_cnt)
       rx_err_cnt <= 0;
     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_data_mismatch)
       rx_err_cnt <= rx_err_cnt + 32'd1;
     else
       rx_err_cnt <= rx_err_cnt;

   // Raw Pkt Count
   always@(posedge clk)
     if (clr_rx_raw_pkt_cnt)
       rx_raw_pkt_cnt <= 0;
     else if (rx_tvalid && rx_tlast)
       rx_raw_pkt_cnt <= rx_raw_pkt_cnt + 1;
     else
       rx_raw_pkt_cnt <= rx_raw_pkt_cnt;

   // Raw data Count
   always@(posedge clk)
     if (clr_rx_raw_data_cnt)
       rx_raw_data_cnt <= 0;
     else if (rx_tvalid)
       rx_raw_data_cnt <= rx_raw_data_cnt + 1;
     else
       rx_raw_data_cnt <= rx_raw_data_cnt;

   // Raw Err Count
   always@(posedge clk)
     if (clr_rx_raw_err_cnt)
       rx_raw_err_cnt <= 0;
     else if (rx_tvalid && rx_data_mismatch)
       rx_raw_err_cnt <= rx_raw_err_cnt + 1;
     else
       rx_raw_err_cnt <= rx_raw_err_cnt;


   assign next_rx_data_0_in = rx_tvalid && rx_data_mismatch ? rx_tdata[31:0] :
                              rx_data_0;

   assign next_rx_data_0 = (cfg_rx_prbs == 0 && cfg_rx_no_inc == 1) ? next_rx_data_0_in :
                           (cfg_rx_prbs == 0 && cfg_rx_no_inc == 0) ? next_rx_data_0_in + 1 :
                           crc32(next_rx_data_0_in, 1'b1);

   // Data 0
   always@(posedge clk)
     if (rx_tvalid)
       rx_data_0 <= next_rx_data_0;
     else
       rx_data_0 <= rx_data_0;

   assign next_rx_data_1_in = rx_tvalid && rx_data_mismatch ? rx_tdata[63:32] :
                              rx_data_1;

   assign next_rx_data_1 = (cfg_rx_prbs == 0) ? next_rx_data_1_in + 1 :
                           crc32(next_rx_data_1_in, 1'b1);
   // Data 1
   always@(posedge clk)
     if (rx_tvalid)
       rx_data_1 <= next_rx_data_1;
     else
       rx_data_1 <= rx_data_1;

   always_comb begin
          for (int dw_idx = 0; dw_idx < DATA_DW; dw_idx++) begin
             if (cfg_rx_no_scramble == 1)
               rx_exp_tdata[32*dw_idx +: 32]  = {{(DATA_WIDTH-32){1'b0}}, rx_data_0[31:0]};
             else begin
                if (dw_idx % 2 == 0)
                  rx_exp_tdata[32*dw_idx +: 32] = ({rx_data_0[31:0], rx_data_0[31:0]}) >> dw_idx;
                else
                  rx_exp_tdata[32*dw_idx +: 32] = ({rx_data_1[31:0], rx_data_1[31:0]}) >> (dw_idx - 1);
             end

          end // for (int dw_idx = 0; dw_idx < DATA_DW; dw_idx++)

   end // always_comb

//   always_comb begin
//      for (int qw_idx = 0; qw_idx < DATA_DW/2; qw_idx++) begin
//         if (cfg_rx_no_scramble == 1)
//           rx_exp_tdata[64*qw_idx +: 64]  = {rx_data_1[31:0], rx_data_0[31:0]};
//         else
//           rx_exp_tdata[64*qw_idx +: 64] = ({rx_data_1[31:0], rx_data_0[31:0], rx_data_1[31:0], rx_data_0[31:0]}) >> qw_idx;
//
//      end // for (int qw_idx = 0; qw_idx < DATA_DW; qw_idx++)
//
//   end // always_comb

   always_comb
     for (int byte_idx = 0; byte_idx < (DATA_WIDTH>>3); byte_idx++) begin
        if (rx_tlast && (rx_tkeep[byte_idx] == 0)) begin
           rx_exp_tdata_w_mask[8*byte_idx +: 8] = 8'd0;
           rx_tdata_w_mask[8*byte_idx +: 8] = 8'd0;
        end
        else begin
           rx_exp_tdata_w_mask[8*byte_idx +: 8] = rx_exp_tdata[8*byte_idx +: 8];
           rx_tdata_w_mask[8*byte_idx +: 8] = rx_tdata[8*byte_idx +: 8];
        end
     end

   // Packet Data error when
   assign rx_data_mismatch = (rx_exp_tdata_w_mask != rx_tdata_w_mask);
   assign rx_data_err = cfg_rx_en && cfg_rx_data_chk && (rx_pkt_state == PKT_DATA) && rx_tvalid && rx_data_mismatch;

   // Rx Timer Count Enable
   always@(posedge clk)
     if (rx_pkt_state == IDLE)
       rx_timer_en <= 0;
     else if (rx_lock)
       rx_timer_en <= 1;
     else
       rx_timer_en <= rx_timer_en;

   // Rx Timer
   always@(posedge clk)
     if (clr_rx_timer)
       rx_timer <= 0;
     else if ((sec_tick == 0) && rx_timer_en)
       rx_timer <= rx_timer + 32'd1;
     else
       rx_timer <= rx_timer;

   // TODO: Have to fix packet length check. For now, this logic does not work because the RX seed functionality changed

   // Next Rx Pkt Len
   assign next_rx_exp_pktlen = (rx_exp_pktlen >= cfg_rx_pktlen_max) ? cfg_rx_pktlen_min :
                               cfg_rx_pktlen_mode ? rx_exp_pktlen + 1 : cfg_rx_pktlen_min;

   always@(posedge clk)
     if ((rx_pkt_state == PREAMBLE) && rx_lock)
       rx_exp_pktlen <= cfg_rx_pktlen_min;
     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_tlast)
       rx_exp_pktlen <= next_rx_exp_pktlen;
     else
       rx_exp_pktlen <= rx_exp_pktlen;

   // Slice Index
   always@(posedge clk)
     if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_tlast)
       rx_slice_idx <= 0;
     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid)
       rx_slice_idx <= rx_slice_idx + 1;
     else
       rx_slice_idx <= rx_slice_idx;

   assign rx_exp_tlast = (rx_pkt_state == PKT_DATA) && (rx_slice_idx == (rx_exp_pktlen - 1));

   // TKeep
   // Keep incrementing
//TODO: TEMP   always_ff @(negedge rst_n or posedge clk)
//TODO: TEMP     if (!rst_n) rx_exp_tkeep[TKEEP_WIDTH-1:0] <= ({TKEEP_WIDTH{1'b0}});
//TODO: TEMP     else if (rx_pkt_state == IDLE)
//TODO: TEMP       rx_exp_tkeep[TKEEP_WIDTH-1:0] <= ({{(TKEEP_WIDTH-1){1'b0}}, 1'b1});
//TODO: TEMP     else if ((rx_pkt_state == PKT_DATA) && rx_tvalid && rx_tlast)
//TODO: TEMP       rx_exp_tkeep[TKEEP_WIDTH-1:0] <= rx_exp_tkeep[TKEEP_WIDTH-1:0] + 1;
//TODO: TEMP     else
//TODO: TEMP       rx_exp_tkeep[TKEEP_WIDTH-1:0] <= rx_exp_tkeep[TKEEP_WIDTH-1:0];

   assign rx_exp_tkeep = {TKEEP_WIDTH{1'b1}};

   // Packet length error when
   // 1. Number of slices are different between expected and incoming
   // 2. For the last slice, the tkeep is different
//   assign rx_pktlen_err = cfg_rx_en && ~cfg_rx_pktlen_chk_dis && (rx_pkt_state == PKT_DATA) &&
//                          rx_tvalid && (rx_exp_tlast || rx_tlast) && ((rx_exp_tlast  != rx_tlast) ||
//                                                                      ((rx_exp_pktlen - 1) != rx_slice_idx) ||
//                                                                      (rx_exp_tkeep  != rx_tkeep));
   assign rx_pktlen_err = 1'b0;

   // Rx lock error
   // When we get packets that are multiple slices or tkeep != 3 when not locked
   assign rx_lock_err = 1'b0; // ~rx_lock & rx_tvalid & (~rx_tlast || (rx_tkeep != PREAMBLE_TKEEP));

   // Last Rx data
   always@(posedge clk)
     if (clr_last_rx_data_0)
       {last_rx_data_1, last_rx_data_0} <= 64'd0;
     else if (rx_tvalid)
       {last_rx_data_1, last_rx_data_0} <= rx_tdata[63:0];
     else
       {last_rx_data_1, last_rx_data_0} <= {last_rx_data_1, last_rx_data_0};

   // Debug - add a RAM to capture the last 4 data
if (DBG_RAM_PRESENT) begin //{
   logic ram_wr;
   logic [1+1+TKEEP_WIDTH+DATA_WIDTH-1:0] ram_wdata;
   logic [4:0]                            ram_waddr = 0;
   logic [4:0]                            ram_raddr;
   logic                                  ram_phase = 0;
   logic [1+1+TKEEP_WIDTH+DATA_WIDTH-1:0] ram_rdata;
   logic [1+1+TKEEP_WIDTH+DATA_WIDTH-1:0] ram_rdata_q = 0;
   logic [30+1+1+TKEEP_WIDTH+DATA_WIDTH-1:0] ram_rdata_adj;
   logic [4:0]                               ram_waddr_p1;

   assign ram_wr = rx_tvalid;
   assign ram_wdata = {ram_phase, rx_tlast, rx_tkeep, rx_tdata};

   assign ram_waddr_p1 = ram_waddr + 5'd1;

   always @(posedge clk)
     if (!sync_rst_n) begin
	ram_waddr <= '0;
        ram_phase <= '0;
     end else begin
        ram_waddr <= rx_tvalid ? ram_waddr_p1 : ram_waddr;
        ram_phase <= (rx_tvalid && (ram_waddr_p1 == 0)) ? ~ram_phase : ram_phase;
     end

   bram_2rw #(.WIDTH(1+1+TKEEP_WIDTH+DATA_WIDTH), .DEPTH(32), .ADDR_WIDTH(5))
   RX_DATA_RAM (.clk   (clk),
                .wea   (ram_wr),
                .ena   (1'b1),
                .addra (ram_waddr),
                .da    (ram_wdata),
                .qa    (),

                .web   (1'b0),
                .enb   (1'b1),
                .addrb (ram_raddr),
                .db    ({(1+1+TKEEP_WIDTH+DATA_WIDTH){1'b0}}),
                .qb    (ram_rdata)
                );

   assign ram_raddr = cfg_rx_dbg_ram_index[9:5];
   always @(posedge clk)
     ram_rdata_q <= ram_rdata;

   assign ram_rdata_adj = {30'd0, ram_rdata_q};

   always  @(posedge clk)
     for (int i = 0; i < 19; i++)
       if (i == cfg_rx_dbg_ram_index[4:0])
         cfg_rx_dbg_ram_rdata[31:0] <= ram_rdata_adj[i*32+:32];
end // if (DBG_RAM_PRESENT) }

end // if (TX_ONLY == 0)


   function [31:0] crc32(input [31:0] in_crc, input bit data_in);

      // got this code from crc32_w_seed.pl
      crc32[ 0] = data_in ^ in_crc[05] ^ in_crc[08] ^ in_crc[09] ^ in_crc[11] ^ in_crc[15] ^ in_crc[23] ^ in_crc[24] ^ in_crc[25] ^ in_crc[27] ^ in_crc[28] ^ in_crc[29] ^ in_crc[30] ^ in_crc[31]                                           ;
      crc32[ 1] = data_in ^ in_crc[00] ^ in_crc[05] ^ in_crc[06] ^ in_crc[08] ^ in_crc[10] ^ in_crc[11] ^ in_crc[12] ^ in_crc[15] ^ in_crc[16] ^ in_crc[23] ^ in_crc[26] ^ in_crc[27]                                                        ;
      crc32[ 2] = data_in ^ in_crc[00] ^ in_crc[01] ^ in_crc[05] ^ in_crc[06] ^ in_crc[07] ^ in_crc[08] ^ in_crc[12] ^ in_crc[13] ^ in_crc[15] ^ in_crc[16] ^ in_crc[17] ^ in_crc[23] ^ in_crc[25] ^ in_crc[29] ^ in_crc[30] ^ in_crc[31]    ;
      crc32[ 3] = in_crc[00] ^ in_crc[01] ^ in_crc[02] ^ in_crc[06] ^ in_crc[07] ^ in_crc[08] ^ in_crc[09] ^ in_crc[13] ^ in_crc[14] ^ in_crc[16] ^ in_crc[17] ^ in_crc[18] ^ in_crc[24] ^ in_crc[26] ^ in_crc[30] ^ in_crc[31]              ;
      crc32[ 4] = data_in ^ in_crc[01] ^ in_crc[02] ^ in_crc[03] ^ in_crc[05] ^ in_crc[07] ^ in_crc[10] ^ in_crc[11] ^ in_crc[14] ^ in_crc[17] ^ in_crc[18] ^ in_crc[19] ^ in_crc[23] ^ in_crc[24] ^ in_crc[28] ^ in_crc[29] ^ in_crc[30]    ;
      crc32[ 5] = data_in ^ in_crc[00] ^ in_crc[02] ^ in_crc[03] ^ in_crc[04] ^ in_crc[05] ^ in_crc[06] ^ in_crc[09] ^ in_crc[12] ^ in_crc[18] ^ in_crc[19] ^ in_crc[20] ^ in_crc[23] ^ in_crc[27] ^ in_crc[28]                              ;
      crc32[ 6] = in_crc[00] ^ in_crc[01] ^ in_crc[03] ^ in_crc[04] ^ in_crc[05] ^ in_crc[06] ^ in_crc[07] ^ in_crc[10] ^ in_crc[13] ^ in_crc[19] ^ in_crc[20] ^ in_crc[21] ^ in_crc[24] ^ in_crc[28] ^ in_crc[29]                           ;
      crc32[ 7] = data_in ^ in_crc[01] ^ in_crc[02] ^ in_crc[04] ^ in_crc[06] ^ in_crc[07] ^ in_crc[09] ^ in_crc[14] ^ in_crc[15] ^ in_crc[20] ^ in_crc[21] ^ in_crc[22] ^ in_crc[23] ^ in_crc[24] ^ in_crc[27] ^ in_crc[28] ^ in_crc[31]    ;
      crc32[ 8] = data_in ^ in_crc[00] ^ in_crc[02] ^ in_crc[03] ^ in_crc[07] ^ in_crc[09] ^ in_crc[10] ^ in_crc[11] ^ in_crc[16] ^ in_crc[21] ^ in_crc[22] ^ in_crc[27] ^ in_crc[30] ^ in_crc[31]                                           ;
      crc32[ 9] = in_crc[00] ^ in_crc[01] ^ in_crc[03] ^ in_crc[04] ^ in_crc[08] ^ in_crc[10] ^ in_crc[11] ^ in_crc[12] ^ in_crc[17] ^ in_crc[22] ^ in_crc[23] ^ in_crc[28] ^ in_crc[31]                                                     ;
      crc32[10] = data_in ^ in_crc[01] ^ in_crc[02] ^ in_crc[04] ^ in_crc[08] ^ in_crc[12] ^ in_crc[13] ^ in_crc[15] ^ in_crc[18] ^ in_crc[25] ^ in_crc[27] ^ in_crc[28] ^ in_crc[30] ^ in_crc[31]                                           ;
      crc32[11] = data_in ^ in_crc[00] ^ in_crc[02] ^ in_crc[03] ^ in_crc[08] ^ in_crc[11] ^ in_crc[13] ^ in_crc[14] ^ in_crc[15] ^ in_crc[16] ^ in_crc[19] ^ in_crc[23] ^ in_crc[24] ^ in_crc[25] ^ in_crc[26] ^ in_crc[27] ^ in_crc[30]    ;
      crc32[12] = data_in ^ in_crc[00] ^ in_crc[01] ^ in_crc[03] ^ in_crc[04] ^ in_crc[05] ^ in_crc[08] ^ in_crc[11] ^ in_crc[12] ^ in_crc[14] ^ in_crc[16] ^ in_crc[17] ^ in_crc[20] ^ in_crc[23] ^ in_crc[26] ^ in_crc[29] ^ in_crc[30]    ;
      crc32[13] = in_crc[00] ^ in_crc[01] ^ in_crc[02] ^ in_crc[04] ^ in_crc[05] ^ in_crc[06] ^ in_crc[09] ^ in_crc[12] ^ in_crc[13] ^ in_crc[15] ^ in_crc[17] ^ in_crc[18] ^ in_crc[21] ^ in_crc[24] ^ in_crc[27] ^ in_crc[30] ^ in_crc[31] ;
      crc32[14] = in_crc[01] ^ in_crc[02] ^ in_crc[03] ^ in_crc[05] ^ in_crc[06] ^ in_crc[07] ^ in_crc[10] ^ in_crc[13] ^ in_crc[14] ^ in_crc[16] ^ in_crc[18] ^ in_crc[19] ^ in_crc[22] ^ in_crc[25] ^ in_crc[28] ^ in_crc[31]              ;
      crc32[15] = in_crc[02] ^ in_crc[03] ^ in_crc[04] ^ in_crc[06] ^ in_crc[07] ^ in_crc[08] ^ in_crc[11] ^ in_crc[14] ^ in_crc[15] ^ in_crc[17] ^ in_crc[19] ^ in_crc[20] ^ in_crc[23] ^ in_crc[26] ^ in_crc[29]                           ;
      crc32[16] = data_in ^ in_crc[03] ^ in_crc[04] ^ in_crc[07] ^ in_crc[11] ^ in_crc[12] ^ in_crc[16] ^ in_crc[18] ^ in_crc[20] ^ in_crc[21] ^ in_crc[23] ^ in_crc[25] ^ in_crc[28] ^ in_crc[29] ^ in_crc[31]                              ;
      crc32[17] = in_crc[00] ^ in_crc[04] ^ in_crc[05] ^ in_crc[08] ^ in_crc[12] ^ in_crc[13] ^ in_crc[17] ^ in_crc[19] ^ in_crc[21] ^ in_crc[22] ^ in_crc[24] ^ in_crc[26] ^ in_crc[29] ^ in_crc[30]                                        ;
      crc32[18] = in_crc[01] ^ in_crc[05] ^ in_crc[06] ^ in_crc[09] ^ in_crc[13] ^ in_crc[14] ^ in_crc[18] ^ in_crc[20] ^ in_crc[22] ^ in_crc[23] ^ in_crc[25] ^ in_crc[27] ^ in_crc[30] ^ in_crc[31]                                        ;
      crc32[19] = in_crc[02] ^ in_crc[06] ^ in_crc[07] ^ in_crc[10] ^ in_crc[14] ^ in_crc[15] ^ in_crc[19] ^ in_crc[21] ^ in_crc[23] ^ in_crc[24] ^ in_crc[26] ^ in_crc[28] ^ in_crc[31]                                                     ;
      crc32[20] = in_crc[03] ^ in_crc[07] ^ in_crc[08] ^ in_crc[11] ^ in_crc[15] ^ in_crc[16] ^ in_crc[20] ^ in_crc[22] ^ in_crc[24] ^ in_crc[25] ^ in_crc[27] ^ in_crc[29]                                                                  ;
      crc32[21] = in_crc[04] ^ in_crc[08] ^ in_crc[09] ^ in_crc[12] ^ in_crc[16] ^ in_crc[17] ^ in_crc[21] ^ in_crc[23] ^ in_crc[25] ^ in_crc[26] ^ in_crc[28] ^ in_crc[30]                                                                  ;
      crc32[22] = data_in ^ in_crc[08] ^ in_crc[10] ^ in_crc[11] ^ in_crc[13] ^ in_crc[15] ^ in_crc[17] ^ in_crc[18] ^ in_crc[22] ^ in_crc[23] ^ in_crc[25] ^ in_crc[26] ^ in_crc[28] ^ in_crc[30]                                           ;
      crc32[23] = data_in ^ in_crc[00] ^ in_crc[05] ^ in_crc[08] ^ in_crc[12] ^ in_crc[14] ^ in_crc[15] ^ in_crc[16] ^ in_crc[18] ^ in_crc[19] ^ in_crc[25] ^ in_crc[26] ^ in_crc[28] ^ in_crc[30]                                           ;
      crc32[24] = in_crc[00] ^ in_crc[01] ^ in_crc[06] ^ in_crc[09] ^ in_crc[13] ^ in_crc[15] ^ in_crc[16] ^ in_crc[17] ^ in_crc[19] ^ in_crc[20] ^ in_crc[26] ^ in_crc[27] ^ in_crc[29] ^ in_crc[31]                                        ;
      crc32[25] = in_crc[01] ^ in_crc[02] ^ in_crc[07] ^ in_crc[10] ^ in_crc[14] ^ in_crc[16] ^ in_crc[17] ^ in_crc[18] ^ in_crc[20] ^ in_crc[21] ^ in_crc[27] ^ in_crc[28] ^ in_crc[30]                                                     ;
      crc32[26] = data_in ^ in_crc[02] ^ in_crc[03] ^ in_crc[05] ^ in_crc[09] ^ in_crc[17] ^ in_crc[18] ^ in_crc[19] ^ in_crc[21] ^ in_crc[22] ^ in_crc[23] ^ in_crc[24] ^ in_crc[25] ^ in_crc[27] ^ in_crc[30]                              ;
      crc32[27] = in_crc[00] ^ in_crc[03] ^ in_crc[04] ^ in_crc[06] ^ in_crc[10] ^ in_crc[18] ^ in_crc[19] ^ in_crc[20] ^ in_crc[22] ^ in_crc[23] ^ in_crc[24] ^ in_crc[25] ^ in_crc[26] ^ in_crc[28] ^ in_crc[31]                           ;
      crc32[28] = in_crc[01] ^ in_crc[04] ^ in_crc[05] ^ in_crc[07] ^ in_crc[11] ^ in_crc[19] ^ in_crc[20] ^ in_crc[21] ^ in_crc[23] ^ in_crc[24] ^ in_crc[25] ^ in_crc[26] ^ in_crc[27] ^ in_crc[29]                                        ;
      crc32[29] = in_crc[02] ^ in_crc[05] ^ in_crc[06] ^ in_crc[08] ^ in_crc[12] ^ in_crc[20] ^ in_crc[21] ^ in_crc[22] ^ in_crc[24] ^ in_crc[25] ^ in_crc[26] ^ in_crc[27] ^ in_crc[28] ^ in_crc[30]                                        ;
      crc32[30] = in_crc[03] ^ in_crc[06] ^ in_crc[07] ^ in_crc[09] ^ in_crc[13] ^ in_crc[21] ^ in_crc[22] ^ in_crc[23] ^ in_crc[25] ^ in_crc[26] ^ in_crc[27] ^ in_crc[28] ^ in_crc[29] ^ in_crc[31]                                        ;
      crc32[31] = in_crc[04] ^ in_crc[07] ^ in_crc[08] ^ in_crc[10] ^ in_crc[14] ^ in_crc[22] ^ in_crc[23] ^ in_crc[24] ^ in_crc[26] ^ in_crc[27] ^ in_crc[28] ^ in_crc[29] ^ in_crc[30]                                                     ;
   endfunction // crc32


endmodule // cl_pkt_tst

