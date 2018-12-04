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

//Registers
//
// 0x00-0xFC - CL_PKT_TST (TX)
// 0x180: RX Control
//    0 - loopback mode
//    1 - Timer go
//    2 - Timer start on first data
//    3 - Timer stop on number of data phases
//    4 - INP Backpressure enable
//    5 - RX mismatch check enable
//
// 0x184: RX Rst
//    0 - Reset the RX FIFO pointers
//
// 0x18c:  INP FIFO pointers
//    15:0 - INP FIFO Read Pointer
//    31:16 - INP FIFO Write Pointer
//
// 0x190-0x1E0: INP Data {last, user[63:0], keep[63:0], data[511:0]}
//
//
// 0x1E8: Timer[31:0]
// 0x1EC: Timer[63:32]
//
// 0x1F0: RX data phases[31:0]
// 0x1F4: RX data phases[63:32]
//
// 0x1F8: Num pkts[31:0]
// 0x1Fc: Num pkts[63:32]
//
// 0x200: Stop RX data phases[31:0]
// 0x204: Stop RX data phases[63:32]


module cl_sde_srm (

   input clk,
   input rst_n,

   input[11:0] cfg_srm_addr,
   input cfg_srm_wr,
   input cfg_srm_rd,
   input[31:0] cfg_srm_wdata,

   output logic srm_cfg_ack,
   output logic[31:0] srm_cfg_rdata,

   input ins_valid,
   input[511:0] ins_data,
   input[63:0] ins_keep,
   input[63:0] ins_user,
   input ins_last,
   output logic ins_ready,

   output logic ots_valid,
   output logic[511:0] ots_data,
   output logic[63:0] ots_keep,
   output logic[63:0] ots_user,
   output logic ots_last,
   input ots_ready
   );

localparam INP_PTR_WIDTH = 9;
localparam INP_FIFO_SIZE = 2 << (INP_PTR_WIDTH-1);
localparam INP_FIFO_WIDTH = 1+64+64+512;

//-----------------------
// Internal signals
//-----------------------
logic cfg_lb_mode;
logic cfg_mismatch_chk_en;
logic cfg_inp_ram_rd;
logic[63:0] cfg_inp_stop_phases;

logic cfg_timer_go;                       //Enable the timer
logic cfg_timer_go_q;
logic cfg_timer_start_first_data;         //Start the timer on the first data received
logic cfg_timer_stop_num_phases;          //Stop the timer after a certain number of phases
logic cfg_inp_fifo_bp_en;                 //Enable INP FIFO to backpressure INS interface

logic cfg_inp_ptr_reset;                  //Reset INP pointers

logic tst_cfg_ack;
logic[31:0] tst_cfg_rdata;

logic tst_valid;
logic[511:0] tst_data;
logic tst_last;
logic[63:0] tst_keep;


// End internal signals
//----------------------------

//---------------------------------------
// Input FIFO
//---------------------------------------

logic[INP_PTR_WIDTH:0] inp_wr_ptr;
logic[INP_PTR_WIDTH:0] inp_rd_ptr;
logic[INP_PTR_WIDTH:0] inp_ptr_diff;
logic inp_full;
logic inp_empty;
logic inp_wr;

logic[INP_PTR_WIDTH-1:0] inp_ram_rd_addr;

logic inp_ram_pop;
logic[INP_FIFO_WIDTH-1:0] inp_ram_rdata;

logic inp_lb_valid;              //Loopback valid
logic[511:0] inp_lb_data;
logic[63:0] inp_lb_keep;
logic[63:0] inp_lb_user;
logic inp_lb_last;

logic inp_lb_pop;                //Pop and send to OTS interface

assign inp_ptr_diff = (inp_wr_ptr - inp_rd_ptr);
assign inp_full = inp_ptr_diff==INP_FIFO_SIZE;

assign inp_wr = ins_valid && ins_ready;

assign inp_empty = inp_ptr_diff==0;


always @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      inp_wr_ptr <= 0;
      inp_rd_ptr <= 0;
   end
   else if (cfg_inp_ptr_reset)
   begin
      inp_wr_ptr <= 0;
      inp_rd_ptr <= 0;
   end
   else
   begin
      inp_wr_ptr <= (ins_valid && ins_ready)? inp_wr_ptr + 1: inp_wr_ptr;
      inp_rd_ptr <= (cfg_lb_mode && inp_ram_pop)?                             inp_rd_ptr + 1:
                     (!cfg_lb_mode && cfg_srm_rd && (cfg_srm_addr==12'h1e0))?  inp_rd_ptr + 1:
                     (!cfg_lb_mode && cfg_srm_wr && (cfg_srm_addr==12'h18c))?  cfg_srm_wdata[15:0]:
                                                                              inp_rd_ptr;
   end

assign inp_ram_rd_addr = inp_rd_ptr;

//De-assert read if FIFO fills and in lb_mode or enabled to backpressure
assign ins_ready = !((cfg_lb_mode || cfg_inp_fifo_bp_en) && inp_full);


//Instantiate the RAM
bram_1w1r #(.WIDTH(INP_FIFO_WIDTH), .ADDR_WIDTH(INP_PTR_WIDTH), .DEPTH(INP_FIFO_SIZE), .PIPELINE(1)) INP_FIFO_RAM (
   .clk(clk),
   .wea(inp_wr),
   .ena(inp_wr),
   .addra(inp_wr_ptr[INP_PTR_WIDTH-1:0]),
   .da({ins_last, ins_user, ins_keep, ins_data}),

   .enb(1'b1),
   .addrb(inp_ram_rd_addr),
   .qb(inp_ram_rdata)
   );


//Instantiate FT_FIFO
ft_fifo_p #(.FIFO_WIDTH(INP_FIFO_WIDTH)) INP_FT_FIFO (
   .clk(clk),
   .rst_n(rst_n),

   .sync_rst_n(~cfg_inp_ptr_reset),

   .ram_fifo_empty(inp_empty),
   .ram_fifo_data(inp_ram_rdata),
   .ft_pop(inp_lb_pop),

   .ram_pop(inp_ram_pop),

   .ft_valid(inp_lb_valid),
   .ft_data({inp_lb_last, inp_lb_user, inp_lb_keep, inp_lb_data})
   );

//Loopback read
assign inp_lb_pop = cfg_lb_mode && inp_lb_valid && !cfg_inp_ram_rd && ots_ready;

//Configuration accesses to CL_PKT_TST
logic cfg_tst_wr;
logic cfg_tst_rd;

logic cfg_tst_dec;

assign cfg_tst_dec = (cfg_srm_addr<12'h100);

assign cfg_tst_wr = cfg_srm_wr && cfg_tst_dec;
assign cfg_tst_rd = cfg_srm_rd && cfg_tst_dec;

//--------------------------
// INP Configuration
//--------------------------
logic cfg_inp_ram_rd_q;
logic cfg_inp_ram_rd_qq;         //Note we no longer need 2 clocks because the read pointer is always correct.  Left
                                 // because we do need 1 clock to flop the ram offset.

logic[63:0] inp_phase_count = 0;
logic[63:0] inp_pkt_count = 0;
logic[63:0] inp_timer = 0;
logic inp_timer_en = 0;

logic inp_cfg_ack = 0;
logic[31:0] inp_cfg_rdata = 0;

assign cfg_inp_ram_rd = cfg_srm_rd && (cfg_srm_addr>=12'h190) && (cfg_srm_addr<=12'h1e0);

always @(posedge clk)
begin
   cfg_inp_ram_rd_q <= cfg_inp_ram_rd;
   cfg_inp_ram_rd_qq <= cfg_inp_ram_rd_q;
end

//Registers
always @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      cfg_lb_mode <= 1;
      cfg_timer_go <= 0;
      cfg_timer_start_first_data <= 0;
      cfg_timer_stop_num_phases <= 0;
      cfg_inp_fifo_bp_en <= 0;

      cfg_inp_stop_phases <= 0;
      cfg_mismatch_chk_en <= 0;
   end
   else if (cfg_srm_wr && (cfg_srm_addr==12'h180))
   begin
      cfg_lb_mode <= cfg_srm_wdata[0];
      cfg_timer_go <= cfg_srm_wdata[1];
      cfg_timer_start_first_data <= cfg_srm_wdata[2];
      cfg_timer_stop_num_phases <= cfg_srm_wdata[3];
      cfg_inp_fifo_bp_en <= cfg_srm_wdata[4];
      cfg_mismatch_chk_en <= cfg_srm_wdata[5];
   end
   else if (cfg_srm_wr && (cfg_srm_addr==12'h200))
      cfg_inp_stop_phases[31:0] <= cfg_srm_wdata;
   else if (cfg_srm_wr && (cfg_srm_addr==12'h204))
      cfg_inp_stop_phases[63:32] <= cfg_srm_wdata;

//Phase/Pkt counter/timer
always @(posedge clk)
begin
   if (cfg_srm_wr && ((cfg_srm_addr==12'h1f0) || (cfg_srm_addr==12'h1f4)))
      inp_phase_count <= 0;
   else if (ins_valid && ins_ready)
      inp_phase_count <= inp_phase_count + 1;

   if (cfg_srm_wr && ((cfg_srm_addr==12'h1f8) || (cfg_srm_addr==12'h1fc)))
      inp_pkt_count <= 0;
   else if (ins_valid && ins_ready && ins_last)
      inp_pkt_count <= inp_pkt_count + 1;

   if (cfg_srm_wr && ((cfg_srm_addr==12'h1e8) || (cfg_srm_addr==12'h1ec)))
      inp_timer <= 0;
   else if (inp_timer_en)
      inp_timer <= inp_timer + 1;
end

always @(posedge clk)
   cfg_timer_go_q <= cfg_timer_go;

//Timer enable
always @(posedge clk)
   if ((cfg_timer_stop_num_phases && (inp_phase_count >= cfg_inp_stop_phases)) || (cfg_timer_go_q && !cfg_timer_go))
      inp_timer_en <= 0;
   else if (cfg_timer_go || (cfg_timer_start_first_data && ins_valid && ins_ready))
      inp_timer_en <= 1;

logic[7:0] cfg_ram_offset;
always @(posedge clk)
   if (cfg_srm_rd)
      cfg_ram_offset <= cfg_srm_addr - 12'h190;

assign cfg_inp_ptr_reset = cfg_srm_wr && (cfg_srm_addr==12'h184) && cfg_srm_wdata[0];

//Read ack/rdata
always @(posedge clk)
begin
   inp_cfg_ack <= ((cfg_srm_wr || cfg_srm_rd) && !cfg_tst_dec && !cfg_inp_ram_rd) || cfg_inp_ram_rd_qq;

   inp_cfg_rdata <=  (cfg_srm_addr==12'h180)?    {inp_timer_en, 22'h0, cfg_mismatch_chk_en, cfg_inp_fifo_bp_en, cfg_timer_stop_num_phases, cfg_timer_start_first_data, cfg_timer_go, cfg_lb_mode}:
                     (cfg_srm_addr==12'h18c)?    (inp_wr_ptr << 16) | inp_rd_ptr:
                     (cfg_srm_addr==12'h200)?    cfg_inp_stop_phases[31:0]:
                     (cfg_srm_addr==12'h204)?    cfg_inp_stop_phases[63:32]:
                     (cfg_srm_addr==12'h1e8)?    inp_timer[31:0]:
                     (cfg_srm_addr==12'h1ec)?    inp_timer[63:32]:
                     (cfg_srm_addr==12'h1f0)?    inp_phase_count[31:0]:
                     (cfg_srm_addr==12'h1f4)?    inp_phase_count[63:32]:
                     (cfg_srm_addr==12'h1f8)?    inp_pkt_count[31:0]:
                     (cfg_srm_addr==12'h1fc)?    inp_pkt_count[63:32]:
                                                inp_ram_rdata  >> (32 * cfg_ram_offset[6:2]);
end

//Final mux of configuration
assign srm_cfg_ack = inp_cfg_ack || tst_cfg_ack;
assign srm_cfg_rdata = (tst_cfg_ack)? tst_cfg_rdata: inp_cfg_rdata;



cl_pkt_tst #(.DATA_WIDTH(512), .TKEEP_WIDTH(64), .TX_ONLY(0), .DBG_RAM_PRESENT(0)) CL_PKT_TST (
   .clk(clk),
   .rst_n(rst_n),

   .cfg_addr({20'h0, cfg_srm_addr}),
   .cfg_wdata(cfg_srm_wdata),
   .cfg_wr(cfg_tst_wr),
   .cfg_rd(cfg_tst_rd),
   .tst_cfg_ack(tst_cfg_ack),
   .tst_cfg_rdata(tst_cfg_rdata),

   .channel_ready(1'b1),

   .axis_tx_tvalid(tst_valid),
   .axis_tx_tdata(tst_data),
   .axis_tx_tlast(tst_last),
   .axis_tx_tkeep(tst_keep),
   .axis_tx_tready(ots_ready & ~cfg_lb_mode),

   .axis_rx_tvalid(ins_valid),
   .axis_rx_tdata(ins_data),
   .axis_rx_tlast(ins_last),
   .axis_rx_tkeep(ins_keep),
   .axis_rx_tready()
   );


//Mux the LB/TST to output
assign ots_valid = (cfg_lb_mode)? inp_lb_valid: tst_valid;
assign ots_data = (cfg_lb_mode)? inp_lb_data: tst_data;
assign ots_last = (cfg_lb_mode)? inp_lb_last: tst_last;
assign ots_keep = (cfg_lb_mode)? inp_lb_keep: tst_keep;
assign ots_user = (cfg_lb_mode)? inp_lb_user: 0;

endmodule

