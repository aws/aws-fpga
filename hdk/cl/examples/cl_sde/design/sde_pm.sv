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

// PCIM Interface

module sde_pm #(parameter PCIM_DATA_WIDTH = 512,
                parameter PCIM_ID_WIDTH = 3,
                parameter PCIM_LEN_WIDTH = 8,
                parameter PCIM_ADDR_WIDTH = 64,
                parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),
                
                // IDs for Write Channels
                parameter C2H_PCIM_DM_AWID = 0,
                parameter C2H_PCIM_WB_AWID = 1,
                parameter H2C_PCIM_WB_AWID = 2,

                // IDs for Read Channels
                parameter C2H_PCIM_DESC_ARID = 0,
                parameter H2C_PCIM_DESC_ARID = 1,
                parameter H2C_PCIM_DM_ARID = 2,

                // These are internal FIFOs - Dont change unless absolutely required
                parameter PM_WR_WINNER_FIFO_DEPTH = 32                
                
                )
   ( 
     input                                   clk,
     input                                   rst_n,

     // PCIS to PM Config Interface
     input                                   pm_ps_cfg_wr_req,
     input                                   pm_ps_cfg_rd_req,
     input [15:0]                            pm_ps_cfg_addr,
     input [31:0]                            pm_ps_cfg_wdata,
     output                                  pm_ps_cfg_ack,
     output [31:0]                           pm_ps_cfg_rdata,
    

     // PCIM Interface
     output logic                            pcim_awvalid,
     output logic [PCIM_ID_WIDTH-1:0]        pcim_awid,
     output logic [PCIM_ADDR_WIDTH-1:0]      pcim_awaddr,
     output logic [PCIM_LEN_WIDTH-1:0]       pcim_awlen,
     output logic [2:0]                      pcim_awsize,
     input                                   pcim_awready,
   
     output logic                            pcim_wvalid,
     output logic [PCIM_DATA_WIDTH-1:0]      pcim_wdata,
     output logic [(PCIM_DATA_WIDTH>>3)-1:0] pcim_wstrb,
     output logic                            pcim_wlast,
     input                                   pcim_wready,
   
     input logic                             pcim_bvalid,
     input logic [PCIM_ID_WIDTH-1:0]         pcim_bid,
     input logic [1:0]                       pcim_bresp,
     output logic                            pcim_bready,
  
     output logic                            pcim_arvalid,
     output logic [PCIM_ID_WIDTH-1:0]        pcim_arid,
     output logic [PCIM_ADDR_WIDTH-1:0]      pcim_araddr,
     output logic [PCIM_LEN_WIDTH-1:0]       pcim_arlen,
     output logic [2:0]                      pcim_arsize,
     input                                   pcim_arready,
   
     input                                   pcim_rvalid,
     input [PCIM_ID_WIDTH-1:0]               pcim_rid,
     input [PCIM_DATA_WIDTH-1:0]             pcim_rdata,
     input [1:0]                             pcim_rresp,
     input                                   pcim_rlast,
     output logic                            pcim_rready,


     // C2H Interfaces

     // C2H Descriptor to PCIM Interface
     // Read Address to PCIM
     input                                   c2h_desc_pm_arvalid,
     input [PCIM_ADDR_WIDTH-1:0]             c2h_desc_pm_araddr,
     input [PCIM_LEN_WIDTH-1:0]              c2h_desc_pm_arlen,
     output logic                            c2h_pm_desc_arready,

     // Read Data from PCIM
     output logic                            c2h_pm_desc_rvalid,
     output logic [1:0]                      c2h_pm_desc_rresp,
     output logic [PCIM_DATA_WIDTH-1:0]      c2h_pm_desc_rdata,
     output logic                            c2h_pm_desc_rlast,
     input                                   c2h_desc_pm_rready,

     // C2H Data Mover to PCIM Interface
     // Write Address to PCIM
     input                                   c2h_dm_pm_awvalid,
     input [PCIM_ADDR_WIDTH-1:0]             c2h_dm_pm_awaddr,
     input [PCIM_LEN_WIDTH-1:0]              c2h_dm_pm_awlen,
     input [PCIM_ID_WIDTH-1:0]               c2h_dm_pm_awid,
     output logic                            c2h_pm_dm_awready,
    
     // Write Data to PCIM
     input                                   c2h_dm_pm_wvalid,
     input [PCIM_DATA_WIDTH-1:0]             c2h_dm_pm_wdata,
     input [(PCIM_DATA_WIDTH>>3)-1:0]        c2h_dm_pm_wstrb,
     input                                   c2h_dm_pm_wlast,
     output logic                            c2h_pm_dm_wready,

     // Bresp from PCIM
     output logic                            c2h_pm_dm_bvalid,
     output logic [1:0]                      c2h_pm_dm_bresp,
     input                                   c2h_dm_pm_bready,

     // C2H Write-Back Block to PCIM Interface
     // Write Address to PCIM
     input                                   c2h_wb_pm_awvalid,
     input [PCIM_ADDR_WIDTH-1:0]             c2h_wb_pm_awaddr,
     input [PCIM_LEN_WIDTH-1:0]              c2h_wb_pm_awlen,
     input [PCIM_ID_WIDTH-1:0]               c2h_wb_pm_awid,
     output logic                            c2h_pm_wb_awready,
    
    // Write Data to PCIM
     input                                   c2h_wb_pm_wvalid,
     input [PCIM_DATA_WIDTH-1:0]             c2h_wb_pm_wdata,
     input [(PCIM_DATA_WIDTH>>3)-1:0]        c2h_wb_pm_wstrb,
     input                                   c2h_wb_pm_wlast,
     output logic                            c2h_pm_wb_wready,

    // Bresp from PCIM
     output logic                            c2h_pm_wb_bvalid,
     output logic [1:0]                      c2h_pm_wb_bresp,
     input                                   c2h_wb_pm_bready,


     // H2C Descriptor to PCIM Interface
     // Read Address to PCIM
     input                                   h2c_desc_pm_arvalid,
     input [PCIM_ADDR_WIDTH-1:0]             h2c_desc_pm_araddr,
     input [PCIM_LEN_WIDTH-1:0]              h2c_desc_pm_arlen,
     output logic                            h2c_pm_desc_arready,

     // Read Data from PCIM
     output logic                            h2c_pm_desc_rvalid,
     output logic [1:0]                      h2c_pm_desc_rresp,
     output logic [PCIM_DATA_WIDTH-1:0]      h2c_pm_desc_rdata,
     output logic                            h2c_pm_desc_rlast,
     input                                   h2c_desc_pm_rready,
     
     // H2C Data Mover to PCIM Interface
     // Read Address to PCIM
     input                                   h2c_dm_pm_arvalid,
     input [PCIM_ADDR_WIDTH-1:0]             h2c_dm_pm_araddr,
     input [PCIM_LEN_WIDTH-1:0]              h2c_dm_pm_arlen,
     output logic                            h2c_pm_dm_arready,

     // Read Data from PCIM
     output logic                            h2c_pm_dm_rvalid,
     output logic [1:0]                      h2c_pm_dm_rresp,
     output logic [PCIM_DATA_WIDTH-1:0]      h2c_pm_dm_rdata,
     output logic                            h2c_pm_dm_rlast,
     input                                   h2c_dm_pm_rready,

     
     // H2C Write-Back Block to PCIM Interface
     // Write Address to PCIM
     input                                   h2c_wb_pm_awvalid,
     input [PCIM_ADDR_WIDTH-1:0]             h2c_wb_pm_awaddr,
     input [PCIM_LEN_WIDTH-1:0]              h2c_wb_pm_awlen,
     input [PCIM_ID_WIDTH-1:0]               h2c_wb_pm_awid,
     output logic                            h2c_pm_wb_awready,
    
    // Write Data to PCIM
     input                                   h2c_wb_pm_wvalid,
     input [PCIM_DATA_WIDTH-1:0]             h2c_wb_pm_wdata,
     input [(PCIM_DATA_WIDTH>>3)-1:0]        h2c_wb_pm_wstrb,
     input                                   h2c_wb_pm_wlast,
     output logic                            h2c_pm_wb_wready,

    // Bresp from PCIM
     output logic                            h2c_pm_wb_bvalid,
     output logic [1:0]                      h2c_pm_wb_bresp,
     input                                   h2c_wb_pm_bready
     
     );

   localparam PCIM_AXSIZE = PCIM_ADDR_BYTE_IDX_WIDTH;
   localparam WR_WINNER_WIDTH = 2;
   

   logic [WR_WINNER_WIDTH-1:0]               wr_arb_out;
   logic                                     wr_do_arb;
   logic [WR_WINNER_WIDTH-1:0]               wr_winner;
   logic                                     aw_pipe_stall;
   logic                                     pm_wr_winner_ff_full;

   // Round Robin arbiter
   rr_arb #(.WINNER_WIDTH(WR_WINNER_WIDTH),
            .REQ_WIDTH (3),
            .DO_ARB_IS_CHANGE_STATE(1)) WR_RR_ARB (.clk     (clk),
                                                   .rst_n   (rst_n),
                                                   .req     ({h2c_wb_pm_awvalid, c2h_wb_pm_awvalid, c2h_dm_pm_awvalid}),
                                                   .do_arb  (wr_do_arb),
                                                   .winner  (wr_arb_out)
                                                   );

//   assign wr_arb_out = sde_pkg::RR_ARB#(.WINNER_WIDTH(WR_WINNER_WIDTH),
//                                        .REQ_WIDTH(3))::do_arb({h2c_wb_pm_awvalid, c2h_wb_pm_awvalid, c2h_dm_pm_awvalid},
//                                                               wr_winner);
                                        
   // Save the winner
   always @(posedge clk)
     if (!rst_n) 
       wr_winner <= 0;
     else
       wr_winner <= ~aw_pipe_stall ? wr_arb_out : wr_winner;

   assign aw_pipe_stall = pcim_awvalid & ~pcim_awready & ~pm_wr_winner_ff_full;
   
   always @(posedge clk)
     if (!rst_n) begin
        pcim_awvalid <= 0;
        pcim_awid <= '{default:'0};
        pcim_awaddr <= '{default:'0};
        pcim_awlen <= '{default:'0};
     end
     else begin
        if (~aw_pipe_stall) begin
           pcim_awvalid <= (h2c_wb_pm_awvalid | c2h_wb_pm_awvalid | c2h_dm_pm_awvalid) & ~pm_wr_winner_ff_full;
           pcim_awid <= (wr_arb_out == 0) ? C2H_PCIM_DM_AWID :
                        (wr_arb_out == 1) ? C2H_PCIM_WB_AWID : H2C_PCIM_WB_AWID;
           pcim_awaddr <= (wr_arb_out == 0) ? c2h_dm_pm_awaddr :
                          (wr_arb_out == 1) ? c2h_wb_pm_awaddr : h2c_wb_pm_awaddr;
           pcim_awlen <= (wr_arb_out == 0) ? c2h_dm_pm_awlen :
                         (wr_arb_out == 1) ? c2h_wb_pm_awlen : h2c_wb_pm_awlen;
        end
        else begin
           pcim_awvalid <= pcim_awvalid;
           pcim_awid <= pcim_awid;
           pcim_awaddr <= pcim_awaddr;
           pcim_awlen <= pcim_awlen;
        end // else: !if(~aw_pipe_stall)
     end // else: !if(!rst_n)
   assign pcim_awsize = PCIM_AXSIZE;
   
   assign c2h_pm_dm_awready = (wr_arb_out == 0) & ~aw_pipe_stall;
   assign c2h_pm_wb_awready = (wr_arb_out == 1) & ~aw_pipe_stall;
   assign h2c_pm_wb_awready = (wr_arb_out == 2) & ~aw_pipe_stall;

   assign wr_do_arb = (h2c_wb_pm_awvalid | c2h_wb_pm_awvalid | c2h_dm_pm_awvalid) & ~aw_pipe_stall;
   
   
   localparam PM_WR_WINNER_FIFO_DEPTH_MINUS1 = PM_WR_WINNER_FIFO_DEPTH - 1;
   localparam PM_WR_WINNER_FIFO_WIDTH = WR_WINNER_WIDTH;

   logic pm_wr_winner_ff_push;
   logic pm_wr_winner_ff_pop;
   logic [PM_WR_WINNER_FIFO_WIDTH-1:0] pm_wr_winner_ff_pop_data;
   logic                               pm_wr_winner_ff_valid;

   logic wdata_pipe_stall;
   logic requester_wvalid;
   logic requester_wlast;
   logic requester_wready;
   
   
   flop_fifo #(.WIDTH(PM_WR_WINNER_FIFO_WIDTH),
               .DEPTH(PM_WR_WINNER_FIFO_DEPTH)
               ) PM_WR_WINNER_FIFO (.clk         (clk),
                                    .rst_n       (1'b1),
                                    .sync_rst_n  (rst_n),
                                    .cfg_watermark (PM_WR_WINNER_FIFO_DEPTH_MINUS1),
                                    .push        (pm_wr_winner_ff_push),
                                    .push_data   (wr_winner),
                                    .pop         (pm_wr_winner_ff_pop),
                                    .pop_data    (pm_wr_winner_ff_pop_data),
                                    .half_full   (),
                                    .watermark   (pm_wr_winner_ff_full),
                                    .data_valid  (pm_wr_winner_ff_valid)
                                    
                                    );

   assign pm_wr_winner_ff_push = pcim_awvalid & pcim_awready & ~pm_wr_winner_ff_full;
   assign pm_wr_winner_ff_pop = requester_wvalid & requester_wlast & ~wdata_pipe_stall & pm_wr_winner_ff_valid;
      
   // Write Data Channel Pipeline
   
   assign wdata_pipe_stall = pcim_wvalid & ~pcim_wready;
   
   // Pop Winner from FIFO and Send Write Data
   // FIFO output is valid, means that there is write data to be sent
   always @(posedge clk)
     if (!rst_n) begin
        pcim_wvalid <= 0;
        pcim_wdata <= '{default:'0};
        pcim_wstrb <= '{default:'0};
        pcim_wlast <= 0;
     end
     else begin
        if (~wdata_pipe_stall) begin
           pcim_wvalid <=  requester_wvalid;
           pcim_wdata <= (pm_wr_winner_ff_pop_data == 0) ? c2h_dm_pm_wdata :
                         (pm_wr_winner_ff_pop_data == 1) ? c2h_wb_pm_wdata : h2c_wb_pm_wdata;
           pcim_wstrb <= (pm_wr_winner_ff_pop_data == 0) ? c2h_dm_pm_wstrb :
                         (pm_wr_winner_ff_pop_data == 1) ? c2h_wb_pm_wstrb : h2c_wb_pm_wstrb;
           pcim_wlast <= requester_wlast;
        end
        else begin
           pcim_wvalid <= pcim_wvalid;
           pcim_wdata <= pcim_wdata;
           pcim_wstrb <= pcim_wstrb;
           pcim_wlast <= pcim_wlast;
        end // else: !if(~wdata_pipe_stall)
     end // else: !if(!rst_n)

   assign requester_wvalid = pm_wr_winner_ff_valid & ((pm_wr_winner_ff_pop_data == 0) ? c2h_dm_pm_wvalid :
                                                      (pm_wr_winner_ff_pop_data == 1) ? c2h_wb_pm_wvalid : 
                                                      h2c_wb_pm_wvalid);
   assign requester_wlast = pm_wr_winner_ff_valid & ((pm_wr_winner_ff_pop_data == 0) ? c2h_dm_pm_wlast :
                                                     (pm_wr_winner_ff_pop_data == 1) ? c2h_wb_pm_wlast : 
                                                     h2c_wb_pm_wlast);
   assign requester_wready = ~wdata_pipe_stall;
   
   assign c2h_pm_dm_wready = pm_wr_winner_ff_valid & (pm_wr_winner_ff_pop_data == 0) & requester_wready;
   assign c2h_pm_wb_wready = pm_wr_winner_ff_valid & (pm_wr_winner_ff_pop_data == 1) & requester_wready;
   assign h2c_pm_wb_wready = pm_wr_winner_ff_valid & (pm_wr_winner_ff_pop_data == 2) & requester_wready;

   // B-Channel
   logic c2h_dm_bresp_pipe_stall;
   logic c2h_wb_bresp_pipe_stall;
   logic h2c_wb_bresp_pipe_stall;
   logic [1:0] pcim_bresp_q;
   
   // C2H DM BRESP Pipe
   assign c2h_dm_bresp_pipe_stall = c2h_pm_dm_bvalid & ~c2h_dm_pm_bready;
   always @(posedge clk)
     if (!rst_n) begin
        c2h_pm_dm_bvalid <= 0;
//        c2h_pm_dm_bresp <= 0;
     end
     else begin
        if (~c2h_dm_bresp_pipe_stall) begin
           c2h_pm_dm_bvalid <= pcim_bvalid & (pcim_bid == C2H_PCIM_DM_AWID);
//           c2h_pm_dm_bresp <= pcim_bresp;
        end
        else begin
           c2h_pm_dm_bvalid <= c2h_pm_dm_bvalid;
//           c2h_pm_dm_bresp <= c2h_pm_dm_bresp;
        end
     end // else: !if(!rst_n)
                               
   // C2H WB BRESP Pipe
   assign c2h_wb_bresp_pipe_stall = c2h_pm_wb_bvalid & ~c2h_wb_pm_bready;
   always @(posedge clk)
     if (!rst_n) begin
        c2h_pm_wb_bvalid <= 0;
//        c2h_pm_wb_bresp <= 0;
     end
     else begin
        if (~c2h_wb_bresp_pipe_stall) begin
           c2h_pm_wb_bvalid <= pcim_bvalid & (pcim_bid == C2H_PCIM_WB_AWID);
//           c2h_pm_wb_bresp <= pcim_bresp;
        end
        else begin
           c2h_pm_wb_bvalid <= c2h_pm_wb_bvalid;
//           c2h_pm_wb_bresp <= c2h_pm_wb_bresp;
        end
     end // else: !if(!rst_n)

   // H2C WB BRESP Pipe
   assign h2c_wb_bresp_pipe_stall = h2c_pm_wb_bvalid & ~h2c_wb_pm_bready;
   always @(posedge clk)
     if (!rst_n) begin
        h2c_pm_wb_bvalid <= 0;
//        h2c_pm_wb_bresp <= 0;
     end
     else begin
        if (~h2c_wb_bresp_pipe_stall) begin
           h2c_pm_wb_bvalid <= pcim_bvalid & (pcim_bid == H2C_PCIM_WB_AWID);
///           h2c_pm_wb_bresp <= pcim_bresp;
        end
        else begin
           h2c_pm_wb_bvalid <= h2c_pm_wb_bvalid;
//           h2c_pm_wb_bresp <= h2c_pm_wb_bresp;
        end
     end // else: !if(!rst_n)
                
   always @(posedge clk)
     if (!rst_n) 
        pcim_bresp_q <= 0;
     else
       if (((pcim_bid == C2H_PCIM_DM_AWID) & ~c2h_dm_bresp_pipe_stall) ||
           ((pcim_bid == C2H_PCIM_WB_AWID) & ~c2h_wb_bresp_pipe_stall) ||
           ((pcim_bid == H2C_PCIM_WB_AWID) & ~h2c_wb_bresp_pipe_stall))
         pcim_bresp_q <= pcim_bresp;
   
   assign c2h_pm_dm_bresp = pcim_bresp_q;
   assign c2h_pm_wb_bresp = pcim_bresp_q;
   assign h2c_pm_wb_bresp = pcim_bresp_q;

//    assign c2h_pm_dm_bid = C2H_PCIM_DM_AWID;
//    assign c2h_pm_wb_bid = C2H_PCIM_WB_AWID;
//    assign h2c_pm_wb_bid = H2C_PCIM_WB_AWID;

   assign pcim_bready = (pcim_bid == C2H_PCIM_DM_AWID) ? ~c2h_dm_bresp_pipe_stall :
                        (pcim_bid == C2H_PCIM_WB_AWID) ? ~c2h_wb_bresp_pipe_stall :
                        (pcim_bid == H2C_PCIM_WB_AWID) ? ~h2c_wb_bresp_pipe_stall : 1'b0;
   
   
   // Do Round Robin among those requesting read on AR Channel
   // Round Robin arbiter
   localparam RD_WINNER_WIDTH = 2;
   logic [RD_WINNER_WIDTH-1:0] rd_arb_out;
   rr_arb #(.WINNER_WIDTH(RD_WINNER_WIDTH),
            .REQ_WIDTH (3),
            .DO_ARB_IS_CHANGE_STATE(1)) RD_RR_ARB (.clk     (clk),
                                                   .rst_n   (rst_n),
                                                   .req     ({c2h_desc_pm_arvalid, h2c_desc_pm_arvalid, h2c_dm_pm_arvalid}),
                                                   .do_arb  (rd_do_arb),
                                                   .winner  (rd_arb_out)
                                                   );
   logic [RD_WINNER_WIDTH-1:0] rd_winner;
   logic                       ar_pipe_stall;
//   
//   assign rd_arb_out = sde_pkg::RR_ARB#(.WINNER_WIDTH(RD_WINNER_WIDTH),
//                                        .REQ_WIDTH(3))::do_arb({c2h_desc_pm_arvalid, h2c_desc_pm_arvalid, h2c_dm_pm_arvalid},
//                                                               rd_winner);
                                        
   
   // Save the winner
   always @(posedge clk)
     if (!rst_n) 
       rd_winner <= 0;
     else
       rd_winner <= ~ar_pipe_stall ? rd_arb_out : rd_winner;

   assign ar_pipe_stall = pcim_arvalid & ~pcim_arready;
   
   always @(posedge clk)
     if (!rst_n) begin
        pcim_arvalid <= 0;
        pcim_arid <= '{default:'0};
        pcim_araddr <= '{default:'0};
        pcim_arlen <= '{default:'0};
     end
     else begin
        if (~ar_pipe_stall) begin
           pcim_arvalid <= c2h_desc_pm_arvalid | h2c_desc_pm_arvalid | h2c_dm_pm_arvalid;
           pcim_arid <= (rd_arb_out == 0) ? H2C_PCIM_DM_ARID :
                        (rd_arb_out == 1) ? H2C_PCIM_DESC_ARID : C2H_PCIM_DESC_ARID;
           pcim_araddr <= (rd_arb_out == 0) ? h2c_dm_pm_araddr :
                          (rd_arb_out == 1) ? h2c_desc_pm_araddr : c2h_desc_pm_araddr;
           pcim_arlen <= (rd_arb_out == 0) ? h2c_dm_pm_arlen :
                         (rd_arb_out == 1) ? h2c_desc_pm_arlen : c2h_desc_pm_arlen;
        end
        else begin
           pcim_arvalid <= pcim_arvalid;
           pcim_arid <= pcim_arid;
           pcim_araddr <= pcim_araddr;
           pcim_arlen <= pcim_arlen;
        end // else: !if(~ar_pipe_stall)
     end // else: !if(!rst_n)
   assign pcim_arsize = PCIM_AXSIZE;

   assign h2c_pm_dm_arready   = (rd_arb_out == 0) & ~ar_pipe_stall;
   assign h2c_pm_desc_arready = (rd_arb_out == 1) & ~ar_pipe_stall;
   assign c2h_pm_desc_arready = (rd_arb_out == 2) & ~ar_pipe_stall;

   assign rd_do_arb = (c2h_desc_pm_arvalid | h2c_desc_pm_arvalid | h2c_dm_pm_arvalid) & ~ar_pipe_stall;
   

   // For the read data, look at ID and send to appropriate requester
   logic c2h_desc_rresp_pipe_stall;
   logic h2c_desc_rresp_pipe_stall;
   logic h2c_dm_rresp_pipe_stall;
   logic [1:0] pcim_rresp_q;
   logic [PCIM_DATA_WIDTH-1:0] pcim_rdata_q;
   logic                       pcim_rlast_q;
   
   // C2H DM RRESP Pipe
   assign c2h_desc_rresp_pipe_stall = c2h_pm_desc_rvalid & ~c2h_desc_pm_rready;
   always @(posedge clk)
     if (!rst_n) begin
        c2h_pm_desc_rvalid <= 0;
//         c2h_pm_desc_rresp <= 0;
//         c2h_pm_desc_rdata <= '{'default:'0};
//         c2h_dm_desc_rlast <= 0;
     end
     else begin
        if (~c2h_desc_rresp_pipe_stall) begin
           c2h_pm_desc_rvalid <= pcim_rvalid & (pcim_rid == C2H_PCIM_DESC_ARID);
//            c2h_pm_desc_rresp <= pcim_rresp;
//            c2h_pm_desc_rdata <= pcim_rdata;
//            c2h_dm_desc_rlast <= pcim_rlast;
        end
        else begin
           c2h_pm_desc_rvalid <= c2h_pm_desc_rvalid;
//            c2h_pm_desc_rresp <= c2h_pm_desc_rresp;
//            c2h_pm_desc_rdata <= c2h_pm_desc_rdata;
//            c2h_dm_desc_rlast <= c2h_dm_desc_rlast;
        end
     end // else: !if(!rst_n)
                               
   // C2H WB RRESP Pipe
   assign h2c_desc_rresp_pipe_stall = h2c_pm_desc_rvalid & ~h2c_desc_pm_rready;
   always @(posedge clk)
     if (!rst_n) begin
        h2c_pm_desc_rvalid <= 0;
//         h2c_pm_desc_rresp <= 0;
//         h2c_pm_desc_rdata <= '{'default:'0};
//         h2c_dm_desc_rlast <= 0;
     end
     else begin
        if (~h2c_desc_rresp_pipe_stall) begin
           h2c_pm_desc_rvalid <= pcim_rvalid & (pcim_rid == H2C_PCIM_DESC_ARID);
//            h2c_pm_desc_rresp <= pcim_rresp;
//            h2c_pm_desc_rdata <= pcim_rdata;
//            h2c_dm_desc_rlast <= pcim_rlast;
        end
        else begin
           h2c_pm_desc_rvalid <= h2c_pm_desc_rvalid;
//            h2c_pm_desc_rresp <= h2c_pm_desc_rresp;
//            h2c_pm_desc_rdata <= h2c_pm_desc_rdata;
//            h2c_dm_desc_rlast <= h2c_dm_desc_rlast;
        end
     end // else: !if(!rst_n)

   // H2C WB RRESP Pipe
   assign h2c_dm_rresp_pipe_stall = h2c_pm_dm_rvalid & ~h2c_dm_pm_rready;
   always @(posedge clk)
     if (!rst_n) begin
        h2c_pm_dm_rvalid <= 0;
//         h2c_pm_dm_rresp <= 0;
//         h2c_pm_dm_rdata <= '{'default:'0};
//         h2c_dm_dm_rlast <= 0;
     end
     else begin
        if (~h2c_dm_rresp_pipe_stall) begin
           h2c_pm_dm_rvalid <= pcim_rvalid & (pcim_rid == H2C_PCIM_DM_ARID);
//            h2c_pm_dm_rresp <= pcim_rresp;
//            h2c_pm_dm_rdata <= pcim_rdata;
//            h2c_dm_dm_rlast <= pcim_rlast;
        end
        else begin
           h2c_pm_dm_rvalid <= h2c_pm_dm_rvalid;
//            h2c_pm_dm_rresp <= h2c_pm_dm_rresp;
//            h2c_pm_dm_rdata <= h2c_pm_dm_rdata;
//            h2c_dm_dm_rlast <= h2c_dm_dm_rlast;
        end
     end // else: !if(!rst_n)
                     
   always @(posedge clk)
     if (!rst_n) begin
        pcim_rresp_q <= 0;
        pcim_rdata_q <= '{default:'0};
        pcim_rlast_q <= 0;
     end
     else
       if (((pcim_rid == C2H_PCIM_DESC_ARID) & ~c2h_desc_rresp_pipe_stall) ||
           ((pcim_rid == H2C_PCIM_DESC_ARID) & ~h2c_desc_rresp_pipe_stall) ||
           ((pcim_rid == H2C_PCIM_DM_ARID) & ~h2c_dm_rresp_pipe_stall)) begin
          pcim_rresp_q <= pcim_rresp;
          pcim_rdata_q <=pcim_rdata;
          pcim_rlast_q <= pcim_rlast;
       end
   
   assign c2h_pm_desc_rresp = pcim_rresp_q;
   assign h2c_pm_desc_rresp = pcim_rresp_q;
   assign h2c_pm_dm_rresp = pcim_rresp_q;

   assign c2h_pm_desc_rdata = pcim_rdata_q;
   assign h2c_pm_desc_rdata = pcim_rdata_q;
   assign h2c_pm_dm_rdata = pcim_rdata_q;

   assign c2h_pm_desc_rlast = pcim_rlast_q;
   assign h2c_pm_desc_rlast = pcim_rlast_q;
   assign h2c_pm_dm_rlast = pcim_rlast_q;

//    assign c2h_pm_desc_rid = C2H_PCIM_DESC_ARID;
//    assign h2c_pm_desc_rid = H2C_PCIM_DESC_ARID;
//    assign h2c_pm_dm_rid = H2C_PCIM_DM_ARID;
          
   assign pcim_rready = (pcim_rid == C2H_PCIM_DESC_ARID) ? ~c2h_desc_rresp_pipe_stall :
                        (pcim_rid == H2C_PCIM_DESC_ARID) ? ~h2c_desc_rresp_pipe_stall :
                        (pcim_rid == H2C_PCIM_DM_ARID)   ? ~h2c_dm_rresp_pipe_stall : 1'b0;
   

   // Local Config Registers
   // TODO:
   // Temporarily no registers
   assign pm_ps_cfg_ack = 1;
   assign pm_ps_cfg_rdata = 32'hbaad_1000;
   
endmodule // sde_pm


   
