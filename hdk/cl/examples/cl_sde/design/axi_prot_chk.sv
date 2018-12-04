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


module axi_prot_chk #(parameter ID_WIDTH=16,
                      parameter ADDR_WIDTH = 64,
                      parameter LEN_WIDTH=8,
                      parameter DATA_WIDTH=512
                      )
  (
   input                       clk,
   input                       rst_n,

   input [11:0]                cfg_chk_addr,
   input                       cfg_chk_wr,
   input                       cfg_chk_rd,
   input [31:0]                cfg_chk_wdata,
  
   output logic                chk_cfg_ack,
   output logic [31:0]         chk_cfg_rdata,

   output logic                wr_last_error,
   
   input [ID_WIDTH-1:0]        awid,
   input [ADDR_WIDTH-1:0]      awaddr,
   input [LEN_WIDTH-1:0]       awlen,
   input [2:0]                 awsize,
   input                       awvalid,
   input                       awready,
   input [DATA_WIDTH-1:0]      wdata,
   input [(DATA_WIDTH>>3)-1:0] wstrb,
   input                       wlast,
   input                       wvalid,
   input                       wready,
   input [ID_WIDTH-1:0]        bid,
   input [1:0]                 bresp,
   input                       bvalid,
   input                       bready,
   input [ID_WIDTH-1:0]        arid,
   input [ADDR_WIDTH-1:0]      araddr,
   input [LEN_WIDTH-1:0]       arlen,
   input [2:0]                 arsize,
   input                       arvalid,
   input                       arready,
   input [ID_WIDTH-1:0]        rid,
   input [DATA_WIDTH-1:0]      rdata,
   input [1:0]                 rresp,
   input                       rlast,
   input                       rvalid,
   input                       rready

   );

   logic                       aw_fifo_pop;
   logic [ID_WIDTH+LEN_WIDTH+ADDR_WIDTH-1:0] aw_fifo_pop_data;
   logic                             aw_fifo_valid;
   logic                             aw_fifo_full;
   logic [ID_WIDTH-1:0]              aw_fifo_out_id;
   logic [LEN_WIDTH-1:0]             aw_fifo_out_len;
   logic [ADDR_WIDTH-1:0]            aw_fifo_out_addr;
   logic                             wr_fifo_pop;
   logic                             wr_fifo_pop_data;
   logic                             wr_fifo_valid;
   logic                             wr_fifo_full;
   logic                             wr_fifo_out_wlast;
   logic                             set_wr_last_incomplete;
   logic                             set_wr_last_early;
   logic [LEN_WIDTH-1:0]             wr_beat;
   logic                             wr_last_incomplete;
   logic                             wr_last_early;
   logic [63:0]                      err_addr;
   logic [7:0]                       err_id;
   logic                             clr_wr_last_incomplete;
   logic                             clr_wr_last_early;
   logic                             cfg_chk_wr_q;
   logic                             cfg_chk_rd_q;
   logic                             cfg_chk_wr_re;
   logic                             cfg_chk_rd_re;
   
   // Write registers
   always @(posedge clk) begin
      cfg_chk_wr_q <= cfg_chk_wr;
      cfg_chk_rd_q <= cfg_chk_rd;
   end
   assign cfg_chk_wr_re = ~cfg_chk_wr_q & cfg_chk_wr;
   assign cfg_chk_rd_re = ~cfg_chk_rd_q & cfg_chk_rd;

   assign clr_wr_last_incomplete = cfg_chk_wr_re & (cfg_chk_addr == 12'h0) & cfg_chk_wdata[1];
   assign clr_wr_last_early = cfg_chk_wr_re & (cfg_chk_addr == 12'h0) & cfg_chk_wdata[0];
   
   // Read data & Ack
   always @(posedge clk) begin
      chk_cfg_ack <= (cfg_chk_wr || cfg_chk_rd);
      chk_cfg_rdata <= (cfg_chk_addr == 12'h0) ? {wr_last_incomplete, wr_last_early} : 
                       (cfg_chk_addr == 12'h4) ? err_addr[31:0] :
                       (cfg_chk_addr == 12'h8) ? err_addr[63:32] : 
                       err_id;
   end

   // Push AW Channel into a FIFO
   ram_fifo_ft #(.WIDTH(ID_WIDTH + LEN_WIDTH + ADDR_WIDTH),
                 .PIPELINE(0)) AW_FIFO
     (.clk (clk),
      .rst_n (rst_n),

      .push (awvalid & awready),
      .push_data ({awid, awlen, awaddr}),
      .pop  (aw_fifo_pop),
      .pop_data (aw_fifo_pop_data),

      .valid (aw_fifo_valid),
      .wmark (aw_fifo_full)

      );
   assign aw_fifo_pop = aw_fifo_valid & wr_fifo_valid & wr_fifo_out_wlast;
   assign {aw_fifo_out_id, aw_fifo_out_len, aw_fifo_out_addr} = aw_fifo_pop_data;
   
   // Push W Channel into a FIFO
   ram_fifo_ft #(.WIDTH(1),
                 .PIPELINE(0)) WR_FIFO
     (.clk (clk),
      .rst_n (rst_n),

      .push (wvalid & wready),
      .push_data (wlast),
      .pop  (wr_fifo_pop),
      .pop_data (wr_fifo_pop_data),

      .valid (wr_fifo_valid),
      .wmark (wr_fifo_full)

      );
   assign wr_fifo_pop = wr_fifo_valid;   
   assign wr_fifo_out_wlast = wr_fifo_pop_data;

   assign set_wr_last_incomplete = ~(wr_last_incomplete || wr_last_early) & wr_fifo_valid & aw_fifo_valid & (aw_fifo_out_len == wr_beat) & ~wr_fifo_out_wlast;
   assign set_wr_last_early = ~(wr_last_incomplete || wr_last_early) & wr_fifo_valid & aw_fifo_valid & (aw_fifo_out_len != wr_beat) & wr_fifo_out_wlast;
   
   // Check number of wr beats
   always @(posedge clk)
     if (!rst_n) begin
        wr_beat <= 0;
        wr_last_incomplete <= 0;
        wr_last_early <= 0;
        err_addr <= 64'd0;
        err_id <= 8'd0;
        wr_last_error <= 0;
    end
     else begin
        wr_beat <= wr_fifo_out_wlast & wr_fifo_valid & aw_fifo_valid ? 0 :
                   wr_fifo_valid & aw_fifo_valid ? wr_beat + 1 : 
                   wr_beat;
        
        wr_last_incomplete <= set_wr_last_incomplete ? 1'b1 :
                              clr_wr_last_incomplete ? 1'b0 :
                              wr_last_incomplete;
        
        wr_last_early <= set_wr_last_early ? 1'b1 :
                         clr_wr_last_early ? 1'b0 :
                         wr_last_early;
        
        err_addr <= (set_wr_last_incomplete || set_wr_last_early) ? aw_fifo_out_addr : err_addr;
        err_id <= (set_wr_last_incomplete || set_wr_last_early) ? aw_fifo_out_id : err_id;

        wr_last_error <= wr_last_incomplete || wr_last_early;
        
     end // else: !if(!rst_n)
   
endmodule // axi_prot_chk





   
                     
