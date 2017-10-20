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

module  cl_tst_scrb #(parameter DATA_WIDTH=512,
                      NUM_RD_TAG=512,
                      SCRB_BURST_LEN_MINUS1 = 15,
                      SCRB_MAX_ADDR = 64'h3FFFFF,
                      NO_SCRB_INST = 0
) (
   input                             clk,
   input                             rst_n,

   input [31:0]                      cfg_addr,
   input [31:0]                      cfg_wdata,
   input                             cfg_wr,
   input                             cfg_rd,
   output logic                      tst_cfg_ack,
   output logic [31:0]               tst_cfg_rdata,

   input                             scrb_enable,
   output                            scrb_done,
   output [2:0]                      scrb_dbg_state,
   output [63:0]                     scrb_dbg_addr,

   input logic [6:0]                 slv_awid,
   input logic [63:0]                slv_awaddr,
   input logic [7:0]                 slv_awlen,
   input logic [2:0]                 slv_awsize,
   input logic                       slv_awvalid,
   input logic [10:0]                slv_awuser,
   output                            slv_awready,

   input logic [6:0]                 slv_wid,
   input logic [DATA_WIDTH-1:0]      slv_wdata,
   input logic [(DATA_WIDTH/8)-1:0]  slv_wstrb,
   input logic                       slv_wlast,
   input logic                       slv_wvalid,
   output                            slv_wready,

   output [6:0]                      slv_bid,
   output [1:0]                      slv_bresp,
   output                            slv_bvalid,
   output [10:0]                     slv_buser, //This is specific to HMC, other interfaces should tie to '0'
   input logic                       slv_bready,

   input logic [6:0]                 slv_arid,
   input logic [63:0]                slv_araddr,
   input logic [7:0]                 slv_arlen,
   input logic [2:0]                 slv_arsize,
   input logic                       slv_arvalid,
   input logic [10:0]                slv_aruser,
   output                            slv_arready,

   output [6:0]                      slv_rid,
   output [DATA_WIDTH-1:0]           slv_rdata,
   output [1:0]                      slv_rresp,
   output                            slv_rlast,
   output                            slv_rvalid,
   output [10:0]                     slv_ruser,
   input logic                       slv_rready,
   
   output logic [8:0]                awid,
   output logic [63:0]               awaddr,
   output logic [7:0]                awlen,
   output logic [2:0]                awsize,
   output logic                      awvalid,
   output logic [10:0]               awuser,
   input                             awready,

   output logic [8:0]                wid,
   output logic [DATA_WIDTH-1:0]     wdata,
   output logic [(DATA_WIDTH/8)-1:0] wstrb,
   output logic                      wlast,
   output logic                      wvalid,
   input                             wready,

   input [8:0]                       bid,
   input [1:0]                       bresp,
   input                             bvalid,
   input [17:0]                      buser, //This is specific to HMC, other interfaces should tie to '0'
   output logic                      bready,

   output logic [8:0]                arid,
   output logic [63:0]               araddr,
   output logic [7:0]                arlen,
   output logic [2:0]                arsize,
   output logic                      arvalid,
   output logic [10:0]               aruser,
   input                             arready,

   input [8:0]                       rid,
   input [DATA_WIDTH-1:0]            rdata,
   input [1:0]                       rresp,
   input                             rlast,
   input                             rvalid,
   input [17:0]                      ruser,
   output logic                      rready
   );

   logic [5:0]                       scrb_awid;
   logic [63:0]                      scrb_awaddr;
   logic [7:0]                       scrb_awlen;
   logic                             scrb_awvalid;
   logic [10:0]                       scrb_awuser;
   logic                             scrb_awready;

   logic [5:0]                       scrb_wid;
   logic [DATA_WIDTH-1:0]            scrb_wdata;
   logic [(DATA_WIDTH/8)-1:0]        scrb_wstrb;
   logic                             scrb_wlast;
   logic                             scrb_wvalid;
   logic                             scrb_wready;

   logic [5:0]                       scrb_bid;
   logic [1:0]                       scrb_bresp;
   logic                             scrb_bvalid;
   logic [17:0]                      scrb_buser; //This is specific to HMC; other interfaces should tie to '0'
   logic                             scrb_bready;

   logic [5:0]                       scrb_arid;
   logic [63:0]                      scrb_araddr;
   logic [7:0]                       scrb_arlen;
   logic                             scrb_arvalid;
   logic [10:0]                       scrb_aruser;
   logic                             scrb_arready;

   logic [5:0]                       scrb_rid;
   logic [DATA_WIDTH-1:0]            scrb_rdata;
   logic [1:0]                       scrb_rresp;
   logic                             scrb_rlast;
   logic                             scrb_rvalid;
   logic [17:0]                      scrb_ruser;
   logic                             scrb_rready;

   logic                             scrb_enable_q;

   generate
      if (NO_SCRB_INST == 0) begin: gen_scrb
         always_ff @(posedge clk or negedge rst_n)
           if (!rst_n)
             scrb_enable_q <= 1'b0;
           else
             scrb_enable_q <= scrb_enable;
         
         // Instance mem_scrb
         mem_scrb 
           #(.DATA_WIDTH(DATA_WIDTH),
             .ID_WIDTH  (6),
             .USER_WIDTH(11),
             .BURST_LEN_MINUS1 (SCRB_BURST_LEN_MINUS1),
             .MAX_ADDR(SCRB_MAX_ADDR)
             ) 
         MEM_SCRB (
            
                   .clk(clk),
                   .rst_n(rst_n),

                   .awid(scrb_awid),
                   .awaddr(scrb_awaddr), 
                   .awlen(scrb_awlen),
                   .awvalid(scrb_awvalid),
                   .awuser(scrb_awuser),
                   .awready(scrb_awready),

                   .wid(scrb_wid),
                   .wdata(scrb_wdata),
                   .wstrb(scrb_wstrb),
                   .wlast(scrb_wlast),
                   .wvalid(scrb_wvalid),
                   .wready(scrb_wready),

                   .bvalid(scrb_bvalid),
                   .bready(scrb_bready),

                   .arid(scrb_arid),
                   .araddr(scrb_araddr),
                   .arlen(scrb_arlen),
                   .arvalid(scrb_arvalid),
                   .aruser(scrb_aruser),
                   .arready(scrb_arready),

                   .rready(scrb_rready),

                   .scrb_enable(scrb_enable),
                   .scrb_done(scrb_done),

                   .dbg_state(scrb_dbg_state),
                   .dbg_addr (scrb_dbg_addr)
            
                   );

      end // block: gen_scrb_inst
      else begin : gen_noscrb

         assign scrb_enable_q = '{default:'0};
         assign scrb_awid     = '{default:'0};
         assign scrb_awaddr   = '{default:'0};
         assign scrb_awlen    = '{default:'0};
         assign scrb_awvalid  = '{default:'0};
         assign scrb_awuser   = '{default:'0};
         assign scrb_wid      = '{default:'0};
         assign scrb_wdata    = '{default:'0};
         assign scrb_wstrb    = '{default:'0};
         assign scrb_wlast    = '{default:'0};
         assign scrb_wvalid   = '{default:'0};
         assign scrb_bready   = '{default:'0};
         assign scrb_arid     = '{default:'0};
         assign scrb_araddr   = '{default:'0};
         assign scrb_arlen    = '{default:'0};
         assign scrb_arvalid  = '{default:'0};
         assign scrb_aruser   = '{default:'0};
         assign scrb_arready  = '{default:'0};
         assign scrb_rready   = '{default:'0};
         
      end // block: gen_noscrb
         
   endgenerate
   
   
   // Instance cl_tst
   logic [8:0]                       atg_awid;
   logic [63:0]                      atg_awaddr;
   logic [7:0]                       atg_awlen;
   logic                             atg_awvalid;
   logic [10:0]                       atg_awuser;
   logic                             atg_awready;

   logic [8:0]                       atg_wid;
   logic [DATA_WIDTH-1:0]            atg_wdata;
   logic [(DATA_WIDTH/8)-1:0]        atg_wstrb;
   logic                             atg_wlast;
   logic                             atg_wvalid;
   logic                             atg_wready;

   logic [8:0]                       atg_bid;
   logic [1:0]                       atg_bresp;
   logic                             atg_bvalid;
   logic [17:0]                      atg_buser; //This is specific to HMC; other interfaces should tie to '0'
   logic                             atg_bready;

   logic [8:0]                       atg_arid;
   logic [63:0]                      atg_araddr;
   logic [7:0]                       atg_arlen;
   logic                             atg_arvalid;
   logic [10:0]                       atg_aruser;
   logic                             atg_arready;

   logic [8:0]                       atg_rid;
   logic [DATA_WIDTH-1:0]            atg_rdata;
   logic [1:0]                       atg_rresp;
   logic                             atg_rlast;
   logic                             atg_rvalid;
   logic [17:0]                      atg_ruser;
   logic                             atg_rready;

   logic                             atg_enable;

      cl_tst #(.DATA_WIDTH(DATA_WIDTH),
               .NUM_RD_TAG(NUM_RD_TAG)
               ) CL_TST (
   
         .clk(clk),
         .rst_n(rst_n),

         .cfg_addr     (cfg_addr     ),
         .cfg_wdata    (cfg_wdata    ),
         .cfg_wr       (cfg_wr       ),
         .cfg_rd       (cfg_rd       ),
         .tst_cfg_ack  (tst_cfg_ack  ),
         .tst_cfg_rdata(tst_cfg_rdata),

         .atg_enable(atg_enable),
                                               
         .awid(atg_awid),
         .awaddr(atg_awaddr), 
         .awlen(atg_awlen),
         .awvalid(atg_awvalid),
         .awuser(atg_awuser),
         .awready(atg_awready),

         .wid(atg_wid),
         .wdata(atg_wdata),
         .wstrb(atg_wstrb),
         .wlast(atg_wlast),
         .wvalid(atg_wvalid),
         .wready(atg_wready),

         .bid(atg_bid),
         .bresp(atg_bresp),
         .buser(atg_buser),
         .bvalid(atg_bvalid),
         .bready(atg_bready),

         .arid(atg_arid),
         .araddr(atg_araddr),
         .arlen(atg_arlen),
         .arvalid(atg_arvalid),
         .aruser(atg_aruser),
         .arready(atg_arready),

         .rid(atg_rid),
         .rdata(atg_rdata),
         .rresp(atg_rresp),
         .rlast(atg_rlast),
         .ruser(atg_ruser),
         .rvalid(atg_rvalid),
         .rready(atg_rready)
      );


assign awid    = scrb_enable ? scrb_awid    : 
                 atg_enable  ? atg_awid     :
                 {2'b0, slv_awid}    ;
assign awaddr  = scrb_enable ? scrb_awaddr  : 
                 atg_enable  ? atg_awaddr   :
                 slv_awaddr;
assign awlen   = scrb_enable ? scrb_awlen   : 
                 atg_enable  ? atg_awlen    :
                 slv_awlen   ;
assign awsize   = scrb_enable ? 3'b110   : 
                  atg_enable  ? 3'b110   :
                  slv_awsize   ;
assign awvalid = scrb_enable ? scrb_awvalid : 
                 atg_enable  ? atg_awvalid  :
                 slv_awvalid;
assign awuser  = scrb_enable ? scrb_awuser  : 
                 atg_enable  ? atg_awuser   :
                 slv_awuser;
assign atg_awready  =  atg_enable & awready ;
assign scrb_awready =  scrb_enable & awready ;
assign slv_awready = ~atg_enable & ~scrb_enable & awready;

assign wid     = scrb_enable ? scrb_wid    : 
                 atg_enable  ? atg_wid     :
                 {2'b0, slv_wid}   ;
assign wdata   = scrb_enable ? scrb_wdata  : 
                 atg_enable  ? atg_wdata   :
                 slv_wdata;
assign wstrb   = scrb_enable ? scrb_wstrb  : 
                 atg_enable  ? atg_wstrb   :
                 slv_wstrb;
assign wlast   = scrb_enable ? scrb_wlast  : 
                 atg_enable  ? atg_wlast   :
                 slv_wlast;
assign wvalid  = scrb_enable ? scrb_wvalid : 
                 atg_enable  ? atg_wvalid  :
                 slv_wvalid;
assign atg_wready   =  atg_enable & wready ;
assign scrb_wready  =  scrb_enable & wready ;
assign slv_wready = ~atg_enable & ~scrb_enable & wready;
   
assign atg_bid     = bid   ;
assign atg_bresp   = bresp ;
assign atg_bvalid  = atg_enable & bvalid;
assign atg_buser   = buser ;
assign scrb_bid    = bid[5:0]   ;
assign scrb_bresp  = bresp ;
assign scrb_bvalid = scrb_enable & bvalid;
assign scrb_buser  = buser ;
assign slv_bid    = bid[6:0]   ;
assign slv_bresp  = bresp ;
assign slv_bvalid = ~scrb_enable & ~atg_enable & bvalid;
assign slv_buser  = buser[10:0] ;
assign bready = scrb_enable ? scrb_bready : 
                atg_enable  ? atg_bready  :
                slv_bready;

assign arid    = scrb_enable ? {3'b0, scrb_arid}    : 
                 atg_enable  ? atg_arid             :
                 {2'b0, slv_arid};
assign araddr  = scrb_enable ? scrb_araddr  : 
                 atg_enable  ? atg_araddr   :
                 slv_araddr;
assign arlen   = scrb_enable ? scrb_arlen   : 
                 atg_enable  ? atg_arlen    :
                 slv_arlen;
assign arsize  = scrb_enable ? 3'b110 :
                 atg_enable  ? 3'b110 :
                 slv_arsize;
assign arvalid = scrb_enable ? scrb_arvalid : 
                 atg_enable  ? atg_arvalid  :
                 slv_arvalid;
assign aruser  = scrb_enable ? scrb_aruser  : 
                 atg_enable  ? atg_aruser   :
                 slv_aruser;
assign atg_arready  =  atg_enable & arready ;
assign scrb_arready =  scrb_enable & arready ;
assign slv_arready = ~scrb_enable & ~atg_enable & arready;

assign atg_rid     = rid   ;
assign atg_rdata   = rdata ;
assign atg_rresp   = rresp ;
assign atg_rlast   = rlast ;
assign atg_rvalid  = atg_enable & rvalid;
assign atg_ruser   = ruser ;
assign scrb_rid     = rid[5:0]   ;
assign scrb_rdata   = rdata ;
assign scrb_rresp   = rresp ;
assign scrb_rlast   = rlast ;
assign scrb_rvalid  = scrb_enable & rvalid;
assign scrb_ruser   = ruser ;
assign slv_rid     = rid[6:0]   ;
assign slv_rdata   = rdata ;
assign slv_rresp   = rresp ;
assign slv_rlast   = rlast ;
assign slv_rvalid  = ~scrb_enable & ~atg_enable & rvalid;
assign slv_ruser   = ruser[10:0] ;
assign rready = scrb_enable ? scrb_rready : 
                atg_enable  ? atg_rready  :
                slv_rready;
   
endmodule // cl_tst_scrb


