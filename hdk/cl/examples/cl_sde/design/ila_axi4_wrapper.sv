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
//---------------------------------------------------------------------------------
// NOTE: ila_axi4 core supports only Maximum DATA width = 32 on WDATA and RDATA
// ****  AXI_DATA_WIDTH <= 32
//---------------------------------------------------------------------------------

module ila_axi4_wrapper
  #(parameter PIPE_STAGES=2, AXI_DATA_WIDTH=32, ADD_AXI_BUS_PIPE=0)
   (
    input logic                            aclk,
    input logic                            trig_disable,
    input logic [4:0]                      trig_mask,
    //AXI-4 bus signals
    input logic [15:0]                     ila_awid,
    input logic [63:0]                     ila_awaddr,
    input logic                            ila_awvalid,
    input logic                            ila_awready,
    input logic [ 7:0]                     ila_awlen,
    input logic [ 2:0]                     ila_awsize,

    input logic                            ila_wvalid,
    input logic                            ila_wready,
    input logic [AXI_DATA_WIDTH-1     : 0] ila_wdata,
    input logic [(AXI_DATA_WIDTH/8)-1 : 0] ila_wstrb,
    input logic                            ila_wlast,

    input logic [15:0]                     ila_bid,
    input logic                            ila_bvalid,
    input logic                            ila_bready,
    input logic [ 1:0]                     ila_bresp,

    input logic [15:0]                     ila_arid,
    input logic [63:0]                     ila_araddr,
    input logic                            ila_arvalid,
    input logic                            ila_arready,
    input logic [ 7:0]                     ila_arlen,
    input logic [ 2:0]                     ila_arsize,

    input logic [15:0]                     ila_rid,
    input logic                            ila_rvalid,
    input logic                            ila_rready,
    input logic [AXI_DATA_WIDTH-1 : 0]     ila_rdata,
    input logic [ 1:0]                     ila_rresp,
    input logic                            ila_rlast
    );

   //--------------------------------------------
   // if needed to insert reg slices for AXI bus
   //--------------------------------------------
   typedef struct {
      logic [15:0]                     awid    ;
      logic [63:0] 		       awaddr  ;
      logic                            awvalid ;
      logic                            awready ;
      logic [ 7:0]                     awlen   ;
      logic [ 2:0]                     awsize  ;

      logic                            wvalid  ;
      logic                            wready  ;
      logic [AXI_DATA_WIDTH-1     : 0] wdata   ;
      logic [(AXI_DATA_WIDTH/8)-1 : 0] wstrb   ;
      logic 			       wlast   ;

      logic [15:0]                     bid     ;
      logic                            bvalid  ;
      logic                            bready  ;
      logic [ 1:0]                     bresp   ;

      logic [15:0]                     arid    ;
      logic [63:0]                     araddr  ;
      logic                            arvalid ;
      logic                            arready ;
      logic [ 7:0]                     arlen   ;
      logic [ 2:0]                     arsize  ;

      logic [15:0]                     rid     ;
      logic                            rvalid  ;
      logic                            rready  ;
      logic [AXI_DATA_WIDTH-1 : 0]     rdata   ;
      logic [ 1:0]                     rresp   ;
      logic                            rlast   ;
      } axi_bus_t;

   //----------------------------
   // Debug Core ILA for DDRA AXI4 interface monitoring - with TRIGGER
   //----------------------------
   logic       trig_in_q;
   logic       awvalid_q, wvalid_q, bvalid_q, arvalid_q, rvalid_q;
   logic [4:0] trig_mask_q, trig_mask_q2;
   logic       trig_disable_q, trig_disable_q2;
   axi_bus_t   lcl_axi_q;

   // flop to ease timing
   always_ff @(posedge aclk) begin //{
      {trig_disable_q,  trig_mask_q[4:0] } <= {trig_disable, trig_mask[4:0]};
      {trig_disable_q2, trig_mask_q2[4:0]} <= {trig_disable_q, trig_mask_q[4:0]};
   end //}

   if (ADD_AXI_BUS_PIPE != 0) begin //{
      localparam PIPE_WIDTH = 1 + 64 + 2 + 1 + 1 + 64 + 1 + 1 + 1 + 1 + AXI_DATA_WIDTH + 1 + 1 + 2 +
			      AXI_DATA_WIDTH + AXI_DATA_WIDTH/8 + 1 + 16 + 16 + 8 + 3 + 16 + 8 + 3 + 16 + 1 + 1;
      lib_pipe #(.WIDTH(PIPE_WIDTH), .STAGES(PIPE_STAGES))
      PRE_ILA_PIPE (.clk     (aclk),
      		    .rst_n   (1'b1),
      		    .in_bus  ( { ila_wready              , //(WREADY ), // input wire [0:0] probe0
      				 ila_awaddr        [63:0], //( AWADDR), // input wire [63:0]  probe1
      				 ila_bresp         [1:0] , //( BRESP ), // input wire [1:0]  probe2
      				 ila_bvalid              , //( BVALID), // input wire [0:0]  probe3
      				 ila_bready              , //( BREADY), // input wire [0:0]  probe4
      				 ila_araddr        [63:0], //( ARADDR), // input wire [63:0]  probe5
      				 ila_rready              , //( RREADY), // input wire [0:0]  probe6
      				 ila_wvalid              , //( WVALID), // input wire [0:0]  probe7
      				 ila_arvalid             , //( ARVALID),// input wire [0:0]  probe8
      				 ila_arready             , //( ARREADY),// input wire [0:0]  probe9
      				 ila_rdata         [AXI_DATA_WIDTH-1     : 0], //( RDATA),  // input wire [31:0]  probe10
      				 ila_awvalid             , //( AWVALID),// input wire [0:0]  probe11
      				 ila_awready             , //( AWREADY),// input wire [0:0]  probe12
      				 ila_rresp         [1:0] , //( RRESP),  // input wire [1:0]  probe13
      				 ila_wdata         [AXI_DATA_WIDTH-1     : 0], //( WDATA),  // input wire [31:0]  probe14
      				 ila_wstrb         [(AXI_DATA_WIDTH/8)-1 : 0] , //( WSTRB),  // input wire [3:0]  probe15
      				 ila_rvalid              , //( RVALID), // input wire [0:0]  probe16
      				 ila_awid          [15:0], //( AWID),   // input wire [15:0]  probe19
      				 ila_bid           [15:0], //( BID),    // input wire [15:0]  probe20
      				 ila_awlen         [7:0] , //( AWLEN),  // input wire [7:0]  probe21
      				 ila_awsize        [2:0] , //( AWSIZE), // input wire [2:0]  probe23
      				 ila_arid          [15:0], //( ARID),   // input wire [15:0]  probe25
      				 ila_arlen         [7:0] , //( ARLEN),  // input wire [7:0]  probe27
      				 ila_arsize        [2:0] , //( ARSIZE), // input wire [2:0]  probe28
      				 ila_rid           [15:0], //( RID),    // input wire [15:0]  probe38
      				 ila_rlast               , //( RLAST),  // input wire [0:0]  probe41
      				 ila_wlast              }),//( WLAST)   // input wire        probe43,
      		    .out_bus ( { lcl_axi_q.wready        , //( WREADY ),// input wire [0:0] probe0
      				 lcl_axi_q.awaddr  [63:0], //( AWADDR), // input wire [63:0]  probe1
      				 lcl_axi_q.bresp   [1:0] , //( BRESP ), // input wire [1:0]  probe2
      				 lcl_axi_q.bvalid        , //( BVALID), // input wire [0:0]  probe3
      				 lcl_axi_q.bready        , //( BREADY), // input wire [0:0]  probe4
      				 lcl_axi_q.araddr  [63:0], //( ARADDR), // input wire [63:0]  probe5
      				 lcl_axi_q.rready        , //( RREADY), // input wire [0:0]  probe6
      				 lcl_axi_q.wvalid        , //( WVALID), // input wire [0:0]  probe7
      				 lcl_axi_q.arvalid       , //( ARVALID),// input wire [0:0]  probe8
      				 lcl_axi_q.arready       , //( ARREADY),// input wire [0:0]  probe9
      				 lcl_axi_q.rdata   [AXI_DATA_WIDTH-1     : 0], //( RDATA),  // input wire [31:0]  probe10
      				 lcl_axi_q.awvalid       , //( AWVALID),// input wire [0:0]  probe11
      				 lcl_axi_q.awready       , //( AWREADY),// input wire [0:0]  probe12
      				 lcl_axi_q.rresp   [1:0] , //( RRESP),  // input wire [1:0]  probe13
      				 lcl_axi_q.wdata   [AXI_DATA_WIDTH-1     : 0], //( WDATA),  // input wire [31:0]  probe14
      				 lcl_axi_q.wstrb   [(AXI_DATA_WIDTH/8)-1 : 0] , //( WSTRB),  // input wire [3:0]  probe15
      				 lcl_axi_q.rvalid        , //( RVALID), // input wire [0:0]  probe16
      				 lcl_axi_q.awid    [15:0], //( AWID),   // input wire [15:0]  probe19
      				 lcl_axi_q.bid     [15:0], //( BID),    // input wire [15:0]  probe20
      				 lcl_axi_q.awlen   [7:0] , //( AWLEN),  // input wire [7:0]  probe21
      				 lcl_axi_q.awsize  [2:0] , //( AWSIZE), // input wire [2:0]  probe23
      				 lcl_axi_q.arid    [15:0], //( ARID),   // input wire [15:0]  probe25
      				 lcl_axi_q.arlen   [7:0] , //( ARLEN),  // input wire [7:0]  probe27
      				 lcl_axi_q.arsize  [2:0] , //( ARSIZE), // input wire [2:0]  probe28
      				 lcl_axi_q.rid     [15:0], //( RID),    // input wire [15:0]  probe38
      				 lcl_axi_q.rlast         , //( RLAST),  // input wire [0:0]  probe41
      				 lcl_axi_q.wlast        }) //( WLAST)   // input wire [0:0]  probe43
      		    );
      // For trigger
      assign
	awvalid_q = lcl_axi_q.awvalid,
	wvalid_q  = lcl_axi_q.wvalid,
	bvalid_q  = lcl_axi_q.bvalid,
	arvalid_q = lcl_axi_q.arvalid,
	rvalid_q  = lcl_axi_q.rvalid;

   end else begin //}{
      // pipe stages for trigger signals
      localparam PIPE_WIDTH = 5;
      lib_pipe #(.WIDTH(PIPE_WIDTH), .STAGES(PIPE_STAGES))
      PRE_ILA_PIPE (.clk     (aclk),
   		    .rst_n   (1'b1),
   		    .in_bus  ({ila_awvalid, ila_wvalid, ila_bvalid, ila_arvalid, ila_rvalid}),
   		    .out_bus ({awvalid_q, wvalid_q, bvalid_q, arvalid_q, rvalid_q})
   		    );
      assign
	lcl_axi_q.awvalid                            = ila_awvalid       ,
	lcl_axi_q.wvalid 			     = ila_wvalid	 ,
	lcl_axi_q.bvalid 			     = ila_bvalid	 ,
	lcl_axi_q.arvalid 			     = ila_arvalid	 ,
	lcl_axi_q.rvalid                             = ila_rvalid	 ,
	lcl_axi_q.wready                             = ila_wready        ,
	lcl_axi_q.awaddr  [63:0]                     = ila_awaddr  [63:0],
	lcl_axi_q.bresp   [1:0]                      = ila_bresp   [1:0] ,
	lcl_axi_q.bready                             = ila_bready        ,
	lcl_axi_q.araddr  [63:0]                     = ila_araddr  [63:0],
	lcl_axi_q.rready                             = ila_rready        ,
	lcl_axi_q.arready                            = ila_arready       ,
	lcl_axi_q.rdata   [AXI_DATA_WIDTH-1     : 0] = ila_rdata   [AXI_DATA_WIDTH-1:0],
	lcl_axi_q.awready                            = ila_awready       ,
	lcl_axi_q.rresp   [1:0]                      = ila_rresp   [1:0] ,
	lcl_axi_q.wdata   [AXI_DATA_WIDTH-1     : 0] = ila_wdata   [AXI_DATA_WIDTH-1:0],
	lcl_axi_q.wstrb   [(AXI_DATA_WIDTH/8)-1 : 0] = ila_wstrb   [(AXI_DATA_WIDTH/8)-1:0] ,
	lcl_axi_q.awid    [15:0]                     = ila_awid    [15:0],
	lcl_axi_q.bid     [15:0]                     = ila_bid     [15:0],
	lcl_axi_q.awlen   [7:0]                      = ila_awlen   [7:0] ,
	lcl_axi_q.awsize  [2:0]                      = ila_awsize  [2:0] ,
	lcl_axi_q.arid    [15:0]                     = ila_arid    [15:0],
	lcl_axi_q.arlen   [7:0]                      = ila_arlen   [7:0] ,
	lcl_axi_q.arsize  [2:0]                      = ila_arsize  [2:0] ,
	lcl_axi_q.rid     [15:0]                     = ila_rid     [15:0],
	lcl_axi_q.rlast                              = ila_rlast         ,
	lcl_axi_q.wlast                              = ila_wlast         ;
   end //}

   always_ff @(posedge aclk)
     trig_in_q <= trig_disable_q2 ? '0 : ((awvalid_q & ~trig_mask_q2[0]) |
					  (wvalid_q  & ~trig_mask_q2[1]) |
					  (bvalid_q  & ~trig_mask_q2[2]) |
					  (arvalid_q & ~trig_mask_q2[3]) |
					  (rvalid_q  & ~trig_mask_q2[4]));
//`ifndef SIM
if (AXI_DATA_WIDTH==32)
   ila_axi4 AXI4_ILA (
		      .clk         (aclk               ), // input wire clk
		      .trig_in     (trig_in_q          ), // input wire trig_in
		      .trig_in_ack (                   ), // output wire trig_in_ack
		      .probe0      (lcl_axi_q.awid     ), // input wire [15:0]  probe0
		      .probe1      (lcl_axi_q.awaddr   ), // input wire [63:0]  probe1
		      .probe2      (lcl_axi_q.awvalid  ), // input wire [0:0]  probe2
		      .probe3      (lcl_axi_q.awready  ), // input wire [0:0]  probe3
		      .probe4      (lcl_axi_q.awlen    ), // input wire [7:0]  probe4
		      .probe5      (lcl_axi_q.awsize   ), // input wire [2:0]  probe5
		      .probe6      (lcl_axi_q.wvalid   ), // input wire [0:0]  probe6
		      .probe7      (lcl_axi_q.wready   ), // input wire [0:0]  probe7
		      .probe8      (lcl_axi_q.wdata    ), // input wire [31:0]  probe8
		      .probe9      (lcl_axi_q.wstrb    ), // input wire [3:0]  probe9
		      .probe10     (lcl_axi_q.wlast    ), // input wire [0:0]  probe10
		      .probe11     (lcl_axi_q.bid      ), // input wire [15:0]  probe11
		      .probe12     (lcl_axi_q.bvalid   ), // input wire [0:0]  probe12
		      .probe13     (lcl_axi_q.bready   ), // input wire [0:0]  probe13
		      .probe14     (lcl_axi_q.bresp    ), // input wire [1:0]  probe14
		      .probe15     (lcl_axi_q.arid     ), // input wire [15:0]  probe15
		      .probe16     (lcl_axi_q.araddr   ), // input wire [63:0]  probe16
		      .probe17     (lcl_axi_q.arvalid  ), // input wire [0:0]  probe17
		      .probe18     (lcl_axi_q.arready  ), // input wire [0:0]  probe18
		      .probe19     (lcl_axi_q.arlen    ), // input wire [7:0]  probe19
		      .probe20     (lcl_axi_q.arsize   ), // input wire [2:0]  probe20
		      .probe21     (lcl_axi_q.rid      ), // input wire [15:0]  probe21
		      .probe22     (lcl_axi_q.rvalid   ), // input wire [0:0]  probe22
		      .probe23     (lcl_axi_q.rready   ), // input wire [0:0]  probe23
		      .probe24     (lcl_axi_q.rdata    ), // input wire [31:0]  probe24
		      .probe25     (lcl_axi_q.rresp    ), // input wire [1:0]  probe25
		      .probe26     (lcl_axi_q.rlast    )  // input wire [0:0]  probe26
		      );
else
   ila_axi4_512 AXI4_ILA (
		      .clk         (aclk               ), // input wire clk
		      .trig_in     (trig_in_q          ), // input wire trig_in
		      .trig_in_ack (                   ), // output wire trig_in_ack
		      .probe0      (lcl_axi_q.awid     ), // input wire [15:0]  probe0
		      .probe1      (lcl_axi_q.awaddr   ), // input wire [63:0]  probe1
		      .probe2      (lcl_axi_q.awvalid  ), // input wire [0:0]  probe2
		      .probe3      (lcl_axi_q.awready  ), // input wire [0:0]  probe3
		      .probe4      (lcl_axi_q.awlen    ), // input wire [7:0]  probe4
		      .probe5      (lcl_axi_q.awsize   ), // input wire [2:0]  probe5
		      .probe6      (lcl_axi_q.wvalid   ), // input wire [0:0]  probe6
		      .probe7      (lcl_axi_q.wready   ), // input wire [0:0]  probe7
		      .probe8      (lcl_axi_q.wdata    ), // input wire [511:0]  probe8
		      .probe9      (lcl_axi_q.wstrb    ), // input wire [63:0]  probe9
		      .probe10     (lcl_axi_q.wlast    ), // input wire [0:0]  probe10
		      .probe11     (lcl_axi_q.bid      ), // input wire [15:0]  probe11
		      .probe12     (lcl_axi_q.bvalid   ), // input wire [0:0]  probe12
		      .probe13     (lcl_axi_q.bready   ), // input wire [0:0]  probe13
		      .probe14     (lcl_axi_q.bresp    ), // input wire [1:0]  probe14
		      .probe15     (lcl_axi_q.arid     ), // input wire [15:0]  probe15
		      .probe16     (lcl_axi_q.araddr   ), // input wire [63:0]  probe16
		      .probe17     (lcl_axi_q.arvalid  ), // input wire [0:0]  probe17
		      .probe18     (lcl_axi_q.arready  ), // input wire [0:0]  probe18
		      .probe19     (lcl_axi_q.arlen    ), // input wire [7:0]  probe19
		      .probe20     (lcl_axi_q.arsize   ), // input wire [2:0]  probe20
		      .probe21     (lcl_axi_q.rid      ), // input wire [15:0]  probe21
		      .probe22     (lcl_axi_q.rvalid   ), // input wire [0:0]  probe22
		      .probe23     (lcl_axi_q.rready   ), // input wire [0:0]  probe23
		      .probe24     (lcl_axi_q.rdata    ), // input wire [511:0]  probe24
		      .probe25     (lcl_axi_q.rresp    ), // input wire [1:0]  probe25
		      .probe26     (lcl_axi_q.rlast    )  // input wire [0:0]  probe26
		      );

//`endif
endmodule // ila_axi4_wrapper
