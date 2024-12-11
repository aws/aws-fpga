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

`ifndef CL_DRAM_DMA_PKG
`define CL_DRAM_DMA_PKG

interface axi_bus_t #(DATA_WIDTH=512, ADDR_WIDTH=64, ID_WIDTH=16, LEN_WIDTH=8);
   logic [ID_WIDTH-1:0]   awid;
   logic [ADDR_WIDTH-1:0] awaddr;
   logic [LEN_WIDTH-1:0]  awlen;
   logic [2:0]            awsize;
   logic                  awvalid;
   logic                  awready;
   logic [1:0]            awburst;

   logic [ID_WIDTH-1:0]   wid;
   logic [DATA_WIDTH-1:0] wdata;
   logic [DATA_WIDTH/8-1:0] wstrb;
   logic                  wlast;
   logic                  wvalid;
   logic                  wready;

   logic [ID_WIDTH-1:0]   bid;
   logic [1:0]            bresp;
   logic                  bvalid;
   logic                  bready;

   logic [ID_WIDTH-1:0]   arid;
   logic [ADDR_WIDTH-1:0] araddr;
   logic [LEN_WIDTH-1:0]  arlen;
   logic [2:0]            arsize;
   logic                  arvalid;
   logic                  arready;
   logic [1:0]            arburst;

   logic [ID_WIDTH-1:0]   rid;
   logic [DATA_WIDTH-1:0] rdata;
   logic [1:0]            rresp;
   logic                  rlast;
   logic                  rvalid;
   logic                  rready;

   modport master (input awid, awaddr, awlen, awsize, awvalid, awburst, output awready,
                   input  wid, wdata, wstrb, wlast, wvalid, output wready,
                   output bid, bresp, bvalid, input bready,
                   input  arid, araddr, arlen, arsize, arvalid, arburst, output arready,
                   output rid, rdata, rresp, rlast, rvalid, input rready);

   modport slave (output awid, awaddr, awlen, awsize, awvalid, awburst, input awready,
                  output wid, wdata, wstrb, wlast, wvalid, input wready,
                  input  bid, bresp, bvalid, output bready,
                  output arid, araddr, arlen, arsize, arvalid, arburst, input arready,
                  input  rid, rdata, rresp, rlast, rvalid, output rready);
endinterface

interface scrb_bus_t;
   logic [63:0]          addr;
   logic [2:0]           state;
   logic                 enable;
   logic                 done;

   modport master (input enable, output addr, state, done);

   modport slave (output enable, input addr, state, done);
endinterface

`endif //CL_DRAM_DMA_PKG
