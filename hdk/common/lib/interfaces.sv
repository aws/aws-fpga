// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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


// Interfaces

`ifndef __INTERFACE_PKG__
`define __INTERFACE_PKG__

interface axil_bus_t #(DATA_WIDTH=32, ADDR_WIDTH=32);
   logic [ADDR_WIDTH-1:0] awaddr;
   logic                  awvalid;
   logic                  awready;

   logic [DATA_WIDTH-1:0] wdata;
   logic [(DATA_WIDTH>>3)-1:0] wstrb;
   logic                  wvalid;
   logic                  wready;

   logic [1:0]            bresp;
   logic                  bvalid;
   logic                  bready;

   logic [ADDR_WIDTH-1:0] araddr;
   logic                  arvalid;
   logic                  arready;

   logic [DATA_WIDTH-1:0] rdata;
   logic [1:0]            rresp;
   logic                  rvalid;
   logic                  rready;

   modport slave (input awaddr, awvalid, output awready,
                   input  wdata, wstrb, wvalid, output wready,
                   output bresp, bvalid, input bready,
                   input  araddr, arvalid, output arready,
                   output rdata, rresp, rvalid, input rready);

   modport master (output awaddr, awvalid, input awready,
                  output wdata, wstrb, wvalid, input wready,
                  input  bresp, bvalid, output bready,
                  output araddr, arvalid, input arready,
                  input  rdata, rresp, rvalid, output rready);
endinterface // axil_bus_t


interface cfg_bus_t #(parameter ADDR_WIDTH=32, parameter DATA_WIDTH=32, parameter USER_WIDTH=3);
   logic [ADDR_WIDTH-1:0] addr;
   logic [DATA_WIDTH-1:0] wdata;
   logic                  wr;
   logic                  rd;
   logic [USER_WIDTH-1:0] user;

   logic                  ack;
   logic [DATA_WIDTH-1:0] rdata;

   modport slave (input addr, wdata, wr, rd, user, output ack, rdata);

   modport master (output addr, wdata, wr, rd, user, input ack, rdata);
endinterface // cfg_bus_t

`endif //  `ifndef __INTERFACE_PKG__
