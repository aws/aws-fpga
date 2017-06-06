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

 
   interface axi_bus_t;
      logic[15:0] awid;
      logic[63:0] awaddr;
      logic[7:0] awlen;
      logic [2:0] awsize;
      logic awvalid;
      logic awready;
   
      logic[15:0] wid;
      logic[511:0] wdata;
      logic[63:0] wstrb;
      logic wlast;
      logic wvalid;
      logic wready;
         
      logic[15:0] bid;
      logic[1:0] bresp;
      logic bvalid;
      logic bready;
         
      logic[15:0] arid;
      logic[63:0] araddr;
      logic[7:0] arlen;
      logic [2:0] arsize;
      logic arvalid;
      logic arready;
         
      logic[15:0] rid;
      logic[511:0] rdata;
      logic[1:0] rresp;
      logic rlast;
      logic rvalid;
      logic rready;

      modport master (input awid, awaddr, awlen, awsize, awvalid, output awready,
                      input wid, wdata, wstrb, wlast, wvalid, output wready,
                      output bid, bresp, bvalid, input bready,
                      input arid, araddr, arlen, arsize, arvalid, output arready,
                      output rid, rdata, rresp, rlast, rvalid, input rready);

      modport slave (output awid, awaddr, awlen, awsize, awvalid, input awready,
                     output wid, wdata, wstrb, wlast, wvalid, input wready,
                     input bid, bresp, bvalid, output bready,
                     output arid, araddr, arlen, arsize, arvalid, input arready,
                     input rid, rdata, rresp, rlast, rvalid, output rready);
   endinterface


   interface cfg_bus_t;
      logic [31:0] addr;
      logic [31:0] wdata;
      logic wr;
      logic rd;
      logic ack;
      logic[31:0] rdata;

      modport master (input addr, wdata, wr, rd, output ack, rdata);

      modport slave (output addr, wdata, wr, rd, input ack, rdata);
   endinterface

   interface scrb_bus_t;
      logic [63:0] addr;
      logic [2:0] state;
      logic enable;
      logic done;

      modport master (input enable, output addr, state, done);

      modport slave (output enable, input addr, state, done);
   endinterface

