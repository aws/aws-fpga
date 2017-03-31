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

module axil_slave (
   input clk,
   input rst_n,

   input awvalid,                                                                    
   input[63:0] awaddr,                                                               
   output logic awready,                                                                           
   
   //Write data                                                                                    
   input wvalid,                                                                     
   input[31:0] wdata,                                                                
   input[3:0] wstrb,                                                                 
   output logic wready,                                                                            
 
   //Write response                                                                                
   output logic bvalid,                                                                            
   output logic[1:0] bresp,
   input bready,
                                                                                                   
   //Read address
   input arvalid,                                                                    
   input[63:0] araddr,                                                               
   output logic arready,
                                                                                                   
   //Read data/response
   output logic rvalid,                                                                            
   output logic[31:0] rdata,
   output logic[1:0] rresp,
                                                                                                   
   input rready
);

logic[63:0] awaddr_q;
logic arvalid_q;

// Does not work when awvalid and wvalid are asserted at the same time   
//assign awready = !wvalid;
//assign wready = !arvalid;
//
//always_ff @(negedge rst_n or posedge clk)
//   if (!rst_n)
//      awaddr_q <= 0;
//   else if (awvalid && awready)
//      awaddr_q <= awaddr;
//                    
//always_ff @(negedge rst_n or posedge clk)
//   if (!rst_n)
//   begin
//      bvalid <= 0;
//      bresp <= 0;
//   end
//   else
//   begin
//      bvalid <= wvalid && wready;
//      bresp <= 0;
//   end


   logic wr_active;
   logic [63:0] wr_addr;
   
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n) begin
        wr_active <= 0;
        wr_addr <= 0;
     end
     else begin
        wr_active <= wr_active && bvalid && bready ? 1'b0 :
                     awvalid && ~wr_active ? 1'b1 :
                     wr_active;
        wr_addr <= awvalid && ~wr_active ? awaddr : wr_addr;
     end

   assign awready = ~wr_active;
   assign wready = wr_active && wvalid;
   
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n) 
       bvalid <= 0;
     else
       bvalid <= bvalid && bready ? 1'b0 : 
                 ~bvalid && wready ? 1'b1 :
                 bvalid;
   assign bresp = 0;
   
assign arready = !arvalid_q && !rvalid;
   
always_ff @(negedge rst_n or posedge clk)
   if (!rst_n)
      arvalid_q <= 0;
   else
      arvalid_q <= arvalid;

logic[31:0] ram_rdata;

always_ff @(negedge rst_n or posedge clk)
   if (!rst_n)
   begin
      rvalid <= 0;
      rdata <= 0;
      rresp <= 0;
   end
   else if (rvalid && rready)
   begin
      rvalid <= 0;
      rdata <= 0;
      rresp <= 0;
   end
   else if (arvalid_q) 
   begin
      rvalid <= 1;
      rdata <= ram_rdata;
      rresp <= 0;
   end

bram_2rw #(.WIDTH(32), .ADDR_WIDTH(8), .DEPTH(256) ) AXIL_RAM (
   .clk(clk),
//   .wea(wvalid),
//   .ena(wvalid),
//   .addra(awaddr_q[10:2]),
//   .da(wdata),
   .wea(wready),
   .ena(wready),
   .addra(wr_addr[9:2]),
   .da(wdata),

   .qa(),

   .web(1'b0),
   .enb(arvalid),
   .addrb(araddr[9:2]),
   .db(32'h0),
   .qb(ram_rdata)
   );

endmodule

   
