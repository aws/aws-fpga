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

// CL Interrupt Test

module cl_int_tst
   (
    input               clk,
    input               rst_n,

    input [31:0]        cfg_addr,
    input [31:0]        cfg_wdata,
    input               cfg_wr,
    input               cfg_rd,
    output logic        tst_cfg_ack,
    output logic [31:0] tst_cfg_rdata,

`ifndef NO_XDMA
    output [15:0]       cl_sh_irq_req,
    input [15:0]        sh_cl_irq_ack
`else
    output              cl_sh_msix_int,
    output [7:0]        cl_sh_msix_vec,
    input               sh_cl_msix_int_sent,
    input               sh_cl_msix_int_ack
`endif
    
    );

   logic [7:0]          cfg_vec_num;
   logic                cfg_wr_stretch;
   logic                cfg_rd_stretch;
   
   logic [7:0]          cfg_addr_q;        //Only care about lower 8-bits of address, upper bits are decoded somewhere else
   logic [31:0]         cfg_wdata_q;

   logic [31:0]         int_cfg_rdata;
   
   
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
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

   //Readback mux
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n) 
       tst_cfg_rdata <= 0;
     else
       tst_cfg_rdata <= int_cfg_rdata;
       
   //Ack for cycle
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       tst_cfg_ack <= 0;
     else
       tst_cfg_ack <= ((cfg_wr_stretch||cfg_rd_stretch) && !tst_cfg_ack); 
   
`ifndef NO_XDMA

   logic [15:0]         int_ack;
   logic [15:0]         int_trig;
   logic [15:0]         int_wait;
   logic [15:0]         int_done;
   
   // Addr 0x0 - Control Register

   // Bit 15:0  - Trigger (Write) / Interrupt Waiting (Read)
   // Bit 31:16 - Interrupt Done (W1C)
   assign int_cfg_rdata = {int_done, int_wait};
   
   lib_pipe #(.WIDTH(32), .STAGES(4)) PIPE_IN (.clk (clk), 
                                               .rst_n (rst_n), 
                                               .in_bus({int_trig, sh_cl_irq_ack}),
                                               .out_bus({cl_sh_irq_req, int_ack})
                                               );
   
   
   // Create the Edge 
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_trig <= '{default:'0};
     else
       for (int idx = 0; idx < 16; idx++) 
         int_trig[idx] <= int_trig[idx] ? 1'b0 :
                          cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) && cfg_wdata_q[idx] ? 1'b1 :
                          int_trig[idx];

   // Interrupt Waiting
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_wait <= '{default:'0};
     else
       for (int idx = 0; idx < 16; idx++) 
         int_wait[idx] <= int_trig[idx] ? 1'b1 :
                          int_wait[idx] && int_ack[idx] ? 1'b0 :
                          int_wait[idx];

   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_done <= '{default:'0};
     else
       for (int idx = 0; idx < 16; idx++) 
         int_done[idx] <= int_trig[idx] ? 1'b0 :
                          cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) && cfg_wdata_q[16+idx] ? 1'b0 : 
                          int_wait[idx] && int_ack[idx] ? 1'b1 :
                          int_done[idx];
   
   
`else // !`ifndef NO_XDMA
   
   logic                int_ack;
   logic                int_sent;
   logic                int_trig;
   logic                int_wait;
   logic                int_done;
   logic                int_not_sent;
   
   // Addr 0x0 - Control Register

   // Bit 0     - Trigger Interrupt (WO)
   // Bit 7:1   - Reserved
   // Bit 11:8  - Vector Number (RW)
   // Bit 28:12 - Reserved
   // Bit 29    - Wait for ACK  (RO)
   // Bit 30    - Sent  (W1C)
   // Bit 31    - ACK   (W1C)

   assign int_cfg_rdata = {int_done, int_not_sent, int_wait, 13'd0, cfg_vec_num[7:0], 8'd0};
   
   // Pipeline inputs
   lib_pipe #(.WIDTH(2), .STAGES(4)) PIPE_IN (.clk (clk), 
                                              .rst_n (rst_n), 
                                              .in_bus({sh_cl_msix_int_ack, sh_cl_msix_int_sent}),
                                              .out_bus({int_ack, int_sent})
                                              );


   // Pipeline outputs
   lib_pipe #(.WIDTH(8+1), .STAGES(4)) PIPE_OUT (.clk (clk), 
                                                 .rst_n (rst_n), 
                                                 .in_bus({int_trig, cfg_vec_num}),
                                                 .out_bus({cl_sh_msix_int, cl_sh_msix_vec})
                                                 );
   
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       cfg_vec_num[7:0] <= 8'd0;
     else
       cfg_vec_num[7:0] <= cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) ? cfg_wdata_q[15:8] : cfg_vec_num[7:0];

   // Create the Edge 
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_trig <= 1'b0;
     else
       int_trig <= int_trig ? 1'b0 :
                   cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) && cfg_wdata_q[0] ? 1'b1 :
                   int_trig;

   // Interrupt wait
   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_wait <= 1'b0;
     else
       int_wait <= int_trig ? 1'b1 :
                   int_ack ? 1'b0 :
                   int_wait;

   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_done <= 1'b0;
     else
       int_done <= int_trig ? 1'b0 : 
                   int_wait && int_ack ? 1'b1 :
                   cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) && cfg_wdata_q[31] ? 1'b0 :
                   int_done;

   always_ff @(negedge rst_n or posedge clk)
     if (!rst_n)
       int_not_sent <= 1'b0;
     else
       int_not_sent <= int_wait && int_ack ? ~int_sent :
                       cfg_wr_stretch && (cfg_addr_q[7:0] == 8'd0) && cfg_wdata_q[30] ? 1'b0 :
                       int_not_sent;
   
`endif // !`ifndef NO_XDMA
   
endmodule // cl_int_tst
