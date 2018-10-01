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

// C2H AXI-Stream Interface

module sde_c2h_axis #(parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact

                      parameter PCIM_DATA_WIDTH = 512,

                      parameter AXIS_DATA_WIDTH = 512,
                      
                      parameter USER_BIT_WIDTH = DESC_TYPE ? 1 : 64
                      )

   (
    input                                   clk,
    input                                   rst_n,

    // CSR to AXI-S Interface
    input                                   cfg_axis_clr_pkt_cnt,
    output logic [31:0]                     axis_cfg_pkt_cnt,
    
    // AXI-S Interface to CL
    input                                   c2h_axis_valid,
    input [AXIS_DATA_WIDTH-1:0]             c2h_axis_data,
    input [(AXIS_DATA_WIDTH>>3)-1:0]        c2h_axis_keep,
    input [USER_BIT_WIDTH-1:0]              c2h_axis_user,
    input                                   c2h_axis_last,
    output logic                            c2h_axis_ready,
    
    // AXI-S Interface to Buf
    output logic                            axis_buf_valid,
    output logic [PCIM_DATA_WIDTH-1:0]      axis_buf_data,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0] axis_buf_keep,
    output logic [USER_BIT_WIDTH-1:0]       axis_buf_user,
    output logic                            axis_buf_last,
    input                                   buf_axis_ready,

    // AXI-S Interface to Write Back block for packet Count Update
    output logic                            axis_wb_pkt_cnt_req,
    output logic [31:0]                     axis_wb_pkt_cnt
    

    );


   // Do any width conversoin necessary


   // For now, only 512 bit width is supported

   assign axis_buf_valid = c2h_axis_valid;
   assign axis_buf_data = c2h_axis_data;
   assign axis_buf_keep = c2h_axis_keep;
   assign axis_buf_user = c2h_axis_user;
   assign axis_buf_last = c2h_axis_last;
   assign c2h_axis_ready = buf_axis_ready;

   logic [31:0]                             axis_pkt_cnt;
   
   always @(posedge clk)
     if (!rst_n) begin
        axis_wb_pkt_cnt_req <= 0;
        axis_pkt_cnt <= 0;
     end
     else begin
        axis_wb_pkt_cnt_req <= c2h_axis_valid & c2h_axis_ready & c2h_axis_last;
        axis_pkt_cnt <= cfg_axis_clr_pkt_cnt ? 0 : 
                        c2h_axis_valid & c2h_axis_ready & c2h_axis_last ? axis_pkt_cnt + 1 :
                        axis_pkt_cnt;
     end

   assign axis_wb_pkt_cnt = axis_pkt_cnt;
   assign axis_cfg_pkt_cnt = axis_pkt_cnt;

endmodule // sde_c2h_axis


  

    
       
