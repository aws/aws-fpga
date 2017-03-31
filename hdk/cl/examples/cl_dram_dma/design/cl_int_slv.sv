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

module cl_int_slv (

   input clk,
   input rst_n,

   cfg_bus_t.master cfg_bus,

   input [15:0] sh_cl_apppf_irq_ack,
   output logic [15:0] cl_sh_apppf_irq_req

);

localparam NUM_CFG_STGS_INT_TST = 4;


cfg_bus_t cfg_bus_q();
    

    lib_pipe #(.WIDTH(32+32+1+1), .STAGES(NUM_CFG_STGS_INT_TST)) PIPE_SLV_REQ_INT (.clk (clk), 
                                                                .rst_n (rst_n), 
                                                                .in_bus({cfg_bus.addr, cfg_bus.wdata, cfg_bus.wr, cfg_bus.rd}),
                                                                .out_bus({cfg_bus_q.addr, cfg_bus_q.wdata, cfg_bus_q.wr, cfg_bus_q.rd})
                                                                );
    
    lib_pipe #(.WIDTH(32+1), .STAGES(NUM_CFG_STGS_INT_TST)) PIPE_SLV_ACK_INT (.clk (clk), 
                                                           .rst_n (rst_n), 
                                                           .in_bus({cfg_bus_q.ack, cfg_bus_q.rdata}),
                                                           .out_bus({cfg_bus.ack, cfg_bus.rdata})
                                                           );

//---------------------------- 
// Example block for generating IRQ and checking for ack
//---------------------------- 
    
    cl_int_tst CL_INT_TST 
    (
       .clk                 (clk),
       .rst_n               (rst_n),

       .cfg_addr            (cfg_bus_q.addr),
       .cfg_wdata           (cfg_bus_q.wdata),
       .cfg_wr              (cfg_bus_q.wr),
       .cfg_rd              (cfg_bus_q.rd),
       .tst_cfg_ack         (cfg_bus_q.ack),
       .tst_cfg_rdata       (cfg_bus_q.rdata),

       .cl_sh_irq_req       (cl_sh_apppf_irq_req),
       .sh_cl_irq_ack       (sh_cl_apppf_irq_ack)
       
    );

endmodule

