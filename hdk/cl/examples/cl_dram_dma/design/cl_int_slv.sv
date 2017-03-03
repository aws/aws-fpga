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

