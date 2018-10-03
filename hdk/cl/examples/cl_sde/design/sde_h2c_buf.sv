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

// H2C Buffer

module sde_h2c_buf #(parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
                     
                     parameter PCIM_DATA_WIDTH = 512,
                     parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),

                     parameter BUF_DEPTH = 512,
                     parameter BUF_ADDR_RAM_IDX_WIDTH = $clog2(BUF_DEPTH),
                     parameter BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH,

                     parameter BUF_AUX_DEPTH = 64,
                     parameter BUF_AUX_RAM_ADDR_WIDTH = $clog2(BUF_AUX_DEPTH),

                     parameter USER_BIT_WIDTH = DESC_TYPE ? 1 : 64,
                     
                      // These are internal FIFOs - Dont change unless absolutely required
                     parameter OP_OUTPUT_FIFO_DEPTH = 3

                     )

   (
    input                                    clk,
    input                                    rst_n,

    // CSR to Buffer
    output logic                             buf_cfg_buf_oflow,
    output logic                             buf_cfg_buf_uflow,
    output logic                             buf_cfg_buf_full,
    output logic                             buf_cfg_buf_empty,
    output logic [15:0]                      buf_cfg_buf_wr_ptr ,
    output logic [15:0]                      buf_cfg_buf_rd_ptr,
    output logic                             buf_cfg_aux_fifo_oflow,
    output logic                             buf_cfg_aux_fifo_uflow,
    output logic                             buf_cfg_aux_fifo_full , 
    output logic                             buf_cfg_aux_fifo_empty,
    output logic [15:0]                      buf_cfg_aux_ram_wr_ptr,
    output logic [15:0]                      buf_cfg_aux_ram_rd_ptr, 
    output logic [15:0]                      buf_cfg_dm_wr_ptr,
    output logic [15:0]                      buf_cfg_dm_aux_wr_ptr,
    output logic [15:0]                      buf_cfg_num_free_slots,
    output logic [31:0]                      buf_cfg_in_pkt_cnt,
    output logic [31:0]                      buf_cfg_out_pkt_cnt,
    input                                    cfg_buf_clr_in_pkt_cnt,
    input                                    cfg_buf_clr_out_pkt_cnt,
    
    // AXI-S Interface to Buf
    output logic                             buf_axis_valid,
    output logic [PCIM_DATA_WIDTH-1:0]       buf_axis_data,
    output logic [(PCIM_DATA_WIDTH>>3)-1:0]  buf_axis_keep,
    output logic [USER_BIT_WIDTH-1:0]        buf_axis_user,
    output logic                             buf_axis_last,
    input                                    axis_buf_ready,
    
    
    // Buf to Data Mover
//    input logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] dm_buf_wr_ptr,
    input logic [BUF_ADDR_WIDTH-1:0]         dm_buf_wr_byte_addr,
    input logic                              dm_buf_wr_ptr_msb,
    output logic [BUF_ADDR_WIDTH:0]          buf_dm_num_bytes, // Difference in wr_byte_addr + existing read pointer

    input logic [BUF_AUX_RAM_ADDR_WIDTH-1:0] dm_buf_aux_wr_ptr,
    input logic                              dm_buf_aux_wr_ptr_msb,
    output logic                             buf_dm_aux_full,

    input                                    dm_buf_wr,
    input [PCIM_DATA_WIDTH-1:0]              dm_buf_data,
    input                                    dm_buf_eop,
    input [USER_BIT_WIDTH-1:0]               dm_buf_user,
    input [PCIM_ADDR_BYTE_IDX_WIDTH-1:0]     dm_buf_num_bytes_minus1

    );

   localparam BUF_AUX_WIDTH = DESC_TYPE ? BUF_ADDR_WIDTH : BUF_ADDR_WIDTH + USER_BIT_WIDTH;
   localparam PCIM_DATA_WIDTH_BYTES = PCIM_DATA_WIDTH >> 3;
   localparam BUF_SIZE_BYTES = BUF_DEPTH * (PCIM_DATA_WIDTH>>3);
   localparam BUF_DEPTH_MINUS1 = BUF_DEPTH - 1;
   localparam BUF_RAM_ADDR_WIDTH = BUF_ADDR_RAM_IDX_WIDTH;
   
   logic                                     buf_wr_en;
   logic                                     buf_rd_en;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]        buf_wr_ptr;
   logic                                     buf_wr_ptr_msb;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]        buf_wr_ptr_next;
   logic                                     buf_wr_ptr_msb_next;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]        buf_rd_ptr;
   logic                                     buf_rd_ptr_msb;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]        buf_rd_ptr_next;
   logic                                     buf_rd_ptr_msb_next;
   logic                                     buf_empty;
   logic                                     buf_full;
   logic                                     buf_uflow;
   logic                                     buf_oflow;
   
   assign buf_wr_en = dm_buf_wr;
   
   // Manage read and write addresses
   assign buf_wr_ptr_next = (buf_wr_ptr == BUF_DEPTH_MINUS1) ? ({BUF_ADDR_RAM_IDX_WIDTH{1'b0}}) : 
                            buf_wr_ptr + 1;
   assign buf_wr_ptr_msb_next = (buf_wr_ptr == BUF_DEPTH_MINUS1) ? ~buf_wr_ptr_msb : buf_wr_ptr_msb;
   
   assign buf_rd_ptr_next = (buf_rd_ptr == BUF_DEPTH_MINUS1) ? ({BUF_ADDR_RAM_IDX_WIDTH{1'b0}}) : 
                            buf_rd_ptr + 1;
   assign buf_rd_ptr_msb_next = (buf_rd_ptr == BUF_DEPTH_MINUS1) ? ~buf_rd_ptr_msb : buf_rd_ptr_msb;
   
   always @(posedge clk)
     if (!rst_n) begin
        buf_wr_ptr <= 0;
        buf_rd_ptr <= 0;
        buf_wr_ptr_msb <= 0;
        buf_rd_ptr_msb <= 0;
        buf_full <= 0;
        buf_empty <= 1;
        buf_uflow <= 0;
        buf_oflow <= 0;
     end
     else begin
        {buf_wr_ptr_msb, buf_wr_ptr} <= buf_wr_en ? {buf_wr_ptr_msb_next, buf_wr_ptr_next} : {buf_wr_ptr_msb, buf_wr_ptr};
        {buf_rd_ptr_msb, buf_rd_ptr} <= buf_rd_en ? {buf_rd_ptr_msb_next, buf_rd_ptr_next} : {buf_rd_ptr_msb, buf_rd_ptr};
        buf_full <= ~buf_wr_en &&  buf_rd_en ? 1'b0 :
                     buf_wr_en && ~buf_rd_en ? ({buf_wr_ptr_msb_next, buf_wr_ptr_next} == {~buf_rd_ptr_msb, buf_rd_ptr}) :
                    buf_full;
        buf_empty <=  buf_wr_en && ~buf_rd_en ? 1'b0 :
                     ~buf_wr_en &&  buf_rd_en ? ({buf_wr_ptr_msb, buf_wr_ptr} == {buf_rd_ptr_msb_next, buf_rd_ptr_next}) :
                      buf_empty;
        buf_uflow <= buf_empty & buf_rd_en;
        buf_oflow <= buf_full & buf_wr_en;
     end // else: !if(!rst_n)
   assign buf_cfg_buf_oflow = buf_oflow;
   assign buf_cfg_buf_uflow = buf_uflow;
   assign buf_cfg_buf_full  = buf_full;
   assign buf_cfg_buf_empty = buf_empty;
   always_comb begin
      buf_cfg_buf_wr_ptr = 0;
      buf_cfg_buf_rd_ptr = 0;
      buf_cfg_buf_wr_ptr = buf_wr_ptr;
      buf_cfg_buf_rd_ptr = buf_rd_ptr;
      buf_cfg_buf_wr_ptr[15] = buf_wr_ptr_msb;
      buf_cfg_buf_rd_ptr[15] = buf_rd_ptr_msb;
   end

   logic buf_ram_wr;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] buf_ram_waddr;
   logic [PCIM_DATA_WIDTH-1:0]        buf_ram_wdata;
   logic                              buf_ram_rd;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] buf_ram_raddr;
   logic [PCIM_DATA_WIDTH-1:0]        buf_ram_rdata;
   
   // Buffer BRAM
   assign buf_ram_wr    = buf_wr_en;
   assign buf_ram_waddr = buf_wr_ptr;
   assign buf_ram_wdata = dm_buf_data;

   assign buf_ram_rd    = buf_rd_en;
   assign buf_ram_raddr = buf_rd_ptr;
   
   // Desc RAM - Using 2 port RAM (1w1r)
   bram_1w1r #(.WIDTH(PCIM_DATA_WIDTH), 
               .ADDR_WIDTH(BUF_RAM_ADDR_WIDTH),
               .DEPTH(BUF_DEPTH)
               ) BUF_RAM (.clk      (clk),
                           .wea      (1'b1),
                           .ena      (buf_ram_wr),
                           .addra    (buf_ram_waddr),
                           .da       (buf_ram_wdata),

                           .enb      (buf_ram_rd),
                           .addrb    (buf_ram_raddr),
                           .qb       (buf_ram_rdata)
                           );

   localparam BUF_AUX_RAM_WIDTH = BUF_AUX_WIDTH;
   localparam BUF_AUX_RAM_DEPTH = BUF_AUX_DEPTH;
//   localparam BUF_AUX_RAM_ADDR_WIDTH = $clog2(BUF_AUX_RAM_DEPTH);
   localparam BUF_AUX_RAM_DEPTH_MINUS1 = BUF_AUX_RAM_DEPTH - 1;

   logic                               aux_ram_wr;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_waddr;
   logic [BUF_AUX_RAM_WIDTH-1:0]       aux_ram_wdata;
   logic                               aux_ram_rd;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_raddr;
   logic [BUF_AUX_RAM_WIDTH-1:0]       aux_ram_rdata;

   logic                               aux_ram_empty;
   logic                               aux_ram_full;
   logic                               aux_ram_pop;
   logic                               aux_ram_oflow;
   logic                               aux_fifo_uflow;
   
   logic                               aux_ft_ff_pop;
   logic                               aux_ft_ff_valid;
   logic [BUF_AUX_RAM_WIDTH-1:0]       aux_ft_ff_data;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_wr_ptr_next;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_rd_ptr_next;
   logic                               aux_ram_wr_ptr_msb_next;
   logic                               aux_ram_rd_ptr_msb_next;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_wr_ptr;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_rd_ptr;
   logic                               aux_ram_wr_ptr_msb;
   logic                               aux_ram_rd_ptr_msb;
   logic [USER_BIT_WIDTH-1:0]          aux_out_user;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0]  aux_out_eop_wr_ptr;
   logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] aux_out_num_bytes_minus1;
   logic                                aux_out_valid;
   
   logic                                op_stall;
   
   // AUX FT FIFO 
   assign aux_ram_wr = buf_wr_en & dm_buf_eop;
   assign aux_ram_waddr = aux_ram_wr_ptr;
   assign aux_ram_wdata = DESC_TYPE ? {buf_wr_ptr, dm_buf_num_bytes_minus1} : 
                          {dm_buf_user, buf_wr_ptr, dm_buf_num_bytes_minus1};

   assign aux_ram_rd = aux_ram_pop;
   assign aux_ram_raddr = aux_ram_rd_ptr;
   
   // AUX RAM
   bram_1w1r #(.WIDTH(BUF_AUX_RAM_WIDTH),
               .ADDR_WIDTH(BUF_AUX_RAM_ADDR_WIDTH),
               .DEPTH (BUF_AUX_RAM_DEPTH)
               ) AUX_RAM (.clk      (clk),
                          .wea      (1'b1),
                          .ena      (aux_ram_wr),
                          .addra    (aux_ram_waddr),
                          .da       (aux_ram_wdata),
                          
                          .enb      (aux_ram_rd),
                          .addrb    (aux_ram_raddr),
                          .qb       (aux_ram_rdata)
                          );

   // Flow-through FIFO 
   ft_fifo #(.FIFO_WIDTH(BUF_AUX_RAM_WIDTH)
             ) AUX_FT_FIFO (.clk         (clk),
                             .rst_n       (1'b1),
                             .sync_rst_n  (rst_n),
                             .ram_fifo_empty (aux_ram_empty),
                             .ram_fifo_data  (aux_ram_rdata),
                             .ram_pop        (aux_ram_pop),
                             
                             .ft_pop   (aux_ft_ff_pop),
                             .ft_valid (aux_ft_ff_valid),
                             .ft_data  (aux_ft_ff_data)
                             );

   assign aux_ram_wr_ptr_next = (aux_ram_wr_ptr == BUF_AUX_RAM_DEPTH_MINUS1) ? ({BUF_AUX_RAM_ADDR_WIDTH{1'b0}}) :
                                aux_ram_wr_ptr + 1;
   assign aux_ram_wr_ptr_msb_next = (aux_ram_wr_ptr == BUF_AUX_RAM_DEPTH_MINUS1) ? ~aux_ram_wr_ptr_msb : aux_ram_wr_ptr_msb;
   
   assign aux_ram_rd_ptr_next = (aux_ram_rd_ptr == BUF_AUX_RAM_DEPTH_MINUS1) ? ({BUF_AUX_RAM_ADDR_WIDTH{1'b0}}) :
                                aux_ram_rd_ptr + 1;
   assign aux_ram_rd_ptr_msb_next = (aux_ram_rd_ptr == BUF_AUX_RAM_DEPTH_MINUS1) ? ~aux_ram_rd_ptr_msb : aux_ram_rd_ptr_msb;
   
   always @(posedge clk)
     if (!rst_n) begin
        aux_ram_wr_ptr <= 0;
        aux_ram_rd_ptr <= 0;
        aux_ram_wr_ptr_msb <= 0;
        aux_ram_rd_ptr_msb <= 0;
        aux_ram_empty <= 1;
        aux_ram_full <= 0;
        aux_ram_oflow <= 0;
        aux_fifo_uflow <= 0;
     end
     else begin
        {aux_ram_wr_ptr_msb, aux_ram_wr_ptr} <= aux_ram_wr ? {aux_ram_wr_ptr_msb_next, aux_ram_wr_ptr_next} : {aux_ram_wr_ptr_msb, aux_ram_wr_ptr};
        {aux_ram_rd_ptr_msb, aux_ram_rd_ptr} <= aux_ram_pop ? {aux_ram_rd_ptr_msb_next, aux_ram_rd_ptr_next} : {aux_ram_rd_ptr_msb, aux_ram_rd_ptr};
        aux_ram_empty <= aux_ram_wr && ~aux_ram_pop ? 1'b0 :
                         ~aux_ram_wr && aux_ram_pop ? ({aux_ram_wr_ptr_msb, aux_ram_wr_ptr} == {aux_ram_rd_ptr_msb_next, aux_ram_rd_ptr_next}) :
                         aux_ram_empty;
        aux_ram_full <= ~aux_ram_wr &&  aux_ram_pop ? 1'b0 :
                        aux_ram_wr  && ~aux_ram_pop ? (aux_ram_wr_ptr_msb_next != aux_ram_rd_ptr_msb) && (aux_ram_wr_ptr_next == aux_ram_rd_ptr) :
                        aux_ram_full;
        
        aux_ram_oflow <= aux_ram_full & aux_ram_wr;
        aux_fifo_uflow <= ~aux_ft_ff_valid & aux_ft_ff_pop;
     end // else: !if(!rst_n)

   assign buf_cfg_aux_fifo_oflow = aux_ram_oflow;
   assign buf_cfg_aux_fifo_uflow = aux_fifo_uflow;
   assign buf_cfg_aux_fifo_full  = aux_ram_full;
   assign buf_cfg_aux_fifo_empty = ~aux_ft_ff_valid;

   always_comb begin
      buf_cfg_aux_ram_wr_ptr = 0;
      buf_cfg_aux_ram_wr_ptr = aux_ram_wr_ptr;
      buf_cfg_aux_ram_wr_ptr[15] = aux_ram_wr_ptr_msb;
   
      buf_cfg_aux_ram_rd_ptr = 0;
      buf_cfg_aux_ram_rd_ptr = aux_ram_rd_ptr;
      buf_cfg_aux_ram_rd_ptr[15] = aux_ram_rd_ptr_msb;
   end

   assign {aux_out_user,
           aux_out_eop_wr_ptr,
           aux_out_num_bytes_minus1} = aux_ft_ff_data;
   assign aux_out_valid = aux_ft_ff_valid;
   
   // Output Pipeline
   // Stage 0
   // Read data from Buffer when buffer is not empty and no output stall
   assign buf_rd_en = ~buf_empty & ~op_stall;

   logic stg0_op_valid;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] stg0_op_buf_rd_addr;
   logic pl0_op_valid;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] pl0_op_buf_rd_addr;
   
   assign stg0_op_valid = buf_rd_en;
   assign stg0_op_buf_rd_addr = buf_rd_ptr;

   always @(posedge clk)
     if (!rst_n) begin
        pl0_op_valid <= 0;
        pl0_op_buf_rd_addr <= '{default:'0};
     end
     else begin
        pl0_op_valid <= stg0_op_valid;
        pl0_op_buf_rd_addr <= stg0_op_buf_rd_addr;
     end

   // Stage 1 - Get RAM Data
   logic stg1_op_valid;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] stg1_op_buf_rd_addr;
   logic [PCIM_DATA_WIDTH-1:0]        stg1_op_data;
   logic                              stg1_op_ovf;
   logic [PCIM_DATA_WIDTH-1:0]        stg1_op_ovf_data;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] stg1_op_ovf_buf_rd_addr;

   logic pl1_op_valid;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] pl1_op_buf_rd_addr;
   logic [PCIM_DATA_WIDTH-1:0]        pl1_op_data;
   logic                              pl1_op_ovf;
   logic [PCIM_DATA_WIDTH-1:0]        pl1_op_ovf_data;
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] pl1_op_ovf_buf_rd_addr;
   
   assign stg1_op_valid = pl0_op_valid || pl1_op_ovf;
   assign stg1_op_data = pl1_op_ovf ? pl1_op_ovf_data : buf_ram_rdata;
   assign stg1_op_buf_rd_addr = pl1_op_ovf ? pl1_op_ovf_buf_rd_addr : pl0_op_buf_rd_addr;

   assign stg1_op_ovf = pl0_op_valid & op_stall ? 1'b1 :
                        ~op_stall ? 1'b0 : pl1_op_ovf;
   assign stg1_op_ovf_data = pl0_op_valid & op_stall ? buf_ram_rdata : pl1_op_ovf_data;
   assign stg1_op_ovf_buf_rd_addr = pl0_op_valid & op_stall ? pl0_op_buf_rd_addr : pl1_op_ovf_buf_rd_addr;
   
   always @(posedge clk)
     if (!rst_n) begin
        pl1_op_valid <= 0;
        pl1_op_data <= 0;
        pl1_op_buf_rd_addr <= 0;

        pl1_op_ovf <= 0;
        pl1_op_ovf_data <= 0;
        pl1_op_ovf_buf_rd_addr <= 0;
     end
     else begin
        pl1_op_valid <= ~op_stall ? stg1_op_valid : pl1_op_valid;
        pl1_op_data <= ~op_stall ? stg1_op_data : pl1_op_data;
        pl1_op_buf_rd_addr <= ~op_stall ? stg1_op_buf_rd_addr : pl1_op_buf_rd_addr;

        pl1_op_ovf <= stg1_op_ovf;
        pl1_op_ovf_data <= stg1_op_ovf_data;
        pl1_op_ovf_buf_rd_addr <= stg1_op_ovf_buf_rd_addr;
     end // else: !if(!rst_n)

   // Stage 3 - Adding another stage to account for latency in aux ft fifo
   logic                              stg2_op_valid;
   logic [PCIM_DATA_WIDTH-1:0]        stg2_op_data;
   logic                              stg2_op_eop;
   logic [USER_BIT_WIDTH-1:0]         stg2_op_user;
   logic [PCIM_DATA_WIDTH_BYTES-1:0]  stg2_op_keep_last;
   logic [PCIM_DATA_WIDTH_BYTES-1:0]  stg2_op_keep;

   logic                              pl2_op_valid;
   logic [PCIM_DATA_WIDTH-1:0]        pl2_op_data;
   logic                              pl2_op_eop;
   logic [USER_BIT_WIDTH-1:0]         pl2_op_user;
   logic [PCIM_DATA_WIDTH_BYTES-1:0]  pl2_op_keep;

   assign stg2_op_valid = pl1_op_valid;
   assign stg2_op_data = pl1_op_data;
   assign stg2_op_eop = aux_out_valid && (aux_out_eop_wr_ptr == pl1_op_buf_rd_addr);
   assign stg2_op_user = aux_out_user;
   always_comb begin
      stg2_op_keep_last = '{default:'0};
      for (int byte_idx = 0; byte_idx < PCIM_DATA_WIDTH_BYTES; byte_idx++)
        if (byte_idx <= aux_out_num_bytes_minus1)
          stg2_op_keep_last[byte_idx]  = 1;
   end
   assign stg2_op_keep = stg2_op_eop ? stg2_op_keep_last : ({PCIM_DATA_WIDTH_BYTES{1'b1}});
   
   assign aux_ft_ff_pop = aux_ft_ff_valid & stg2_op_valid & stg2_op_eop & ~op_stall;

   always @(posedge clk)
     if (!rst_n) begin
        pl2_op_valid <= 0;
        pl2_op_data <= 0;
        pl2_op_eop <= 0;
        pl2_op_user <= 0;
        pl2_op_keep <= 0;
     end
     else begin
        pl2_op_valid <= ~op_stall ? stg2_op_valid : pl2_op_valid;
        pl2_op_data <= ~op_stall ? stg2_op_data : pl2_op_data;
        pl2_op_eop <= ~op_stall ? stg2_op_eop : pl2_op_eop;
        pl2_op_user <= ~op_stall ? stg2_op_user : pl2_op_user;
        pl2_op_keep <= ~op_stall ? stg2_op_keep : pl2_op_keep;
     end // else: !if(!rst_n)

   // Output FIFO
   localparam OP_OUTPUT_FIFO_WIDTH = DESC_TYPE ? PCIM_DATA_WIDTH + 1 + PCIM_DATA_WIDTH_BYTES : 
                                     PCIM_DATA_WIDTH + 1 + PCIM_DATA_WIDTH_BYTES + USER_BIT_WIDTH;
   localparam OP_OUTPUT_FIFO_DEPTH_MINUS1 = OP_OUTPUT_FIFO_DEPTH - 1;
   
   logic op_out_ff_push;
   logic [OP_OUTPUT_FIFO_WIDTH-1:0] op_out_ff_push_data;
   logic                            op_out_ff_pop;
   logic [OP_OUTPUT_FIFO_WIDTH-1:0] op_out_ff_pop_data;
   logic                            op_out_ff_full;
   logic                            op_out_ff_valid;
   
   assign op_out_ff_push = pl2_op_valid & ~op_stall;
   assign op_out_ff_push_data = DESC_TYPE ? {pl2_op_data, pl2_op_eop, pl2_op_keep} :
                                {pl2_op_user, pl2_op_data, pl2_op_eop, pl2_op_keep};
   
   flop_fifo #(.WIDTH(OP_OUTPUT_FIFO_WIDTH),
               .DEPTH(OP_OUTPUT_FIFO_DEPTH)
               ) OP_OUTPUT_FIFO (.clk         (clk),
                                 .rst_n       (1'b1),
                                 .sync_rst_n  (rst_n),
                                 .cfg_watermark (OP_OUTPUT_FIFO_DEPTH_MINUS1),
                                      .push        (op_out_ff_push),
                                      .push_data   (op_out_ff_push_data),
                                      .pop         (op_out_ff_pop),
                                      .pop_data    (op_out_ff_pop_data),
                                      .half_full   (),
                                      .watermark   (op_out_ff_full),
                                      .data_valid  (op_out_ff_valid)
                                      );

   assign op_stall = op_out_ff_full;

   assign op_out_ff_pop = op_out_ff_valid & axis_buf_ready;

   assign buf_axis_valid = op_out_ff_valid;
   always_comb
     if (DESC_TYPE)
       {buf_axis_data, buf_axis_last, buf_axis_keep} = op_out_ff_pop_data;
     else
       {buf_axis_user, buf_axis_data, buf_axis_last, buf_axis_keep} = op_out_ff_pop_data;
   
   // Logic to compute num_bytes for dm
   // Difference between dm_buf_wr_byte_addr and buf_rd_ptr
   logic [BUF_ADDR_RAM_IDX_WIDTH-1:0] buf_wr_ptr_in;
   logic                              buf_wr_ptr_msb_in;
   logic [BUF_ADDR_RAM_IDX_WIDTH:0]   buf_wr_ptr_in_plus_depth;
   logic [BUF_ADDR_RAM_IDX_WIDTH:0]   buf_rd_ptr_plus_depth;
   logic [BUF_ADDR_RAM_IDX_WIDTH:0]   buf_ptr_diff;
   logic                              buf_ptr_eq;
   logic                              buf_ptr_msb_eq;
   logic [BUF_ADDR_RAM_IDX_WIDTH:0]   buf_free_slots;
   logic [BUF_ADDR_RAM_IDX_WIDTH:0]   buf_free_slots_q;

//   assign buf_wr_ptr_in = dm_buf_wr_ptr[0 +: BUF_ADDR_RAM_IDX_WIDTH];
   assign buf_wr_ptr_in = dm_buf_wr_byte_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH];
   assign buf_wr_ptr_msb_in = dm_buf_wr_ptr_msb;

   assign buf_wr_ptr_in_plus_depth = buf_wr_ptr_in + BUF_DEPTH;
   assign buf_rd_ptr_plus_depth = buf_rd_ptr + BUF_DEPTH;

   assign buf_ptr_diff = (buf_wr_ptr_in > buf_rd_ptr) ? (buf_rd_ptr_plus_depth - buf_wr_ptr_in) :
                         (buf_rd_ptr - buf_wr_ptr_in);

   assign buf_ptr_eq = (buf_wr_ptr_in == buf_rd_ptr);
   assign buf_ptr_msb_eq = (buf_wr_ptr_msb_in == buf_rd_ptr_msb);
   
   // When pointers are not equal, for example - 
   // For case where rd_ptr is greater than wr_ptr, the actual ptr difference is
   // ptr_diff = rd_ptr - wr_ptr.
   // But the wr_ptr will not move even if the data mover writes less than 0x40 bytes.
   // Say, if the wr_byte_addr is at 0x10, the number of free bytes is equal to 0x30.
   // But the logic will report 0x40 with above logic. Therefore, subtracting by 1 to be safe.
   // ptr_diff = rd_ptr - wr_ptr - 1
   // When this is done, if the wr_byte_addr is 0x10, the number of free bytes reported will be 0x0   
   assign buf_free_slots = buf_ptr_eq & buf_ptr_msb_eq ? BUF_DEPTH_MINUS1 :
                           buf_ptr_eq & ~buf_ptr_msb_eq ? 0 :
                           buf_ptr_diff - 1;

//   assign buf_dm_num_bytes = {buf_free_slots, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};

   logic [BUF_ADDR_WIDTH-1:0]         buf_wr_byte_addr;
   logic [BUF_ADDR_WIDTH-1:0]         buf_rd_byte_addr;
   logic [BUF_ADDR_WIDTH:0]           buf_rd_byte_addr_plus_depth;
   logic [BUF_ADDR_WIDTH:0]           buf_byte_addr_diff;
   
   assign buf_wr_byte_addr = dm_buf_wr_byte_addr;
   assign buf_rd_byte_addr = {buf_rd_ptr, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
   assign buf_rd_byte_addr_plus_depth = {buf_rd_ptr_plus_depth, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
   assign buf_byte_addr_diff = (buf_wr_byte_addr > buf_rd_byte_addr) ? buf_rd_byte_addr_plus_depth - buf_wr_byte_addr :
                               buf_rd_byte_addr - buf_wr_byte_addr;
   assign buf_dm_num_bytes = (buf_wr_byte_addr == buf_rd_byte_addr) & buf_ptr_msb_eq ? BUF_SIZE_BYTES :
                             (buf_wr_byte_addr == buf_rd_byte_addr) & ~buf_ptr_msb_eq ? 0 :
                             buf_byte_addr_diff;
   

   // Logic to compute aux fifo full
   assign buf_dm_aux_full = (dm_buf_aux_wr_ptr == aux_ram_rd_ptr) && (dm_buf_aux_wr_ptr_msb != aux_ram_rd_ptr_msb);

   always @(posedge clk)
     if (!rst_n)
       buf_free_slots_q <= 0;
     else
       buf_free_slots_q <= buf_free_slots;

   always_comb begin
      buf_cfg_dm_wr_ptr = 0;
//      buf_cfg_dm_wr_ptr = dm_buf_wr_ptr[0 +: BUF_ADDR_RAM_IDX_WIDTH];
      buf_cfg_dm_wr_ptr = dm_buf_wr_byte_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH];
      buf_cfg_dm_wr_ptr[15] = dm_buf_wr_ptr_msb;

      buf_cfg_dm_aux_wr_ptr = 0;
      buf_cfg_dm_aux_wr_ptr = dm_buf_aux_wr_ptr;
      buf_cfg_dm_aux_wr_ptr[15] = dm_buf_aux_wr_ptr_msb;

      buf_cfg_num_free_slots = 0;
      buf_cfg_num_free_slots = buf_free_slots_q;
   end // always_comb
   
   always @(posedge clk)
     if (!rst_n) begin
        buf_cfg_in_pkt_cnt <= 0;
        buf_cfg_out_pkt_cnt <= 0;
     end
     else begin
        buf_cfg_in_pkt_cnt <= cfg_buf_clr_in_pkt_cnt ? 0 : 
                              dm_buf_wr & dm_buf_eop ? buf_cfg_in_pkt_cnt + 1 : buf_cfg_in_pkt_cnt;
        buf_cfg_out_pkt_cnt <= cfg_buf_clr_out_pkt_cnt ? 0 :
                               buf_axis_valid & buf_axis_last & axis_buf_ready ? buf_cfg_out_pkt_cnt + 1 : buf_cfg_out_pkt_cnt;
     end // else: !if(!rst_n)

 `ifndef NO_SDE_DEBUG_ILA
 
   
ila_sde_h2c_buf ILA_SDE_H2C_BUF
  (
   .clk (clk),

   // 0 - 7
   .probe0(buf_axis_valid),
   .probe1(buf_axis_last),
   .probe2(axis_buf_ready),
   .probe3(dm_buf_wr_ptr),
   .probe4(dm_buf_wr_ptr_msb),
   .probe5(buf_dm_num_bytes),
   .probe6(dm_buf_aux_wr_ptr),
   .probe7(dm_buf_aux_wr_ptr_msb),

   // 8 - 15
   .probe8(buf_dm_aux_full),
   .probe9(dm_buf_wr),
   .probe10(dm_buf_eop),
   .probe11(buf_wr_ptr),
   .probe12(buf_wr_ptr_msb),
   .probe13(buf_rd_ptr),
   .probe14(buf_rd_ptr_msb),
   .probe15( buf_empty),

   // 16- 23
   .probe16(buf_full),
   .probe17(aux_ram_empty),
   .probe18(aux_ram_full),
   .probe19(aux_ram_wr_ptr),
   .probe20(aux_ram_rd_ptr),
   .probe21(aux_ram_wr_ptr_msb),
   .probe22(aux_ram_rd_ptr_msb),
   .probe23(op_out_ff_full),

   // 24 - 31   
   .probe24(op_out_ff_valid),
   .probe25(buf_wr_ptr_in_plus_depth),
   .probe26(buf_rd_ptr_plus_depth),
   .probe27(buf_ptr_diff),
   .probe28(buf_free_slots)

   );

 `endif //  `ifndef NO_SDE_DEBUG_ILA
   
endmodule // sde_h2c_buf
