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

// C2H Buffer

module sde_c2h_buf #(parameter bit DESC_TYPE = 0,  // 0 - Regular, 1 - Compact
                     
                     parameter PCIM_DATA_WIDTH = 512,
                     parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),

                     parameter BUF_DEPTH = 512, // Should be a power of 2
                     parameter BUF_ADDR_RAM_IDX_WIDTH = $clog2(BUF_DEPTH),
                     parameter BUF_ADDR_WIDTH = PCIM_ADDR_BYTE_IDX_WIDTH + BUF_ADDR_RAM_IDX_WIDTH,

                     parameter USER_BIT_WIDTH = DESC_TYPE ? 1 : 64,
                     parameter BUF_AUX_WIDTH = BUF_ADDR_WIDTH + USER_BIT_WIDTH,
                     
                      // These are internal FIFOs - Dont change unless absolutely required
                     parameter BUF_AUX_FT_FIFO_DEPTH = 64
                     )

   (
    input                              clk,
    input                              rst_n,

    // CSR to Buffer
    output logic                       buf_cfg_buf_oflow,
    output logic                       buf_cfg_buf_uflow,
    output logic                       buf_cfg_buf_full,
    output logic                       buf_cfg_buf_empty,
    output logic [15:0]                buf_cfg_buf_wr_ptr ,
    output logic [15:0]                buf_cfg_buf_rd_addr,
    output logic                       buf_cfg_aux_fifo_oflow,
    output logic                       buf_cfg_aux_fifo_uflow,
    output logic                       buf_cfg_aux_fifo_full , 
    output logic                       buf_cfg_aux_fifo_empty,
    output logic [15:0]                buf_cfg_aux_ram_wr_ptr,
    output logic [15:0]                buf_cfg_aux_ram_rd_ptr,    
    output logic [15:0]                buf_cfg_num_bytes,
    output logic [31:0]                buf_cfg_in_pkt_cnt,
    output logic [31:0]                buf_cfg_out_pkt_cnt,
    input                              cfg_buf_clr_in_pkt_cnt,
    input                              cfg_buf_clr_out_pkt_cnt,
    
    // AXI-S Interface to Buf
    input                              axis_buf_valid,
    input [PCIM_DATA_WIDTH-1:0]        axis_buf_data,
    input [(PCIM_DATA_WIDTH>>3)-1:0]   axis_buf_keep,
    input [USER_BIT_WIDTH-1:0]         axis_buf_user,
    input                              axis_buf_last,
    output logic                       buf_axis_ready,
    
    
    // Buf to Data Mover
    output logic                       buf_dm_aux_valid,
    output logic [BUF_AUX_WIDTH-1:0]   buf_dm_aux_data,
    input                              dm_buf_aux_pop,
    
    input [BUF_ADDR_WIDTH-1:0]         dm_buf_rd_byte_addr,

    output logic [BUF_ADDR_WIDTH:0]    buf_dm_num_bytes, // Difference in pointers + plus num of bytes in last beat
    
    input                              dm_buf_rd,
    input [BUF_ADDR_RAM_IDX_WIDTH-1:0] dm_buf_addr,
    output logic [PCIM_DATA_WIDTH-1:0] buf_dm_data


    );

   localparam PCIM_DATA_WIDTH_BYTES = PCIM_DATA_WIDTH>>3;
   localparam BUF_DEPTH_MINUS1 = BUF_DEPTH - 1;
   localparam BUF_RAM_ADDR_WIDTH = BUF_ADDR_RAM_IDX_WIDTH;

   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_wr_ptr_next;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_wr_ptr;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_rd_ptr;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_rd_ptr_q;
   
   logic                                   buf_write_en;

   logic                                   buf_full;
   logic                                   buf_oflow;
   logic                                   buf_uflow;
   logic                                   buf_empty;
   
   logic                                   buf_ram_wr;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_ram_waddr;
   logic [PCIM_DATA_WIDTH-1:0]             buf_ram_wdata;
   logic                                   buf_ram_rd;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_ram_raddr;
   logic [PCIM_DATA_WIDTH-1:0]             buf_ram_rdata;

   logic                                   aux_ram_full;
   logic                                   aux_ram_oflow;
   logic                                   aux_fifo_uflow;
   
   assign buf_wr_ptr_next = (buf_wr_ptr >= BUF_DEPTH_MINUS1) ? 0 : buf_wr_ptr + 1;

   assign buf_rd_ptr = dm_buf_rd_byte_addr[PCIM_ADDR_BYTE_IDX_WIDTH +: BUF_ADDR_RAM_IDX_WIDTH];

   assign buf_write_en = axis_buf_valid & ~buf_full & ~aux_ram_full;

   // Buffer Write Pointer
   always @(posedge clk)
     if (!rst_n) begin
        buf_wr_ptr <= '{default:'0};
        buf_full <= 0;
        buf_empty <= 0;
        
        buf_rd_ptr_q <= 0;        
        buf_oflow <= 0;
        buf_uflow <= 0;
     end   
     else begin
        buf_wr_ptr <= buf_write_en ? buf_wr_ptr_next : buf_wr_ptr;
        buf_full <= buf_write_en ?  (buf_wr_ptr_next == buf_rd_ptr) :
                    buf_full & (buf_wr_ptr != buf_rd_ptr) ? 1'b0 :
                    buf_full;
        buf_empty <= ~buf_write_en & ~buf_full & (buf_wr_ptr == buf_rd_ptr) ? 1'b1 :
                     buf_write_en ? 1'b0 : buf_empty;
        
        buf_rd_ptr_q <= buf_rd_ptr;
        buf_oflow <= buf_full & buf_write_en;
        buf_uflow <= buf_empty & (buf_rd_ptr_q != buf_rd_ptr);
      end
   assign buf_cfg_buf_oflow = buf_oflow;
   assign buf_cfg_buf_uflow = buf_uflow;
   assign buf_cfg_buf_full  = buf_full;
   assign buf_cfg_buf_empty = buf_empty;
   always_comb begin
      buf_cfg_buf_wr_ptr = 0;
      buf_cfg_buf_rd_addr = 0;
      buf_cfg_buf_wr_ptr = buf_wr_ptr;
      buf_cfg_buf_rd_addr = dm_buf_rd_byte_addr;
   end
   
   assign buf_axis_ready = ~buf_full & ~aux_ram_full;
   
   // Buffer BRAM
   assign buf_ram_wr =  buf_write_en;
   assign buf_ram_waddr = buf_wr_ptr;
   assign buf_ram_wdata = axis_buf_data;

   assign buf_ram_rd = dm_buf_rd;
   assign buf_ram_raddr = dm_buf_addr;
   
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

   assign buf_dm_data = buf_ram_rdata;
   
   // Buffer AUX FT FIFO

   localparam BUF_AUX_RAM_WIDTH = DESC_TYPE ? BUF_AUX_WIDTH - 1 : BUF_AUX_WIDTH;
   localparam BUF_AUX_RAM_ADDR_WIDTH = $clog2(BUF_AUX_FT_FIFO_DEPTH);
   localparam BUF_AUX_RAM_DEPTH = BUF_AUX_FT_FIFO_DEPTH;
   localparam BUF_AUX_RAM_DEPTH_MINUS1 = BUF_AUX_RAM_DEPTH - 1;

   logic [PCIM_ADDR_BYTE_IDX_WIDTH-1:0] wr_last_byte_addr;
   logic                               aux_ram_wr;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_waddr;
   logic [BUF_AUX_RAM_WIDTH-1:0]       aux_ram_wdata;
   logic                               aux_ram_rd;
   logic [BUF_AUX_RAM_ADDR_WIDTH-1:0]  aux_ram_raddr;
   logic [BUF_AUX_RAM_WIDTH-1:0]       aux_ram_rdata;

   logic                               aux_ram_empty;
   logic                               aux_ram_pop;

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

   
   always_comb begin
      wr_last_byte_addr = 0;
      for (int byte_idx = 0; byte_idx < PCIM_DATA_WIDTH_BYTES; byte_idx++) begin
         if (axis_buf_keep[byte_idx])
           wr_last_byte_addr = byte_idx;
      end
   end
   
   assign aux_ram_wr = buf_write_en & axis_buf_last;
   assign aux_ram_waddr = aux_ram_wr_ptr;
   assign aux_ram_wdata = DESC_TYPE ? {buf_wr_ptr, wr_last_byte_addr} : 
                          {axis_buf_user, buf_wr_ptr, wr_last_byte_addr};

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

   assign aux_ft_ff_pop = dm_buf_aux_pop;
   assign buf_dm_aux_valid = aux_ft_ff_valid;
   assign buf_dm_aux_data = DESC_TYPE ? {1'b0, aux_ft_ff_data} : aux_ft_ff_data;
   
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
   
   // Number of bytes in the buffer

   localparam BUF_SIZE_BYTES = BUF_DEPTH * (PCIM_DATA_WIDTH>>3);
//   logic [BUF_RAM_ADDR_WIDTH-1:0] buf_ptr_diff;
   logic [BUF_ADDR_WIDTH:0] buf_byte_addr_diff;
   logic [BUF_ADDR_WIDTH:0]   buf_wr_byte_addr_plus_depth;
   logic [BUF_ADDR_WIDTH-1:0] buf_wr_byte_addr;
   logic [BUF_ADDR_WIDTH:0]   num_bytes_no_eop;
   logic [BUF_ADDR_WIDTH-1:0] aux_first_eop_wr_byte_addr;
   logic [BUF_ADDR_WIDTH:0] aux_first_eop_wr_byte_addr_plus_depth;
   logic [BUF_ADDR_WIDTH-1:0] buf_rd_byte_addr;
   logic [BUF_ADDR_WIDTH:0] buf_aux_byte_addr_diff;
   logic [BUF_ADDR_WIDTH:0] num_bytes_eop;

   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_wr_ptr_q;
   logic [BUF_RAM_ADDR_WIDTH-1:0]          buf_wr_ptr_qq;

      always @(posedge clk)
     if (!rst_n) begin
        buf_wr_ptr_q <= '{default:'0};
        buf_wr_ptr_qq <= '{default:'0};

     end
     else begin
        buf_wr_ptr_q <= buf_wr_ptr;
        buf_wr_ptr_qq <= buf_wr_ptr_q;
     end
   
   // When EOP is not valid
   // This is difference between read and write pointer
//    assign buf_ptr_diff = (buf_wr_ptr > buf_rd_ptr) ? (buf_wr_ptr - buf_rd_ptr) :
//                          (BUF_DEPTH + buf_wr_ptr - buf_rd_ptr);

   
   assign buf_wr_byte_addr = {buf_wr_ptr_qq, {PCIM_ADDR_BYTE_IDX_WIDTH{1'b0}}};
   assign buf_wr_byte_addr_plus_depth = BUF_SIZE_BYTES + buf_wr_byte_addr;
   assign buf_byte_addr_diff = (buf_wr_byte_addr > buf_rd_byte_addr) ? ({1'b0, buf_wr_byte_addr} - {1'b0, buf_rd_byte_addr}) :
                               (buf_wr_byte_addr_plus_depth - {1'b0, buf_rd_byte_addr});
   
   assign num_bytes_no_eop = ~buf_full & (buf_wr_byte_addr == buf_rd_byte_addr) ? 0 :
                             buf_byte_addr_diff;
   
   // When EOP is valid
   // This is the difference between the write and the first EOP pointer
   assign aux_first_eop_wr_byte_addr = aux_ft_ff_data[0 +: BUF_ADDR_WIDTH];
   assign aux_first_eop_wr_byte_addr_plus_depth = BUF_SIZE_BYTES + aux_first_eop_wr_byte_addr;
   assign buf_rd_byte_addr = dm_buf_rd_byte_addr;
   assign buf_aux_byte_addr_diff = (aux_first_eop_wr_byte_addr >= buf_rd_byte_addr) ? ({1'b0, aux_first_eop_wr_byte_addr} - {1'b0, buf_rd_byte_addr}) :
                                   (aux_first_eop_wr_byte_addr_plus_depth - {1'b0, buf_rd_byte_addr});
   assign num_bytes_eop = buf_aux_byte_addr_diff + 1;
   
// CANNOT FLOP//   always @(posedge clk)
// CANNOT FLOP//     if (!rst_n)
// CANNOT FLOP//       buf_dm_num_bytes <= '{default:'0};
// CANNOT FLOP//     else
// CANNOT FLOP//       buf_dm_num_bytes <= aux_ft_ff_valid ? num_bytes_eop : num_bytes_no_eop;
   assign buf_dm_num_bytes = aux_ft_ff_valid ? num_bytes_eop : num_bytes_no_eop;

   logic [31:0] buf_in_pkt_cnt;
   logic [31:0] buf_out_pkt_cnt;
   logic [BUF_ADDR_WIDTH:0] buf_dm_num_bytes_q;
   
   // Error detection
   // if buf_dm_num_bytes decreases by 24K, thats an error
   always @(posedge clk)
     if (!rst_n) begin
        buf_cfg_in_pkt_cnt <= 0;
        buf_cfg_out_pkt_cnt <= 0;
        
        buf_cfg_num_bytes <= 0;
        // buf_cfg_num_bytes_eop <= 0;
        // buf_cfg_num_bytes_no_eop <= 0;
     end
     else begin
        buf_cfg_in_pkt_cnt <= cfg_buf_clr_in_pkt_cnt ? 0 : 
                              (axis_buf_valid & axis_buf_last & buf_axis_ready) ? buf_cfg_in_pkt_cnt + 1 : buf_cfg_in_pkt_cnt;
        buf_cfg_out_pkt_cnt <= cfg_buf_clr_out_pkt_cnt ? 0 :
                               aux_ft_ff_valid & aux_ft_ff_pop ? buf_cfg_out_pkt_cnt + 1 : buf_cfg_out_pkt_cnt;
        
        buf_cfg_num_bytes <= buf_dm_num_bytes;
        // buf_cfg_num_bytes_eop <= num_bytes_eop;
        // buf_cfg_num_bytes_no_eop <= num_bytes_no_eop;
     end // else: !if(!rst_n)

   
 `ifndef NO_SDE_DEBUG_ILA
 
   // ILA Signals
   ila_sde_c2h_buf SDE_C2H_BUF_ILA
     (
      .clk (clk),
      
      // 0
      .probe0(buf_full                    ),
      .probe1(buf_wr_ptr_qq               ),
      .probe2(buf_wr_byte_addr            ),
      .probe3(buf_rd_byte_addr            ),
      .probe4(buf_wr_byte_addr_plus_depth ),
      .probe5(buf_byte_addr_diff          ),
      .probe6(num_bytes_no_eop            ),
      .probe7(aux_ft_ff_valid             ),

      .probe8(aux_first_eop_wr_byte_addr            ),
      .probe9(aux_first_eop_wr_byte_addr_plus_depth ),
      .probe10(buf_aux_byte_addr_diff               ),
      .probe11(num_bytes_eop                        ),
      .probe12(buf_dm_num_bytes                     ),
      .probe13(buf_cfg_num_bytes_err                ),
      .probe14(aux_ram_oflow                        ),
      .probe15(buf_oflow                            ),
      
      .probe16(buf_in_pkt_cnt ),
      .probe17(buf_out_pkt_cnt)

      );


 `endif //  `ifndef NO_SDE_DEBUG_ILA
      
endmodule // sde_c2h_buf

    
