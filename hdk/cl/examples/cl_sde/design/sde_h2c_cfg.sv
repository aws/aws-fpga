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

// H2C Config Access

module sde_h2c_cfg #(parameter bit DESC_TYPE = 0,
                     parameter DESC_RAM_DEPTH = 64,
                     parameter DESC_WIDTH = 256
                     )
    (
    input                         clk,
    input                         rst_n,

     // PCIS to H2C Config Interface
    input                         h2c_ps_cfg_wr_req,
    input                         h2c_ps_cfg_rd_req,
    input [15:0]                  h2c_ps_cfg_addr,
    input [31:0]                  h2c_ps_cfg_wdata,
    output logic                  h2c_ps_cfg_ack,
    output logic [31:0]           h2c_ps_cfg_rdata,

    input                         desc_ooo_error,
    input                         desc_unalin_error,
     
     // Config to Desc
    output logic                  cfg_desc_clr_cdt_consumed,
    output logic                  cfg_desc_clr_cdt_limit,
    output logic                  cfg_desc_clr_desc_cnt,

    output logic                  cfg_desc_cdt_wc_en,
    output logic                  cfg_desc_cnt_wc_en,
    output logic                  cfg_pkt_cnt_wc_en,
    output logic [19:0]           cfg_wc_tick_cnt,
    output logic [3:0]            cfg_wc_to_cnt,
    output logic [5:0]            cfg_wc_cnt_minus1,
         
    input [31:0]                  desc_cfg_cdt_consumed,
    input [31:0]                  desc_cfg_cdt_limit,
    input [31:0]                  desc_cfg_desc_cnt,
    input [15:0]                  desc_cfg_wr_ptr,
    input [15:0]                  desc_cfg_rd_ptr,

    output logic                  cfg_desc_ram_wr_req,
    output logic                  cfg_desc_ram_rd_req,
    output logic [15:0]           cfg_desc_ram_addr,
    output logic [DESC_WIDTH-1:0] cfg_desc_ram_wdata,
    input                         desc_cfg_ram_ack,
    input [DESC_WIDTH-1:0]        desc_cfg_ram_rdata,

    input                         desc_cfg_oflow,
    input                         desc_cfg_uflow,
    input                         desc_cfg_full,
    input                         desc_cfg_empty,

    input                         dm_cfg_rresp_err,
    input                         dm_cfg_desc_len_err,
     
    output logic                  cfg_wb_desc_cdt_en,
    output logic                  cfg_wb_desc_cnt_en,
    output logic                  cfg_wb_pkt_cnt_en,
    output logic [47:0]           cfg_wb_status_addr,
     
    input                         wb_cfg_sts_bresp_err,

    output logic                  cfg_wb_desc_error, 
    output logic                  cfg_wb_dm_error, 
    output logic                  cfg_wb_wb_error,
    input [31:0]                  wb_cfg_status_dw,
     
     // Config Buf
    input                         buf_cfg_buf_oflow,
    input                         buf_cfg_buf_uflow,
    input                         buf_cfg_buf_full,
    input                         buf_cfg_buf_empty,
    input [15:0]                  buf_cfg_buf_wr_ptr ,
    input [15:0]                  buf_cfg_buf_rd_ptr,
    input                         buf_cfg_aux_fifo_oflow,
    input                         buf_cfg_aux_fifo_uflow,
    input                         buf_cfg_aux_fifo_full , 
    input                         buf_cfg_aux_fifo_empty,
    input [15:0]                  buf_cfg_aux_ram_wr_ptr,
    input [15:0]                  buf_cfg_aux_ram_rd_ptr, 
    input [15:0]                  buf_cfg_dm_wr_ptr,
    input [15:0]                  buf_cfg_dm_aux_wr_ptr,
    input [15:0]                  buf_cfg_num_free_slots,
    input [31:0]                  buf_cfg_in_pkt_cnt,
    input [31:0]                  buf_cfg_out_pkt_cnt,
    output logic                  cfg_buf_clr_in_pkt_cnt,
    output logic                  cfg_buf_clr_out_pkt_cnt,

    output logic                  cfg_axis_clr_pkt_cnt,
    input [31:0]                  axis_cfg_pkt_cnt
     );

   localparam DESC_WIDTH_DW = DESC_WIDTH >> 5;
   localparam DESC_WIDTH_DW_MINUS1 = DESC_WIDTH_DW - 1;
   
   // Address range is 1.5KB (0x000 - 0x600)
   
   /////////////////////////////////////////////////
   // H2C Global Control and Status (0x0000 - 0x00FC)
   /////////////////////////////////////////////////
   // No registers yet
   
   /////////////////////////////////////////////////
   // Desc Config and Status (0x0100 - 0x01FC)
   /////////////////////////////////////////////////

   // 0x00: Desc Credit "Consumed" (RW0C)

   // 0x04: Desc Credit "Limit" (RW0C)

   // 0x08: Desc Count - Number of completed Descriptors (RW0C)

   // 0x0C : Desc FIFO Pointers (RO)
   //   14:0  - Desc FIFO Write Pointer
   //   15    - Desc FIFO Write Pointer MSB
   //   30:16 - Desc FIFO Read Pointer
   //   31    - Desc FIFO Read Pointer MSB

   // 0x10 : Desc Address Registers (RW)
   //   15:0  - Desc RAM Address (RW)
   //   31:16 - Desc DW Index (W0C) (Auto increment)
   
   // 0x14 : Desc Read/Write Data (RW)
   
   // 0x18 : Desc Status
   //   0     - Desc Overflow (RW1C)
   //   1     - Desc Out of Order Error (RW1C)
   //   2     - Desc Unaligned Error (RW1C)
   //   3     - Desc Full (RO)
   //   4     - Desc Empty (RO)
   // 31:5    - RSVD

   // 0x20 : Desc Info
   //    0    - Descriptor Type (0 - Regular, 1 - Compact) (RO)
   // 15:1    - RSVD
   // 31:16   - Descriptor RAM Depth (Maximum number of descriptors) (RO)
   
   /////////////////////////////////////////////////
   // Data Mover Config and Status (0x0200 - 0x02FC)
   /////////////////////////////////////////////////
   // 0x00 : Data Mover Config Reg 0
   //  31:0  - RSVD (RW)

   // 0x04 : Data Mover Status
   //   0     - RRESP Error (RW1C)
   //   1     - Descriptor length Error (RW1C)
   // 31:2    - RSVD
   
   /////////////////////////////////////////////////
   // Write Back Config and Status (0x0300 - 0x34FC)
   /////////////////////////////////////////////////
   // 0x00 : Config Reg 0 (RW)
   //   0   - Enable Descriptor Count Write-Back
   //   1   - Enable Packet Count Write-Back
   //   2   - Enable Descriptor Limit Write-Back
   //   3   - RSVD
   //   4   - Descriptor Limit Write-Back Coalescing Enable
   //   5   - Completed Descriptor Count Write-Back Coalescing Enable
   //   6   - AXIS Packet Count Write-Back Coalescing Enable
   //   7   - RSVD
   // 13:8  - Write-Back Coalescing Count Minus 1
   // 31:14 - RSVD
   
   // 0x04 : Status Write-Back Address Low (RW)

   // 0x08 : Status Write-back Address High (RW)

   // 0x0C : Coalescing Timeout Count Register
   // 19:0  - Coalescing Timeout Resolution Count (RW)
   // 23:20 - Coalescing Timeout Count (RW)
   // 31:24 - RSVD

   // 0x10 : Write Back Status Register
   //   0   - BRESP Error for Status Write
   // 31:1  - RSVD
   
   // 0x14 : Status DW
   //   0   - Desc Error
   //   1   - Data Mover Error
   //   2   - Write-Back Error
   // 31:3  - RSVD
   
   /////////////////////////////////////////////////
   // Buffer & SPB Config and Status (0x0400 - 0x04FC)
   /////////////////////////////////////////////////
   // 0x00 : Buf Config Reg 0
   //  31:0  - RSVD (RW)

   // 0x04 : Buf Status
   //   0    - Buffer Full (RO)   
   //   1    - Buffer Empty (RO)  
   //   2    - Aux FIFO Full (RO) 
   //   3    - Aux FIFO Valid (RO)
   // 31:4   - RSVD
   
   // 0x08 : Input Packet Count (RW0C)

   // 0x0C : Ouput Packet Count (RW0C)

   // 0x10 : Buffer Pointers (RO)
   //  15:0  - Buffer Write Pointer
   //  31:16 - Buffer Read Address

   // 0x14 : Aux RAM Pointers (RO)
   //  14:0  - AUX RAM Write Pointer
   //   15   - AUX RAM Write Pointer MSB
   //  30:16 - AUX RAM Read Pointer
   //   31   - AUX RAM Read Pointer MSB

   // 0x18 : Number of Bytes
   //  15:0  - Buffer Number of Free Entries (RO)
   //  31:16 - RSVD
   
   // 0x1C : Data Mover In Buffer Pointers (RO)
   //  14:0  - Buffer Write Pointer
   //   15   - Buffer Write Pointer MSB
   //  30:16 - Aux FIFO Write Pointer
   //   31   - Aux FIFO Write Pointer MSB
   
   /////////////////////////////////////////////////
   // AXIS Config and Status (0x0500 - 0x05FC)
   /////////////////////////////////////////////////
   // 0x00 : Packet Count (RW0C)
   
   logic              cfg_wr_q;
   logic              cfg_rd_q;
   logic              cfg_wr_re;
   logic              cfg_rd_re;
   logic              cfg_wr_fe;
   logic              cfg_rd_fe;
   logic              dec_range_0;
   logic              dec_range_1;
   logic              dec_range_2;
   logic              dec_range_3;
   logic              dec_range_4;
   logic              dec_range_5;
   logic              ack_range_0;
   logic              ack_range_1;
   logic              ack_range_2;
   logic              ack_range_3;
   logic              ack_range_4;
   logic              ack_range_5;
   logic [31:0]       rdata_range_0;
   logic [31:0]       rdata_range_1;
   logic [31:0]       rdata_range_2;
   logic [31:0]       rdata_range_3;
   logic [31:0]       rdata_range_4;
   logic [31:0]       rdata_range_5;

   
   always @(posedge clk)
     if (!rst_n) begin
        cfg_wr_q <= 0;
        cfg_rd_q <= 0;
     end
     else begin
        cfg_wr_q <= h2c_ps_cfg_wr_req;
        cfg_rd_q <= h2c_ps_cfg_rd_req;
     end
   assign cfg_wr_re = ~cfg_wr_q & h2c_ps_cfg_wr_req;
   assign cfg_rd_re = ~cfg_rd_q & h2c_ps_cfg_rd_req;
   assign cfg_wr_fe = cfg_wr_q & ~h2c_ps_cfg_wr_req;
   assign cfg_rd_fe = cfg_rd_q & ~h2c_ps_cfg_rd_req;
                             
   // Decode Address ranges
   assign dec_range_0 = (h2c_ps_cfg_addr >= 16'h0000) & (h2c_ps_cfg_addr < 16'h0100);
   assign dec_range_1 = (h2c_ps_cfg_addr >= 16'h0100) & (h2c_ps_cfg_addr < 16'h0200);
   assign dec_range_2 = (h2c_ps_cfg_addr >= 16'h0200) & (h2c_ps_cfg_addr < 16'h0300);
   assign dec_range_3 = (h2c_ps_cfg_addr >= 16'h0300) & (h2c_ps_cfg_addr < 16'h0400);
   assign dec_range_4 = (h2c_ps_cfg_addr >= 16'h0400) & (h2c_ps_cfg_addr < 16'h0500);
   assign dec_range_5 = (h2c_ps_cfg_addr >= 16'h0500) & (h2c_ps_cfg_addr < 16'h0600);
   
   always @(posedge clk)
     if (!rst_n) begin
        h2c_ps_cfg_ack <= 0;
        h2c_ps_cfg_rdata <= 0;
     end
     else begin
        h2c_ps_cfg_ack <= (cfg_wr_q || cfg_rd_q) & (dec_range_0 ? ack_range_0 :
                                                    dec_range_1 ? ack_range_1 :
                                                    dec_range_2 ? ack_range_2 :
                                                    dec_range_3 ? ack_range_3 :
                                                    dec_range_4 ? ack_range_4 :
                                                    dec_range_5 ? ack_range_5 : 1'b1);
                                                                
        h2c_ps_cfg_rdata <= dec_range_0 ? rdata_range_0 :
                            dec_range_1 ? rdata_range_1 :
                            dec_range_2 ? rdata_range_2 :
                            dec_range_3 ? rdata_range_3 :
                            dec_range_4 ? rdata_range_4 :
                            dec_range_5 ? rdata_range_5 : 32'hbaad_3600;
     end // else: !if(!rst_n)
   
   /////////////////////////////////////////////////
   // Range 0 (0x0000 - 0x00FC)
   /////////////////////////////////////////////////
   // TODO: No registers in this range yet
   assign ack_range_0 = 1;
   assign rdata_range_0 = 32'hbaad_3000;
   
   /////////////////////////////////////////////////
   // Range 1 (0x0100 - 0x01FC)
   /////////////////////////////////////////////////
   logic ack_wr_range_1;
   logic ack_rd_range_1;
   
   logic clr_desc_ram_idx;
   logic inc_desc_ram_idx_wr;
   logic inc_desc_ram_idx_rd;
   logic inc_desc_ram_idx;
   logic [3:0] desc_ram_idx;
   logic [31:0] cfg_desc_ram_rd_dw;
   logic [31:0] cfg_desc_ram_wr_dw;
   logic        cfg_desc_type;
   logic [15:0] cfg_desc_ram_depth;
   logic [DESC_WIDTH-1:0] cfg_desc_ram_data_q;
   logic                  cfg_desc_ram_wr_ack;
   logic                  cfg_desc_ram_rd_ack;
   logic                  cfg_desc_ram_rd_ack_q;
   logic                  cfg_desc_ram_addr_reg_wr;
   logic                  cfg_desc_ram_data_reg_wr;
   logic                  cfg_desc_ram_data_reg_wr_last;
   logic                  cfg_desc_oflow;
   logic                  cfg_desc_ooo_error;
   logic                  cfg_desc_unalin_error;
   logic                  clr_desc_oflow;
   logic                  clr_desc_ooo_error;
   logic                  clr_desc_unalin_error;

   assign ack_range_1 = h2c_ps_cfg_wr_req ? ack_wr_range_1 : ack_rd_range_1;

   // Register Writes
   always @(posedge clk)
     if (!rst_n) begin
        ack_wr_range_1 <= 0;
        cfg_desc_ram_addr <= 16'd0;
        cfg_desc_ram_wr_dw <= 32'd0;
      end
     else if (h2c_ps_cfg_wr_req & dec_range_1) begin
        ack_wr_range_1 <= 0;
        case (h2c_ps_cfg_addr[7:0]) 
          8'h10 : begin
             ack_wr_range_1 <= 1;
             cfg_desc_ram_addr <= h2c_ps_cfg_wdata;
          end
          8'h14 : begin
             ack_wr_range_1 <= cfg_desc_ram_wr_ack;
             cfg_desc_ram_wr_dw <= h2c_ps_cfg_wdata;
          end
          default :
            ack_wr_range_1 <= 1;
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // if (h2c_ps_cfg_wr_req & dec_range_1)

   // Signals based off of writes
   always @(posedge clk)
     if (!rst_n) begin
        cfg_desc_clr_cdt_consumed <= 0;
        cfg_desc_clr_cdt_limit    <= 0;
        cfg_desc_clr_desc_cnt     <= 0;
     end
     else begin
        cfg_desc_clr_cdt_consumed <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h00) & (h2c_ps_cfg_wdata == 32'd0);
        cfg_desc_clr_cdt_limit    <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h04) & (h2c_ps_cfg_wdata == 32'd0);
        cfg_desc_clr_desc_cnt     <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h08) & (h2c_ps_cfg_wdata == 32'd0);
     end
   assign clr_desc_oflow        = cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h18) & h2c_ps_cfg_wdata[0];
   assign clr_desc_ooo_error    = cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h18) & h2c_ps_cfg_wdata[1];
   assign clr_desc_unalin_error = cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h18) & h2c_ps_cfg_wdata[2];

   assign cfg_desc_type = DESC_TYPE;
   assign cfg_desc_ram_depth = DESC_RAM_DEPTH;

   // Read data and ack
   always @(posedge clk)
     if (!rst_n) begin
        ack_rd_range_1 <= 0;
        rdata_range_1 <= 32'h0;
     end
     else begin
        case (h2c_ps_cfg_addr[7:0])
          8'h00 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= desc_cfg_cdt_consumed;
          end
          8'h04 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= desc_cfg_cdt_limit;
          end
          8'h08 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= desc_cfg_desc_cnt;
          end
          8'h0C : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= {desc_cfg_rd_ptr, desc_cfg_wr_ptr};
          end
          8'h10 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1[15:0] <= cfg_desc_ram_addr;
             rdata_range_1[31:16] <= desc_ram_idx;
          end
          8'h14 : begin
             ack_rd_range_1 <= cfg_desc_ram_rd_ack_q;
             rdata_range_1 <= cfg_desc_ram_rd_dw;
          end
          8'h18 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= {desc_cfg_empty, desc_cfg_full, cfg_desc_unalin_error, cfg_desc_ooo_error, cfg_desc_oflow};
          end
          8'h20 : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= {cfg_desc_ram_depth, 15'd0, cfg_desc_type};
          end
          default : begin
             ack_rd_range_1 <= 1;
             rdata_range_1 <= 32'hbaad_3100;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // else: !if(!rst_n)

   assign clr_desc_ram_idx = cfg_desc_ram_addr_reg_wr;
   assign inc_desc_ram_idx_wr = cfg_desc_ram_data_reg_wr;
   assign inc_desc_ram_idx_rd = cfg_rd_fe & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h14);
   assign inc_desc_ram_idx = cfg_rd_q ? inc_desc_ram_idx_rd : inc_desc_ram_idx_wr;

   always @(posedge clk) 
     if (!rst_n) begin
        desc_ram_idx <= 4'd0;
        cfg_desc_ram_rd_dw <= 32'd0;
        cfg_desc_ram_data_q <= '{default:'0};
        
        cfg_desc_ram_wr_ack <= 0;
        cfg_desc_ram_rd_ack <= 0;
        cfg_desc_ram_rd_ack_q <= 0;
        
        cfg_desc_ram_addr_reg_wr <= 0;
        cfg_desc_ram_data_reg_wr <= 0;
        
        cfg_desc_ram_data_reg_wr_last <= 0;
        cfg_desc_ram_wr_req <= 0;
        cfg_desc_ram_rd_req <= 0;

     end
     else begin
        desc_ram_idx <= clr_desc_ram_idx ? 4'd0 :
                        inc_desc_ram_idx ? desc_ram_idx + 4'd1 : desc_ram_idx;

        for (int dw_idx = 0; dw_idx < DESC_WIDTH_DW; dw_idx++)
          if (desc_ram_idx == dw_idx) 
            cfg_desc_ram_rd_dw <= cfg_desc_ram_data_q[32*dw_idx +: 32];
        
        if (desc_cfg_ram_ack)
          cfg_desc_ram_data_q <= desc_cfg_ram_rdata;
        else 
          for (int dw_idx = 0; dw_idx < DESC_WIDTH_DW; dw_idx++)
            if (desc_ram_idx == dw_idx) 
              cfg_desc_ram_data_q[32*dw_idx +: 32] <= cfg_desc_ram_data_reg_wr ? cfg_desc_ram_wr_dw : cfg_desc_ram_data_q[32*dw_idx +: 32];
        
        
        cfg_desc_ram_wr_ack <= (desc_ram_idx == DESC_WIDTH_DW_MINUS1) ? desc_cfg_ram_ack : 1'b1;
        cfg_desc_ram_rd_ack <= (desc_ram_idx == 0) ? desc_cfg_ram_ack : 1'b1;
        cfg_desc_ram_rd_ack_q <= cfg_desc_ram_rd_ack;
        
        cfg_desc_ram_addr_reg_wr <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h10);
        cfg_desc_ram_data_reg_wr <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h14);
        
        cfg_desc_ram_data_reg_wr_last <= cfg_wr_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h14) & (desc_ram_idx == DESC_WIDTH_DW_MINUS1);

        cfg_desc_ram_wr_req <= cfg_desc_ram_data_reg_wr_last;
        cfg_desc_ram_rd_req <= cfg_rd_re & dec_range_1 & (h2c_ps_cfg_addr[7:0] == 8'h14) & (desc_ram_idx == 0);
        
     end // else: !if(!rst_n)
   assign cfg_desc_ram_wdata = cfg_desc_ram_data_q;
   
   always @(posedge clk)
     if (!rst_n) begin
        cfg_desc_oflow <= 0;
        cfg_desc_ooo_error <= 0;
        cfg_desc_unalin_error <= 0;
     end
     else begin
        cfg_desc_oflow <= desc_cfg_oflow ? 1'b1 :
                          clr_desc_oflow ? 1'b0 : cfg_desc_oflow;
        cfg_desc_ooo_error <= desc_ooo_error ? 1'b1 :
                              clr_desc_ooo_error ? 1'b0 : cfg_desc_ooo_error;
        cfg_desc_unalin_error <= desc_unalin_error ? 1'b1 :
                                 clr_desc_unalin_error ? 1'b0 : cfg_desc_unalin_error;
     end // else: !if(!rst_n)

   /////////////////////////////////////////////////
   // Range 2 (0x0200 - 0x02FC)
   /////////////////////////////////////////////////
   logic ack_wr_range_2;
   logic ack_rd_range_2;

   logic [31:0] cfg_dm_ctl_reg0;
   logic cfg_dm_rresp_err;
   logic clr_cfg_dm_rresp_err;
   logic cfg_dm_desc_len_err;
   logic clr_cfg_dm_desc_len_err;
   
   assign ack_range_2 = h2c_ps_cfg_wr_req ? ack_wr_range_2 : ack_rd_range_2;

   // Register Writes
   always @(posedge clk)
     if (!rst_n) begin
        ack_wr_range_2 <= 0;
        cfg_dm_ctl_reg0 <= 32'd0;
     end
     else if (h2c_ps_cfg_wr_req & dec_range_2) begin
        ack_wr_range_2 <= 0;
        case (h2c_ps_cfg_addr[7:0]) 
          8'h00 : begin
             ack_wr_range_2 <= 1;
             cfg_dm_ctl_reg0 <= h2c_ps_cfg_wdata;
          end
          default: begin
             ack_wr_range_2 <= 1;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // if (h2c_ps_cfg_wr_req & dec_range_2)

   always @(posedge clk)
     if (!rst_n) begin
        ack_rd_range_2 <= 0;
        rdata_range_2 <= 0;
     end
     else begin
        case (h2c_ps_cfg_addr[7:0])
          8'h00 : begin
             ack_rd_range_2 <= 1;
             rdata_range_2 <= cfg_dm_ctl_reg0;
          end
          8'h04 : begin
             ack_rd_range_2 <= 1;
             rdata_range_2 <= {cfg_dm_desc_len_err, cfg_dm_rresp_err};
          end
          default : begin
             ack_rd_range_2 <= 1;
             rdata_range_2 <= 32'hbaad_2200;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // else: !if(!rst_n)

   // Signals based off of writes
   assign clr_cfg_dm_rresp_err    = cfg_wr_re & dec_range_2 & (h2c_ps_cfg_addr[7:0] == 8'h04) & h2c_ps_cfg_wdata[0];
   assign clr_cfg_dm_desc_len_err = cfg_wr_re & dec_range_2 & (h2c_ps_cfg_addr[7:0] == 8'h04) & h2c_ps_cfg_wdata[1];

   always @(posedge clk)
     if (!rst_n) begin
        cfg_dm_rresp_err <= 0;
        cfg_dm_desc_len_err <= 0;
     end
     else begin
        cfg_dm_rresp_err <= dm_cfg_rresp_err ? 1'b1 :
                            clr_cfg_dm_rresp_err ? 1'b0 : cfg_dm_rresp_err;
        cfg_dm_desc_len_err <= dm_cfg_desc_len_err ? 1'b1 :
                               clr_cfg_dm_desc_len_err ? 1'b0 : cfg_dm_desc_len_err;
     end

   /////////////////////////////////////////////////
   // Range 3 (0x0300 - 0x34FC)
   /////////////////////////////////////////////////
   logic ack_wr_range_3;
   logic ack_rd_range_3;
   logic [31:0] cfg_wb_ctl_reg0;

   logic        clr_wb_sts_bresp_err;
   logic        cfg_wb_sts_bresp_err;
   
   assign ack_range_3 = h2c_ps_cfg_wr_req ? ack_wr_range_3 : ack_rd_range_3;

   // Register Writes
   always @(posedge clk)
     if (!rst_n) begin
        ack_wr_range_3 <= 0;
        cfg_wb_ctl_reg0 <= 32'd0;
        cfg_wb_status_addr <= 48'd0;
        cfg_wc_to_cnt <= 0;
        cfg_wc_tick_cnt <= 0;
     end
     else if (h2c_ps_cfg_wr_req & dec_range_3) begin
        ack_wr_range_3 <= 0;
        case (h2c_ps_cfg_addr[7:0]) 
          8'h00 : begin
             ack_wr_range_3 <= 1;
             cfg_wb_ctl_reg0 <= h2c_ps_cfg_wdata;
          end
          8'h04 : begin
             ack_wr_range_3 <= 1;
             cfg_wb_status_addr[31:0] <= h2c_ps_cfg_wdata;
          end
          8'h08 : begin
             ack_wr_range_3 <= 1;
             cfg_wb_status_addr[47:32] <= h2c_ps_cfg_wdata;
          end
          8'h0C : begin
             ack_wr_range_3 <= 1;
             {cfg_wc_to_cnt, cfg_wc_tick_cnt} <= h2c_ps_cfg_wdata;
          end
          default :
            ack_wr_range_3 <= 1;
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // if (h2c_ps_cfg_wr_req & dec_range_2)
          
   // Register Reads
   always @(posedge clk)
     if (!rst_n) begin
        ack_rd_range_3 <= 0;
        rdata_range_3 <= 0;
     end
     else begin
        case (h2c_ps_cfg_addr[7:0])
          8'h00 : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= cfg_wb_ctl_reg0;
          end
          8'h04 : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= cfg_wb_status_addr[31:0];
          end
          8'h08 : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= cfg_wb_status_addr[47:32];
          end
          8'h0C : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= {cfg_wc_to_cnt, cfg_wc_tick_cnt};
          end
          8'h10 : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= cfg_wb_sts_bresp_err;
          end
          8'h14 : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= wb_cfg_status_dw;
          end
          default : begin
             ack_rd_range_3 <= 1;
             rdata_range_3 <= 32'hbaad_3300;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // else: !if(!rst_n)
       
   assign clr_wb_sts_bresp_err = cfg_wr_re & dec_range_3 & (h2c_ps_cfg_addr[7:0] == 8'h10) & h2c_ps_cfg_wdata[0];
                        
   assign cfg_wb_desc_cnt_en = cfg_wb_ctl_reg0[0];
   assign cfg_wb_pkt_cnt_en = cfg_wb_ctl_reg0[1];
   assign cfg_wb_desc_cdt_en = cfg_wb_ctl_reg0[2];
   assign cfg_desc_cdt_wc_en = cfg_wb_ctl_reg0[4];
   assign cfg_desc_cnt_wc_en = cfg_wb_ctl_reg0[5];
   assign cfg_pkt_cnt_wc_en = cfg_wb_ctl_reg0[6];
   assign cfg_wc_cnt_minus1 = cfg_wb_ctl_reg0[13:8];

   always @(posedge clk)
     if (!rst_n) begin
        cfg_wb_sts_bresp_err <= 0;
     end
     else begin
        cfg_wb_sts_bresp_err <= wb_cfg_sts_bresp_err ? 1'b1 :
                                clr_wb_sts_bresp_err ? 1'b0 : cfg_wb_sts_bresp_err;
     end // else: !if(!rst_n)

   /////////////////////////////////////////////////
   // Range 4 (0x0400 - 0x04FC)
   /////////////////////////////////////////////////
//   assign ack_range_4 = 1;
//   assign rdata_range_4 = 32'hbaad_3400;

   logic ack_wr_range_4;
   logic ack_rd_range_4;
   logic [31:0] cfg_buf_ctl_reg0;

   assign ack_range_4 = h2c_ps_cfg_wr_req ? ack_wr_range_4 : ack_rd_range_4;

   // Register Writes
   always @(posedge clk)
     if (!rst_n) begin
        ack_wr_range_4 <= 0;
        cfg_buf_ctl_reg0 <= 32'd0;
     end
     else if (h2c_ps_cfg_wr_req & dec_range_4) begin
        ack_wr_range_4 <= 0;
        case (h2c_ps_cfg_addr[7:0]) 
          8'h00 : begin
             ack_wr_range_4 <= 1;
             cfg_buf_ctl_reg0 <= h2c_ps_cfg_wdata;
          end
          default: begin
             ack_wr_range_4 <= 1;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // if (h2c_ps_cfg_wr_req & dec_range_2)

   always @(posedge clk)
     if (!rst_n) begin
        cfg_buf_clr_in_pkt_cnt <= 0;
        cfg_buf_clr_out_pkt_cnt <= 0;
     end
     else begin
        cfg_buf_clr_in_pkt_cnt <= cfg_wr_re & dec_range_4 & (h2c_ps_cfg_addr[7:0] == 8'h08) & (h2c_ps_cfg_wdata == 0);
        cfg_buf_clr_out_pkt_cnt <= cfg_wr_re & dec_range_4 & (h2c_ps_cfg_addr[7:0] == 8'h0C) & (h2c_ps_cfg_wdata == 0);
     end

   // Register Reads
   always @(posedge clk)
     if (!rst_n) begin
        ack_rd_range_4 <= 0;
        rdata_range_4 <= 0;
     end
     else begin
        case (h2c_ps_cfg_addr[7:0])
          8'h00 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= cfg_buf_ctl_reg0;
          end
          8'h04 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= {buf_cfg_aux_fifo_empty, buf_cfg_aux_fifo_full, buf_cfg_buf_empty, buf_cfg_buf_full};
          end
          8'h08 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= buf_cfg_in_pkt_cnt;
          end
          8'h0C : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= buf_cfg_out_pkt_cnt;
          end
          8'h10 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= {buf_cfg_buf_rd_ptr, buf_cfg_buf_wr_ptr};
          end
          8'h14 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= {buf_cfg_aux_ram_rd_ptr, buf_cfg_aux_ram_wr_ptr};
          end
          8'h18 : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= buf_cfg_num_free_slots;
          end
          8'h1C : begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= {buf_cfg_dm_aux_wr_ptr, buf_cfg_dm_wr_ptr};
          end
          default: begin
             ack_rd_range_4 <= 1;
             rdata_range_4 <= 32'hbaad_3400;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // else: !if(!rst_n)

   /////////////////////////////////////////////////
   // Range 5 (0x0500 - 0x05FC)
   /////////////////////////////////////////////////
   logic ack_wr_range_5;
   logic ack_rd_range_5;
   assign ack_range_5 = h2c_ps_cfg_wr_req ? ack_wr_range_5 : ack_rd_range_5;

   // No registers to update on writes in Range 1 yet
   assign ack_wr_range_5 = 1;

   // Signals based off of writes
   always @(posedge clk)
     if (!rst_n) begin
        cfg_axis_clr_pkt_cnt <= 0;
     end
     else begin
        cfg_axis_clr_pkt_cnt <= cfg_wr_re & dec_range_5 & (h2c_ps_cfg_addr[7:0] == 8'h00) & (h2c_ps_cfg_wdata == 32'd0);
     end
   
   // Read data and ack
   always @(posedge clk)
     if (!rst_n) begin
        ack_rd_range_5 <= 0;
        rdata_range_5 <= 32'h0;
     end
     else begin
        case (h2c_ps_cfg_addr[7:0])
          8'h00 : begin
             ack_rd_range_5 <= 1;
             rdata_range_5 <= axis_cfg_pkt_cnt;
          end
          default : begin
             ack_rd_range_5 <= 1;
             rdata_range_5 <= 32'hbaad_3500;
          end
        endcase // case (h2c_ps_cfg_addr[7:0])
     end // else: !if(!rst_n)

   /////////////////////////////////////////////////
   // Error Signals to WB block
   /////////////////////////////////////////////////
   always @(posedge clk)
     if (!rst_n) begin
        cfg_wb_desc_error <= 0;
        cfg_wb_dm_error <= 0;
        cfg_wb_wb_error <= 0;
     end
     else begin
        cfg_wb_desc_error <= cfg_desc_unalin_error | cfg_desc_ooo_error | cfg_desc_oflow;
        cfg_wb_dm_error <= cfg_dm_rresp_err | cfg_dm_desc_len_err;
        cfg_wb_wb_error <= cfg_wb_sts_bresp_err;
     end
   
endmodule // sde_h2c_cfg
