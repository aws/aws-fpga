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


// Module is common for H2C and C2H

module sde_desc #(parameter bit H2C_N_C2H = 0, // 1 - H2C, 0 - C2H
                  parameter bit DESC_TYPE = 0,
                  parameter DESC_WIDTH = DESC_TYPE ? 128 : 256,
                  parameter DESC_RAM_DEPTH = 64,
                  parameter DESC_ADDR_WIDTH = $clog2(DESC_RAM_DEPTH),

                  parameter PCIM_DATA_WIDTH = 512,
                  parameter PCIM_ID_WIDTH = 3,
                  parameter PCIM_LEN_WIDTH = 8,
                  parameter PCIM_ADDR_WIDTH = 64,
                  parameter PCIM_ADDR_BYTE_IDX_WIDTH = $clog2(PCIM_DATA_WIDTH>>3),

                  parameter PCIM_DESC_ARID = 2
                  )
   (
    input                              clk,
    input                              rst_n,

    // PCIS to Descriptor
    input                              ps_desc_wr_req,
    input [DESC_WIDTH-1:0]             ps_desc_wdata,
    output logic                       ps_desc_ack,

    // CSR to Descriptor
    input                              cfg_desc_ram_wr_req,
    input                              cfg_desc_ram_rd_req,
    input [15:0]                       cfg_desc_ram_addr,
    input [DESC_WIDTH-1:0]             cfg_desc_ram_wdata,
    output logic                       desc_cfg_ram_ack,
    output logic [DESC_WIDTH-1:0]      desc_cfg_ram_rdata,

    input                              cfg_desc_clr_desc_cnt,
    input                              cfg_desc_clr_cdt_limit,
    input                              cfg_desc_clr_cdt_consumed,

    output logic [31:0]                desc_cfg_cdt_consumed,
    output logic [31:0]                desc_cfg_cdt_limit,
    output logic [31:0]                desc_cfg_desc_cnt,
    output logic [15:0]                desc_cfg_wr_ptr,
    output logic [15:0]                desc_cfg_rd_ptr,

    output logic                       desc_cfg_oflow,
    output logic                       desc_cfg_uflow,
    output logic                       desc_cfg_full,
    output logic                       desc_cfg_empty,
    
    // Descriptor to Data Mover
    output logic                       desc_dm_empty,
    input                              dm_desc_pop,
    output                             sde_pkg::comm_desc_t desc_dm_desc,
    output logic                       desc_dm_desc_valid,

    input                              dm_desc_cnt_inc,
    
    // Descriptor to Write Back Block
    output logic                       desc_wb_limit_req,
    output logic [31:0]                desc_wb_limit,

    output logic                       desc_wb_cnt_req,
    output logic [31:0]                desc_wb_cnt,

    // Descriptor to PCIM
    output logic                       desc_pm_arvalid,
    output logic [PCIM_ADDR_WIDTH-1:0] desc_pm_araddr,
    output logic [PCIM_LEN_WIDTH-1:0]  desc_pm_arlen,
    input                              pm_desc_arready,
    
     // Read Data from PCIM
    input                              pm_desc_rvalid,
    input [1:0]                        pm_desc_rresp,
    input [PCIM_DATA_WIDTH-1:0]        pm_desc_rdata,
    input                              pm_desc_rlast,
    output logic                       desc_pm_rready
    
    );

   localparam DESC_RAM_WIDTH = ~DESC_TYPE & H2C_N_C2H ? $bits(sde_pkg::h2c_reg_sav_desc_t) :
                               DESC_TYPE  & H2C_N_C2H ? $bits(sde_pkg::h2c_comp_sav_desc_t) :
                               ~DESC_TYPE & ~H2C_N_C2H ? $bits(sde_pkg::c2h_reg_sav_desc_t) :
                               $bits(sde_pkg::c2h_comp_sav_desc_t);
   
   logic                             ps_desc_wr_req_q = 0;
   logic [DESC_RAM_WIDTH-1:0]        ps_desc_wdata_q = 0;
   logic                             cfg_desc_ram_wr_req_q = 0;
   logic                             cfg_desc_ram_rd_req_q = 0;
   logic [DESC_ADDR_WIDTH-1:0]       cfg_desc_ram_addr_q   = 0;
   logic [DESC_RAM_WIDTH-1:0]        cfg_desc_ram_wdata_q  = 0;
   logic                             cfg_desc_ram_rd_req_winner_q = 0;
   logic                             cfg_desc_ram_wr_req_winner;
   logic                             cfg_desc_ram_rd_req_winner;
   
   logic                             desc_ram_wr;
   logic [DESC_RAM_WIDTH-1:0]        desc_ram_wdata;
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_waddr;
   logic                             desc_ram_rd;
   logic [DESC_RAM_WIDTH-1:0]        desc_ram_rdata;
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_raddr;
   
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_wr_ptr;
   logic                             desc_ram_wr_ptr_msb;
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_rd_ptr;
   logic                             desc_ram_rd_ptr_msb;
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_wr_ptr_next;
   logic                             desc_ram_wr_ptr_msb_next;
   logic [DESC_ADDR_WIDTH-1:0]       desc_ram_rd_ptr_next;
   logic                             desc_ram_rd_ptr_msb_next;
   logic                             desc_ram_pop;
   logic                             desc_ram_empty;
   logic                             desc_ram_full;
   
   logic                             desc_ram_oflow;
   logic                             desc_fifo_uflow;
   
   logic [DESC_RAM_WIDTH-1:0]        desc_dm_desc_ff_out;
   logic [DESC_WIDTH-1:0]            desc_dm_desc_ff_out_from_sav;
   
   // Pipeline the data into the descriptor RAM
   always @(posedge clk)
     if (!rst_n) begin
        ps_desc_wr_req_q <= 0;
        ps_desc_wdata_q <= '{default:'0};
     end
     else begin
        ps_desc_wr_req_q <= ps_desc_wr_req;
        if (~DESC_TYPE & H2C_N_C2H)
          ps_desc_wdata_q  <= h2c_cnv_desc_reg2sav(ps_desc_wdata);
        else if (DESC_TYPE & H2C_N_C2H)
          ps_desc_wdata_q  <= h2c_cnv_desc_comp2sav(ps_desc_wdata);
        else if (~DESC_TYPE & ~H2C_N_C2H)
          ps_desc_wdata_q  <= c2h_cnv_desc_reg2sav(ps_desc_wdata);
        else if (DESC_TYPE & ~H2C_N_C2H)
          ps_desc_wdata_q  <= c2h_cnv_desc_comp2sav(ps_desc_wdata);
        else
          ps_desc_wdata_q  <= ps_desc_wdata;
     end
   
   // PCIS has highest priority for write path
   assign ps_desc_ack = 1;
   
   // CSR Path to the Desc RAM
   always @(posedge clk)
     if (!rst_n) begin
        cfg_desc_ram_wr_req_q <= 0;
        cfg_desc_ram_rd_req_q <= 0;
        cfg_desc_ram_addr_q   <= 0;
        cfg_desc_ram_wdata_q  <= 0;
        cfg_desc_ram_rd_req_winner_q <= 0;
        desc_cfg_ram_ack <= 0;
        
     end
     else begin
        cfg_desc_ram_wr_req_q <= ~cfg_desc_ram_wr_req_q & cfg_desc_ram_wr_req ? 1'b1 : 
                        cfg_desc_ram_wr_req_q & cfg_desc_ram_wr_req_winner ? 1'b0 :
                        cfg_desc_ram_wr_req_q;
        
        cfg_desc_ram_rd_req_q <= ~cfg_desc_ram_rd_req_q & cfg_desc_ram_rd_req ? 1'b1 : 
                        cfg_desc_ram_rd_req_q & cfg_desc_ram_rd_req_winner ? 1'b0 :
                        cfg_desc_ram_rd_req_q;

        cfg_desc_ram_addr_q  <= cfg_desc_ram_addr;
        
        // cfg_desc_ram_wdata_q <= cfg_desc_ram_wdata;
        if (~DESC_TYPE & H2C_N_C2H)
          cfg_desc_ram_wdata_q <= h2c_cnv_desc_reg2sav(cfg_desc_ram_wdata);
        else if (DESC_TYPE & H2C_N_C2H)
          cfg_desc_ram_wdata_q <= h2c_cnv_desc_comp2sav(cfg_desc_ram_wdata);
        else if (~DESC_TYPE & ~H2C_N_C2H)
          cfg_desc_ram_wdata_q <= c2h_cnv_desc_reg2sav(cfg_desc_ram_wdata);
        else if (DESC_TYPE & ~H2C_N_C2H)
          cfg_desc_ram_wdata_q <= c2h_cnv_desc_comp2sav(cfg_desc_ram_wdata);
        else 
          cfg_desc_ram_wdata_q <= cfg_desc_ram_wdata;
        
        cfg_desc_ram_rd_req_winner_q <= cfg_desc_ram_rd_req_winner;
        
        desc_cfg_ram_ack <= cfg_desc_ram_wr_req_q ? cfg_desc_ram_wr_req_winner :
                            cfg_desc_ram_rd_req_winner_q;

        if (~DESC_TYPE & H2C_N_C2H)
          desc_cfg_ram_rdata <= h2c_cnv_desc_sav2reg(desc_ram_rdata);
        else if (DESC_TYPE & H2C_N_C2H)
          desc_cfg_ram_rdata <= h2c_cnv_desc_sav2comp(desc_ram_rdata);
        else if (~DESC_TYPE & ~H2C_N_C2H)
          desc_cfg_ram_rdata <= c2h_cnv_desc_sav2reg(desc_ram_rdata);
        else if (DESC_TYPE & ~H2C_N_C2H)
          desc_cfg_ram_rdata <= c2h_cnv_desc_sav2comp(desc_ram_rdata);
        else
          desc_cfg_ram_rdata <= desc_ram_rdata;

     end // else: !if(!rst_n)

   // Arbitrate between cfg write access and pcis writes
   assign desc_ram_wr = ps_desc_wr_req_q || cfg_desc_ram_wr_req_q;
   assign desc_ram_waddr = ps_desc_wr_req_q ? desc_ram_wr_ptr :
                           cfg_desc_ram_addr_q;
   assign desc_ram_wdata = ps_desc_wr_req_q ? ps_desc_wdata_q :
                           cfg_desc_ram_wdata_q;
   assign cfg_desc_ram_wr_req_winner = cfg_desc_ram_wr_req_q & ~ps_desc_wr_req_q;
   
   // Arbitrate between cfg read access and pcis reads
   assign desc_ram_rd = desc_ram_pop || cfg_desc_ram_rd_req_q;
   assign desc_ram_raddr = cfg_desc_ram_rd_req_winner ? cfg_desc_ram_addr_q : 
                           desc_ram_rd_ptr;
   assign cfg_desc_ram_rd_req_winner = cfg_desc_ram_rd_req_q & ~desc_ram_pop;
   
   // Desc RAM - Using 2 port RAM (1w1r)
   bram_1w1r #(.WIDTH(DESC_RAM_WIDTH), 
               .ADDR_WIDTH(DESC_ADDR_WIDTH),
               .DEPTH (DESC_RAM_DEPTH)
               ) DESC_RAM (.clk      (clk),
                           .wea      (1'b1),
                           .ena      (desc_ram_wr),
                           .addra    (desc_ram_waddr),
                           .da       (desc_ram_wdata),

                           .enb      (desc_ram_rd),
                           .addrb    (desc_ram_raddr),
                           .qb       (desc_ram_rdata)
                           );

   // FLow-through FIFO logic - need to read 1 desc per clock
   localparam DESC_RAM_DEPTH_MINUS1 = DESC_RAM_DEPTH - 1;
   
   ft_fifo #(.FIFO_WIDTH(DESC_RAM_WIDTH)
             ) DESC_FT_FIFO (.clk         (clk),
                             .rst_n       (1'b1),
                             .sync_rst_n  (rst_n),
                             .ram_fifo_empty (desc_ram_empty),
                             .ram_fifo_data  (desc_ram_rdata),
                             .ram_pop        (desc_ram_pop),
                             
                             .ft_pop   (dm_desc_pop),
                             .ft_valid (desc_dm_desc_valid),
                             .ft_data  (desc_dm_desc_ff_out)
                             );

   assign desc_dm_desc_ff_out_from_sav = (~DESC_TYPE & H2C_N_C2H)  ? h2c_cnv_desc_sav2reg(desc_dm_desc_ff_out) :
                                         ( DESC_TYPE & H2C_N_C2H)  ? h2c_cnv_desc_sav2comp(desc_dm_desc_ff_out) :
                                         (~DESC_TYPE & ~H2C_N_C2H) ? c2h_cnv_desc_sav2reg(desc_dm_desc_ff_out) :
                                         ( DESC_TYPE & ~H2C_N_C2H) ? c2h_cnv_desc_sav2comp(desc_dm_desc_ff_out) :
                                         desc_dm_desc_ff_out;
                                     
   assign desc_dm_desc = (~DESC_TYPE & H2C_N_C2H)  ? sde_pkg::h2c_cnv_desc_reg2comm (desc_dm_desc_ff_out_from_sav) : 
                         ( DESC_TYPE & H2C_N_C2H)  ? sde_pkg::h2c_cnv_desc_comp2comm(desc_dm_desc_ff_out_from_sav) : 
                         (~DESC_TYPE & ~H2C_N_C2H) ? sde_pkg::c2h_cnv_desc_reg2comm (desc_dm_desc_ff_out_from_sav) : sde_pkg::c2h_cnv_desc_comp2comm (desc_dm_desc_ff_out_from_sav);
   
   assign desc_ram_wr_ptr_next = (desc_ram_wr_ptr == DESC_RAM_DEPTH_MINUS1) ? ({DESC_ADDR_WIDTH{1'b0}}) : 
                                  desc_ram_wr_ptr + 1;
   assign desc_ram_wr_ptr_msb_next = (desc_ram_wr_ptr == DESC_RAM_DEPTH_MINUS1) ? ~desc_ram_wr_ptr_msb : desc_ram_wr_ptr_msb;
   
   assign desc_ram_rd_ptr_next = (desc_ram_rd_ptr == DESC_RAM_DEPTH_MINUS1) ? ({DESC_ADDR_WIDTH{1'b0}}) :
                                  desc_ram_rd_ptr + 1;
   assign desc_ram_rd_ptr_msb_next = (desc_ram_rd_ptr == DESC_RAM_DEPTH_MINUS1) ? ~desc_ram_rd_ptr_msb : desc_ram_rd_ptr_msb;
   
   always @(posedge clk)
     if (!rst_n) begin
        desc_ram_wr_ptr <= 0;
        desc_ram_rd_ptr <= 0;
        desc_ram_wr_ptr_msb <= 0;
        desc_ram_rd_ptr_msb <= 0;
        desc_ram_full <= 0;
        desc_ram_empty <= 1;
        desc_ram_oflow <= 0;
     end
     else begin
        {desc_ram_wr_ptr_msb, desc_ram_wr_ptr} <= ps_desc_wr_req_q ? {desc_ram_wr_ptr_msb_next, desc_ram_wr_ptr_next} : {desc_ram_wr_ptr_msb, desc_ram_wr_ptr};
        {desc_ram_rd_ptr_msb, desc_ram_rd_ptr} <= desc_ram_pop ? {desc_ram_rd_ptr_msb_next, desc_ram_rd_ptr_next} : {desc_ram_rd_ptr_msb, desc_ram_rd_ptr};
        desc_ram_empty <= ps_desc_wr_req_q  && ~desc_ram_pop ? 1'b0 :
                          ~ps_desc_wr_req_q &&  desc_ram_pop ? ({desc_ram_wr_ptr_msb, desc_ram_wr_ptr} == {desc_ram_rd_ptr_msb_next, desc_ram_rd_ptr_next}) :
                          desc_ram_empty;
        desc_ram_full <= ps_desc_wr_req_q  && ~desc_ram_pop ? (desc_ram_wr_ptr_msb_next != desc_ram_rd_ptr_msb) && (desc_ram_wr_ptr_next == desc_ram_rd_ptr) : 
                         ~ps_desc_wr_req_q &&  desc_ram_pop ? 1'b0 : desc_ram_full;
        desc_ram_oflow <= desc_ram_full & ps_desc_wr_req_q;
        desc_fifo_uflow <= ~desc_dm_desc_valid & dm_desc_pop;
     end // else: !if(!rst_n)
   assign desc_cfg_oflow = desc_ram_oflow;
   assign desc_cfg_uflow = desc_fifo_uflow;
   assign desc_cfg_empty = ~desc_dm_desc_valid;
   assign desc_cfg_full = desc_ram_full;
   
   always_comb begin
      desc_cfg_wr_ptr = 0;
      desc_cfg_wr_ptr = desc_ram_wr_ptr;
      desc_cfg_wr_ptr[15] = desc_ram_wr_ptr_msb;
      desc_cfg_rd_ptr = 0;
      desc_cfg_rd_ptr = desc_ram_rd_ptr;
      desc_cfg_rd_ptr[15] = desc_ram_rd_ptr_msb;
   end
   
   logic [31:0] cdt_consumed = 0;
   logic [31:0] cdt_limit = 0;
   
   // Credit Management
   
   always @(posedge clk)
     if (!rst_n) begin
        cdt_consumed <= 0;
        cdt_limit <= DESC_RAM_DEPTH;
     end
     else begin
        // Consumed
        // Will be incremented on every write from PCIS
        cdt_consumed <= cfg_desc_clr_cdt_consumed ? 0 : 
                        ps_desc_wr_req_q ? cdt_consumed + 1 : cdt_consumed;
        
        // Limit
        // Will be incremented on every pop of the descriptor from PCIS
        cdt_limit <= cfg_desc_clr_cdt_limit ? DESC_RAM_DEPTH : 
                     dm_desc_pop ? cdt_limit + 1 : cdt_limit;
        
     end // else: !if(!rst_n)
   assign desc_cfg_cdt_consumed = cdt_consumed;
   assign desc_cfg_cdt_limit = cdt_limit;
   
   logic [31:0] num_compl_desc;
   // Credit counters
   always @(posedge clk)
     if (!rst_n)
       num_compl_desc <= 0;
     else
       num_compl_desc <= cfg_desc_clr_desc_cnt ? 0 :
                         dm_desc_cnt_inc ? num_compl_desc + 1 : num_compl_desc;

   assign desc_cfg_desc_cnt = num_compl_desc;

   always @(posedge clk)
     if (!rst_n) begin
        desc_wb_limit_req <= 0;
        desc_wb_cnt_req   <= 0;
     end
     else begin
        desc_wb_limit_req <= dm_desc_pop;
        desc_wb_cnt_req   <= dm_desc_cnt_inc;
     end
   assign desc_wb_limit = cdt_limit;
   assign desc_wb_cnt   = num_compl_desc;

   // Temporarily
   assign desc_pm_arvalid = 0;
   assign desc_pm_rready = 0;



   function logic [DESC_RAM_WIDTH-1:0] h2c_cnv_desc_reg2sav (input [DESC_WIDTH-1:0] in_desc);
      sde_pkg::h2c_reg_sav_desc_t out_desc;
      sde_pkg::h2c_reg_desc_t in_desc_reg;

      out_desc = '{default:'0};
      in_desc_reg = '{default:'0};

      in_desc_reg = in_desc;

      out_desc.src_addr = in_desc_reg.src_addr;
      out_desc.len = in_desc_reg.len;
      out_desc.eop = in_desc_reg.eop;
      out_desc.spb = in_desc_reg.spb;
      out_desc.user = in_desc_reg.user;

      h2c_cnv_desc_reg2sav = out_desc;
   endfunction // h2c_cnv_desc_reg2sav

   function logic [DESC_RAM_WIDTH-1:0] c2h_cnv_desc_reg2sav (input [DESC_WIDTH-1:0] in_desc);
      sde_pkg::c2h_reg_sav_desc_t out_desc;
      sde_pkg::c2h_reg_desc_t in_desc_reg;

      out_desc = '{default:'0};
      in_desc_reg = '{default:'0};

      in_desc_reg = in_desc;

      out_desc.dest_addr = in_desc_reg.dest_addr;
      out_desc.len = in_desc_reg.len;

      c2h_cnv_desc_reg2sav = out_desc;   
   endfunction // c2h_cnv_desc_reg2sav
        
   function logic [DESC_WIDTH-1:0] h2c_cnv_desc_sav2reg (input [DESC_RAM_WIDTH-1:0] in_desc);
      sde_pkg::h2c_reg_desc_t out_desc;
      sde_pkg::h2c_reg_sav_desc_t in_desc_sav;
      
      out_desc = '{default:'0};
      in_desc_sav = '{default:'0};

      in_desc_sav = in_desc;

      out_desc.src_addr = in_desc_sav.src_addr;
      out_desc.len = in_desc_sav.len;
      out_desc.eop = in_desc_sav.eop;
      out_desc.spb = in_desc_sav.spb;
      out_desc.user = in_desc_sav.user;

      h2c_cnv_desc_sav2reg = out_desc;
   endfunction // h2c_cnv_desc_sav2reg

   function logic [DESC_WIDTH-1:0] c2h_cnv_desc_sav2reg (input [DESC_RAM_WIDTH-1:0] in_desc);
      sde_pkg::c2h_reg_desc_t out_desc;
      sde_pkg::c2h_reg_sav_desc_t in_desc_sav;
      
      out_desc = '{default:'0};
      in_desc_sav = '{default:'0};

      in_desc_sav = in_desc;

      out_desc.dest_addr = in_desc_sav.dest_addr;
      out_desc.len = in_desc_sav.len;

      c2h_cnv_desc_sav2reg = out_desc;
   endfunction // c2h_cnv_desc_sav2reg

   function logic [DESC_RAM_WIDTH-1:0] h2c_cnv_desc_comp2sav (input [DESC_WIDTH-1:0] in_desc);
      sde_pkg::h2c_comp_sav_desc_t out_desc;
      sde_pkg::h2c_comp_desc_t in_desc_comp;

      out_desc = '{default:'0};
      in_desc_comp = '{default:'0};

      in_desc_comp = in_desc;

      out_desc.src_addr = in_desc_comp.src_addr;
      out_desc.len = in_desc_comp.len;
      out_desc.eop = in_desc_comp.eop;
      out_desc.spb = in_desc_comp.spb;

      h2c_cnv_desc_comp2sav = out_desc;
   endfunction // h2c_cnv_desc_comp2sav

   function logic [DESC_RAM_WIDTH-1:0] c2h_cnv_desc_comp2sav (input [DESC_WIDTH-1:0] in_desc);
      sde_pkg::c2h_comp_sav_desc_t out_desc;
      sde_pkg::c2h_comp_desc_t in_desc_comp;

      out_desc = '{default:'0};
      in_desc_comp = '{default:'0};

      in_desc_comp = in_desc;

      out_desc.dest_addr = in_desc_comp.dest_addr;
      out_desc.len = in_desc_comp.len;

      c2h_cnv_desc_comp2sav = out_desc;   
   endfunction // c2h_cnv_desc_comp2sav
        
   function logic [DESC_WIDTH-1:0] h2c_cnv_desc_sav2comp (input [DESC_RAM_WIDTH-1:0] in_desc);
      sde_pkg::h2c_comp_desc_t out_desc;
      sde_pkg::h2c_comp_sav_desc_t in_desc_sav;
      
      out_desc = '{default:'0};
      in_desc_sav = '{default:'0};

      in_desc_sav = in_desc;

      out_desc.src_addr = in_desc_sav.src_addr;
      out_desc.len = in_desc_sav.len;
      out_desc.eop = in_desc_sav.eop;
      out_desc.spb = in_desc_sav.spb;

      h2c_cnv_desc_sav2comp = out_desc;
   endfunction // h2c_cnv_desc_sav2comp

   function logic [DESC_WIDTH-1:0] c2h_cnv_desc_sav2comp (input [DESC_RAM_WIDTH-1:0] in_desc);
      sde_pkg::c2h_comp_desc_t out_desc;
      sde_pkg::c2h_comp_sav_desc_t in_desc_sav;
      
      out_desc = '{default:'0};
      in_desc_sav = '{default:'0};

      in_desc_sav = in_desc;

      out_desc.dest_addr = in_desc_sav.dest_addr;
      out_desc.len = in_desc_sav.len;

      c2h_cnv_desc_sav2comp = out_desc;
   endfunction // c2h_cnv_desc_sav2comp

   
      

endmodule // sde_desc




    
    
    
    
    

