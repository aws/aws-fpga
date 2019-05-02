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

module axi4_slave_bfm #( parameter ECC_EN = 0, parameter ECC_ADDR_HI = 'h410, parameter ECC_ADDR_LO = 'h400, parameter RND_ECC_EN = 0, parameter RND_ECC_WEIGHT = 100)
   (

   input clk_core,
   input rst_n,
    
   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[15:0] cl_sh_ddr_awid,
   input[63:0] cl_sh_ddr_awaddr,
   input[7:0] cl_sh_ddr_awlen,
   input[2:0] cl_sh_ddr_awsize,
   input[1:0] cl_sh_ddr_awburst,        //Note only INCR/WRAP supported.  If un-supported mode on this signal, will default to INCR
   //input[10:0] cl_sh_ddr_awuser,
   input cl_sh_ddr_awvalid,
   output logic sh_cl_ddr_awready,

   input[15:0] cl_sh_ddr_wid,
   input[511:0] cl_sh_ddr_wdata,
   input[63:0] cl_sh_ddr_wstrb,
   input cl_sh_ddr_wlast,
   input cl_sh_ddr_wvalid,
   output logic sh_cl_ddr_wready,

   output logic[15:0] sh_cl_ddr_bid,
   output logic[1:0] sh_cl_ddr_bresp,
   output logic sh_cl_ddr_bvalid,
   input cl_sh_ddr_bready,

   input[15:0] cl_sh_ddr_arid,
   input[63:0] cl_sh_ddr_araddr,
   input[7:0] cl_sh_ddr_arlen,
   input[2:0] cl_sh_ddr_arsize,
   //input[10:0] cl_sh_ddr_aruser,
   input[1:0] cl_sh_ddr_arburst,     //Note only INCR/WRAP supported.  If un-supported mode on this signal, will default to INCR
   input cl_sh_ddr_arvalid,
   output logic sh_cl_ddr_arready,

   output logic[15:0] sh_cl_ddr_rid,
   output logic[511:0] sh_cl_ddr_rdata,
   output logic[1:0] sh_cl_ddr_rresp,
   output logic sh_cl_ddr_rlast,
   output logic sh_cl_ddr_rvalid,
   input        cl_sh_ddr_rready
   );

`include "axi_bfm_defines.svh"

   AXI_Command cl_sh_wr_cmds[$];
   AXI_Data    cl_sh_wr_data[$];
   AXI_Command cl_sh_rd_cmds[$];
   AXI_Command sh_cl_rd_data[$];
   AXI_Command sh_cl_b_resps[$];
   
   logic [31:0] model_memory[*];

   int   wr_cmd_cnt[0:3];
   AXI_Command  mem_wr_que[$];
   logic        first_wr_beat = 1;
   int          wr_last_cnt = 0;
   logic [63:0] wr_addr, wr_addr_t;

   bit           debug;

   initial begin
      debug = 1'b0;
   end
   
   // initial various counts for DMA operations
   initial begin
      for(int i=0; i<4; i++)
         wr_cmd_cnt[i] = 0;
   end

   //
   // cl->sh Write Address Channel
   //

   always @(posedge clk_core) begin
      AXI_Command cmd;
`ifdef QUESTA_SIM
      automatic int awready_cnt = 0;
`else
      int awready_cnt = 0;
`endif      
      if (cl_sh_ddr_awvalid && sh_cl_ddr_awready) begin
         cmd.addr = cl_sh_ddr_awaddr;
         cmd.id   = cl_sh_ddr_awid;
         cmd.len  = cl_sh_ddr_awlen;
         cmd.size = cl_sh_ddr_awsize;
         cmd.last = 0;
         
         cl_sh_wr_cmds.push_back(cmd);         
         sh_cl_b_resps.push_back(cmd);
         mem_wr_que.push_back(cmd);
      end

      if ((cl_sh_wr_cmds.size() < 32) || (awready_cnt == 0)) begin
         sh_cl_ddr_awready <= 1'b1;
         awready_cnt = $urandom_range(0, 80);
      end
      else begin
         sh_cl_ddr_awready <= 1'b0;
         awready_cnt--;
      end
   end

   //
   // cl->sh write Data Channel
   //

   always @(posedge clk_core) begin
      AXI_Data wr_data;
`ifdef QUESTA_SIM
      automatic int wready_cnt = 0;
      automatic int wready_nonzero_wait = 0;
`else      
      int wready_cnt = 0;
      int wready_nonzero_wait = 0;
`endif      
      if (sh_cl_ddr_wready && cl_sh_ddr_wvalid) begin
         wr_data.data = cl_sh_ddr_wdata;
         wr_data.strb = cl_sh_ddr_wstrb;
         wr_data.last = cl_sh_ddr_wlast;

         cl_sh_wr_data.push_back(wr_data);

         if (wr_data.last == 1)
           wr_last_cnt += 1;
         
      end // if (sh_cl_ddr_wready && cl_sh_ddr_wvalid)
      
      if ((cl_sh_wr_data.size() > 64) || (wready_cnt > 0)) begin
         sh_cl_ddr_wready <= 1'b0;
         wready_cnt--;
      end
      else begin
         sh_cl_ddr_wready <= 1'b1;
         wready_cnt = $urandom_range(10, 0);
         wready_nonzero_wait = $urandom_range(8, 0);
         wready_cnt = (wready_nonzero_wait == 0) ? wready_cnt : 0;
      end
   end

   //
   // cl->sh B Response Channel
   //

   always @(posedge clk_core) begin
      if (sh_cl_b_resps.size() != 0) begin
         if (debug) begin
            $display("[%t] : DEBUG resp.size  %2d ", $realtime, sh_cl_b_resps.size());
         end
         if (wr_last_cnt != 0) begin
            sh_cl_ddr_bid     <= sh_cl_b_resps[0].id;
            sh_cl_ddr_bresp   <= 2'b00;

            sh_cl_ddr_bvalid   <= !sh_cl_ddr_bvalid ? 1'b1 :
                                   !cl_sh_ddr_bready ? 1'b1 : 1'b0;

            if (cl_sh_ddr_bready && sh_cl_ddr_bvalid) begin
               wr_last_cnt -= 1;
               sh_cl_b_resps.pop_front();
               cl_sh_wr_cmds.pop_front();
            end
         end
      end
      else
        sh_cl_ddr_bvalid <= 1'b0;
      
   end // always @ (posedge clk_core)

   //
   // sh->cl Address Read Channel
   //

   always @(posedge clk_core) begin
      AXI_Command cmd;
`ifdef QUESTA_SIM      
      automatic int arready_cnt = 0;
`else
      int arready_cnt = 0;
`endif
      if (cl_sh_ddr_arvalid && sh_cl_ddr_arready) begin
         cmd.addr = cl_sh_ddr_araddr;
         cmd.id   = cl_sh_ddr_arid;
         cmd.len  = cl_sh_ddr_arlen;
         cmd.size = cl_sh_ddr_arsize;
         cmd.last = 0;

         cl_sh_rd_cmds.push_back(cmd);
         sh_cl_rd_data.push_back(cmd);
      end

      if ((cl_sh_rd_cmds.size() < 4) || (arready_cnt == 0)) begin
         sh_cl_ddr_arready <= 1'b1;
         arready_cnt = $urandom_range(0, 80);
      end
      else begin
         sh_cl_ddr_arready <= 1'b0;
         arready_cnt--;
      end
   end // always @ (posedge clk_core)


   
   //=================================================
   //
   // cl->sh PCIeM Interface
   //
   //=================================================
   
   
   always @(posedge clk_core) begin

      if (mem_wr_que.size() > 0) begin
         if (first_wr_beat == 1) begin
            wr_addr = mem_wr_que[0].addr;
            first_wr_beat = 1'b0;
         end

         if (cl_sh_wr_data.size() > 0) begin
            if (debug) begin
               $display("[%t] - DEBUG fb:  %1d  0x%0128x  0x%016x", $realtime, first_wr_beat, cl_sh_wr_data[0].data, cl_sh_wr_data[0].strb);
            end
            for(int i=wr_addr[5:2]; i<16; i++) begin
               logic [31:0] word;

               if (model_memory.exists({wr_addr[63:2], 2'b00}))
                 word = model_memory[{wr_addr[63:2], 2'b00}];
               else
                 word = 32'hffff_ffff;   // return a default value
               
               
               for(int j=0; j<4; j++) begin
                  logic [7:0] c;
                  int         index;
                  index = j + (i * 4);
                  
                  if (cl_sh_wr_data[0].strb[index]) begin
                     c = cl_sh_wr_data[0].data >> (index * 8);
                     //FIX partial DW order word = {c, word[31:8]};
                     word[8*j+:8] = c;
                  end
               end // for (int j=0; j<4; j++)

               model_memory[{wr_addr[63:2], 2'b00}] = word;
               
               wr_addr += 4;
            end
            if (cl_sh_wr_data[0].last == 1) begin
               first_wr_beat = 1'b1;
               mem_wr_que.pop_front();
               if (debug) begin
                  $display("[%t] - DEBUG reseting...", $realtime);
               end
               
            end
            
            cl_sh_wr_data.pop_front();
         end // if (cl_sh_wr_data.size() > 0)
      end // if (mem_wr_que.size() > 0)
   end // always @ (posedge clk_core)

   //
   // sh->cl Read Data Channel
   //
   logic first_rd_beat;
   logic [63:0] rd_addr, rd_addr_t;
   
   always @(posedge clk_core) begin
      AXI_Command rd_cmd;
      logic [511:0] beat;

      if (sh_cl_rd_data.size() != 0) begin
         sh_cl_ddr_rid    <= sh_cl_rd_data[0].id;
         sh_cl_ddr_rresp  <= 2'b00;
         sh_cl_ddr_rvalid <= !sh_cl_ddr_rvalid ? 1'b1 :
                                 !cl_sh_ddr_rready ? 1'b1 :
                                 !sh_cl_ddr_rlast  ? 1'b1 : 1'b0;

         sh_cl_ddr_rlast <= (sh_cl_rd_data[0].len == 0) ? 1'b1 :
                                (sh_cl_rd_data[0].len == 1) && sh_cl_ddr_rvalid && cl_sh_ddr_rready ? 1'b1 : 1'b0;
         
         if (first_rd_beat == 1'b1) begin
            rd_addr = sh_cl_rd_data[0].addr;
            first_rd_beat = 1'b0;
         end

         if (!sh_cl_ddr_rvalid || (sh_cl_ddr_rvalid && cl_sh_ddr_rready))
         begin
            beat = {512{1'b1}}; 
            for(int i=rd_addr[5:2]; i<16; i++) begin
               logic [31:0] c;

               if (debug) begin
                  $display("[%t] : DEBUG reading addr 0x%016x", $realtime, rd_addr);
               end
               
               if (model_memory.exists({rd_addr[63:2], 2'b00}))
                 c = model_memory[{rd_addr[63:2], 2'b00}];
               else
                 c = 32'hffffffff;
               
               beat = {c, beat[511:32]};
               rd_addr +=4;
            end
         end

         if (debug) begin
            $display("[%t] : DEBUG beat 0x%0128x", $realtime, beat);
         end
         sh_cl_ddr_rdata <= beat;

      end
      else begin
         sh_cl_ddr_rvalid <= 1'b0;
         sh_cl_ddr_rlast  <= 1'b0;         
         first_rd_beat = 1'b1;
      end

      if (cl_sh_ddr_rready && sh_cl_ddr_rvalid && (sh_cl_rd_data.size() != 0)) begin
         if (sh_cl_rd_data[0].len == 0) begin
            sh_cl_rd_data.pop_front();
            cl_sh_rd_cmds.pop_front();
            first_rd_beat = 1'b1;
         end
         else
         begin
           sh_cl_rd_data[0].len--;         
         end

      end
      
   end // always @ (posedge clk_core)

   function void axi_mem_bdr_write(input longint unsigned addr, byte d);
      int unsigned t;

      if (model_memory.exists({addr[63:2], 2'b00})) begin
         t = model_memory[{addr[63:2], 2'b00}];
      end
      else
         t = 32'hffff_ffff;
      
      t = t & ~(32'h0000_00ff  << (addr[1:0] * 8) );
      t = t | ({24'h000000, d} << (addr[1:0] * 8) );
      model_memory[{addr[63:2], 2'b00}] = t;
   endfunction // axi_mem_bdr_write

   function byte axi_mem_bdr_read(input longint unsigned addr);
      byte d;

      int unsigned t;
      if (model_memory.exists({addr[63:2], 2'b00})) begin
         t = model_memory[{addr[63:2], 2'b00}];
         t = t >> (addr[1:0] * 8);
         d = t[7:0];
      end
      else
         d = 'hff;
      return d;
   endfunction // axi_mem_bdr_read
   
endmodule
