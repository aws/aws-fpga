// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

   import "DPI-C" function longint fopen(input string name, string mode);
   import "DPI-C" function void fclose(input longint handle);
   import "DPI-C" function byte fgetc(input longint handle);
   import "DPI-C" function byte fputc(input byte c, longint handle);
   import "DPI-C" function int feof(input longint handle);
   import "DPI-C" function int fseek(input longint handle, longint offset, int whence);
   
typedef struct {
   logic [63:0] addr;
   logic [7:0]  len;
   logic [5:0]  id;
   longint      clock_cnt;
} AXI_Command;
   
typedef struct {
   logic [511:0] data;
   logic [63:0]  strb;
   logic [5:0]   id;
   logic         last;
} AXI_Data;
   
module ddr_ctrl #( parameter ID = 0)(
   //---------------------------
   // Main clock/reset
   //---------------------------
   input clk,
   input rst_n,

   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[5:0] cl_hl_ddr_awid,
   input[63:0] cl_hl_ddr_awaddr,
   input[7:0] cl_hl_ddr_awlen,

   input cl_hl_ddr_awvalid,
   output logic hl_cl_ddr_awready,

   input[5:0] cl_hl_ddr_wid,
   input[511:0] cl_hl_ddr_wdata,
   input[63:0] cl_hl_ddr_wstrb,
   input cl_hl_ddr_wlast,
   input cl_hl_ddr_wvalid,
   output logic hl_cl_ddr_wready,

   output logic[5:0] hl_cl_ddr_bid,
   output logic[1:0] hl_cl_ddr_bresp,
   output logic hl_cl_ddr_bvalid,
   input cl_hl_ddr_bready,

   input[5:0] cl_hl_ddr_arid,
   input[63:0] cl_hl_ddr_araddr,
   input[7:0] cl_hl_ddr_arlen,
   //input[10:0] cl_hl_ddr_aruser,
   input cl_hl_ddr_arvalid,
   output logic hl_cl_ddr_arready,

   output logic[5:0] hl_cl_ddr_rid,
   output logic[511:0] hl_cl_ddr_rdata,
   output logic[1:0] hl_cl_ddr_rresp,
   output logic hl_cl_ddr_rlast,
   output logic hl_cl_ddr_rvalid,
   input cl_hl_ddr_rready

                );


   AXI_Command wr_cmds[$];
   AXI_Data    wr_data[$];
   AXI_Command rd_cmds[$];
   AXI_Command rd_data[$];
   AXI_Command b_resps[$];
   AXI_Command file_wr_que[$];
   
   longint w_clk_cnt;
   longint r_clk_cnt;
   
   string  memory_file;   
   longint h;  // memory file handle
   
   
   function void sv_fseek(input longint pos);
      begin
         int result;
         
         result = fseek(h, pos[34:0], 0); // TODO: add check for address beyond file size
         if (result != 0) begin
            $display("Error - memory file seek error - pos: %9x", pos);
            $finish;
         end
         else
           $display("%t seeking to %x", $time(), pos[34:0]);
         
      end
   endfunction // sv_fseek
   
   //
   // Address Write Channel
   //
   always @(posedge clk) begin
      AXI_Command cmd;

      if (rst_n) begin
         if (cl_hl_ddr_awvalid & hl_cl_ddr_awready) begin
            cmd.addr      = cl_hl_ddr_awaddr;
            cmd.len       = cl_hl_ddr_awlen;
            cmd.id        = cl_hl_ddr_awid;
            cmd.clock_cnt = w_clk_cnt;
            
            $display("%t - awaddr: %h", $time(), cl_hl_ddr_awaddr);
            
            wr_cmds.push_back(cmd);
         end

         w_clk_cnt++;
         
      end
      else
        w_clk_cnt = 0;
   end

   always @(posedge clk) begin
      if (~rst_n) 
        hl_cl_ddr_awready <= 1'b0;
      else
        hl_cl_ddr_awready <= (wr_cmds.size() < 4) ? 1'b1 : 1'b0;
   end

   always @(posedge clk) begin
      
      if (wr_cmds.size() != 0) begin

         if (w_clk_cnt > (wr_cmds[0].clock_cnt + 10)) begin
            file_wr_que.push_back(wr_cmds.pop_front());      // send command to write file
         end
      end
      
   end

   //
   // Write Data Channel
   //
   always @(posedge clk) begin
      AXI_Data data;

      if (rst_n) begin
         if (cl_hl_ddr_wvalid & hl_cl_ddr_wready) begin
            data.data     = cl_hl_ddr_wdata;
            data.id       = cl_hl_ddr_wid;
            data.strb     = cl_hl_ddr_wstrb;
            data.last     = cl_hl_ddr_wlast;

            $display("%t - wdata: %h", $time(), cl_hl_ddr_wdata);
            
            wr_data.push_back(data);
         end

      end

   end

   //
   // Write memory file
   //
   logic first_wr_beat;
   logic [63:0] wr_addr;
   
   always @(posedge clk) begin
      if (rst_n == 1'b0)
        first_wr_beat = 1;
      else if (file_wr_que.size() > 0) begin

         if (first_wr_beat == 1'b1) begin
            wr_addr = file_wr_que[0].addr;
            first_wr_beat = 1'b0;
         end

         if (wr_data.size() > 0) begin
            sv_fseek(wr_addr[34:0]);

            $display("%t - fb: %d writing data: %x, %x", $time(), first_wr_beat, wr_data[0].data, wr_data[0].strb);
            
            for(int i=0; i<64; i++) begin
               byte c;
               c = wr_data[0].data >> (i * 8);

               if (wr_data[0].strb[i] == 1'b1)     // TODO: verify masked byptes
                 fputc(c, h);
               else
                 fputc(fgetc(h), h);  // read and write same byte to advance file ptr
               
               wr_addr++;
            end
//         else begin
//            $display("Error - Write data underrun");
//            $finish;
//         end

            if (wr_data[0].last == 1) begin
               b_resps.push_back(file_wr_que.pop_front());
               first_wr_beat = 1'b1;            
            end
                  
            wr_data.pop_front();
         end // if (wr_data.size() > 0)
         
      end // if (file_wr_que.size() > 0)
//      else begin
//         first_wr_beat = 1'b1;            
//      end
   end
   
   always @(posedge clk) begin
      if (~rst_n) 
        hl_cl_ddr_wready <= 1'b0;
      else
        hl_cl_ddr_wready <= (wr_data.size() < 16) ? 1'b1 : 1'b0;
   end

   //
   // BResp Channel
   //
   always @(posedge clk) begin
      if (b_resps.size() != 0) begin

         hl_cl_ddr_bid    <= b_resps[0].id;
         hl_cl_ddr_bresp  <= 2'b00;
         hl_cl_ddr_bvalid <= !hl_cl_ddr_bvalid ? 1'b1 :
                             !cl_hl_ddr_bready ? 1'b1 : 1'b0;

         if (cl_hl_ddr_bready && hl_cl_ddr_bvalid) begin
            $display("%t - debug popping bresp fifo - %d", $time(), b_resps.size());
            b_resps.pop_front();
         end

      end
      else
         hl_cl_ddr_bvalid <= 1'b0;


   end
   
   //
   // Address Read Channel
   //
   always @(posedge clk) begin
      AXI_Command cmd;

      if (rst_n) begin
         if (cl_hl_ddr_arvalid & hl_cl_ddr_arready) begin
            cmd.addr      = cl_hl_ddr_araddr;
            cmd.len       = cl_hl_ddr_arlen;
            cmd.id        = cl_hl_ddr_arid;
            cmd.clock_cnt = r_clk_cnt;
            
            rd_cmds.push_back(cmd);
         end

         r_clk_cnt++;
         
      end
      else
        r_clk_cnt = 0;
   end

   always @(posedge clk) begin
      if (~rst_n) 
        hl_cl_ddr_arready <= 1'b0;
      else
        hl_cl_ddr_arready <= (rd_cmds.size() < 4) ? 1'b1 : 1'b0;
   end

   //
   // Read Data Channel
   //

   always @(posedge clk) begin
      
      if (rd_cmds.size() != 0) begin
         if (r_clk_cnt > (rd_cmds[0].clock_cnt + 10))
           rd_data.push_back(rd_cmds.pop_front());
      end
      
   end

   logic first_rd_beat;
   logic [63:0] rd_addr;
   
   always @(posedge clk) begin
      int cnt;
      logic [511:0] beat;
      
      if (rd_data.size() != 0) begin

         $display("%t - debug %d", $time(), rd_data[0].len);
         
         hl_cl_ddr_rid    <= rd_data[0].id;
         hl_cl_ddr_rresp  <= 2'b00;
         hl_cl_ddr_rvalid <= !hl_cl_ddr_rvalid ? 1'b1 :
                             !cl_hl_ddr_rready ? 1'b1 : 
                             !hl_cl_ddr_rlast  ? 1'b1 : 1'b0;
         
         hl_cl_ddr_rlast  <= (rd_data[0].len == 0) ? 1'b1 : 
                             (rd_data[0].len == 1) && hl_cl_ddr_rvalid && cl_hl_ddr_rready ? 1'b1: 1'b0;
          
         if (first_rd_beat == 1'b1) begin
            rd_addr = rd_data[0].addr;
            first_rd_beat = 1'b0;
         end

         if (hl_cl_ddr_rvalid & cl_hl_ddr_rready)
           rd_addr+=64;
            
         sv_fseek(rd_addr[34:0]);

         for(int i=0; i<64; i++) begin
            beat[503:0] = beat[511:8];
            beat[511:504] = fgetc(h);
         end
         hl_cl_ddr_rdata <= beat;
         
      end
      else begin
         hl_cl_ddr_rvalid <= 1'b0;
         hl_cl_ddr_rlast  <= 1'b1;
         first_rd_beat = 1'b1;
      end

      if (cl_hl_ddr_rready && hl_cl_ddr_rvalid && (rd_data.size() != 0)) begin
         if (rd_data[0].len == 0) begin
            rd_data.pop_front();
            first_rd_beat = 1'b1;
         end
         else
           rd_data[0].len--;         

      end

   end
   
initial begin
   string filename;
   string arg;
   string index;
   
   index = "0123";
   arg = "MEMORY_FILE";
   arg = {arg, index[ID], "=%s"};  // append index ID = %s to arg string
   
   if ($value$plusargs(arg, filename))
     memory_file = filename;
   else
     memory_file = "memory.bin";
   
   $display("%m - ID: %1d - opening memory %s", ID, memory_file);
   
   h = fopen(memory_file, "r+b");
   if (h == 0) begin
      $display("Error - Unable to open memory file.");
      $finish;
   end
   
end
   

endmodule // ddr_ctrl

module hl_ddr #( parameter NUM_DDR = 4)
   (

   //---------------------------
   // Main clock/reset
   //---------------------------
   input clk,
   input rst_n,

   //--------------------------
   // DDR Physical Interface
   //--------------------------

// ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
    input                CLK_300M_DIMM0_DP,
    input                CLK_300M_DIMM0_DN,
    output logic         M_A_ACT_N,
    output logic[16:0]   M_A_MA,
    output logic[1:0]    M_A_BA,
    output logic[1:0]    M_A_BG,
    output logic[0:0]    M_A_CKE,
    output logic[0:0]    M_A_ODT,
    output logic[0:0]    M_A_CS_N,
    output logic[0:0]    M_A_CLK_DN,
    output logic[0:0]    M_A_CLK_DP,
    output logic         RST_DIMM_A_N,
    output logic         M_A_PAR,
    inout  [63:0]        M_A_DQ,
    inout  [7:0]         M_A_ECC,
    inout  [17:0]        M_A_DQS_DP,
    inout  [17:0]        M_A_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
    input                CLK_300M_DIMM1_DP,
    input                CLK_300M_DIMM1_DN,
    output logic         M_B_ACT_N,
    output logic[16:0]   M_B_MA,
    output logic[1:0]    M_B_BA,
    output logic[1:0]    M_B_BG,
    output logic[0:0]    M_B_CKE,
    output logic[0:0]    M_B_ODT,
    output logic[0:0]    M_B_CS_N,
    output logic[0:0]    M_B_CLK_DN,
    output logic[0:0]    M_B_CLK_DP,
    output logic         RST_DIMM_B_N,
    output logic         M_B_PAR,
    inout  [63:0]        M_B_DQ,
    inout  [7:0]         M_B_ECC,
    inout  [17:0]        M_B_DQS_DP,
    inout  [17:0]        M_B_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
    input                CLK_300M_DIMM2_DP,
    input                CLK_300M_DIMM2_DN,
    output logic         M_C_ACT_N,
    output logic[16:0]   M_C_MA,
    output logic[1:0]    M_C_BA,
    output logic[1:0]    M_C_BG,
    output logic[0:0]    M_C_CKE,
    output logic[0:0]    M_C_ODT,
    output logic[0:0]    M_C_CS_N,
    output logic[0:0]    M_C_CLK_DN,
    output logic[0:0]    M_C_CLK_DP,
    output logic         RST_DIMM_C_N,
    output logic         M_C_PAR,
    inout  [63:0]        M_C_DQ,
    inout  [7:0]         M_C_ECC,
    inout  [17:0]        M_C_DQS_DP,
    inout  [17:0]        M_C_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
    input                CLK_300M_DIMM3_DP,
    input                CLK_300M_DIMM3_DN,
    output logic         M_D_ACT_N,
    output logic[16:0]   M_D_MA,
    output logic[1:0]    M_D_BA,
    output logic[1:0]    M_D_BG,
    output logic[0:0]    M_D_CKE,
    output logic[0:0]    M_D_ODT,
    output logic[0:0]    M_D_CS_N,
    output logic[0:0]    M_D_CLK_DN,
    output logic[0:0]    M_D_CLK_DP,
    output logic         RST_DIMM_D_N,
    output logic         M_D_PAR,
    inout  [63:0]        M_D_DQ,
    inout  [7:0]         M_D_ECC,
    inout  [17:0]        M_D_DQS_DP,
    inout  [17:0]        M_D_DQS_DN,


   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[5:0] cl_hl_ddr_awid[NUM_DDR-1:0],
   input[63:0] cl_hl_ddr_awaddr[NUM_DDR-1:0],
   input[7:0] cl_hl_ddr_awlen[NUM_DDR-1:0],
   //input[10:0] cl_hl_ddr_awuser[NUM_DDR-1:0],
   input cl_hl_ddr_awvalid[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] hl_cl_ddr_awready,

   input[5:0] cl_hl_ddr_wid[NUM_DDR-1:0],
   input[511:0] cl_hl_ddr_wdata[NUM_DDR-1:0],
   input[63:0] cl_hl_ddr_wstrb[NUM_DDR-1:0],
   input[NUM_DDR-1:0] cl_hl_ddr_wlast,
   input[NUM_DDR-1:0] cl_hl_ddr_wvalid,
   output logic[NUM_DDR-1:0] hl_cl_ddr_wready,

   output logic[5:0] hl_cl_ddr_bid[NUM_DDR-1:0],
   output logic[1:0] hl_cl_ddr_bresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] hl_cl_ddr_bvalid,
   input[NUM_DDR-1:0] cl_hl_ddr_bready,

   input[5:0] cl_hl_ddr_arid[NUM_DDR-1:0],
   input[63:0] cl_hl_ddr_araddr[NUM_DDR-1:0],
   input[7:0] cl_hl_ddr_arlen[NUM_DDR-1:0],

   input[NUM_DDR-1:0] cl_hl_ddr_arvalid,
   output logic[NUM_DDR-1:0] hl_cl_ddr_arready,

   output logic[5:0] hl_cl_ddr_rid[NUM_DDR-1:0],
   output logic[511:0] hl_cl_ddr_rdata[NUM_DDR-1:0],
   output logic[1:0] hl_cl_ddr_rresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] hl_cl_ddr_rlast,
   output logic[NUM_DDR-1:0] hl_cl_ddr_rvalid,
   input[NUM_DDR-1:0] cl_hl_ddr_rready,

   output logic[NUM_DDR-1:0] hl_cl_ddr_is_ready,

   input[31:0] hl_ddr_stat_addr,
   input hl_ddr_stat_wr,
   input hl_ddr_stat_rd,
   input[31:0] hl_ddr_stat_wdata,
   input[1:0] hl_ddr_stat_sel,
                                                         
   output logic ddr_hl_stat_ack,
   output logic[31:0] ddr_hl_stat_rdata
   );

//-------------------------------------------
// Internal signals
//-------------------------------------------

//----------------------------------------------------------
// DDR Controllers
//----------------------------------------------------------
   
genvar gi;
generate
begin
   for (gi=0; gi<NUM_DDR; gi++)
   begin:ddr_inst

      ddr_ctrl #(.ID(gi)) 
               ddr_ctrl_inst(.clk(clk),
                             .rst_n(rst_n),

                             .cl_hl_ddr_awvalid(cl_hl_ddr_awvalid[gi]),
                             .cl_hl_ddr_awaddr(cl_hl_ddr_awaddr[gi]),
                             .cl_hl_ddr_awlen(cl_hl_ddr_awlen[gi]),
                             .cl_hl_ddr_awid(cl_hl_ddr_awid[gi]),
                             .hl_cl_ddr_awready(hl_cl_ddr_awready[gi]),
                             
                             .cl_hl_ddr_wid(cl_hl_ddr_wid[gi]),
                             .cl_hl_ddr_wdata(cl_hl_ddr_wdata[gi]),
                             .cl_hl_ddr_wstrb(cl_hl_ddr_wstrb[gi]),
                             .cl_hl_ddr_wlast(cl_hl_ddr_wlast[gi]),
                             .cl_hl_ddr_wvalid(cl_hl_ddr_wvalid[gi]),
                             .hl_cl_ddr_wready(hl_cl_ddr_wready[gi]),

                             .hl_cl_ddr_bid(hl_cl_ddr_bid[gi]),
                             .hl_cl_ddr_bresp(hl_cl_ddr_bresp[gi]),
                             .hl_cl_ddr_bvalid(hl_cl_ddr_bvalid[gi]),
                             .cl_hl_ddr_bready(cl_hl_ddr_bready[gi]),

                             .cl_hl_ddr_arid(cl_hl_ddr_arid[gi]),
                             .cl_hl_ddr_araddr(cl_hl_ddr_araddr[gi]),
                             .cl_hl_ddr_arlen(cl_hl_ddr_arlen[gi]),
                             .cl_hl_ddr_arvalid(cl_hl_ddr_arvalid[gi]),
                             .hl_cl_ddr_arready(hl_cl_ddr_arready[gi]),
                             .hl_cl_ddr_rid(hl_cl_ddr_rid[gi]),
                             .hl_cl_ddr_rdata(hl_cl_ddr_rdata[gi]),
                             .hl_cl_ddr_rresp(hl_cl_ddr_rresp[gi]),
                             .hl_cl_ddr_rlast(hl_cl_ddr_rlast[gi]),
                             .hl_cl_ddr_rvalid(hl_cl_ddr_rvalid[gi]),
                             .cl_hl_ddr_rready(cl_hl_ddr_rready[gi])
                             );
      
   end



end
endgenerate


   always @(posedge clk) begin
      if (~rst_n) 
        hl_cl_ddr_is_ready <= 4'b0;
      else begin
        hl_cl_ddr_is_ready <= 4'hf;
      end
   end

endmodule // hl_ddr
