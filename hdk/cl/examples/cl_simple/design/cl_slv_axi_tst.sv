// AXI Transaction Generator

module cl_slv_axi_tst #(parameter DATA_WIDTH = 512,
                        parameter ADDR_WIDTH = 64,
                        parameter A_ID_WIDTH = 5,
                        parameter D_ID_WIDTH = 5,
                        parameter LEN_WIDTH  = 8,
                        parameter A_USER_WIDTH = 10,
                        parameter W_USER_WIDTH = 10,
                        parameter B_USER_WIDTH = 10,
                        parameter R_USER_WIDTH = 10,
                        parameter RST_SYNC = 1
                        ) 
   (
    input                           clk,
    input                           rst_n,

    input [31:0]                    cfg_addr,
    input [31:0]                    cfg_wdata,
    input                           cfg_wr,
    input                           cfg_rd,
    output logic                    tst_cfg_ack,
    output logic [31:0]             tst_cfg_rdata,

    input [A_ID_WIDTH-1:0]          awid,
    input [ADDR_WIDTH-1:0]          awaddr,
    input [LEN_WIDTH-1:0]           awlen,
    input                           awvalid,
    input [A_USER_WIDTH-1:0]        awuser,
    output logic                    awready,

    input [5:0]                     wid,
    input [DATA_WIDTH-1:0]          wdata,
    input [(DATA_WIDTH/8)-1:0]      wstrb,
    input                           wlast,
    input                           wvalid,
    input [W_USER_WIDTH-1:0]        wuser,
    output logic                    wready,

    output logic [D_ID_WIDTH-1:0]   bid,
    output logic [1:0]              bresp,
    output logic                    bvalid,
    output logic [B_USER_WIDTH-1:0] buser,
    input                           bready,

    input [A_ID_WIDTH-1:0]          arid,
    input [ADDR_WIDTH-1:0]          araddr,
    input [LEN_WIDTH-1:0]           arlen,
    input                           arvalid,
    input [A_USER_WIDTH-1:0]        aruser,
    output logic                    arready,

    output logic [D_ID_WIDTH-1:0]   rid,
    output logic [DATA_WIDTH-1:0]   rdata,
    output logic [1:0]              rresp,
    output logic                    rlast,
    output logic                    rvalid,
    output logic [R_USER_WIDTH-1:0] ruser,
    input                           rready
   );

   // Registers

   // Write Address Channel
   // 0x0 : Write Address Control
   //       0 : Set AW Ready (Write), AWREADY (Read)
   //       1 : AW Done (W1C)
   // 0x4 : Write Address [31:0]  (RO)
   // 0x8 : Write Address [63:32] (RO)
   // 0xC : AW Length and ID (RO)
   //   15:00 : AW Length
   //   31:16 : AW ID
   // 0x10 : AW User (RO)
   
   // Write Data Channel
   // 0x20 : Write Data Control
   //       0 : Set W Ready (Write), WREADY (Read)
   //       1 : W Done (W1C)
   //     3:2 : RSVD
   //       4 : WLAST (RO)
   // 0x24 : Write Data Index (Auto Increment on Write Data Read)
   // 0x28 : Write Data (RO)
   // 0x2C : Write Strobe [31:00] (RO)
   // 0x30 : Write Strobe [63:32] (RO)
   // 0x34 : Write ID (RO)
   // 0x38 : Write User (RO)
   
   // Write Resp Channel 
   // 0x40 : B Channel Control (BRESP)
   //       0 : Set B Valid (Write), BVALID (Read)
   //       1 : B Done (W1C)
   //     3:2 : B RESP (RW)
   // 0x44 : B ID (RW)
   // 0x48 : B User (RW)

   // Read Address Channel
   // 0x60 : Read Address Control
   //       0 : Set AR Ready (Write), ARREADY (Read)
   //       1 : AR Done (W1C)
   // 0x64 : Read Address [31:00] (RO)
   // 0x68 : Read Address [63:32] (RO)
   // 0x6C : AR Length and ID (RO)
   //   15:00 : AR Length 
   //   31:16 : AR ID
   // 0x70 : AR User (RO)
   
   // Read Data Channel
   // 0x80 : Read Channel Control (RRESP, RLAST)
   //       0 : Set R Valid (Write), RVALID (Read)
   //       1 : R Done (W1C)
   //     3:2 : R RESP (RW)
   //       4 : R LAST (RW)
   // 0x84 : Read Data Index (Auto Increment on Read Data Write)
   // 0x88 : Read Data
   // 0x8C : Read ID (RW)
   // 0x90 : Read User (RW)

   parameter NUM_DW = DATA_WIDTH / 32;

   logic     pre_sync_rst_n;
   logic     sync_rst_n;
   
   // Synchronize RST
   generate
      if (RST_SYNC != 0)
        always_ff @(negedge rst_n or posedge clk)
          if (!rst_n)
            begin
               pre_sync_rst_n <= 0;
               sync_rst_n <= 0;
            end
          else
            begin
               pre_sync_rst_n <= 1;
               sync_rst_n <= pre_sync_rst_n;
            end
      else
        assign sync_rst_n = rst_n;
   endgenerate

   logic                        cfg_wr_stretch;
   logic                        cfg_rd_stretch;

   logic [7:0]                  cfg_addr_q;        //Only care about lower 8-bits of address, upper bits are decoded somewhere else
   logic [31:0]                 cfg_wdata_q;

   logic                        cfg_aw_done;
   logic [63:0]                 cfg_aw_addr;
   logic [LEN_WIDTH-1:0]        cfg_aw_len;
   logic [A_ID_WIDTH-1:0]       cfg_aw_id;
   logic [A_USER_WIDTH-1:0]     cfg_aw_user;
   logic                        cfg_w_done;
   logic [DATA_WIDTH-1:0]       cfg_w_data;
   logic [15:0]                 cfg_w_index;
   logic [31:0]                 cfg_w_data_mx;
   logic [D_ID_WIDTH-1:0]       cfg_w_id;
   logic [W_USER_WIDTH-1:0]     cfg_w_user;
   logic [63:0]                 cfg_w_strb;
   logic                        cfg_w_last;
   logic                        cfg_b_done;
   logic [1:0]                  cfg_b_resp;
   logic [D_ID_WIDTH-1:0]       cfg_b_id;
   logic [B_USER_WIDTH-1:0]     cfg_b_user;
   logic                        cfg_ar_done;
   logic [63:0]                 cfg_ar_addr;
   logic [LEN_WIDTH-1:0]        cfg_ar_len;
   logic [A_ID_WIDTH-1:0]       cfg_ar_id;
   logic [A_USER_WIDTH-1:0]     cfg_ar_user;
   logic                        cfg_r_done;
   logic [DATA_WIDTH-1:0]       cfg_r_data;
   logic                        cfg_r_last;
   logic [1:0]                  cfg_r_resp;
   logic [D_ID_WIDTH-1:0]       cfg_r_id;
   logic [R_USER_WIDTH-1:0]     cfg_r_user;
   logic [31:0]                 cfg_r_data_mx;
   logic [15:0]                 cfg_r_index;
   
   //Commands are single cycle pulse, stretch here
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
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
       end // else: !if(!sync_rst_n)

   //Ack for cycle
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n)
       tst_cfg_ack <= 0;
     else
       tst_cfg_ack <= ((cfg_wr_stretch||cfg_rd_stretch) && !tst_cfg_ack); 

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) begin

        cfg_b_resp <= '{default:'0};
        cfg_b_id <= '{default:'0};
        cfg_b_user <= '{default:'0};
        
        cfg_r_last <= 1'b0;
        cfg_r_resp <= '{default:'0};
        cfg_r_id <= '{default:'0};
        cfg_r_user <= '{default:'0};

     end // if (!sync_rst_n)
     else if (cfg_wr_stretch) begin

        if (cfg_addr_q == 8'h40)
          cfg_b_resp <= cfg_wdata_q[3:2];
        else if (cfg_addr_q == 8'h44)
          cfg_b_id <= cfg_wdata_q;
        else if (cfg_addr_q == 8'h48)
          cfg_b_user <= cfg_wdata_q;

        else if (cfg_addr_q == 8'h80)
          {cfg_r_last, cfg_r_resp} <= {cfg_wdata_q[4], cfg_wdata_q[3:2]};
        else if (cfg_addr_q == 8'h8C)
          cfg_r_id <= cfg_wdata_q;
        else if (cfg_addr_q == 8'h90)
          cfg_r_user <= cfg_wdata_q;
        
     end // if (cfg_wr_stretch)
   
   //Readback mux
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       tst_cfg_rdata <= 0;
   else
     case (cfg_addr_q)
       8'h00 : tst_cfg_rdata <= {cfg_aw_done, awready};
       8'h04 : tst_cfg_rdata <= cfg_aw_addr[31:0];
       8'h08 : tst_cfg_rdata <= cfg_aw_addr[63:32];
       8'h0C : tst_cfg_rdata <= {cfg_aw_id, cfg_aw_len};
       8'h10 : tst_cfg_rdata <= cfg_aw_user;

       8'h20 : tst_cfg_rdata <= {cfg_w_last, 2'b00, cfg_w_done, wready};
       8'h24 : tst_cfg_rdata <= cfg_w_index;
       8'h28 : tst_cfg_rdata <= cfg_w_data_mx;
       8'h2C : tst_cfg_rdata <= cfg_w_strb[31:0];
       8'h30 : tst_cfg_rdata <= cfg_w_strb[63:32];
       8'h34 : tst_cfg_rdata <= cfg_w_id;
       8'h38 : tst_cfg_rdata <= cfg_w_user;

       8'h40 : tst_cfg_rdata <= {cfg_b_resp, cfg_b_done, bvalid};
       8'h44 : tst_cfg_rdata <= cfg_b_id;
       8'h48 : tst_cfg_rdata <= cfg_b_user;
       
       8'h60 : tst_cfg_rdata <= {cfg_ar_done, arready};
       8'h64 : tst_cfg_rdata <= cfg_ar_addr[31:0];
       8'h68 : tst_cfg_rdata <= cfg_ar_addr[63:32];
       8'h6C : tst_cfg_rdata <= {cfg_ar_id, cfg_ar_len};
       8'h70 : tst_cfg_rdata <= cfg_ar_user;

       8'h80 : tst_cfg_rdata <= {cfg_r_last, cfg_r_resp, cfg_r_done, rvalid};
       8'h84 : tst_cfg_rdata <= cfg_r_index;
       8'h88 : tst_cfg_rdata <= cfg_r_data_mx;
       8'h8C : tst_cfg_rdata <= cfg_r_id;
       8'h90 : tst_cfg_rdata <= cfg_r_user;

       default: tst_cfg_rdata <= 32'hdeaddead;
     endcase // case (cfg_addr_q)


   ///////////////////////// AW Channel ///////////////////////////
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       awready <= 1'b0;
     else
       awready <= cfg_wr_stretch && cfg_wdata_q[0] && (cfg_addr_q == 8'h00) ? 1'b1 :
                  awvalid && awready ? 1'b0 :
                  awready;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_aw_done <= 1'b0;
     else
       cfg_aw_done <= awvalid && awready ? 1'b1 :
                      cfg_wr_stretch && cfg_wdata_q[1] && (cfg_addr_q == 8'h00) ? 1'b0 :
                      cfg_aw_done;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       {cfg_aw_len, cfg_aw_id, cfg_aw_user} <= '{default:'0};
     else
       {cfg_aw_len, cfg_aw_id, cfg_aw_user} <= awvalid && awready ? {awlen, awid, awuser} : {cfg_aw_len, cfg_aw_id, cfg_aw_user};

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_aw_addr <= '{default:'0};
     else
       cfg_aw_addr <= awvalid && awready ? awaddr : cfg_aw_addr;


   /////////////////////////  W Channel ///////////////////////////
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       wready <= 1'b0;
     else
       wready <= cfg_wr_stretch && cfg_wdata_q[0] && (cfg_addr_q == 8'h20) ? 1'b1 :
                 wvalid && wready ? 1'b0 :
                 wready;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_w_done <= 1'b0;
     else
       cfg_w_done <= wvalid && wready ? 1'b1 :
                     cfg_wr_stretch && cfg_wdata_q[1] && (cfg_addr_q == 8'h20) ? 1'b0 :
                     cfg_w_done;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       {cfg_w_data, cfg_w_last, cfg_w_id, cfg_w_user} <= '{default:'0};
     else
       {cfg_w_data, cfg_w_last, cfg_w_id, cfg_w_user} <= wvalid && wready ? {wdata, wlast, wid, wuser} : {cfg_w_data, cfg_w_last, cfg_w_id, cfg_w_user};

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_w_strb <= '{default:'0};
     else
       cfg_w_strb <= wvalid && wready ? wstrb : cfg_w_strb;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_w_index <= '{default:'0};
     else
       cfg_w_index <= cfg_wr_stretch && (cfg_addr_q == 8'h24) ? cfg_wdata_q : 
                      cfg_rd_stretch && (cfg_addr_q == 8'h28) ? (cfg_w_index + 1) : cfg_w_index;

   always_comb
     for (int idx = 0; idx < NUM_DW; idx ++)
       if (idx == cfg_w_index)
         cfg_w_data_mx = cfg_w_data[32*idx +: 32];

   /////////////////////////  B Channel ///////////////////////////
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       bvalid <= 1'b0;
     else
       bvalid <= cfg_wr_stretch && cfg_wdata_q[0] && (cfg_addr_q == 8'h40) ? 1'b1 :
                 bvalid && bready ? 1'b0 :
                 bvalid;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_b_done <= 1'b0;
     else
       cfg_b_done <= bvalid && bready ? 1'b1 :
                     cfg_wr_stretch && cfg_wdata_q[1] && (cfg_addr_q == 8'h40) ? 1'b0 :
                     cfg_b_done;

   assign {bresp, bid, buser} = {cfg_b_resp, cfg_b_id, cfg_b_user};
   
   ///////////////////////// AR Channel ///////////////////////////
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       arready <= 1'b0;
     else
       arready <= cfg_wr_stretch && cfg_wdata_q[0] && (cfg_addr_q == 8'h60) ? 1'b1 :
                  arvalid && arready ? 1'b0 :
                  arready;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_ar_done <= 1'b0;
     else
       cfg_ar_done <= arvalid && arready ? 1'b1 :
                      cfg_wr_stretch && cfg_wdata_q[1] && (cfg_addr_q == 8'h60) ? 1'b0 :
                      cfg_ar_done;

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       {cfg_ar_len, cfg_ar_id, cfg_ar_user} <= '{default:'0};
     else
       {cfg_ar_len, cfg_ar_id, cfg_ar_user} <= arvalid && arready ? {arlen, arid, aruser} : {cfg_ar_len, cfg_ar_id, cfg_ar_user};

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_ar_addr <= '{default:'0};
     else
       cfg_ar_addr <= arvalid && arready ? araddr : cfg_ar_addr;

   /////////////////////////  R Channel ///////////////////////////
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       rvalid <= 1'b0;
     else
       rvalid <= cfg_wr_stretch && cfg_wdata_q[0] && (cfg_addr_q == 8'h80) ? 1'b1 :
                  rvalid && rready ? 1'b0 :
                  rvalid;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_r_done <= 1'b0;
     else
       cfg_r_done <= rvalid && rready ? 1'b1 :
                     cfg_wr_stretch && cfg_wdata_q[1] && (cfg_addr_q == 8'h80) ? 1'b0 :
                     cfg_r_done;
   
   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_r_data <= '{default:'0};
     else
       for (int idx = 0; idx < NUM_DW; idx ++)
         if ((idx == cfg_r_index) && cfg_wr_stretch && (cfg_addr_q == 8'h88))
           cfg_r_data[32*idx +: 32] <= cfg_wdata_q;
         else
           cfg_r_data[32*idx +: 32] <= cfg_r_data[32*idx +: 32];

   always_ff @(negedge sync_rst_n or posedge clk)
     if (!sync_rst_n) 
       cfg_r_index <= '{default:'0};
     else
       cfg_r_index <= cfg_wr_stretch && (cfg_addr_q == 8'h84) ? cfg_wdata_q : 
                      cfg_wr_stretch && (cfg_addr_q == 8'h88) ? (cfg_r_index + 1) : cfg_r_index;

   always_comb
     for (int idx = 0; idx < NUM_DW; idx ++)
       if (idx == cfg_r_index)
         cfg_r_data_mx = cfg_r_data[32*idx +: 32];

   assign rid = cfg_r_id;
   assign ruser = cfg_r_user;
   assign rdata = cfg_r_data;
   assign rlast = cfg_r_last;

endmodule // cl_slv_axi_tst


