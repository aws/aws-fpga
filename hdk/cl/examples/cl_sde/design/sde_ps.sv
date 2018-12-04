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

// Data Engine PCIS Interface

module sde_ps #(parameter bit C2H_ONLY = 0,
                parameter bit H2C_ONLY = 0,
                
                parameter PCIS_DATA_WIDTH = 512,
                parameter PCIS_ID_WIDTH = 5,
                parameter PCIS_LEN_WIDTH = 8,
                parameter PCIS_ADDR_WIDTH = 64,

                parameter bit C2H_DESC_TYPE = 0,
                parameter C2H_DESC_WIDTH = C2H_DESC_TYPE ? 128 : 256,
                
                parameter PCIS_VALID_ADDR_WIDTH = 14, // This represents the address bits required for the 16KB window
                
                parameter C2H_PCIS_DESC_APERTURE = 14'h1000,
                parameter H2C_PCIS_DESC_APERTURE = 14'h1000,
                parameter H2C_PCIS_PKT_APERTURE = 14'h1000,

                parameter PS_PCIS_CFG_APERTURE = 14'h0200,
                parameter PM_PCIS_CFG_APERTURE = 14'h0200,
                parameter C2H_PCIS_CFG_APERTURE = 14'h0600,
                parameter H2C_PCIS_CFG_APERTURE = 14'h0600,
                
                parameter bit H2C_DESC_TYPE = 0,
                parameter H2C_DESC_WIDTH = H2C_DESC_TYPE ? 128 : 256,
                
                
                parameter H2C_PKT_SIZE_BYTES = 64,
                parameter H2C_PKT_WIDTH = H2C_PKT_SIZE_BYTES*8,

                // These are internal FIFOs - Dont change unless absolutely required
                parameter WR_CH_IN_FIFO_DEPTH = 3
                )
   (
    input                              clk,
    input                              rst_n,

    // PCIS to SDE Interface
    input [PCIS_ID_WIDTH-1:0]          pcis_awid,
    input [PCIS_ADDR_WIDTH-1:0]        pcis_awaddr,
    input [PCIS_LEN_WIDTH-1:0]         pcis_awlen,
    input [2:0]                        pcis_awsize,
    input                              pcis_awvalid,
    output logic                       pcis_awready,
    input [PCIS_DATA_WIDTH-1:0]        pcis_wdata,
    input [(PCIS_DATA_WIDTH>>3)-1:0]   pcis_wstrb,
    input                              pcis_wlast,
    input                              pcis_wvalid,
    output logic                       pcis_wready,
    output logic [PCIS_ID_WIDTH-1:0]   pcis_bid,
    output logic [1:0]                 pcis_bresp,
    output logic                       pcis_bvalid,
    input                              pcis_bready,
    input [PCIS_ID_WIDTH-1:0]          pcis_arid,
    input [PCIS_ADDR_WIDTH-1:0]        pcis_araddr,
    input [PCIS_LEN_WIDTH-1:0]         pcis_arlen,
    input [2:0]                        pcis_arsize,
    input                              pcis_arvalid,
    output logic                       pcis_arready,
    output logic [PCIS_ID_WIDTH-1:0]   pcis_rid,
    output logic [PCIS_DATA_WIDTH-1:0] pcis_rdata,
    output logic [1:0]                 pcis_rresp,
    output logic                       pcis_rlast,
    output logic                       pcis_rvalid,
    input                              pcis_rready,

    // Soft Reset
    output logic                       c2h_sync_rst_n,
    output logic                       h2c_sync_rst_n,
    output logic                       pm_sync_rst_n,
    
    // PCIS to C2H Descriptor
    output logic                       c2h_ps_desc_wr_req,
    output logic [C2H_DESC_WIDTH-1:0]  c2h_ps_desc_wdata,
    input                              c2h_ps_desc_ack,
    
    // PCIS to H2C Descriptor
    output logic                       h2c_ps_desc_wr_req,
    output logic [H2C_DESC_WIDTH-1:0]  h2c_ps_desc_wdata,
    input                              h2c_ps_desc_ack,
    
    // PCIS to H2C Small Pkt Buffer
    output logic                       h2c_ps_pkt_wr_req,
    output logic [H2C_PKT_WIDTH-1:0]   h2c_ps_pkt_wdata,
    input                              h2c_ps_pkt_ack,
    
    // PCIS to PM Config Interface
    output logic                       pm_ps_cfg_wr_req,
    output logic                       pm_ps_cfg_rd_req,
    output logic [15:0]                pm_ps_cfg_addr,
    output logic [31:0]                pm_ps_cfg_wdata,
    input                              pm_ps_cfg_ack,
    input [31:0]                       pm_ps_cfg_rdata,
    

    // PCIS to C2H Config Interface
    output logic                       c2h_ps_cfg_wr_req,
    output logic                       c2h_ps_cfg_rd_req,
    output logic [15:0]                c2h_ps_cfg_addr,
    output logic [31:0]                c2h_ps_cfg_wdata,
    input                              c2h_ps_cfg_ack,
    input [31:0]                       c2h_ps_cfg_rdata,

    output logic                       c2h_desc_ooo_error,
    output logic                       c2h_desc_unalin_error,

    
    // PCIS to H2C Config Interface
    output logic                       h2c_ps_cfg_wr_req,
    output logic                       h2c_ps_cfg_rd_req,
    output logic [15:0]                h2c_ps_cfg_addr,
    output logic [31:0]                h2c_ps_cfg_wdata,
    input                              h2c_ps_cfg_ack,
    input [31:0]                       h2c_ps_cfg_rdata,
    
    output logic                       h2c_desc_ooo_error,
    output logic                       h2c_desc_unalin_error

    
    );

   // Remove these flops to save area (but timing will be tight)
   // Flop W Channel signals
   logic [PCIS_DATA_WIDTH-1:0]         pcis_wdata_q;
   logic [(PCIS_DATA_WIDTH>>3)-1:0]    pcis_wstrb_q;
   logic                               pcis_wlast_q;
   logic                               pcis_wvalid_q;
   logic                               pcis_wready_q;
   
   // PCIS FSM
   typedef enum logic [3:0] {
                             PCIS_REQ_IDLE     = 4'd0,
                             PCIS_REQ_AW_AR    = 4'd1,
                             PCIS_REQ_DEC      = 4'd2,
                             PCIS_REQ_WR_DESC  = 4'd3,
                             PCIS_REQ_WR_PKT   = 4'd4,
                             PCIS_REQ_RD_DUMMY = 4'd5,
                             PCIS_REQ_WR_DUMMY = 4'd6,
                             PCIS_REQ_CFG      = 4'd7,
                             PCIS_REQ_RESP     = 4'd8
                             } pcis_req_state_t;

   pcis_req_state_t pcis_req_state, pcis_req_state_next;
   logic        pcis_req_active;
   logic [PCIS_ID_WIDTH-1:0] pcis_req_id;
   logic [2:0]               pcis_req_size;
   logic [PCIS_VALID_ADDR_WIDTH-1:0] pcis_req_addr;
   logic [PCIS_LEN_WIDTH-1:0]  pcis_req_len;
   logic                     pcis_req_rd_n_wr;
   logic                     pcis_req_c2h_wr_desc;
   logic                     pcis_req_h2c_wr_desc;
   logic                     pcis_req_h2c_wr_pkt;
   logic                     pcis_req_ps_cfg;
   logic                     pcis_req_pm_cfg;
   logic                     pcis_req_c2h_cfg;
   logic                     pcis_req_h2c_cfg;
   logic                     pcis_req_rd_dummy;
   logic                     pcis_req_wr_dummy;
   
   logic                      c2h_pcis_desc_wready;
   logic                      h2c_pcis_desc_wready;
   logic                      h2c_pcis_pkt_wready;
   
   logic                      pm_pcis_cfg_wready;
   logic                      pm_pcis_cfg_rvalid;
   logic [31:0]               pm_pcis_cfg_rdata;

   logic                      ps_pcis_cfg_wready;
   logic                      ps_pcis_cfg_rvalid;
   logic [31:0]               ps_pcis_cfg_rdata;

   logic                      c2h_pcis_cfg_wready;
   logic                      c2h_pcis_cfg_rvalid;
   logic [31:0]               c2h_pcis_cfg_rdata;

   logic                      h2c_pcis_cfg_wready;
   logic                      h2c_pcis_cfg_rvalid;
   logic [31:0]               h2c_pcis_cfg_rdata;
   
   logic                      ps_ps_cfg_wr_req;
   logic                      ps_ps_cfg_rd_req;
   logic [15:0]               ps_ps_cfg_addr;
   logic [31:0]               ps_ps_cfg_wdata;
   logic                      ps_ps_cfg_ack;
   logic [31:0]               ps_ps_cfg_rdata;
   
   localparam WR_CH_IN_FIFO_WIDTH = PCIS_DATA_WIDTH + 1 + (PCIS_DATA_WIDTH>>3);
   localparam WR_CH_IN_FIFO_DEPTH_MINUS1 = WR_CH_IN_FIFO_DEPTH - 1;
   logic [WR_CH_IN_FIFO_WIDTH-1:0] wr_ch_in_ff_pop_data;
   logic [WR_CH_IN_FIFO_WIDTH-1:0] wr_ch_in_ff_push_data;
   logic                         wr_ch_in_ff_pop;
   logic                         wr_ch_in_ff_push;
   logic                         wr_ch_in_ff_full;
   logic                         wr_ch_in_ff_valid;

   assign wr_ch_in_ff_push = pcis_wvalid & ~wr_ch_in_ff_full;
   assign wr_ch_in_ff_push_data = {pcis_wlast, pcis_wstrb, pcis_wdata};

//    // Small flop fifo for write-channel
//    flop_fifo #(.WIDTH(WR_CH_IN_FIFO_WIDTH),
//                .DEPTH(WR_CH_IN_FIFO_DEPTH)
//                ) WR_CH_IN_FIFO (.clk         (clk),
//                                 .rst_n       (1'b1),
//                                 .sync_rst_n  (rst_n),
//                                 .cfg_watermark (WR_CH_IN_FIFO_DEPTH_MINUS1),
//                                 .push        (wr_ch_in_ff_push),
//                                 .push_data   (wr_ch_in_ff_push_data),
//                                 .pop         (wr_ch_in_ff_pop),
//                                 .pop_data    (wr_ch_in_ff_pop_data),
//                                 .half_full   (),
//                                 .watermark   (wr_ch_in_ff_full),
//                                 .data_valid  (wr_ch_in_ff_valid)
//                                 );
// 
//    assign wr_ch_in_ff_pop = wr_ch_in_ff_valid & pcis_wready_q;
//    assign {pcis_wlast_q, pcis_wstrb_q, pcis_wdata_q} = wr_ch_in_ff_pop_data;
//    assign pcis_wvalid_q = wr_ch_in_ff_valid;
//    assign pcis_wready = ~wr_ch_in_ff_full;

   assign {pcis_wvalid_q, pcis_wlast_q, pcis_wstrb_q, pcis_wdata_q} = {pcis_wvalid, pcis_wlast, pcis_wstrb, pcis_wdata};
   assign pcis_wready = pcis_wready_q;   
                       
   always @(posedge clk)
     if (!rst_n)
       pcis_req_state <= PCIS_REQ_IDLE;
     else 
       pcis_req_state <= pcis_req_state_next;

   always_comb
     begin
        pcis_req_state_next = pcis_req_state;
        case (pcis_req_state)
          
          PCIS_REQ_IDLE:
            if (pcis_awvalid || pcis_arvalid)
              pcis_req_state_next = PCIS_REQ_AW_AR;
            else
              pcis_req_state_next = PCIS_REQ_IDLE;
          
          PCIS_REQ_AW_AR:
            pcis_req_state_next = PCIS_REQ_DEC;
               
          PCIS_REQ_DEC:
            if (pcis_req_c2h_wr_desc || pcis_req_h2c_wr_desc)
              pcis_req_state_next = PCIS_REQ_WR_DESC;
            else if (pcis_req_h2c_wr_pkt)
              pcis_req_state_next = PCIS_REQ_WR_PKT;
            else if (pcis_req_ps_cfg || pcis_req_pm_cfg || pcis_req_c2h_cfg || pcis_req_h2c_cfg)
              pcis_req_state_next = PCIS_REQ_CFG;
            else if (pcis_req_rd_n_wr)
              pcis_req_state_next = PCIS_REQ_RESP;
            else 
              pcis_req_state_next = PCIS_REQ_WR_DUMMY;
          
          PCIS_REQ_CFG:
            if ((pcis_req_pm_cfg & ((pcis_req_rd_n_wr  & pm_pcis_cfg_rvalid ) || (~pcis_req_rd_n_wr & pm_pcis_cfg_wready ))) ||
                (pcis_req_ps_cfg & ((pcis_req_rd_n_wr  & ps_pcis_cfg_rvalid ) || (~pcis_req_rd_n_wr & ps_pcis_cfg_wready ))) ||
                (pcis_req_c2h_cfg & ((pcis_req_rd_n_wr & c2h_pcis_cfg_rvalid) || (~pcis_req_rd_n_wr & c2h_pcis_cfg_wready))) ||
                (pcis_req_h2c_cfg & ((pcis_req_rd_n_wr & h2c_pcis_cfg_rvalid) || (~pcis_req_rd_n_wr & h2c_pcis_cfg_wready))))
              pcis_req_state_next = PCIS_REQ_RESP;
            else
              pcis_req_state_next = PCIS_REQ_CFG;

          PCIS_REQ_WR_DESC:
            if (pcis_wvalid_q & pcis_wlast_q & pcis_req_c2h_wr_desc & c2h_pcis_desc_wready)
              pcis_req_state_next = PCIS_REQ_RESP;
            else if (pcis_wvalid_q & pcis_wlast_q & pcis_req_h2c_wr_desc & h2c_pcis_desc_wready)
              pcis_req_state_next = PCIS_REQ_RESP;
            else
              pcis_req_state_next = PCIS_REQ_WR_DESC;
          
          PCIS_REQ_WR_PKT:
            if (pcis_wvalid_q & pcis_wlast_q & pcis_req_h2c_wr_pkt & h2c_pcis_pkt_wready)
              pcis_req_state_next = PCIS_REQ_RESP;
            else
              pcis_req_state_next = PCIS_REQ_WR_PKT;
          
          PCIS_REQ_WR_DUMMY:
           if (pcis_wvalid_q & pcis_wlast_q)
             pcis_req_state_next = PCIS_REQ_RESP;
           else
             pcis_req_state_next = PCIS_REQ_WR_DUMMY;

          PCIS_REQ_RD_DUMMY:
            // TBD - Need to figure this out
            pcis_req_state_next = PCIS_REQ_RESP;

          PCIS_REQ_RESP:
            if ((~pcis_req_rd_n_wr & pcis_bvalid & pcis_bready) ||
                (pcis_req_rd_n_wr & pcis_rvalid & pcis_rready))
              pcis_req_state_next = PCIS_REQ_IDLE;
            else
              pcis_req_state_next = PCIS_REQ_RESP;
          
          default:
            pcis_req_state_next = pcis_req_state;
          
        endcase // case pcis_req_state

     end // else: !if(!rst_n)

   // Save request info
   always @(posedge clk)
     if (!rst_n) 
       {pcis_req_id, pcis_req_size, pcis_req_len, pcis_req_addr, pcis_req_rd_n_wr} <= '{default:'0};
     else begin
        if ((pcis_req_state == PCIS_REQ_IDLE) && pcis_awvalid)
          {pcis_req_id, pcis_req_size, pcis_req_len, pcis_req_addr, pcis_req_rd_n_wr} <= {pcis_awid, pcis_awsize, pcis_awlen, pcis_awaddr[PCIS_VALID_ADDR_WIDTH-1:0], 1'b0};
        else if ((pcis_req_state == PCIS_REQ_IDLE) && pcis_arvalid)
          {pcis_req_id, pcis_req_size, pcis_req_len, pcis_req_addr, pcis_req_rd_n_wr} <= {pcis_arid, pcis_arsize, pcis_arlen, pcis_araddr[PCIS_VALID_ADDR_WIDTH-1:0], 1'b1};
        else
          {pcis_req_id, pcis_req_size, pcis_req_len, pcis_req_addr, pcis_req_rd_n_wr} <= {pcis_req_id, pcis_req_size, pcis_req_len, pcis_req_addr, pcis_req_rd_n_wr};
     end

   always @(posedge clk)
     if (!rst_n)
       pcis_req_active <= 0;
     else
       pcis_req_active <= (pcis_req_state == PCIS_REQ_DEC) ? 1'b1 :
                          (pcis_req_state_next == PCIS_REQ_RESP) ? 1'b0 : pcis_req_active;

   localparam C2H_PCIS_DESC_ADDR_START = 0; //PCIS_BASE_ADDR;
   localparam C2H_PCIS_DESC_ADDR_END = C2H_PCIS_DESC_ADDR_START + C2H_PCIS_DESC_APERTURE;

   localparam H2C_PCIS_DESC_ADDR_START = C2H_PCIS_DESC_ADDR_END;
   localparam H2C_PCIS_DESC_ADDR_END  = H2C_PCIS_DESC_ADDR_START + H2C_PCIS_DESC_APERTURE;

   localparam H2C_PCIS_PKT_ADDR_START  = H2C_PCIS_DESC_ADDR_END;
   localparam H2C_PCIS_PKT_ADDR_END = H2C_PCIS_PKT_ADDR_START + H2C_PCIS_PKT_APERTURE;

   localparam PS_PCIS_CFG_ADDR_START = H2C_PCIS_PKT_ADDR_END;
   localparam PS_PCIS_CFG_ADDR_END = PS_PCIS_CFG_ADDR_START + PS_PCIS_CFG_APERTURE;
   
   localparam PM_PCIS_CFG_ADDR_START = PS_PCIS_CFG_ADDR_END;
   localparam PM_PCIS_CFG_ADDR_END = PM_PCIS_CFG_ADDR_START + PM_PCIS_CFG_APERTURE;
   
   localparam C2H_PCIS_CFG_ADDR_START = PM_PCIS_CFG_ADDR_END;
   localparam C2H_PCIS_CFG_ADDR_END = C2H_PCIS_CFG_ADDR_START + C2H_PCIS_CFG_APERTURE;
   
   localparam H2C_PCIS_CFG_ADDR_START = C2H_PCIS_CFG_ADDR_END;
   localparam H2C_PCIS_CFG_ADDR_END = H2C_PCIS_CFG_ADDR_START + H2C_PCIS_CFG_APERTURE;
   
   // Decode addresses
   always @(posedge clk)
     if (!rst_n) begin
        pcis_req_c2h_wr_desc <= 0;
        pcis_req_h2c_wr_desc <= 0;
        pcis_req_h2c_wr_pkt  <= 0;
        pcis_req_ps_cfg      <= 0;
        pcis_req_pm_cfg      <= 0;
        pcis_req_c2h_cfg     <= 0;
        pcis_req_h2c_cfg     <= 0;
        pcis_req_rd_dummy    <= 0;
        pcis_req_wr_dummy    <= 0;
     end
     else begin
        if (pcis_req_state == PCIS_REQ_AW_AR) begin
           pcis_req_c2h_wr_desc <= ~pcis_req_rd_n_wr && 
                                   (pcis_req_addr >= C2H_PCIS_DESC_ADDR_START) && (pcis_req_addr < C2H_PCIS_DESC_ADDR_END);
           
           pcis_req_h2c_wr_desc <= ~pcis_req_rd_n_wr && 
                                   (pcis_req_addr >= H2C_PCIS_DESC_ADDR_START) && (pcis_req_addr < H2C_PCIS_DESC_ADDR_END);

           pcis_req_h2c_wr_pkt    <= ~pcis_req_rd_n_wr && 
                                 ((pcis_req_addr >= H2C_PCIS_PKT_ADDR_START) && (pcis_req_addr < H2C_PCIS_PKT_ADDR_END));

           pcis_req_ps_cfg  <= (pcis_req_addr >= PS_PCIS_CFG_ADDR_START ) && (pcis_req_addr < PS_PCIS_CFG_ADDR_END );
           pcis_req_pm_cfg  <= (pcis_req_addr >= PM_PCIS_CFG_ADDR_START ) && (pcis_req_addr < PM_PCIS_CFG_ADDR_END );
           pcis_req_c2h_cfg <= (pcis_req_addr >= C2H_PCIS_CFG_ADDR_START) && (pcis_req_addr < C2H_PCIS_CFG_ADDR_END);
           pcis_req_h2c_cfg <= (pcis_req_addr >= H2C_PCIS_CFG_ADDR_START) && (pcis_req_addr < H2C_PCIS_CFG_ADDR_END);
           
           pcis_req_rd_dummy <= pcis_req_rd_n_wr && 
                                ((pcis_req_addr <  C2H_PCIS_DESC_ADDR_START) || (pcis_req_addr >= H2C_PCIS_CFG_ADDR_END) ||
                                 ((pcis_req_addr >= C2H_PCIS_DESC_ADDR_START) && (pcis_req_addr <  H2C_PCIS_PKT_ADDR_END)));
           
           pcis_req_wr_dummy <= ~pcis_req_rd_n_wr && ((pcis_req_addr <  C2H_PCIS_DESC_ADDR_START) || (pcis_req_addr >= H2C_PCIS_CFG_ADDR_END));

        end // if (pcis_req_state == PCIS_REQ_AW_AR)
        else begin
           pcis_req_c2h_wr_desc <= pcis_req_c2h_wr_desc;
           pcis_req_h2c_wr_desc <= pcis_req_h2c_wr_desc;
           pcis_req_h2c_wr_pkt  <= pcis_req_h2c_wr_pkt ;
           pcis_req_ps_cfg      <= pcis_req_ps_cfg ;
           pcis_req_pm_cfg      <= pcis_req_pm_cfg ;
           pcis_req_c2h_cfg     <= pcis_req_c2h_cfg;
           pcis_req_h2c_cfg     <= pcis_req_h2c_cfg;
           pcis_req_rd_dummy    <= pcis_req_rd_dummy ;
           pcis_req_wr_dummy    <= pcis_req_wr_dummy ;
        end // else: !if(pcis_req_state == PCIS_REQ_AW_AR)
        
     end // else: !if(!rst_n)
   
   // AW & AR Channel
   always @(posedge clk)
      if (!rst_n) begin
         pcis_awready <= 1'b0;
         pcis_arready <= 1'b0;
      end
      else begin
         pcis_awready <= ~pcis_req_rd_n_wr & (pcis_req_state == PCIS_REQ_AW_AR);
         pcis_arready <=  pcis_req_rd_n_wr & (pcis_req_state == PCIS_REQ_AW_AR);
      end

   assign pcis_wready_q = (pcis_req_c2h_wr_desc & c2h_pcis_desc_wready) || 
                          (pcis_req_h2c_wr_desc & h2c_pcis_desc_wready) ||
                          (pcis_req_h2c_wr_pkt  & h2c_pcis_pkt_wready)  ||
                          (pcis_req_ps_cfg      & ps_pcis_cfg_wready )  ||
                          (pcis_req_pm_cfg      & pm_pcis_cfg_wready )  ||
                          (pcis_req_c2h_cfg     & c2h_pcis_cfg_wready)  ||
                          (pcis_req_h2c_cfg     & h2c_pcis_cfg_wready)  ||
                          pcis_req_wr_dummy;
   
   // B Channel
   always @(posedge clk)
     if (!rst_n) begin
        pcis_bvalid <= 0;
     end
     else begin
        pcis_bvalid <= pcis_bvalid & pcis_bready ? 1'b0 :
                       ~pcis_req_rd_n_wr & (pcis_req_state == PCIS_REQ_RESP) ? 1'b1 :
                       pcis_bvalid;
     end
   assign pcis_bid = pcis_req_id;
   assign pcis_bresp = 2'b00;
   
   // R Channel
   logic [PCIS_LEN_WIDTH-1:0] pcis_req_read_len;
   logic [31:0]               cfg_pcis_rdata;
   
   assign cfg_pcis_rdata = pcis_req_ps_cfg  ? ps_pcis_cfg_rdata : 
                           pcis_req_pm_cfg  ? pm_pcis_cfg_rdata : 
                           pcis_req_c2h_cfg ? c2h_pcis_cfg_rdata : 
                           pcis_req_h2c_cfg ? h2c_pcis_cfg_rdata : 32'hbaad_0000;
   always @(posedge clk)
     if (!rst_n) begin
        pcis_rvalid <= 0;
        pcis_rdata <= 512'd0;
        pcis_rlast <= 0;

        pcis_req_read_len <= 0;
     end
     else begin
        pcis_rvalid <= pcis_rvalid && pcis_rready && (pcis_req_read_len == 0) ? 1'b0 : 
                       (pcis_req_state == PCIS_REQ_RESP) && pcis_req_rd_n_wr ? 1'b1 : 
                       pcis_rvalid;
        pcis_rdata <= cfg_pcis_rdata << {pcis_req_addr[5:2], 5'd0};
        pcis_rlast <= (pcis_req_state == PCIS_REQ_RESP) && pcis_req_rd_n_wr && (pcis_req_read_len == 0);
        
        pcis_req_read_len <= pcis_arvalid & pcis_arready ? pcis_arlen :
                             pcis_rvalid & pcis_rready ? pcis_req_read_len - 1 :
                             pcis_req_read_len;
     end // else: !if(!rst_n)
   assign pcis_rid = pcis_req_id;
   assign pcis_rresp = 2'b00;
   
   // W Channel to C2H Descriptor
   logic c2h_pcis_req_wr_desc;
   assign c2h_pcis_req_wr_desc =  pcis_req_active & pcis_req_c2h_wr_desc;
   sde_ps_acc #(.PCIS_DATA_WIDTH (PCIS_DATA_WIDTH),
                .PCIS_ADDR_WIDTH (PCIS_VALID_ADDR_WIDTH),
                .ACC_WIDTH       (C2H_DESC_WIDTH),
                .START_ADDR      (C2H_PCIS_DESC_ADDR_START)
                )
   C2H_DESC_ACC
     (.clk           (clk),
      .rst_n         (c2h_sync_rst_n),
      .ooo_error     (c2h_desc_ooo_error),
      .unalin_error  (c2h_desc_unalin_error),
      .pcis_req_wr   (c2h_pcis_req_wr_desc),
      .pcis_req_addr (pcis_req_addr),
      .pcis_wdata    (pcis_wdata_q ),
      .pcis_wstrb    (pcis_wstrb_q ),
      .pcis_wlast    (pcis_wlast_q ),
      .pcis_wvalid   (pcis_wvalid_q),
      .pcis_wready   (c2h_pcis_desc_wready),
      .acc_wr_req    (c2h_ps_desc_wr_req),
      .acc_wdata     (c2h_ps_desc_wdata),
      .acc_ack       (c2h_ps_desc_ack)
      );
   
   // W Channel to H2C Descriptor
   logic h2c_pcis_req_wr_desc;
   assign h2c_pcis_req_wr_desc = pcis_req_active & pcis_req_h2c_wr_desc;
   sde_ps_acc #(.PCIS_DATA_WIDTH (PCIS_DATA_WIDTH),
                .PCIS_ADDR_WIDTH (PCIS_VALID_ADDR_WIDTH),
                .ACC_WIDTH       (H2C_DESC_WIDTH),
                .START_ADDR      (H2C_PCIS_DESC_ADDR_START)
                )
   H2C_DESC_ACC
     (.clk           (clk),
      .rst_n         (h2c_sync_rst_n),
      .ooo_error     (h2c_desc_ooo_error),
      .unalin_error  (h2c_desc_unalin_error),
      .pcis_req_wr   (h2c_pcis_req_wr_desc),
      .pcis_req_addr (pcis_req_addr),
      .pcis_wdata    (pcis_wdata_q ),
      .pcis_wstrb    (pcis_wstrb_q ),
      .pcis_wlast    (pcis_wlast_q ),
      .pcis_wvalid   (pcis_wvalid_q),
      .pcis_wready   (h2c_pcis_desc_wready),
      .acc_wr_req    (h2c_ps_desc_wr_req),
      .acc_wdata     (h2c_ps_desc_wdata),
      .acc_ack       (h2c_ps_desc_ack)
      );
   
//    // W Channel to H2C Pkt Buffer
//    logic h2c_pcis_req_wr_pkt;
//    assign h2c_pcis_req_wr_pkt = pcis_req_active & pcis_req_h2c_wr_pkt;
//    sde_ps_acc #(.PCIS_DATA_WIDTH (PCIS_DATA_WIDTH),
//                 .PCIS_ADDR_WIDTH (PCIS_VALID_ADDR_WIDTH),
//                 .ACC_WIDTH       (H2C_PKT_WIDTH),
//                 .START_ADDR      (H2C_PCIS_PKT_ADDR_START)
//                 )
//    H2C_PKT_ACC
//      (.clk           (clk),
//       .rst_n         (rst_n),
//       .pcis_req_wr   (h2c_pcis_req_wr_pkt),
//       .pcis_req_addr (pcis_req_addr),
//       .pcis_wdata    (pcis_wdata_q ),
//       .pcis_wstrb    (pcis_wstrb_q ),
//       .pcis_wlast    (pcis_wlast_q ),
//       .pcis_wvalid   (pcis_wvalid_q),
//       .pcis_wready   (h2c_pcis_pkt_wready),
//       .acc_wr_req    (h2c_ps_pkt_wr_req),
//       .acc_wdata     (h2c_ps_pkt_wdata),
//       .acc_ack       (h2c_ps_pkt_ack)
//       );
//    
   assign h2c_pcis_pkt_wready = 0;
   assign h2c_ps_pkt_wr_req = 0;
   assign h2c_ps_pkt_wdata = ({H2C_PKT_WIDTH{1'b0}});
   
   // W Channel to PM Cfg
   // R Channel from PM Cfg
   always @(posedge clk)
      if (!rst_n) begin
         pm_ps_cfg_wr_req <= 0;
         pm_ps_cfg_rd_req <= 0;
         pm_ps_cfg_addr <= '{default:'0};
         pm_ps_cfg_wdata  <= '{default:'0};
         pm_pcis_cfg_wready <= 0; 
         pm_pcis_cfg_rvalid <= 0;
         pm_pcis_cfg_rdata  <= '{default:'0};
      end
      else begin
         pm_ps_cfg_wr_req <= ~pm_ps_cfg_wr_req & ~pm_pcis_cfg_wready & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_pm_cfg & ~pcis_req_rd_n_wr & pcis_wvalid_q ? 1'b1 :
                              pm_ps_cfg_wr_req & pcis_req_pm_cfg & ~pcis_req_rd_n_wr & pm_ps_cfg_ack ? 1'b0 :
                              pm_ps_cfg_wr_req;

         pm_ps_cfg_rd_req <= ~pm_ps_cfg_rd_req & ~pm_pcis_cfg_rvalid & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_pm_cfg & pcis_req_rd_n_wr ? 1'b1 :
                              pm_ps_cfg_rd_req & pcis_req_pm_cfg & pcis_req_rd_n_wr & pm_ps_cfg_ack ? 1'b0 :
                              pm_ps_cfg_rd_req;

         pm_ps_cfg_addr <= ~(pm_ps_cfg_wr_req || pm_ps_cfg_rd_req) ? pcis_req_addr - PM_PCIS_CFG_ADDR_START : pm_ps_cfg_addr;

         pm_ps_cfg_wdata <= ~(pm_ps_cfg_wr_req || pm_ps_cfg_rd_req) ? (pcis_wdata_q >> {pcis_req_addr[5:2], 5'd0}) : pm_ps_cfg_wdata;
         
         pm_pcis_cfg_wready <= pm_ps_cfg_wr_req & pm_ps_cfg_ack;

         pm_pcis_cfg_rvalid <= pm_ps_cfg_rd_req & pm_ps_cfg_ack;

         pm_pcis_cfg_rdata <= pm_ps_cfg_rd_req & pm_ps_cfg_ack ? pm_ps_cfg_rdata : pm_pcis_cfg_rdata;

      end // else: !if(!rst_n)
   
   // W Channel to PS Cfg
   // R Channel from PS Cfg
   always @(posedge clk)
      if (!rst_n) begin
         ps_ps_cfg_wr_req <= 0;
         ps_ps_cfg_rd_req <= 0;
         ps_ps_cfg_addr <= '{default:'0};
         ps_ps_cfg_wdata  <= '{default:'0};
         ps_pcis_cfg_wready <= 0; 
         ps_pcis_cfg_rvalid <= 0;
         ps_pcis_cfg_rdata  <= '{default:'0};
      end
      else begin
         ps_ps_cfg_wr_req <= ~ps_ps_cfg_wr_req & ~ps_pcis_cfg_wready & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_ps_cfg & ~pcis_req_rd_n_wr & pcis_wvalid_q ? 1'b1 :
                              ps_ps_cfg_wr_req & pcis_req_ps_cfg & ~pcis_req_rd_n_wr & ps_ps_cfg_ack ? 1'b0 :
                              ps_ps_cfg_wr_req;

         ps_ps_cfg_rd_req <= ~ps_ps_cfg_rd_req &~ps_pcis_cfg_rvalid & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_ps_cfg & pcis_req_rd_n_wr ? 1'b1 :
                              ps_ps_cfg_rd_req & pcis_req_ps_cfg & pcis_req_rd_n_wr & ps_ps_cfg_ack ? 1'b0 :
                              ps_ps_cfg_rd_req;

         ps_ps_cfg_addr <= ~(ps_ps_cfg_wr_req || ps_ps_cfg_rd_req) ? pcis_req_addr - PS_PCIS_CFG_ADDR_START : ps_ps_cfg_addr;

         ps_ps_cfg_wdata <= ~(ps_ps_cfg_wr_req || ps_ps_cfg_rd_req) ? (pcis_wdata_q >> {pcis_req_addr[5:2], 5'd0}) : ps_ps_cfg_wdata;
         
         ps_pcis_cfg_wready <= ps_ps_cfg_wr_req & ps_ps_cfg_ack;

         ps_pcis_cfg_rvalid <= ps_ps_cfg_rd_req & ps_ps_cfg_ack;

         ps_pcis_cfg_rdata <= ps_ps_cfg_rd_req & ps_ps_cfg_ack ? ps_ps_cfg_rdata : ps_pcis_cfg_rdata;

      end // else: !if(!rst_n)

   // W Channel to C2H Cfg
   // R Channel from C2H Cfg
   always @(posedge clk)
      if (!rst_n) begin
         c2h_ps_cfg_wr_req <= 0;
         c2h_ps_cfg_rd_req <= 0;
         c2h_ps_cfg_addr <= '{default:'0};
         c2h_ps_cfg_wdata  <= '{default:'0};
         c2h_pcis_cfg_wready <= 0; 
         c2h_pcis_cfg_rvalid <= 0;
         c2h_pcis_cfg_rdata  <= '{default:'0};
      end
      else begin
         c2h_ps_cfg_wr_req <= ~c2h_ps_cfg_wr_req & ~c2h_pcis_cfg_wready & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_c2h_cfg & ~pcis_req_rd_n_wr & pcis_wvalid_q ? 1'b1 :
                              c2h_ps_cfg_wr_req & pcis_req_c2h_cfg & ~pcis_req_rd_n_wr & c2h_ps_cfg_ack ? 1'b0 :
                              c2h_ps_cfg_wr_req;

         c2h_ps_cfg_rd_req <= ~c2h_ps_cfg_rd_req & ~c2h_pcis_cfg_rvalid & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_c2h_cfg & pcis_req_rd_n_wr ? 1'b1 :
                              c2h_ps_cfg_rd_req & pcis_req_c2h_cfg & pcis_req_rd_n_wr & c2h_ps_cfg_ack ? 1'b0 :
                              c2h_ps_cfg_rd_req;

         c2h_ps_cfg_addr <= ~(c2h_ps_cfg_wr_req || c2h_ps_cfg_rd_req) ? pcis_req_addr - C2H_PCIS_CFG_ADDR_START : c2h_ps_cfg_addr;

         c2h_ps_cfg_wdata <= ~(c2h_ps_cfg_wr_req || c2h_ps_cfg_rd_req) ? (pcis_wdata_q >> {pcis_req_addr[5:2], 5'd0}) : c2h_ps_cfg_wdata;
         
         c2h_pcis_cfg_wready <= c2h_ps_cfg_wr_req & c2h_ps_cfg_ack;

         c2h_pcis_cfg_rvalid <= c2h_ps_cfg_rd_req & c2h_ps_cfg_ack;

         c2h_pcis_cfg_rdata <= c2h_ps_cfg_rd_req & c2h_ps_cfg_ack ? c2h_ps_cfg_rdata : c2h_pcis_cfg_rdata;

      end // else: !if(!rst_n)
   
   // W Channel to H2C Cfg
   // R Channel from H2C Cfg
   always @(posedge clk)
      if (!rst_n) begin
         h2c_ps_cfg_wr_req <= 0;
         h2c_ps_cfg_rd_req <= 0;
         h2c_ps_cfg_addr <= '{default:'0};
         h2c_ps_cfg_wdata  <= '{default:'0};
         h2c_pcis_cfg_wready <= 0; 
         h2c_pcis_cfg_rvalid <= 0;
         h2c_pcis_cfg_rdata  <= '{default:'0};
      end
      else begin
         h2c_ps_cfg_wr_req <= ~h2c_ps_cfg_wr_req & ~h2c_pcis_cfg_wready & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_h2c_cfg & ~pcis_req_rd_n_wr & pcis_wvalid_q ? 1'b1 :
                              h2c_ps_cfg_wr_req & pcis_req_h2c_cfg & ~pcis_req_rd_n_wr & h2c_ps_cfg_ack ? 1'b0 :
                              h2c_ps_cfg_wr_req;

         h2c_ps_cfg_rd_req <= ~h2c_ps_cfg_rd_req & ~h2c_pcis_cfg_rvalid & (pcis_req_state == PCIS_REQ_CFG) & pcis_req_h2c_cfg & pcis_req_rd_n_wr ? 1'b1 :
                              h2c_ps_cfg_rd_req & pcis_req_h2c_cfg & pcis_req_rd_n_wr & h2c_ps_cfg_ack ? 1'b0 :
                              h2c_ps_cfg_rd_req;

         h2c_ps_cfg_addr <= ~(h2c_ps_cfg_wr_req || h2c_ps_cfg_rd_req) ? pcis_req_addr - H2C_PCIS_CFG_ADDR_START : h2c_ps_cfg_addr;

         h2c_ps_cfg_wdata <= ~(h2c_ps_cfg_wr_req || h2c_ps_cfg_rd_req) ? (pcis_wdata_q >> {pcis_req_addr[5:2], 5'd0}) : h2c_ps_cfg_wdata;
         
         h2c_pcis_cfg_wready <= h2c_ps_cfg_wr_req & h2c_ps_cfg_ack;

         h2c_pcis_cfg_rvalid <= h2c_ps_cfg_rd_req & h2c_ps_cfg_ack;

         h2c_pcis_cfg_rdata <= h2c_ps_cfg_rd_req & h2c_ps_cfg_ack ? h2c_ps_cfg_rdata : h2c_pcis_cfg_rdata;

      end // else: !if(!rst_n)

   // Local Config Registers
   // TODO:
   // Temporarily no registers
   
   logic ps_ps_cfg_rd_ack;
   logic ps_ps_cfg_wr_ack;
   logic cfg_ps_reset;
   
   assign ps_ps_cfg_ack = ps_ps_cfg_wr_req ? ps_ps_cfg_wr_ack : ps_ps_cfg_rd_ack;

   /////////////////////////////////////////////////
   // PCIS Registers
   /////////////////////////////////////////////////

   // 0x00 : SDE Reset
   //     0  - Global Reset (RW)
   //  31:1  - RSVD (RW)

   // 0x04 : SDE Info
   //     0  - C2H Present
   //  15:1  - RSVD
   //    16  - H2C Present
   // 31:17  - RSVD
   
   // Register Writes
   always @(posedge clk)
     if (!rst_n) begin
        ps_ps_cfg_wr_ack <= 0;
        cfg_ps_reset <= 0;
     end
     else if (ps_ps_cfg_wr_req) begin
        case (c2h_ps_cfg_addr[8:0]) 
          9'h000 : begin
             ps_ps_cfg_wr_ack <= 1;
             cfg_ps_reset <= ps_ps_cfg_wdata;
          end
          default: begin
             ps_ps_cfg_wr_ack <= 1;
          end
        endcase // case (c2h_ps_cfg_addr[8:0])
     end // if (ps_ps_cfg_wr_req)
   
   logic [15:0] cfg_c2h_present;
   logic [15:0] cfg_h2c_present;
   logic        h2c_only;
   logic        c2h_only;

   assign h2c_only = H2C_ONLY;
   assign c2h_only = C2H_ONLY;
   
   assign cfg_c2h_present = {15'd0, ~h2c_only};
   assign cfg_h2c_present = {15'd0, ~c2h_only};
   
   // Signals based on writes
   always @(posedge clk)
      if (!rst_n) begin
         ps_ps_cfg_rd_ack <= 0;
         ps_ps_cfg_rdata <= 32'd0;
      end
      else begin
         case(ps_ps_cfg_addr[8:0])
           9'h000: begin
              ps_ps_cfg_rd_ack <= 1;
              ps_ps_cfg_rdata <= cfg_ps_reset;
           end
           9'h004: begin
              ps_ps_cfg_rd_ack <= 1;
              ps_ps_cfg_rdata <= {cfg_h2c_present, cfg_c2h_present};
           end
           default : begin
              ps_ps_cfg_rd_ack <= 1;
              ps_ps_cfg_rdata <= 32'hbaad_2000;
           end
         endcase // case (ps_ps_cfg_addr[8:0])
      end // else: !if(!rst_n)

   always @(posedge clk)
     if (!rst_n) begin
        c2h_sync_rst_n <= 0;
        h2c_sync_rst_n <= 0;
        pm_sync_rst_n  <= 0;
     end
     else begin
        c2h_sync_rst_n <= ~cfg_ps_reset;
        h2c_sync_rst_n <= ~cfg_ps_reset;
        pm_sync_rst_n  <= ~cfg_ps_reset;
     end // else: !if(!rst_n)
   
      
// `ifndef NO_SDE_DEBUG_ILA
// 
//    ila_sde_ps SDE_PS_ILA (.clk     (clk),
//                           .probe0  (c2h_ps_desc_wr_req   ),
//                           .probe1  (c2h_ps_desc_wdata    ),
//                           .probe2  (c2h_ps_desc_ack      ),
//                           .probe3  (h2c_ps_desc_wr_req   ),
//                           .probe4  (h2c_ps_desc_wdata    ),
//                           .probe5  (h2c_ps_desc_ack      ),
//                           .probe6  (h2c_ps_pkt_wr_req    ),
//                           .probe7  (h2c_ps_pkt_wdata     ),
//                           .probe8  (h2c_ps_pkt_ack       ),
//                           .probe9  (pm_ps_cfg_wr_req     ),
//                           .probe10 (pm_ps_cfg_rd_req     ),
//                           .probe11 (pm_ps_cfg_addr       ),
//                           .probe12 (pm_ps_cfg_wdata      ),
//                           .probe13 (pm_ps_cfg_ack        ),
//                           .probe14 (pm_ps_cfg_rdata      ),
//                           .probe15 (c2h_ps_cfg_wr_req    ),
//                           .probe16 (c2h_ps_cfg_rd_req    ),
//                           .probe17 (c2h_ps_cfg_addr      ),
//                           .probe18 (c2h_ps_cfg_wdata     ),
//                           .probe19 (c2h_ps_cfg_ack       ),
//                           .probe20 (c2h_ps_cfg_rdata     ),
//                           .probe21 (h2c_ps_cfg_wr_req    ),
//                           .probe22 (h2c_ps_cfg_rd_req    ),
//                           .probe23 (h2c_ps_cfg_addr      ),
//                           .probe24 (h2c_ps_cfg_wdata     ),
//                           .probe25 (h2c_ps_cfg_ack       ),
//                           .probe26 (h2c_ps_cfg_rdata     ),
//                           .probe27 (ps_ps_cfg_wr_req     ),
//                           .probe28 (ps_ps_cfg_rd_req     ),
//                           .probe29 (ps_ps_cfg_addr       ),
//                           .probe30 (ps_ps_cfg_wdata      ),
//                           .probe31 (ps_ps_cfg_ack        ),
//                           .probe32 (ps_ps_cfg_rdata      ),
//                           .probe33 (pcis_req_active      ),
//                           .probe34 (pcis_req_state       ),
//                           .probe35 (pcis_req_c2h_wr_desc ),
//                           .probe36 (pcis_req_h2c_wr_desc ),
//                           .probe37 (pcis_req_h2c_wr_pkt  ),
//                           .probe38 (pcis_req_ps_cfg      ),
//                           .probe39 (pcis_req_pm_cfg      ),
//                           .probe40 (pcis_req_c2h_cfg     ),
//                           .probe41 (pcis_req_h2c_cfg     ),
//                           .probe42 (pcis_req_rd_dummy    ),
//                           .probe43 (pcis_req_wr_dummy    ),
//                           .probe44 (c2h_pcis_req_wr_desc ),
//                           .probe45 (h2c_pcis_req_wr_desc ),
//                           .probe46 (h2c_pcis_req_wr_pkt  )                          
//                           );
//      
// `endif //  `ifndef NO_SDE_DEBUG_ILA
   
   
endmodule // sde_ps

