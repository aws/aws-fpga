//  (c) Copyright 2019 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES. 
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module axi_register_slice_v2_1_22_test_master #
  (
   parameter integer C_AXI_ID_WIDTH = 0,
   parameter integer C_AXI_ADDR_WIDTH = 32,
   parameter integer C_AXI_DATA_WIDTH = 32,
   parameter integer C_AXI_PROTOCOL = 0,
   parameter integer C_AXI_AWUSER_WIDTH = 0,
   parameter integer C_AXI_ARUSER_WIDTH = 0,
   parameter integer C_AXI_WUSER_WIDTH = 0,
   parameter integer C_AXI_RUSER_WIDTH = 0,
   parameter integer C_AXI_BUSER_WIDTH = 0,
   parameter integer C_SUPPORTS_NARROW = 0,
   parameter integer C_AXI_SUPPORTS_WRITE = 1,
   parameter integer C_AXI_SUPPORTS_READ = 1,
   parameter [C_AXI_ADDR_WIDTH-1:0] C_AXI_ADDR = 0,  // Base address
   parameter integer C_NUM_ADDR = 1,  // Number of address iterations; range 1..2**16 (fixed increment = 32'h10000
   parameter integer C_NUM_ID = 1,  // Number of ID iterations; range 1..2**C_ID_WIDTH (base = 0; fixed increment = 1)
   parameter integer C_NUM_LEN = 1,  // Number of LEN iterations; range 1..9 (base = 0; value = 2**i - 1)
   parameter integer C_NUM_TRANS = 1  // Number of transactions; range >=1 (read and write)
   )
  (
  /**************** Write Address Channel Signals ****************/
  (* dont_touch="true" *) output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_awaddr,
  (* dont_touch="true" *) output reg [3-1:0]                     m_axi_awprot = 3'b0,
  (* dont_touch="true" *) output wire                             m_axi_awvalid,
  input  wire                            m_axi_awready,
  (* dont_touch="true" *) output reg [3-1:0]                     m_axi_awsize = 3'b0,
  (* dont_touch="true" *) output reg [2-1:0]                     m_axi_awburst = 2'b01,
  (* dont_touch="true" *) output reg [4-1:0]                     m_axi_awcache = 4'b0,
  (* dont_touch="true" *) output wire [(C_AXI_PROTOCOL==1?4:8)-1:0]        m_axi_awlen,
  (* dont_touch="true" *) output reg [(C_AXI_PROTOCOL==1?2:1)-1:0]       m_axi_awlock = 1'b0,
  (* dont_touch="true" *) output reg [4-1:0]                     m_axi_awqos = 4'b0,
  (* dont_touch="true" *) output reg [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]         m_axi_awid = 'b0,
  (* dont_touch="true" *) output reg [(C_AXI_AWUSER_WIDTH==0?1:C_AXI_AWUSER_WIDTH)-1:0]    m_axi_awuser = 'b0,
  /**************** Write Data Channel Signals ****************/
  (* dont_touch="true" *) output wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]         m_axi_wid,
  (* dont_touch="true" *) output wire [C_AXI_DATA_WIDTH-1:0]      m_axi_wdata,
  (* dont_touch="true" *) output reg [C_AXI_DATA_WIDTH/8-1:0]     m_axi_wstrb = {(C_AXI_DATA_WIDTH/8){1'b1}},
  (* dont_touch="true" *) output wire                             m_axi_wvalid,
  input  wire                            m_axi_wready,
  (* dont_touch="true" *) output wire                             m_axi_wlast,
  (* dont_touch="true" *) output reg [(C_AXI_WUSER_WIDTH==0?1:C_AXI_WUSER_WIDTH)-1:0]     m_axi_wuser = 'b0,
  /**************** Write Response Channel Signals ****************/
  input  wire [2-1:0]                    m_axi_bresp,
  input  wire                            m_axi_bvalid,
  (* dont_touch="true" *) output wire                             m_axi_bready,
  input  wire [(C_AXI_BUSER_WIDTH==0?1:C_AXI_BUSER_WIDTH)-1:0]     m_axi_buser,
  input  wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]        m_axi_bid,
  /**************** Read Address Channel Signals ****************/
  (* dont_touch="true" *) output wire [C_AXI_ADDR_WIDTH-1:0]       m_axi_araddr,
  (* dont_touch="true" *) output reg [3-1:0]                     m_axi_arprot = 3'b0,
  (* dont_touch="true" *) output wire                             m_axi_arvalid,
  input  wire                            m_axi_arready,
  (* dont_touch="true" *) output reg [3-1:0]                     m_axi_arsize = 3'b0,
  (* dont_touch="true" *) output reg [2-1:0]                     m_axi_arburst = 2'b01,
  (* dont_touch="true" *) output reg [4-1:0]                     m_axi_arcache = 4'b0,
  (* dont_touch="true" *) output wire [(C_AXI_PROTOCOL==1?4:8)-1:0]        m_axi_arlen,
  (* dont_touch="true" *) output reg [(C_AXI_PROTOCOL==1?2:1)-1:0]       m_axi_arlock = 1'b0,
  (* dont_touch="true" *) output reg [4-1:0]                     m_axi_arqos = 4'b0,
  (* dont_touch="true" *) output reg [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]         m_axi_arid = 'b0,
  (* dont_touch="true" *) output reg [(C_AXI_ARUSER_WIDTH==0?1:C_AXI_ARUSER_WIDTH)-1:0]    m_axi_aruser = 'b0,
  /**************** Read Data Channel Signals ****************/
  input  wire [C_AXI_DATA_WIDTH-1:0]      m_axi_rdata,
  input  wire [2-1:0]                    m_axi_rresp,
  input  wire                            m_axi_rvalid,
  (* dont_touch="true" *) output wire                             m_axi_rready,
  input  wire                            m_axi_rlast,
  input  wire [(C_AXI_RUSER_WIDTH==0?1:C_AXI_RUSER_WIDTH)-1:0]     m_axi_ruser,
  input  wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]        m_axi_rid,
  /**************** System Signals ****************/
  input  wire                            aclk,
  input  wire                            aresetn
  );

  function integer f_ceil_log2
    (
     input integer x
     );
    integer acc;
    begin
      acc=0;
      while ((2**acc) < x)
        acc = acc + 1;
      f_ceil_log2 = acc;
    end
  endfunction

  /**************** Local Parameters ****************/
  localparam integer  P_ID_WIDTH = C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH;
  localparam integer  P_NUM_ID_LOG = f_ceil_log2(C_NUM_ID);
  localparam integer  P_NUM_ADDR_LOG = f_ceil_log2(C_NUM_ADDR);
  localparam integer  P_LEN_WIDTH = (C_AXI_PROTOCOL==0 ? 8 : C_AXI_PROTOCOL==1 ? 4 : 1);
  localparam integer  P_LOCK_WIDTH = (C_AXI_PROTOCOL == 1) ? 2 : 1;
  localparam integer               P_M_AXI_DATA_BYTES = (C_AXI_DATA_WIDTH / 8);
  localparam integer               P_M_AXI_DONE_WIDTH = f_ceil_log2(C_NUM_TRANS<2?2:C_NUM_TRANS);
  localparam integer               P_M_AXI_SIZE = f_ceil_log2(C_AXI_DATA_WIDTH)-3;

  /**************** Internal Wires/Regs - Global ****************/
   wire                            done;
    wire                            dummy ;
  reg                         done_i;
  reg                         done_sel;
  wire                         done_cycle;
  reg                          done_d1 = 1'b0;
  reg                   areset = 1'b0;
  reg [P_M_AXI_DONE_WIDTH:0] arcnt_i = {P_M_AXI_DONE_WIDTH{1'b0}};
  reg [P_M_AXI_DONE_WIDTH:0] rcnt_i = {P_M_AXI_DONE_WIDTH{1'b1}};
  reg [3:0]                    acc_r_i = 4'b0;
  reg [P_M_AXI_DONE_WIDTH:0] awcnt_i = {P_M_AXI_DONE_WIDTH{1'b0}};
  reg [P_M_AXI_DONE_WIDTH:0] wcnt_i = {P_M_AXI_DONE_WIDTH{1'b0}};
  reg [P_M_AXI_DONE_WIDTH:0] bcnt_i = {P_M_AXI_DONE_WIDTH{1'b1}};
  reg [2:0]                    acc_b_i = 3'b0;

  // Register Reset
  always @(posedge aclk) begin
      areset <= ~aresetn;
  end

    
    /**************** Internal Wires/Regs - Read Channels ****************/
    wire                         read_xaction_done_i;
    reg [C_AXI_ADDR_WIDTH-1:0]     m_axi_araddr_i = C_AXI_ADDR;
    reg [C_NUM_ID:0]     m_axi_arid_i = 0;
    reg [P_LEN_WIDTH-1:0]     m_axi_arlen_i = {P_LEN_WIDTH{1'b0}};
    reg [C_AXI_ADDR_WIDTH:0]      araddr_i = {(C_AXI_ADDR_WIDTH+1){1'b0}};
    reg [3-1:0]                  arprot_i = 3'b0;
    reg [3-1:0]                  arsize_i = 3'b0;
    reg [2-1:0]                  arburst_i = 2'b0;
    reg [4-1:0]                  arcache_i = 4'b0;
    reg [2-1:0]                  arlock_i = 2'b0;
    reg [P_LEN_WIDTH-1:0]     arlen_i = {P_LEN_WIDTH{1'b0}};
    reg [4-1:0]                  arqos_i = 4'b0;
    reg [P_ID_WIDTH-1:0]        arid_i = {P_ID_WIDTH{1'b0}};
    reg [C_AXI_ARUSER_WIDTH:0]    aruser_i = {(C_AXI_ARUSER_WIDTH+1){1'b0}};
    reg [C_AXI_DATA_WIDTH-1:0]    rdata_i = {C_AXI_DATA_WIDTH{1'b0}};
    reg [2-1:0]                  rresp_i = 2'b00;
    reg [C_AXI_RUSER_WIDTH:0]   ruser_i = {(C_AXI_RUSER_WIDTH+1){1'b0}};
    reg [P_ID_WIDTH:0]      rid_i = {P_ID_WIDTH{1'b0}};
    reg                        m_axi_arvalid_i = 1'b0;
    reg                        m_axi_rready_i = 1'b0;
    reg [P_NUM_ADDR_LOG:0]    araddr_cnt = 0;
  
    /**************** Assign Read Channel Outputs ****************/
    assign read_xaction_done_i = m_axi_rvalid && m_axi_rready_i && ((C_AXI_PROTOCOL==2)?1'b1:m_axi_rlast);
    assign m_axi_arvalid = m_axi_arvalid_i;
    assign m_axi_rready = m_axi_rready_i;
    assign m_axi_araddr = m_axi_araddr_i;
    assign m_axi_arlen = m_axi_arlen_i;
    always @(posedge aclk) begin
      m_axi_arprot <= dummy ? arprot_i : 3'b000;
      m_axi_arsize <= dummy ? arsize_i : C_SUPPORTS_NARROW==0 ? P_M_AXI_SIZE : P_M_AXI_SIZE-1;
      m_axi_arburst <= dummy ? arburst_i : 2'b01;
      m_axi_arlock <= dummy ? arlock_i : 1'b0;
      m_axi_arcache <= dummy ? arcache_i : 4'h3;
      m_axi_arqos <= dummy  ? arqos_i : 4'h0;
      m_axi_aruser <= dummy ? aruser_i : 0;
    end
  
    //**********************************************
    // Read Channel: ARVALID, ARADDR, ARLEN, RREADY
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        m_axi_arvalid_i <= 1'b0;
        arcnt_i <= C_NUM_TRANS;
        m_axi_arlen_i <= 0;
        m_axi_araddr_i <= C_AXI_ADDR;
        m_axi_arid_i <= 1;
        araddr_cnt <= C_NUM_ADDR;
      end else if (C_AXI_SUPPORTS_READ!=0) begin
        if (m_axi_arready & m_axi_arvalid_i) begin
          arcnt_i <= arcnt_i - 1;
          if (araddr_cnt == 1) begin
            m_axi_araddr_i <= dummy ? araddr_i : C_AXI_ADDR;
            araddr_cnt <= C_NUM_ADDR;
          end else begin
            m_axi_araddr_i <= m_axi_araddr_i + 32'h10000;
            araddr_cnt <= araddr_cnt - 1;
          end
          if (C_NUM_LEN<2 || |(m_axi_arlen_i>>(C_NUM_LEN-2))) begin
            m_axi_arlen_i <= dummy ? arlen_i : 0;
          end else begin
            m_axi_arlen_i <= (m_axi_arlen_i<<1) | 1'b1;
          end
          if (C_NUM_ID<2 || (m_axi_arid_i == C_NUM_ID)) begin
            m_axi_arid <= dummy ? arid_i : 0;
            m_axi_arid_i <= 1;
          end else begin
            m_axi_arid <= m_axi_arid_i;
            m_axi_arid_i <= m_axi_arid_i + 1;
          end
          if (arcnt_i == 1) begin
            m_axi_arvalid_i <= 1'b0;
          end
        end else if (arcnt_i != 0) begin
          m_axi_arvalid_i <= 1'b1;
        end
      end
    end
  
    //**********************************************
    // Read Channel: Random outputs
    //**********************************************
    always @(posedge aclk) begin
      araddr_i <= {araddr_i, ~araddr_i[C_AXI_ADDR_WIDTH]};
      arprot_i <= {arprot_i, ~arprot_i[3-1]};
      arlen_i <= {arlen_i, ~arlen_i[P_LEN_WIDTH-1]};
      arsize_i <= {arsize_i, ~arsize_i[3-1]};
      arburst_i <= {arburst_i, ~arburst_i[2-1]};
      arlock_i <= {arlock_i, ~arlock_i[2-1]};
      arcache_i <= {arcache_i, ~arcache_i[4-1]};
      arqos_i <= {arqos_i, ~arqos_i[4-1]};
      aruser_i <= {aruser_i, ~aruser_i[C_AXI_ARUSER_WIDTH]};
      arid_i <= {arid_i, ~arid_i[P_ID_WIDTH-1]};
    end
  
    //**********************************************
    // Read Channel: PROCESS INPUTS
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        m_axi_rready_i <= 1'b0;
        rcnt_i <= C_NUM_TRANS;
        rdata_i <= {C_AXI_DATA_WIDTH{1'b0}};
        rresp_i <= {2{1'b0}};
        ruser_i <= {(C_AXI_RUSER_WIDTH+1){1'b0}};
        rid_i <= {P_ID_WIDTH{1'b0}};
        acc_r_i <= 4'b0;
      end else if (C_AXI_SUPPORTS_READ!=0) begin
        if (m_axi_rvalid & m_axi_rready_i) begin
          m_axi_rready_i <= 1'b0;
          rdata_i <= m_axi_rdata;
            acc_r_i[0] <= rdata_i[0];
          rresp_i <= m_axi_rresp;
            acc_r_i[1] <= rresp_i[0];
          ruser_i <= m_axi_ruser;
            acc_r_i[2] <= ruser_i[0];
          rid_i <= m_axi_rid;
            acc_r_i[3] <= rid_i[0];
          if (m_axi_rlast) begin
            rcnt_i <= rcnt_i - 1;
          end
        end else begin
          rdata_i <= rdata_i>>1;
          rresp_i <= rresp_i>>1;
          ruser_i <= ruser_i>>1;
          rid_i <= rid_i>>1;
          acc_r_i <= acc_r_i>>1;
          if (m_axi_rvalid) begin
            m_axi_rready_i <= 1'b1;
          end
        end
      end
    end
    
    assign dummy = rdata_i[0];
    
    

    /**************** Internal Wires/Regs - Write Channels ****************/
    reg [C_AXI_ADDR_WIDTH-1:0]     m_axi_awaddr_i = C_AXI_ADDR;
    reg [C_NUM_ID:0]     m_axi_awid_i = 0;
    reg [P_LEN_WIDTH-1:0]     m_axi_awlen_i = {P_LEN_WIDTH{1'b0}};
    reg [C_AXI_DATA_WIDTH-1:0]    wdata_i = {C_AXI_DATA_WIDTH{1'b0}};
    reg [8-1:0]                  xfer_w_i = 8'h00;
    wire                         write_burst_done_i;
    reg [C_AXI_ADDR_WIDTH:0]      awaddr_i = {(C_AXI_ADDR_WIDTH+1){1'b0}};
    reg [3-1:0]                  awprot_i = 3'b0;
    reg [P_LEN_WIDTH-1:0]     awlen_i = {P_LEN_WIDTH{1'b0}};
    reg [3-1:0]                  awsize_i = 3'b0;
    reg [2-1:0]                  awburst_i = 2'b0;
    reg [4-1:0]                  awcache_i = 4'b0;
    reg [2-1:0]                  awlock_i = 2'b0;
    reg [4-1:0]                  awqos_i = 4'b0;
    reg [P_ID_WIDTH:0]        awid_i = {P_ID_WIDTH{1'b0}};
    reg [C_AXI_AWUSER_WIDTH:0]    awuser_i = {(C_AXI_AWUSER_WIDTH+1){1'b0}};
    reg [P_M_AXI_DATA_BYTES-1:0] wstrb_i = {P_M_AXI_DATA_BYTES{1'b1}};
    reg [C_AXI_WUSER_WIDTH:0]     wuser_i = {(C_AXI_WUSER_WIDTH+1){1'b0}};
    reg [P_ID_WIDTH:0]        wid_i = {P_ID_WIDTH{1'b0}};
    reg [2-1:0]                  bresp_i = 2'b00;
    reg [C_AXI_BUSER_WIDTH:0]   buser_i = {(C_AXI_BUSER_WIDTH+1){1'b0}};
    reg [P_ID_WIDTH:0]      bid_i = {P_ID_WIDTH{1'b0}};
    reg                        m_axi_awvalid_i = 1'b0;
    reg                        m_axi_wvalid_i = 1'b0;
    reg                        m_axi_bready_i = 1'b0;
    reg                        m_axi_wlast_i = 1'b0;
    reg                        m_axi_wid_i = {P_ID_WIDTH{1'b0}};
    reg [P_LEN_WIDTH-1:0]     wlen_i = {P_LEN_WIDTH{1'b0}};
    reg [P_NUM_ADDR_LOG:0]    awaddr_cnt = 0;
  
    /**************** Assign Write Channel Outputs ****************/
    assign m_axi_wdata = {wdata_i, done};
    assign write_burst_done_i = m_axi_wready && m_axi_wvalid_i && ((C_AXI_PROTOCOL==2) || m_axi_wlast_i);
    assign m_axi_awvalid = m_axi_awvalid_i;
    assign m_axi_wvalid = m_axi_wvalid_i;
    assign m_axi_bready = m_axi_bready_i;
    assign m_axi_wlast = m_axi_wlast_i;
    assign m_axi_awaddr = m_axi_awaddr_i;
    assign m_axi_awlen = m_axi_awlen_i;
    assign m_axi_wid = m_axi_wid_i;
    always @(posedge aclk) begin
      m_axi_awprot <= dummy ? awprot_i : 3'b000;
      m_axi_awsize <= dummy ? awsize_i : C_SUPPORTS_NARROW==0 ? P_M_AXI_SIZE : P_M_AXI_SIZE-1;
      m_axi_awburst <= dummy ? awburst_i : 2'b01;
      m_axi_awlock <= dummy ? awlock_i : 1'b0;
      m_axi_awcache <= dummy ? awcache_i : 4'h3;
      m_axi_awqos <= dummy ? awqos_i : 4'h0;
      m_axi_wstrb <= dummy ? wstrb_i : {P_M_AXI_DATA_BYTES{1'b1}};
      m_axi_awuser <= dummy ?  awuser_i : 0;
      m_axi_wuser <= dummy ?  wuser_i : 0;
    end
  
    //**********************************************
    // Write Channel: AWVALID, AWADDR, AWLEN, WVALID, WLAST, BREADY
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        m_axi_awvalid_i <= 1'b0;
        m_axi_wvalid_i <= 1'b0;
        awcnt_i <= C_NUM_TRANS;
        wcnt_i <= C_NUM_TRANS;
        xfer_w_i <= 8'h00;
        m_axi_awlen_i <= 0;
        m_axi_awaddr_i <= C_AXI_ADDR;
        m_axi_awid_i <= 1;
        m_axi_wid_i <= 0;
        m_axi_wlast_i <= 1'b0;
        wlen_i <= 0;
        wid_i <= 0;
        awaddr_cnt <= C_NUM_ADDR;
      end else if (C_AXI_SUPPORTS_WRITE!=0) begin
        if (m_axi_awready & m_axi_awvalid_i) begin
          m_axi_awvalid_i <= 1'b0;
          awcnt_i <= awcnt_i - 1;
          if (awaddr_cnt == 1) begin
            m_axi_awaddr_i <= dummy ? awaddr_i : C_AXI_ADDR;
            awaddr_cnt <= C_NUM_ADDR;
          end else begin
            m_axi_awaddr_i <= m_axi_awaddr_i + 32'h10000;
            awaddr_cnt <= awaddr_cnt - 1;
          end
          if (C_NUM_LEN<2 || |(m_axi_awlen_i>>(C_NUM_LEN-2))) begin
            m_axi_awlen_i <= dummy ? awlen_i : 0;
          end else begin
            m_axi_awlen_i <= (m_axi_awlen_i<<1) | 1'b1;
          end
          if (C_NUM_ID<2 || (m_axi_awid_i == C_NUM_ID)) begin
            m_axi_awid <= dummy ? awid_i : 0;
            m_axi_awid_i <= 1;
          end else begin
            m_axi_awid <= m_axi_awid_i;
            m_axi_awid_i <= m_axi_awid_i + 1;
          end
        end else if (~m_axi_wvalid_i) begin
          if (awcnt_i != 0) begin
            m_axi_awvalid_i <= 1'b1;
          end
        end
  
        /**************** Write Data Channel ****************/

        if (m_axi_wready && m_axi_wvalid_i) begin
          xfer_w_i <= xfer_w_i - 1'b1;
          if (m_axi_wlast_i) begin
            m_axi_wvalid_i <= 1'b0;
            wcnt_i <= wcnt_i - 1'b1;
          end else begin
            m_axi_wlast_i <=  (xfer_w_i == 1);
          end
        end else if (m_axi_awready & m_axi_awvalid_i) begin
          m_axi_wvalid_i <= 1'b1;
          xfer_w_i <= m_axi_awlen_i;
          m_axi_wlast_i <= (m_axi_awlen_i==0);
          m_axi_wid_i <= m_axi_awid_i;
        end
      end
    end
  
    //**********************************************
    // Write Channel: WDATA
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        wdata_i <= {C_AXI_DATA_WIDTH{1'b0}};
      end else begin
        wdata_i <= (m_axi_wvalid_i && m_axi_wready) ? {wdata_i[C_AXI_DATA_WIDTH-2 : 0], ~wdata_i[C_AXI_DATA_WIDTH-1]} : wdata_i;
      end
    end
  
    //**********************************************
    // Write Channel: Random outputs
    //**********************************************
    always @(posedge aclk) begin
      awaddr_i <= {awaddr_i, ~awaddr_i[C_AXI_ADDR_WIDTH]};
      awprot_i <= {awprot_i[3-2:0], ~awprot_i[3-1]};
      wstrb_i <= {wstrb_i, ~wstrb_i[C_AXI_DATA_WIDTH/8-1]};
      awlen_i <= {awlen_i, ~awlen_i[P_LEN_WIDTH-1]};
      awsize_i <= {awsize_i, ~awsize_i[3-1]};
      awburst_i <= {awburst_i, ~awburst_i[2-1]};
      awlock_i <= {awlock_i, ~awlock_i[2-1]};
      awcache_i <= {awcache_i, ~awcache_i[4-1]};
      awqos_i <= {awqos_i, ~awqos_i[4-1]};
      awid_i <= {awid_i, ~awid_i[P_ID_WIDTH-1]};
      awuser_i <= {awuser_i, ~awuser_i[C_AXI_AWUSER_WIDTH]};
      wuser_i <= {wuser_i, ~wuser_i[C_AXI_WUSER_WIDTH]};
    end
  
    //**********************************************
    // Write Channel: PROCESS INPUTS
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        m_axi_bready_i <= 1'b0;
        bcnt_i <= C_NUM_TRANS;
        bresp_i <= {2{1'b0}};
        buser_i <= {(C_AXI_BUSER_WIDTH+1){1'b0}};
        bid_i <= {P_ID_WIDTH{1'b0}};
        acc_b_i <= 3'b0;
      end else if (C_AXI_SUPPORTS_WRITE!=0) begin
        if (m_axi_bvalid & m_axi_bready_i) begin
          m_axi_bready_i <= 1'b0;
          bresp_i <= m_axi_bresp;
            acc_b_i[0] <= bresp_i[0];
          buser_i <= m_axi_buser;
            acc_b_i[1] <= buser_i[0];
          bid_i <= m_axi_bid;
            acc_b_i[2] <= bid_i[0];
          bcnt_i <= bcnt_i - 1;
        end else begin
          bresp_i <= bresp_i>>1;
          buser_i <= buser_i>>1;
          bid_i <= bid_i>>1;
          acc_b_i <= acc_b_i>>1;
          if (m_axi_bvalid) begin
            m_axi_bready_i <= 1'b1;
          end
        end
      end
    end


  //**********************************************
  // Assert Done
  //**********************************************
  always @(posedge aclk) begin
    if (~aresetn) begin
      done_d1 <= 1'b0;
    end else begin
      done_d1 <= done_i;
    end
  end

  assign done = done_sel ? done_i : done_d1;
  assign done_cycle = done_i & ~done_d1;
  
  always @ * begin
    if (C_AXI_SUPPORTS_WRITE == 0) begin : gen_readonly_done
       done_i = rcnt_i==0;
       done_sel = acc_r_i[0];
    end else if (C_AXI_SUPPORTS_READ == 0) begin : gen_writeonly_done
       done_i = bcnt_i==0;
       done_sel = acc_b_i[0];
    end else begin : gen_readwrite_done
       done_i = (rcnt_i==0) && (bcnt_i==0);
       done_sel = acc_r_i[0] ^ acc_b_i[0];
    end
  end
  
endmodule

`default_nettype wire


//  (c) Copyright 2019 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES. 
//-----------------------------------------------------------------------------

`timescale 1ps/1ps

module axi_register_slice_v2_1_22_test_slave #
  (
   parameter integer C_AXI_ID_WIDTH = 0,
   parameter integer C_AXI_ADDR_WIDTH = 32,
   parameter integer C_AXI_DATA_WIDTH = 32,
   parameter integer C_AXI_PROTOCOL = 0,
   parameter integer C_AXI_AWUSER_WIDTH = 0,
   parameter integer C_AXI_ARUSER_WIDTH = 0,
   parameter integer C_AXI_WUSER_WIDTH = 0,
   parameter integer C_AXI_RUSER_WIDTH = 0,
   parameter integer C_AXI_BUSER_WIDTH = 0,
   parameter integer C_AXI_SUPPORTS_WRITE = 1,
   parameter integer C_AXI_SUPPORTS_READ = 1
   )
  (
  /**************** Write Address Channel Signals ****************/
  input  wire [C_AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
  input  wire [3-1:0]                   s_axi_awprot,
  input  wire                           s_axi_awvalid,
  (* dont_touch="true" *) output wire                            s_axi_awready,
  input  wire [3-1:0]                   s_axi_awsize,
  input  wire [2-1:0]                   s_axi_awburst,
  input  wire [4-1:0]                   s_axi_awcache,
  input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]      s_axi_awlen,
  input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]     s_axi_awlock,
  input  wire [4-1:0]                   s_axi_awqos,
  input  wire [4-1:0]                   s_axi_awregion,
  input  wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]       s_axi_awid,
  input  wire [(C_AXI_AWUSER_WIDTH==0?1:C_AXI_AWUSER_WIDTH)-1:0]   s_axi_awuser,
  /**************** Write Data Channel Signals ****************/
  input  wire [C_AXI_DATA_WIDTH-1:0]     s_axi_wdata,
  input  wire [C_AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
  input  wire                           s_axi_wvalid,
  (* dont_touch="true" *) output wire                            s_axi_wready,
  input  wire                           s_axi_wlast,
  input  wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]       s_axi_wid,
  input  wire [(C_AXI_WUSER_WIDTH==0?1:C_AXI_WUSER_WIDTH)-1:0]    s_axi_wuser,
  /**************** Write Response Channel Signals ****************/
  (* dont_touch="true" *) output reg [2-1:0]                    s_axi_bresp = 2'b0,
  (* dont_touch="true" *) output wire                            s_axi_bvalid,
  input  wire                           s_axi_bready,
  (* dont_touch="true" *) output reg [(C_AXI_BUSER_WIDTH==0?1:C_AXI_BUSER_WIDTH)-1:0]    s_axi_buser = 'b0,
  (* dont_touch="true" *) output reg [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]        s_axi_bid = 'b0,
  /**************** Read Address Channel Signals ****************/
  input  wire [C_AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
  input  wire [3-1:0]                   s_axi_arprot,
  input  wire                           s_axi_arvalid,
  (* dont_touch="true" *) output wire                            s_axi_arready,
  input  wire [3-1:0]                   s_axi_arsize,
  input  wire [2-1:0]                   s_axi_arburst,
  input  wire [4-1:0]                   s_axi_arcache,
  input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]     s_axi_arlock,
  input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]      s_axi_arlen,
  input  wire [4-1:0]                   s_axi_arqos,
  input  wire [4-1:0]                   s_axi_arregion,
  input  wire [(C_AXI_ARUSER_WIDTH==0?1:C_AXI_ARUSER_WIDTH)-1:0]   s_axi_aruser,
  input  wire [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]       s_axi_arid,
  /**************** Read Data Channel Signals ****************/
  (* dont_touch="true" *) output wire [C_AXI_DATA_WIDTH-1:0]     s_axi_rdata,
  (* dont_touch="true" *) output reg [2-1:0]                    s_axi_rresp = 2'b0,
  (* dont_touch="true" *) output wire                            s_axi_rvalid,
  input  wire                           s_axi_rready,
  (* dont_touch="true" *) output wire                            s_axi_rlast,
  (* dont_touch="true" *) output reg [(C_AXI_RUSER_WIDTH==0?1:C_AXI_RUSER_WIDTH)-1:0]    s_axi_ruser = 'b0,
  (* dont_touch="true" *) output reg [(C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH)-1:0]        s_axi_rid = 'b0,
  /**************** System Signals ****************/
  input  wire                           aclk,
  input  wire                           aresetn
   );

  /**************** Local Parameters ****************/
  localparam integer  P_LEN_WIDTH = (C_AXI_PROTOCOL == 1) ? 4 : 8;
  localparam integer  P_LOCK_WIDTH = (C_AXI_PROTOCOL == 1) ? 2 : 1;
  localparam integer P_S_AXI_DATA_BYTES = 32/8;
  localparam integer P_ID_WIDTH = C_AXI_ID_WIDTH==0?1:C_AXI_ID_WIDTH;

  /**************** Internal Wires/Regs - Global ****************/
  reg                   areset = 1'b0;
  always @(posedge aclk) begin
      areset <= ~aresetn;
  end

    /**************** Internal Wires/Regs - Read Channels ****************/
    reg [8-1:0]                   xfer_r_cnt = 8'h00;
    reg [16-1:0]                  arcnt_i = 16'h0000;
    wire                          read_xaction_done_i;
    reg [C_AXI_DATA_WIDTH-1:0]     rdata_i = {C_AXI_DATA_WIDTH{1'b0}};
    reg [P_LEN_WIDTH-1:0]      arlen_i = {P_LEN_WIDTH{1'b0}};
    reg                           arvalid_i = 1'b0;
    reg [C_AXI_ADDR_WIDTH-1:0]     araddr_i = {C_AXI_ADDR_WIDTH{1'b0}};
    reg [3-1:0]                   arprot_i = 3'b000;
    reg [3-1:0]                   arsize_i = 3'b000;
    reg [2-1:0]                   arburst_i = 2'b00;
    reg [4-1:0]                   arcache_i = 4'b0000;
    reg [1-1:0]     arlock_i = 1'b0;
    reg [4-1:0]                   arqos_i = 4'b0000;
    reg [4-1:0]                   arregion_i = 4'b0000;
    reg [C_AXI_ARUSER_WIDTH:0]    aruser_i = {(C_AXI_ARUSER_WIDTH+1){1'b0}};
    reg [C_AXI_RUSER_WIDTH:0]     ruser_i = {(C_AXI_RUSER_WIDTH+1){1'b0}};
    reg [8:0]                     acc_ar_i = 9'b0;
    reg                           s_axi_rvalid_i = 1'b0;
    reg                           s_axi_arready_i = 1'b0;
    reg                           s_axi_rlast_i = 1'b0;
  
    /**************** Assign Read Channel Outputs ****************/
    assign s_axi_rdata = rdata_i;
    assign read_xaction_done_i = (s_axi_rready && s_axi_rvalid_i && s_axi_rlast_i);
    assign s_axi_rvalid = s_axi_rvalid_i;
    assign s_axi_arready = s_axi_arready_i;
    assign s_axi_rlast = s_axi_rlast_i;
    //**********************************************
    // Read Channel: ARREADY, RVALID, RLAST, RID
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        s_axi_arready_i <= 1'b0;
        s_axi_rvalid_i <= 1'b0;
        xfer_r_cnt <= 8'h00;
        arcnt_i <= 16'h0000;
        arlen_i <= {P_LEN_WIDTH{1'b0}};
        s_axi_rlast_i <= 1'b0;
      end else begin
        /**************** Read Address Channel ****************/
        // arready
        if(s_axi_arready_i && s_axi_arvalid) begin
          s_axi_arready_i <= 1'b0;
          arcnt_i <= arcnt_i + 1'b1;
        end else if (~s_axi_rvalid_i) begin
          s_axi_arready_i <= 1'b1;
        end
  
        /**************** Read Data Channel ****************/
        // rvalid
        if(s_axi_arready_i && s_axi_arvalid) begin
          s_axi_rvalid_i <= 1'b1;
          s_axi_rid <= s_axi_arid;
          s_axi_ruser <= ruser_i;
        end else if(read_xaction_done_i) begin
          s_axi_rvalid_i <= 1'b0;
        end
  
        // rlast
        if(s_axi_rready && s_axi_rvalid_i) begin
          xfer_r_cnt <= xfer_r_cnt - 1;
          if(xfer_r_cnt == 1) begin
            s_axi_rlast_i <= 1'b1;
          end
        end else if(s_axi_arready_i && s_axi_arvalid) begin
          xfer_r_cnt <= s_axi_arlen;
          s_axi_rlast_i <= (s_axi_arlen==0);
        end
      end
    end
  
  
    //**********************************************
    // Read Channel: RDATA
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        rdata_i <= {C_AXI_DATA_WIDTH{1'b0}};
      end else begin
        rdata_i <= (s_axi_rready && s_axi_rvalid_i) ? {rdata_i[C_AXI_DATA_WIDTH-2 : 0], ~rdata_i[C_AXI_DATA_WIDTH-1]} : rdata_i;
      end
    end
  
    //**********************************************
    // Read Channel: RRESP
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        s_axi_rresp <= {2{1'b0}};
      end else if (~s_axi_rvalid_i) begin
        s_axi_rresp <= {acc_ar_i[0], 1'b0};
      end
    end
  
    //**********************************************
    // Read Channel: RUSER
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        ruser_i <= {(C_AXI_RUSER_WIDTH+1){1'b0}};
      end else begin
        ruser_i <= (s_axi_arready_i && s_axi_arvalid) ? {ruser_i, ~ruser_i[C_AXI_RUSER_WIDTH]} : 0;
      end
    end
  
    //**********************************************
    // Read Channel: PROCESS INPUTS
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        araddr_i <= {C_AXI_ADDR_WIDTH{1'b0}};
        arprot_i <= {3{1'b0}};
        arsize_i <= {3{1'b0}};
        arburst_i <= {2{1'b0}};
        arcache_i <= {4{1'b0}};
        arlock_i <= {1{1'b0}};
        arqos_i <= {4{1'b0}};
        arregion_i <= {4{1'b0}};
        aruser_i <= {(C_AXI_ARUSER_WIDTH+1){1'b0}};
        acc_ar_i <= 9'b0;
      end else if (s_axi_arvalid) begin
        // Register Inputs
        araddr_i <= s_axi_araddr;
          acc_ar_i[0] <= araddr_i[0];
        arprot_i <= s_axi_arprot;
          acc_ar_i[1] <= arprot_i[0];
        arsize_i <= s_axi_arsize;
          acc_ar_i[2] <= arsize_i[0];
        arburst_i <= s_axi_arburst;
          acc_ar_i[3] <= arburst_i[0];
        arcache_i <= s_axi_arcache;
          acc_ar_i[4] <= arcache_i[0];
        arlock_i <= s_axi_arlock;
          acc_ar_i[5] <= arlock_i[0];
        arqos_i <= s_axi_arqos;
          acc_ar_i[6] <= arqos_i[0];
        arregion_i <= s_axi_arregion;
          acc_ar_i[7] <= arregion_i[0];
        aruser_i <= s_axi_aruser;
          acc_ar_i[8] <= aruser_i[0];
      end else begin
        araddr_i <= araddr_i>>1;
        arprot_i <= arprot_i>>1;
        arsize_i <= arsize_i>>1;
        arburst_i <= arburst_i>>1;
        arcache_i <= arcache_i>>1;
        arlock_i <= arlock_i>>1;
        arqos_i <= arqos_i>>1;
        arregion_i <= arregion_i>>1;
        aruser_i <= aruser_i>>1;
        acc_ar_i <= acc_ar_i>>1;
      end
    end
  
  
    /**************** Internal Wires/Regs - Write Channels ****************/
    wire                          write_burst_done_i;
    reg [16-1:0]                  awcnt_i = 16'h0000;
    reg                           awvalid_i = 1'b0;
    reg [C_AXI_ADDR_WIDTH-1:0]     awaddr_i = {C_AXI_ADDR_WIDTH{1'b0}};
    reg [3-1:0]                   awprot_i = 3'b000;
    reg [3-1:0]                   awsize_i = 3'b000;
    reg [2-1:0]                   awburst_i = 2'b00;
    reg [4-1:0]                   awcache_i = 4'b0000;
    reg [P_LEN_WIDTH-1:0]      awlen_i = {P_LEN_WIDTH{1'b0}};
    reg [1-1:0]     awlock_i = 1'b0;
    reg [4-1:0]                   awqos_i = 4'b0000;
    reg [4-1:0]                   awregion_i = 4'b0000;
    reg [C_AXI_AWUSER_WIDTH:0]     awuser_i = {(C_AXI_AWUSER_WIDTH+1){1'b0}};
    reg                           wvalid_i = 1'b0;
    reg [C_AXI_DATA_WIDTH-1:0]     wdata_i = {C_AXI_DATA_WIDTH{1'b0}};
    reg [C_AXI_DATA_WIDTH/8-1:0]   wstrb_i = {(C_AXI_DATA_WIDTH/8){1'b0}};
    reg [C_AXI_WUSER_WIDTH:0]     wuser_i = {(C_AXI_WUSER_WIDTH+1){1'b0}};
    reg [C_AXI_BUSER_WIDTH:0]     buser_i = {(C_AXI_BUSER_WIDTH+1){1'b0}};
    reg [8:0]                     acc_aw_i = 9'b0;
    reg [3:0]                     acc_w_i = 4'b0;
    reg                           s_axi_bvalid_i = 1'b0;
    reg                           s_axi_awready_i = 1'b0;
    reg                           s_axi_wready_i = 1'b0;
    /**************** Assign Write Channel Outputs ****************/
    assign write_burst_done_i =s_axi_wready_i && s_axi_wvalid && ((C_AXI_PROTOCOL == 2) ? 1'b1 : s_axi_wlast);
    assign s_axi_bvalid = s_axi_bvalid_i;
    assign s_axi_awready = s_axi_awready_i;
    assign s_axi_wready = s_axi_wready_i;
  
    //**********************************************
    // Write Channel: AWREADY, WREADY, BVALID, BID
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        awcnt_i <= 16'h0000;
        s_axi_awready_i <= 1'b0;
        s_axi_wready_i <= 1'b0;
        s_axi_bvalid_i <= 1'b0;
      end else begin
        /**************** Write Address Channel ****************/
        // awready
        if(s_axi_awready_i && s_axi_awvalid) begin
          s_axi_awready_i <= 1'b0;
          awcnt_i <= awcnt_i + 1'b1;
          s_axi_bid <= s_axi_awid;
          s_axi_buser <= buser_i;
        end else if(~s_axi_wready_i & ~s_axi_bvalid_i) begin
          s_axi_awready_i <= 1'b1;
        end
  
        /**************** Write Data Channel ****************/
        // wready
        if(write_burst_done_i) begin
          s_axi_wready_i <= 1'b0;
        end else if(s_axi_awready_i && s_axi_awvalid) begin
          s_axi_wready_i <= 1'b1;
        end
  
        /**************** Write Response Channel ****************/
        // bvalid
        if(write_burst_done_i) begin
          s_axi_bvalid_i <= 1'b1;
        end else if(s_axi_bready && s_axi_bvalid_i) begin
          s_axi_bvalid_i <= 1'b0;
        end
      end
    end
  
  
    //**********************************************
    // Write Channel: BRESP
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        s_axi_bresp <= {2{1'b0}};
      end else if (~s_axi_bvalid_i) begin
        s_axi_bresp <= {(acc_aw_i[0] ^ acc_w_i[0]), 1'b0};
      end
    end
  
    //**********************************************
    // Read Channel: BUSER
    //**********************************************
    always @(posedge aclk) begin
      if (aresetn) begin
        buser_i <= {(C_AXI_BUSER_WIDTH+1){1'b0}};
      end else begin
        buser_i <= (s_axi_awready_i && s_axi_awvalid) ? {buser_i, ~buser_i[C_AXI_BUSER_WIDTH]} : 0;
      end
    end
  
    //**********************************************
    // Write Address Channel: PROCESS INPUTS
    //**********************************************
    always @(posedge aclk) begin
      if (areset) begin
        awaddr_i <= {C_AXI_ADDR_WIDTH{1'b0}};
        awprot_i <= {3{1'b0}};
        awsize_i <= {3{1'b0}};
        awburst_i <= {2{1'b0}};
        awcache_i <= {4{1'b0}};
        awlen_i <= {P_LEN_WIDTH{1'b0}};
        awlock_i <= {1{1'b0}};
        awqos_i <= {4{1'b0}};
        awregion_i <= {4{1'b0}};
        awuser_i <= {(C_AXI_AWUSER_WIDTH+1){1'b0}};
        acc_aw_i <= 9'b0;
      end else if (s_axi_awvalid) begin
        // Register Inputs
        awaddr_i <= s_axi_awaddr;
          acc_aw_i[0] <= awaddr_i[0];
        awprot_i <= s_axi_awprot;
          acc_aw_i[1] <= awprot_i[0];
        awsize_i <= s_axi_awsize;
          acc_aw_i[2] <= awsize_i[0];
        awburst_i <= s_axi_awburst;
          acc_aw_i[3] <= awburst_i[0];
        awcache_i <= s_axi_awcache;
          acc_aw_i[4] <= awcache_i[0];
        awlock_i <= s_axi_awlock;
          acc_aw_i[5] <= awlock_i[0];
        awqos_i <= s_axi_awqos;
          acc_aw_i[6] <= awqos_i[0];
        awregion_i <= s_axi_awregion;
          acc_aw_i[7] <= awregion_i[0];
        awuser_i <= s_axi_awuser;
          acc_aw_i[8] <= awuser_i[0];
      end else begin
        awaddr_i <= awaddr_i>>1;
        awprot_i <= awprot_i>>1;
        awsize_i <= awsize_i>>1;
        awburst_i <= awburst_i>>1;
        awcache_i <= awcache_i>>1;
        awlock_i <= awlock_i>>1;
        awqos_i <= awqos_i>>1;
        awregion_i <= awregion_i>>1;
        awuser_i <= awuser_i>>1;
        acc_aw_i <= acc_aw_i>>1;
      end
    end
  
    //**********************************************
    // Write Data Channel: PROCESS INPUTS
    //**********************************************
    always @(posedge aclk) begin
      if(areset) begin
        wdata_i <= {C_AXI_DATA_WIDTH{1'b0}};
        wstrb_i <= {(C_AXI_DATA_WIDTH/8){1'b0}};
        wuser_i <= {(C_AXI_WUSER_WIDTH+1){1'b0}};
        acc_w_i <= 4'b0;
      end else if (s_axi_wvalid) begin
        // Register Inputs
        wdata_i <= s_axi_wdata;
          acc_w_i[0] <= wdata_i[0];
        wstrb_i <= s_axi_wstrb;
          acc_w_i[1] <= wstrb_i[0];
        wuser_i <= s_axi_wuser;
          acc_w_i[2] <= wuser_i[0];
      end else begin
        wdata_i <= wdata_i>>1;
        wstrb_i <= wstrb_i>>1;
        wuser_i <= wuser_i>>1;
        acc_w_i <= acc_w_i>>1;
      end
    end
  
endmodule



//  (c) Copyright 2017 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES. 
//-----------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

module axi_register_slice_v2_1_22_tdm_sample (
///////////////////////////////////////////////////////////////////////////////
// Port Declarations
///////////////////////////////////////////////////////////////////////////////
  input  wire                    slow_clk,
  input  wire                    fast_clk,
  output wire                    sample_cycle
);

////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
reg                slow_clk_div2 = 1'b0;
reg                posedge_finder_first;
reg                posedge_finder_second;
wire               first_edge;
wire               second_edge;
reg                sample_cycle_d;
(* shreg_extract = "no" *) reg                sample_cycle_r;


////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
////////////////////////////////////////////////////////////////////////////////
    always @(posedge slow_clk) begin 
      slow_clk_div2 <= ~slow_clk_div2;
    end

    // Find matching rising edges by clocking slow_clk_div2 onto faster clock
    always @(posedge fast_clk) begin 
      posedge_finder_first <= slow_clk_div2;
    end
    always @(posedge fast_clk) begin 
      posedge_finder_second <= ~slow_clk_div2;
    end

    assign first_edge = slow_clk_div2 & ~posedge_finder_first;
    assign second_edge = ~slow_clk_div2 & ~posedge_finder_second;

    always @(*) begin 
      sample_cycle_d = first_edge | second_edge;
    end
   
    always @(posedge fast_clk) begin 
      sample_cycle_r <= sample_cycle_d;
    end
    
    assign sample_cycle = sample_cycle_r;

endmodule // tdm_sample

`default_nettype wire


// -- (c) Copyright 2017 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
(* autopipeline_module="yes" *)
module axi_register_slice_v2_1_22_auto_slr #
  (
   parameter integer C_DATA_WIDTH = 32
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESETN,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
   input  wire S_VALID,
   output wire S_READY,

   // Master side
   output wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA,
   output wire M_VALID,
   input  wire M_READY
   );

    wire                    handshake_pipe;
    wire                    ready_pipe;
    wire [C_DATA_WIDTH-1:0] payload_pipe;
    (* keep="true" *)                                                                reg  s_aclear = 1'b0;
    (* autopipeline_group="fwd",autopipeline_limit=24,autopipeline_include="resp" *) reg  s_areset_fwd   = 1'b0;
    (* autopipeline_group="resp" *)                                                  reg  s_areset_resp  = 1'b0;
    (* keep="true" *)                                                                reg  s_areset_resp2 = 1'b0;
    (* keep="true" *)                                                                reg  m_aclear = 1'b0;
    (* autopipeline_group="fwd",autopipeline_limit=24,autopipeline_include="resp" *) reg  m_areset_fwd   = 1'b0;
    (* autopipeline_group="resp" *)                                                  reg  m_areset_resp  = 1'b0;
    (* keep="true" *)                                                                reg  m_areset_resp2 = 1'b0;
    
  // Global Reset pipelining
  
    always @(posedge ACLK) begin
      s_aclear       <= ~ARESETN;
      s_areset_fwd   <= ~ARESETN; 
      s_areset_resp  <= s_areset_fwd;  // Auto-pipeline
      s_areset_resp2 <= s_areset_resp; // Auto-pipeline
    end
    
    always @(posedge ACLK) begin
      m_aclear       <= ~ARESETN;
      m_areset_fwd   <= ~ARESETN; 
      m_areset_resp  <= m_areset_fwd;  // Auto-pipeline
      m_areset_resp2 <= m_areset_resp; // Auto-pipeline
    end
    
  // Source-side submodule
    
    axi_register_slice_v2_1_22_auto_src #
      (
       .C_DATA_WIDTH (C_DATA_WIDTH)
      )
      slr_auto_src
      (
       .ACLK             (ACLK),    
       .s_aclear         (s_aclear),
       .s_areset_resp2   (s_areset_resp2),  
       .S_VALID          (S_VALID),  
       .S_READY          (S_READY), 
       .S_PAYLOAD_DATA   (S_PAYLOAD_DATA),
       .ready_pipe        (ready_pipe), 
       .handshake_pipe    (handshake_pipe),
       .payload_pipe      (payload_pipe)  
      );
    
  // Destination-side submodule
    
    axi_register_slice_v2_1_22_auto_dest #
      (
       .C_DATA_WIDTH (C_DATA_WIDTH)
      )
      slr_auto_dest
      (
       .ACLK           (ACLK),    
       .m_aclear       (m_aclear),
       .m_areset_resp2 (m_areset_resp2),  
       .M_READY        (M_READY), 
       .M_VALID        (M_VALID),  
       .M_PAYLOAD_DATA (M_PAYLOAD_DATA),
       .handshake_pipe  (handshake_pipe),
       .ready_pipe      (ready_pipe),  
       .payload_pipe    (payload_pipe)  
      );
    
endmodule  // auto_slr

module axi_register_slice_v2_1_22_auto_src #
  (
   parameter integer C_DATA_WIDTH = 32
  )
  (
   input  wire ACLK,
   input  wire s_aclear,
   input  wire s_areset_resp2,
   input  wire S_VALID,
   input  wire ready_pipe,
   output wire S_READY,
   output wire handshake_pipe,
   output wire  [C_DATA_WIDTH-1:0] payload_pipe,
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA
   );
    
   (* autopipeline_group="fwd",autopipeline_limit=24,autopipeline_include="resp" *) reg  [C_DATA_WIDTH-1:0] payload_pipe_r;
    (* keep="true" *) reg [2:0] s_aresetn_resp4 = 3'b000;
    wire s_aresetn_resp3;
    wire s_aresetn_d;
    wire s_aresetn_q;
    wire s_handshake_d;
    wire s_ready_i;
    
    assign S_READY = s_ready_i & s_aresetn_q;
    assign s_aresetn_d = (~s_aresetn_resp4[2] & s_aresetn_resp4[0]) | s_aresetn_q;
    assign s_handshake_d = S_VALID & s_ready_i & s_aresetn_q;
    assign payload_pipe = payload_pipe_r;
    
    always @(posedge ACLK or posedge s_aclear) begin
      if (s_aclear) begin
        s_aresetn_resp4 <= 3'b000;
      end else begin
        s_aresetn_resp4 <= {s_aresetn_resp4[1:0], s_aresetn_resp3};
      end
    end
    
    always @(posedge ACLK) begin
      payload_pipe_r <= S_PAYLOAD_DATA;
    end
    
    FDCE #(
        .INIT(1'b0)
     ) s_aresetn_resp3_inst (
        .Q   (s_aresetn_resp3),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (1'b0),
        .D   (~s_areset_resp2)
     );
    
    // Assert s_aresetn_q asynchronously on leading edge of s_aclear; De-assert synchronously on trailing edge of s_areset_resp2.
    FDCE #(
        .INIT(1'b0)
     ) reset_asyncclear (
        .Q   (s_aresetn_q),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (s_aclear),
        .D   (s_aresetn_d)
     );
    
    (* autopipeline_group="fwd",autopipeline_limit=24,autopipeline_include="resp" *)
    FDCE #(
        .INIT(1'b0)
     ) handshake_asyncclear (
        .Q   (handshake_pipe),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (s_aclear),
        .D   (s_handshake_d)
     );
    
    FDCE #(
        .INIT(1'b0)
     ) ready_asyncclear (
        .Q   (s_ready_i),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (s_aclear),
        .D   (ready_pipe)
     );
    
endmodule  // auto_src

module axi_register_slice_v2_1_22_auto_dest #
  (
   parameter integer C_DATA_WIDTH = 32
   )
  (
   input  wire ACLK,
   input  wire m_aclear,
   input  wire m_areset_resp2,
   input  wire M_READY,
   input  wire handshake_pipe,
   output wire ready_pipe,
   output wire M_VALID,
   input  wire [C_DATA_WIDTH-1:0] payload_pipe,
   output wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA
   );
    
    (* keep="true" *) reg [2:0] m_aresetn_resp4 = 3'b000;
    wire m_aresetn_resp3;
    wire m_aresetn_d;
    wire m_aresetn_q;
    wire m_valid_i;
    wire pop;
    wire m_ready_d;
    wire m_handshake_q;
    reg  [C_DATA_WIDTH-1:0] m_payload_q;
    
    assign M_VALID = m_valid_i;
    assign m_aresetn_d = (~m_aresetn_resp4[2] & m_aresetn_resp4[0]) | m_aresetn_q;
    assign m_ready_d = (M_READY | ~m_valid_i) & m_aresetn_q;
    assign pop     = M_READY & m_valid_i;
    
    always @(posedge ACLK or posedge m_aclear) begin
      if (m_aclear) begin
        m_aresetn_resp4 <= 3'b000;
      end else begin
        m_aresetn_resp4 <= {m_aresetn_resp4[1:0], m_aresetn_resp3};
      end
    end
    
    always @(posedge ACLK) begin
      m_payload_q <= payload_pipe;
    end
    
    FDCE #(
        .INIT(1'b0)
     ) m_aresetn_resp3_inst (
        .Q   (m_aresetn_resp3),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (1'b0),
        .D   (~m_areset_resp2)
     );
    
    // Assert m_aresetn_q asynchronously on leading edge of m_aclear; De-assert synchronously on trailing edge of m_areset_resp2.
    FDCE #(
        .INIT(1'b0)
     ) reset_asyncclear (
        .Q   (m_aresetn_q),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (m_aclear),
        .D   (m_aresetn_d)
     );
    
    FDCE #(
        .INIT(1'b0)
     ) handshake_asyncclear (
        .Q   (m_handshake_q),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (m_aclear),
        .D   (handshake_pipe)
     );
    
    (* autopipeline_group="resp" *)
    FDCE #(
        .INIT(1'b0)
     ) ready_asyncclear (
        .Q   (ready_pipe),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (m_aclear),
        .D   (m_ready_d)
     );
    
    axi_register_slice_v2_1_22_axic_reg_srl_fifo #
      (
       .C_FIFO_WIDTH (C_DATA_WIDTH), 
       .C_FIFO_SIZE  (5)  
      )
      srl_fifo
      (
       .aclk    (ACLK),    
       .areset  (~m_aresetn_q),
       .aclear  (m_aclear),  
       .s_mesg  (m_payload_q),  
       .s_valid (m_handshake_q), 
       .m_mesg  (M_PAYLOAD_DATA),  
       .m_valid (m_valid_i), 
       .m_ready (pop)
      );
    
endmodule  // auto_dest



// -- (c) Copyright 2010 - 2017 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Register Slice
//   Generic single-channel AXI pipeline register on forward and/or reverse signal path
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axic_register_slice
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_srl_rtl #
  (
   parameter         C_A_WIDTH = 2          // Address Width (>= 1)
   )
  (
   input  wire                 clk, // Clock
   input  wire [C_A_WIDTH-1:0] a,   // Address
   input  wire                 ce,  // Clock Enable
   input  wire                 d,   // Input Data
   output wire                 q    // Output Data
   );

  localparam integer P_SRLDEPTH = 2**C_A_WIDTH;
  
    reg [P_SRLDEPTH-1:0] shift_reg = {P_SRLDEPTH{1'b0}};
    always @(posedge clk)
      if (ce)
        shift_reg <= {shift_reg[P_SRLDEPTH-2:0], d};
    assign q = shift_reg[a];

endmodule  // srl_rtl

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_axic_register_slice #
  (
   parameter C_FAMILY     = "virtex6",
   parameter C_DATA_WIDTH = 32,
   parameter C_REG_CONFIG = 32'h00000000
   // C_REG_CONFIG:
   //   0 => BYPASS    = The channel is just wired through the module.
   //   1 => FWD_REV   = Both FWD and REV (fully-registered)
   //   2 => FWD       = The master VALID and payload signals are registrated. 
   //   3 => REV       = The slave ready signal is registrated
   //   4 => RESERVED (all outputs driven to 0).
   //   5 => RESERVED (all outputs driven to 0).
   //   6 => INPUTS    = Slave and Master side inputs are registrated.
   //   7 => LIGHT_WT  = 1-stage pipeline register with bubble cycle, both FWD and REV pipelining
   //   9 => SI/MI_REG = Source side completely registered (including S_VALID input)
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESET,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
   input  wire S_VALID,
   output wire S_READY,

   // Master side
   output  wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA,
   output wire M_VALID,
   input  wire M_READY
   );

  (* use_clock_enable = "yes" *)

  generate
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 0
  // Bypass mode
  //
  ////////////////////////////////////////////////////////////////////
    if (C_REG_CONFIG == 32'h00000000) begin
      assign M_PAYLOAD_DATA = S_PAYLOAD_DATA;
      assign M_VALID        = S_VALID;
      assign S_READY        = M_READY;      
    end
    
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 9
  // Source (SI) interface completely registered
  //
  ////////////////////////////////////////////////////////////////////
      
    else if (C_REG_CONFIG == 32'h00000009) begin
      reg [C_DATA_WIDTH-1:0] s_payload_d;
      wire [C_DATA_WIDTH-1:0] srl_out;
      reg s_ready_i = 1'b0;
      reg m_valid_i = 1'b0;
      reg payld_sel;
      reg push;
      reg pop;
      wire s_handshake_d;
      reg s_valid_d;
      reg s_ready_d = 1'b0;
      reg s_ready_reg = 1'b0;
      reg [2:0] fifoaddr = 3'b110;
      
      reg areset_d = 1'b0;
      always @(posedge ACLK) begin
        areset_d <= ARESET;
      end
      
      assign s_handshake_d = s_valid_d & s_ready_d;

      always @ * begin
        case (fifoaddr)
          3'b111: begin  // EMPTY: No payload in SRL; pre-assert m_ready
            s_ready_i = 1'b1;
            payld_sel = 1'b0;
            pop = 1'b0;
            case ({s_handshake_d, M_READY}) 
              2'b00, 2'b01: begin  // Idle
                m_valid_i = 1'b0;
                push = 1'b0;
              end
              2'b10: begin  // Payload received
                m_valid_i = 1'b1;
                push = 1'b1;
              end
              2'b11: begin  // Payload received and read out combinatorially
                m_valid_i = 1'b1;
                push = 1'b0;
              end
            endcase
          end

          3'b000: begin  // 1 payload item in SRL
            m_valid_i = 1'b1;
            payld_sel = 1'b1;
            case ({s_handshake_d, M_READY}) 
              2'b00: begin  // Idle
                s_ready_i = 1'b1;
                push = 1'b0;
                pop = 1'b0;
              end
              2'b01: begin  // Pop
                s_ready_i = 1'b1;
                push = 1'b0;
                pop = 1'b1;
              end
              2'b10: begin  // Push
                s_ready_i = 1'b0;  // Doesn't de-assert on SI until next cycle
                push = 1'b1;
                pop = 1'b0;
              end
              2'b11: begin  // Push and Pop
                s_ready_i = 1'b1;
                push = 1'b1;
                pop = 1'b1;
              end
            endcase
          end

          3'b001: begin  // 2 payload items in SRL
            m_valid_i = 1'b1;
            payld_sel = 1'b1;
            case ({s_handshake_d, M_READY}) 
              2'b00: begin  // Idle
                s_ready_i = 1'b0;
                push = 1'b0;
                pop = 1'b0;
              end
              2'b01: begin  // Pop
                s_ready_i = 1'b1;
                push = 1'b0;
                pop = 1'b1;
              end
              2'b10: begin  // Push (Handshake completes on SI while pushing 2nd item into SRL)
                s_ready_i = 1'b0;
                push = 1'b1;
                pop = 1'b0;
              end
              2'b11: begin  // Push and Pop
                s_ready_i = 1'b0;
                push = 1'b1;
                pop = 1'b1;
              end
            endcase
          end

          3'b010: begin  // 3 payload items in SRL
            m_valid_i = 1'b1;
            s_ready_i = 1'b0;
            payld_sel = 1'b1;
            push = 1'b0;
            if (M_READY) begin  // Handshake cannot complete on SI
              pop = 1'b1;
            end else begin
              pop = 1'b0;
            end
          end

          default: begin  // RESET state (fifoaddr = 3'b110)
            m_valid_i = 1'b0;
            s_ready_i = 1'b0;
            payld_sel = 1'b0;
            push = 1'b1;  // Advance to Empty state
            pop = 1'b0;
          end  // RESET
        endcase
      end

      always @(posedge ACLK) begin
        if (areset_d) begin
          fifoaddr <= 3'b110;
          s_ready_reg <= 1'b0;
          s_ready_d <= 1'b0;
        end else begin
          s_ready_reg <= s_ready_i;
          s_ready_d <= s_ready_reg;
          if (push & ~pop) begin
            fifoaddr <= fifoaddr + 1;
          end else if (~push & pop) begin
            fifoaddr <= fifoaddr - 1;
          end
        end
      end

      always @(posedge ACLK) begin
        s_valid_d <= S_VALID;
        s_payload_d <= S_PAYLOAD_DATA;
      end

      assign S_READY = s_ready_reg;
      assign M_VALID = m_valid_i;
      assign M_PAYLOAD_DATA = payld_sel ? srl_out : s_payload_d;

    //---------------------------------------------------------------------------
    // Instantiate SRLs
    //---------------------------------------------------------------------------
      genvar i;
      for (i=0;i<C_DATA_WIDTH;i=i+1) begin : gen_srls
        axi_register_slice_v2_1_22_srl_rtl #
          (
           .C_A_WIDTH (2)
          )
          srl_nx1
          (
           .clk (ACLK),
           .a   (fifoaddr[1:0]),
           .ce  (push),
           .d   (s_payload_d[i]),
           .q   (srl_out[i])
          );
      end      
    end 
        
        
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 1 (or 8)
  // Both FWD and REV mode
  //
  ////////////////////////////////////////////////////////////////////
    else if ((C_REG_CONFIG == 32'h00000001) || (C_REG_CONFIG == 32'h00000008)) begin
      reg [C_DATA_WIDTH-1:0] m_payload_i;
      reg [C_DATA_WIDTH-1:0] skid_buffer;
      reg                    s_ready_i = 1'b0; 
      reg                    m_valid_i = 1'b0;

      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;
      assign M_PAYLOAD_DATA = m_payload_i;

      reg [1:0] aresetn_d = 2'b00; // Reset delay shifter
      always @(posedge ACLK) begin
        if (ARESET) begin
          aresetn_d <= 2'b00;
        end else begin
          aresetn_d <= {aresetn_d[0], ~ARESET};
        end
      end
      
      always @(posedge ACLK) begin
        if (~aresetn_d[0]) begin
          s_ready_i <= 1'b0;
        end else begin
          s_ready_i <= M_READY | ~m_valid_i | (s_ready_i & ~S_VALID);
        end
        
        if (~aresetn_d[1]) begin
          m_valid_i <= 1'b0;
        end else begin
          m_valid_i <= S_VALID | ~s_ready_i | (m_valid_i & ~M_READY);
        end
        
        if (M_READY | ~m_valid_i) begin
          m_payload_i <= s_ready_i ? S_PAYLOAD_DATA : skid_buffer;
        end
        
        if (s_ready_i) begin
          skid_buffer <= S_PAYLOAD_DATA;
        end
      end

    end // if (C_REG_CONFIG == 1)
    
    
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 2
  // Only FWD mode
  //
  ////////////////////////////////////////////////////////////////////
    else if (C_REG_CONFIG == 32'h00000002)
    begin
      reg [C_DATA_WIDTH-1:0] storage_data;
      wire                   s_ready_i; //local signal of output
      reg                    m_valid_i = 1'b0; //local signal of output

      // assign local signal to its output signal
      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;

      reg aresetn_d = 1'b0; // Reset delay register
      always @(posedge ACLK) begin
        if (ARESET) begin
          aresetn_d <= 1'b0;
        end else begin
          aresetn_d <= ~ARESET;
        end
      end
      
      // Save payload data whenever we have a transaction on the slave side
      always @(posedge ACLK) 
      begin
        if (S_VALID & s_ready_i)
          storage_data <= S_PAYLOAD_DATA;
      end

      assign M_PAYLOAD_DATA = storage_data;
      
      // M_Valid set to high when we have a completed transfer on slave side
      // Is removed on a M_READY except if we have a new transfer on the slave side
      always @(posedge ACLK) 
      begin
        if (~aresetn_d) 
          m_valid_i <= 1'b0;
        else
          if (S_VALID) // Always set m_valid_i when slave side is valid
            m_valid_i <= 1'b1;
          else
            if (M_READY) // Clear (or keep) when no slave side is valid but master side is ready
              m_valid_i <= 1'b0;
      end // always @ (posedge ACLK)
      
      // Slave Ready is either when Master side drives M_Ready or we have space in our storage data
      assign s_ready_i = (M_READY | ~m_valid_i) & aresetn_d;

    end // if (C_REG_CONFIG == 2)
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 3
  // Only REV mode
  //
  ////////////////////////////////////////////////////////////////////
    else if (C_REG_CONFIG == 32'h00000003)
    begin
      reg [C_DATA_WIDTH-1:0] storage_data;
      reg                    s_ready_i = 1'b0; //local signal of output
      reg                    has_valid_storage_i;
      reg                    has_valid_storage;

      reg [1:0] aresetn_d = 2'b00; // Reset delay register
      always @(posedge ACLK) begin
        if (ARESET) begin
          aresetn_d <= 2'b00;
        end else begin
          aresetn_d <= {aresetn_d[0], ~ARESET};
        end
      end
      
      // Save payload data whenever we have a transaction on the slave side
      always @(posedge ACLK) 
      begin
        if (S_VALID & s_ready_i)
          storage_data <= S_PAYLOAD_DATA;
      end

      assign M_PAYLOAD_DATA = has_valid_storage?storage_data:S_PAYLOAD_DATA;

      // Need to determine when we need to save a payload
      // Need a combinatorial signals since it will also effect S_READY
      always @ *
      begin
        // Set the value if we have a slave transaction but master side is not ready
        if (S_VALID & s_ready_i & ~M_READY)
          has_valid_storage_i = 1'b1;
        
        // Clear the value if it's set and Master side completes the transaction but we don't have a new slave side 
        // transaction 
        else if ( (has_valid_storage == 1) && (M_READY == 1) && ( (S_VALID == 0) || (s_ready_i == 0)))
          has_valid_storage_i = 1'b0;
        else
          has_valid_storage_i = has_valid_storage;
      end // always @ *

      always @(posedge ACLK) 
      begin
        if (~aresetn_d[0]) 
          has_valid_storage <= 1'b0;
        else
          has_valid_storage <= has_valid_storage_i;
      end

      // S_READY is either clocked M_READY or that we have room in local storage
      always @(posedge ACLK) 
      begin
        if (~aresetn_d[0]) 
          s_ready_i <= 1'b0;
        else
          s_ready_i <= M_READY | ~has_valid_storage_i;
      end

      // assign local signal to its output signal
      assign S_READY = s_ready_i;

      // M_READY is either combinatorial S_READY or that we have valid data in local storage
      assign M_VALID = (S_VALID | has_valid_storage) & aresetn_d[1];
      
    end // if (C_REG_CONFIG == 3)
    
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 4 or 5 is NO LONGER SUPPORTED
  //
  ////////////////////////////////////////////////////////////////////
    else if ((C_REG_CONFIG == 32'h00000004) || (C_REG_CONFIG == 32'h00000005))
    begin
// synthesis translate_off
      initial begin  
        $display ("ERROR: For axi_register_slice, C_REG_CONFIG = 4 or 5 is RESERVED.");
      end
// synthesis translate_on
      assign M_PAYLOAD_DATA = 0;
      assign M_VALID        = 1'b0;
      assign S_READY        = 1'b0;    
    end  

  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 6
  // INPUTS mode
  //
  ////////////////////////////////////////////////////////////////////
    else if (C_REG_CONFIG == 32'h00000006)
    begin
      localparam [1:0] 
        ZERO = 2'b00,
        ONE  = 2'b01,
        TWO  = 2'b11;
      reg [1:0] state = ZERO;
      reg [1:0] next_state;

      reg [C_DATA_WIDTH-1:0] storage_data1;
      reg [C_DATA_WIDTH-1:0] storage_data2;
      reg                    s_valid_d = 1'b0;
      reg                    s_ready_d = 1'b0;
      reg                    m_ready_d = 1'b0;
      reg                    m_valid_d = 1'b0;
      reg                    load_s2;
      reg                    sel_s2;
      wire                   new_access;
      wire                   access_done;
      wire                   s_ready_i; //local signal of output
      reg                    s_ready_ii;
      reg                    m_valid_i; //local signal of output
      
      reg [1:0] aresetn_d = 2'b00; // Reset delay register
      always @(posedge ACLK) begin
        if (ARESET) begin
          aresetn_d <= 2'b00;
        end else begin
          aresetn_d <= {aresetn_d[0], ~ARESET};
        end
      end
      
      // assign local signal to its output signal
      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;
      assign s_ready_i = s_ready_ii & aresetn_d[1];

      // Registrate input control signals
      always @(posedge ACLK) 
      begin
        if (~aresetn_d[0]) begin          
          s_valid_d <= 1'b0;
          s_ready_d <= 1'b0;
          m_ready_d <= 1'b0;
        end else begin
          s_valid_d <= S_VALID;
          s_ready_d <= s_ready_i;
          m_ready_d <= M_READY;
        end
      end // always @ (posedge ACLK)

      // Load storage1 with slave side payload data when slave side ready is high
      always @(posedge ACLK) 
      begin
        if (s_ready_i)
          storage_data1 <= S_PAYLOAD_DATA;          
      end

      // Load storage2 with storage data 
      always @(posedge ACLK) 
      begin
        if (load_s2)
          storage_data2 <= storage_data1;
      end

      always @(posedge ACLK) 
      begin
        if (~aresetn_d[0]) 
          m_valid_d <= 1'b0;
        else 
          m_valid_d <= m_valid_i;
      end

      // Local help signals
      assign new_access  = s_ready_d & s_valid_d;
      assign access_done = m_ready_d & m_valid_d;


      // State Machine for handling output signals
      always @*
      begin
        next_state = state; // Stay in the same state unless we need to move to another state
        load_s2   = 0;
        sel_s2    = 0;
        m_valid_i = 0;
        s_ready_ii = 0;
        case (state)
            // No transaction stored locally
            ZERO: begin
              load_s2   = 0;
              sel_s2    = 0;
              m_valid_i = 0;
              s_ready_ii = 1;
              if (new_access) begin
                next_state = ONE; // Got one so move to ONE
                load_s2   = 1;
                m_valid_i = 0;
              end
              else begin
                next_state = next_state;
                load_s2   = load_s2;
                m_valid_i = m_valid_i;
              end

            end // case: ZERO

            // One transaction stored locally
            ONE: begin
              load_s2   = 0;
              sel_s2    = 1;
              m_valid_i = 1;
              s_ready_ii = 1;
              if (~new_access & access_done) begin
                next_state = ZERO; // Read out one so move to ZERO
                m_valid_i = 0;                      
              end
              else if (new_access & ~access_done) begin
                next_state = TWO;  // Got another one so move to TWO
                s_ready_ii = 0;
              end
              else if (new_access & access_done) begin
                load_s2   = 1;
                sel_s2    = 0;
              end
              else begin
                load_s2   = load_s2;
                sel_s2    = sel_s2;
              end


            end // case: ONE

            // TWO transaction stored locally
            TWO: begin
              load_s2   = 0;
              sel_s2    = 1;
              m_valid_i = 1;
              s_ready_ii = 0;
              if (access_done) begin 
                next_state = ONE; // Read out one so move to ONE
                s_ready_ii  = 1;
                load_s2    = 1;
                sel_s2     = 0;
              end
              else begin
                next_state = next_state;
                s_ready_ii  = s_ready_ii;
                load_s2    = load_s2;
                sel_s2     = sel_s2;
              end
            end // case: TWO
        endcase // case (state)
      end // always @ *


      // State Machine for handling output signals
      always @(posedge ACLK) 
      begin
        if (~aresetn_d[0]) 
          state <= ZERO;
        else
          state <= next_state; // Stay in the same state unless we need to move to another state
      end
      
      // Master Payload mux
      assign M_PAYLOAD_DATA = sel_s2?storage_data2:storage_data1;

    end // if (C_REG_CONFIG == 6)
  ////////////////////////////////////////////////////////////////////
  //
  // C_REG_CONFIG = 7
  // Light-weight mode.
  // 1-stage pipeline register with bubble cycle, both FWD and REV pipelining
  // Operates same as 1-deep FIFO
  //
  ////////////////////////////////////////////////////////////////////
    else if (C_REG_CONFIG == 32'h00000007) begin
      reg [C_DATA_WIDTH-1:0] m_payload_i;
      reg                    s_ready_i = 1'b0; 
      reg                    m_valid_i = 1'b0;

      assign S_READY = s_ready_i;
      assign M_VALID = m_valid_i;
      assign M_PAYLOAD_DATA = m_payload_i;

      reg [1:0] aresetn_d = 2'b00; // Reset delay shifter
      always @(posedge ACLK) begin
        if (ARESET) begin
          aresetn_d <= 2'b00;
        end else begin
          aresetn_d <= {aresetn_d[0], ~ARESET};
        end
      end
      
      always @(posedge ACLK) begin
        if (~aresetn_d[0]) begin
          s_ready_i <= 1'b0;
        end else if (~aresetn_d[1]) begin
          s_ready_i <= 1'b1;
        end else begin
          s_ready_i <= m_valid_i ? M_READY : ~S_VALID;
        end
        
        if (~aresetn_d[1]) begin
          m_valid_i <= 1'b0;
        end else begin
          m_valid_i <= s_ready_i ? S_VALID : ~M_READY;
        end
        
        if (~m_valid_i) begin
          m_payload_i <= S_PAYLOAD_DATA;
        end
      end
      
    end // if (C_REG_CONFIG == 7)
    
    else begin : default_case
      // Passthrough
      assign M_PAYLOAD_DATA = S_PAYLOAD_DATA;
      assign M_VALID        = S_VALID;
      assign S_READY        = M_READY;      
    end

  endgenerate
endmodule // axic_register_slice


// -- (c) Copyright 2017 Xilinx, Inc. All rights reserved.
// --
// -- This file contains confidential and proprietary information
// -- of Xilinx, Inc. and is protected under U.S. and 
// -- international copyright and other intellectual property
// -- laws.
// --
// -- DISCLAIMER
// -- This disclaimer is not a license and does not grant any
// -- rights to the materials distributed herewith. Except as
// -- otherwise provided in a valid license issued to you by
// -- Xilinx, and to the maximum extent permitted by applicable
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of
// -- liability) for any loss or damage of any kind or nature
// -- related to, arising under or in connection with these
// -- materials, including for any direct, or any indirect,
// -- special, incidental, or consequential loss or damage
// -- (including loss of data, profits, goodwill, or any type of
// -- loss or damage suffered as a result of any action brought
// -- by a third party) even if such damage or loss was
// -- reasonably foreseeable or Xilinx had been advised of the
// -- possibility of the same.
// --
// -- CRITICAL APPLICATIONS
// -- Xilinx products are not designed or intended to be fail-
// -- safe, or for use in any application requiring fail-safe
// -- performance, such as life-support or safety devices or
// -- systems, Class III medical devices, nuclear facilities,
// -- applications related to the deployment of airbags, or any
// -- other applications that could lead to death, personal
// -- injury, or severe property or environmental damage
// -- (individually and collectively, "Critical
// -- Applications"). Customer assumes the sole risk and
// -- liability of any use of Xilinx products in Critical
// -- Applications, subject only to applicable laws and
// -- regulations governing limitations on product liability.
// --
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// -- PART OF THIS FILE AT ALL TIMES.
//-----------------------------------------------------------------------------
//
// Register Slice
//   Generic single-channel AXI pipeline register on forward and/or reverse signal path
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axic_register_slice_slr
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_multi_slr #
  (
   parameter C_FAMILY     = "virtex6",
   parameter integer C_DATA_WIDTH = 32,
   parameter integer C_CHANNEL = 0,  // 0=Forward, 1=Response
   parameter integer C_NUM_SLR_CROSSINGS = 0,
   parameter integer C_PIPELINES_MASTER = 0,
   parameter integer C_PIPELINES_SLAVE = 0,
   parameter integer C_PIPELINES_MIDDLE = 0
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESETN,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
   input  wire S_VALID,
   output wire S_READY,

   // Master side
   output  wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA,
   output wire M_VALID,
   input  wire M_READY
   );
   
  localparam integer P_FORWARD = 0;
  localparam integer P_RESPONSE = 1;
  localparam integer P_REG_CONFIG = 15;
  localparam integer P_FWD_MIDDLE_LATENCY = C_PIPELINES_MASTER + 2;
  localparam integer P_RESP_MIDDLE_LATENCY = C_PIPELINES_SLAVE + 2;
  localparam integer P_FWD_MIDDLE2_LATENCY = C_PIPELINES_MASTER + 2 + C_PIPELINES_MIDDLE + 2;
  localparam integer P_RESP_MIDDLE2_LATENCY = C_PIPELINES_SLAVE + 2 + C_PIPELINES_MIDDLE + 2;
  localparam integer P_FWD_DEST_LATENCY = C_PIPELINES_MASTER + 2 + ((C_NUM_SLR_CROSSINGS>1) ? (C_PIPELINES_MIDDLE+2) : 0) + ((C_NUM_SLR_CROSSINGS==3) ? (C_PIPELINES_MIDDLE+2) : 0);
  localparam integer P_RESP_DEST_LATENCY = C_PIPELINES_SLAVE + 2 + ((C_NUM_SLR_CROSSINGS>1) ? (C_PIPELINES_MIDDLE+2) : 0) + ((C_NUM_SLR_CROSSINGS==3) ? (C_PIPELINES_MIDDLE+2) : 0);

  generate
  
  if (C_NUM_SLR_CROSSINGS==0) begin : single_slr
    
    axi_register_slice_v2_1_22_single_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
      .C_PIPELINES  (C_PIPELINES_MASTER) 
    )
    slr_master (
      .ACLK           (ACLK),
      .ARESETN         (ARESETN),
      .S_PAYLOAD_DATA (S_PAYLOAD_DATA),
      .S_VALID        (S_VALID),
      .S_READY        (S_READY),
      .M_PAYLOAD_DATA (M_PAYLOAD_DATA),
      .M_VALID        (M_VALID),
      .M_READY        (M_READY)
    );
    
  end else if (C_NUM_SLR_CROSSINGS==1) begin : dual_slr
    
    wire [C_DATA_WIDTH-1:0] src_payload;
    wire src_handshake;
    wire src_reset;
    wire src_ready;
    wire dummy_reset;
        
    if (C_CHANNEL==P_FORWARD) begin : fwd
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  ( C_PIPELINES_MASTER) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_master (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN             (ARESETN),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( src_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset   ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE),
        .C_SOURCE_LATENCY (P_FWD_DEST_LATENCY)
      )
      slr_slave (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN             ( ARESETN ) ,
        .laguna_s_reset_out ( dummy_reset   ) ,
        .laguna_s_reset_in  ( src_reset   ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
      
    end else begin : resp
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_slave (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN             ( ARESETN ),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( dummy_reset   ) ,
        .laguna_m_reset_in  ( src_reset  ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_MASTER),
        .C_SOURCE_LATENCY (P_RESP_DEST_LATENCY)
      )
      slr_master (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN             ( ARESETN        ) ,
        .laguna_s_reset_out ( src_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset    ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
    end
    
  end else if (C_NUM_SLR_CROSSINGS==2) begin : triple_slr
    
    wire [C_DATA_WIDTH-1:0] src_payload;
    wire src_handshake;
    wire src_ready;
    wire src_reset;
    wire [C_DATA_WIDTH-1:0] dest_payload;
    wire dest_handshake;
    wire dest_ready;
    wire dest_reset;
    wire dummy_reset1;
    wire dummy_reset2;
        
    if (C_CHANNEL==P_FORWARD) begin : fwd
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_MASTER) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_master (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN             (ARESETN),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( src_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset1   ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_FWD_MIDDLE_LATENCY)
      )
      slr_middle (
        .ACLK               ( ACLK ) ,
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( dummy_reset1   ) ,
        .laguna_s_reset_in  ( src_reset    ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .laguna_m_reset_out ( dest_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset2   ) ,
        .laguna_m_payload   ( dest_payload ) , 
        .laguna_m_handshake ( dest_handshake   ) ,
        .laguna_m_ready     ( dest_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE),
        .C_SOURCE_LATENCY (P_FWD_DEST_LATENCY)
      )
      slr_slave (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( dummy_reset2   ) ,
        .laguna_s_reset_in  ( dest_reset    ) ,
        .laguna_s_payload   ( dest_payload ) ,
        .laguna_s_handshake ( dest_handshake   ) ,
        .laguna_s_ready     ( dest_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
      
    end else begin : resp
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_slave (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN            ( ARESETN ),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( dummy_reset1   ) ,
        .laguna_m_reset_in  ( src_reset   ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_RESP_MIDDLE_LATENCY)
      )
      slr_middle (
        .ACLK               ( ACLK ) ,
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( src_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset1    ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .laguna_m_reset_out ( dummy_reset2   ) ,
        .laguna_m_reset_in  ( dest_reset   ) ,
        .laguna_m_payload   ( dest_payload ) , 
        .laguna_m_handshake ( dest_handshake   ) ,
        .laguna_m_ready     ( dest_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_MASTER),
        .C_SOURCE_LATENCY (P_RESP_DEST_LATENCY)
      )
      slr_master (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN             ( ARESETN        ) ,
        .laguna_s_reset_out ( dest_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset2    ) ,
        .laguna_s_payload   ( dest_payload ) ,
        .laguna_s_handshake ( dest_handshake   ) ,
        .laguna_s_ready     ( dest_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
    end
      
  end else if (C_NUM_SLR_CROSSINGS==3) begin : quad_slr
    
    wire [C_DATA_WIDTH-1:0] src_payload;
    wire src_handshake;
    wire src_ready;
    wire src_reset;
    wire [C_DATA_WIDTH-1:0] mid_payload;
    wire mid_handshake;
    wire mid_ready;
    wire mid_reset;
    wire [C_DATA_WIDTH-1:0] dest_payload;
    wire dest_handshake;
    wire dest_ready;
    wire dest_reset;
    wire dummy_reset1;
    wire dummy_reset2;
    wire dummy_reset3;
        
    if (C_CHANNEL==P_FORWARD) begin : fwd
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_MASTER) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_master (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN             (ARESETN),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( src_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset1   ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_FWD_MIDDLE_LATENCY)
      )
      slr_middle_master (
        .ACLK               ( ACLK ) ,
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( dummy_reset1   ) ,
        .laguna_s_reset_in  ( src_reset    ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .laguna_m_reset_out ( mid_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset2   ) ,
        .laguna_m_payload   ( mid_payload ) , 
        .laguna_m_handshake ( mid_handshake   ) ,
        .laguna_m_ready     ( mid_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_FWD_MIDDLE2_LATENCY)
      )
      slr_middle_slave (
        .ACLK               ( ACLK ) ,
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( dummy_reset2   ) ,
        .laguna_s_reset_in  ( mid_reset    ) ,
        .laguna_s_payload   ( mid_payload ) ,
        .laguna_s_handshake ( mid_handshake   ) ,
        .laguna_s_ready     ( mid_ready   ) ,
        .laguna_m_reset_out ( dest_reset   ) ,
        .laguna_m_reset_in  ( dummy_reset3   ) ,
        .laguna_m_payload   ( dest_payload ) , 
        .laguna_m_handshake ( dest_handshake   ) ,
        .laguna_m_ready     ( dest_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE),
        .C_SOURCE_LATENCY (P_FWD_DEST_LATENCY)
      )
      slr_slave (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN            ( ARESETN ),
        .laguna_s_reset_out ( dummy_reset3   ) ,
        .laguna_s_reset_in  ( dest_reset    ) ,
        .laguna_s_payload   ( dest_payload ) ,
        .laguna_s_handshake ( dest_handshake   ) ,
        .laguna_s_ready     ( dest_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
      
    end else begin : resp
      axi_register_slice_v2_1_22_source_region_slr # (
        .C_FAMILY     ( C_FAMILY ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_SLAVE) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_REG_CONFIG ( P_REG_CONFIG ) 
      )
      slr_slave (
        .ACLK               (ACLK),
        .ACLK2X             (1'b0),
        .ARESETN            ( ARESETN ),
        .S_PAYLOAD_DATA     (S_PAYLOAD_DATA),
        .S_VALID            (S_VALID),
        .S_READY            (S_READY),
        .laguna_m_reset_out ( dummy_reset1   ) ,
        .laguna_m_reset_in  ( src_reset   ) ,
        .laguna_m_payload   ( src_payload ) , 
        .laguna_m_handshake ( src_handshake   ) ,
        .laguna_m_ready     ( src_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_RESP_MIDDLE_LATENCY)
      )
      slr_middle_slave (
        .ACLK               ( ACLK ) ,
        .ARESETN             ( ARESETN ) ,
        .laguna_s_reset_out ( src_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset1    ) ,
        .laguna_s_payload   ( src_payload ) ,
        .laguna_s_handshake ( src_handshake   ) ,
        .laguna_s_ready     ( src_ready   ) ,
        .laguna_m_reset_out (  dummy_reset2  ) ,
        .laguna_m_reset_in  ( mid_reset   ) ,
        .laguna_m_payload   ( mid_payload ) , 
        .laguna_m_handshake ( mid_handshake   ) ,
        .laguna_m_ready     ( mid_ready   )
      );
      
      axi_register_slice_v2_1_22_middle_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_PIPELINES  (C_PIPELINES_MIDDLE),
        .C_SOURCE_LATENCY (P_RESP_MIDDLE2_LATENCY)
      )
      slr_middle_master (
        .ACLK               ( ACLK ) ,
        .ARESETN             ( ARESETN ) ,
        .laguna_s_reset_out ( mid_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset2   ) ,
        .laguna_s_payload   ( mid_payload ) ,
        .laguna_s_handshake ( mid_handshake   ) ,
        .laguna_s_ready     ( mid_ready   ) ,
        .laguna_m_reset_out ( dummy_reset3   ) ,
        .laguna_m_reset_in  ( dest_reset   ) ,
        .laguna_m_payload   ( dest_payload ) , 
        .laguna_m_handshake ( dest_handshake   ) ,
        .laguna_m_ready     ( dest_ready   )
      );
      
      axi_register_slice_v2_1_22_dest_region_slr #(
        .C_FAMILY     ( C_FAMILY         ) ,
        .C_REG_CONFIG ( P_REG_CONFIG ) ,
        .C_CHANNEL    ( C_CHANNEL ),
        .C_DATA_WIDTH ( C_DATA_WIDTH ) ,
        .C_SLR_WIDTH  ( C_DATA_WIDTH ),
        .C_PIPELINES  (C_PIPELINES_MASTER),
        .C_SOURCE_LATENCY (P_RESP_DEST_LATENCY)
      )
      slr_master (
        .ACLK               ( ACLK            ) ,
        .ACLK2X             (1'b0),
        .ARESETN             ( ARESETN        ) ,
        .laguna_s_reset_out ( dest_reset   ) ,
        .laguna_s_reset_in  ( dummy_reset3    ) ,
        .laguna_s_payload   ( dest_payload ) ,
        .laguna_s_handshake ( dest_handshake   ) ,
        .laguna_s_ready     ( dest_ready   ) ,
        .M_PAYLOAD_DATA     (M_PAYLOAD_DATA),
        .M_VALID            (M_VALID),
        .M_READY            (M_READY)
      );
    end
  end
  
endgenerate
endmodule  // multi_slr

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_middle_region_slr #
  (
   parameter C_FAMILY     = "virtex6",
   parameter integer C_DATA_WIDTH = 32,
   parameter integer C_CHANNEL = 0,  // 0=Forward, 1=Response
   parameter integer C_PIPELINES = 0,
   parameter integer C_SOURCE_LATENCY = 1
      // Number of cycles to wait after laguna_s_ready output to enable shifting internal pipeline stages, to stay in sync with pipeline enables in source slr .
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESETN,

   // Slave side
   input  wire laguna_s_reset_in,
   output wire laguna_s_reset_out,
   input  wire [C_DATA_WIDTH-1:0] laguna_s_payload,
   input  wire laguna_s_handshake,
   output wire laguna_s_ready,

   // Master side
   input  wire laguna_m_reset_in,
   output wire laguna_m_reset_out,
   output wire [C_DATA_WIDTH-1:0] laguna_m_payload,
   output wire laguna_m_handshake,
   input  wire laguna_m_ready
   );
   
  localparam integer P_PIPE_WIDTH = C_PIPELINES>0 ? C_PIPELINES : 1;
  localparam integer P_PIPE_LATENCY = ((C_SOURCE_LATENCY>0)?C_SOURCE_LATENCY:1) + C_PIPELINES;
  localparam integer P_FANOUT = 256;
  localparam integer P_REPLICATION = (C_DATA_WIDTH>P_FANOUT) ? (C_DATA_WIDTH/P_FANOUT + 1) : 1;
  localparam integer P_FORWARD = 0;
  localparam integer P_RESPONSE = 1;
   
  generate

  (* keep="true" *) reg s_reset_dd = 1'b0;
  (* keep="true" *) reg m_reset_dd = 1'b0;
  (* USER_SLL_REG="true", keep="true" *) reg laguna_s_reset_in_d = 1'b0;
  (* USER_SLL_REG="true", keep="true" *) reg laguna_m_reset_in_d = 1'b0;
  (* USER_SLL_REG="true", keep="true" *) reg laguna_s_reset_out_i = 1'b0;
  (* USER_SLL_REG="true", keep="true" *) reg laguna_m_reset_out_i = 1'b0;
  
  assign laguna_s_reset_out = laguna_s_reset_out_i;
  assign laguna_m_reset_out = laguna_m_reset_out_i;
  
  always @(posedge ACLK) begin
    laguna_s_reset_in_d <= laguna_s_reset_in;
    laguna_m_reset_in_d <= laguna_m_reset_in;
    s_reset_dd <= laguna_s_reset_in_d;
    m_reset_dd <= laguna_m_reset_in_d;
    laguna_s_reset_out_i <= C_PIPELINES==0 ? laguna_m_reset_in_d : m_reset_dd;
    laguna_m_reset_out_i <= C_PIPELINES==0 ? laguna_s_reset_in_d : s_reset_dd;
  end
  
  wire ACLEAR;
  assign ACLEAR = ~ARESETN;
  
  if (1) begin : common
    (* USER_SLL_REG="true", shreg_extract="no" *) reg [C_DATA_WIDTH-1:0] laguna_s_payload_d;
    (* USER_SLL_REG="true", shreg_extract="no" *) reg [C_DATA_WIDTH-1:0] laguna_m_payload_i;
    wire laguna_s_handshake_q;
    wire m_handshake_d;
    (* USER_SLL_REG="true", keep="true" *)  reg laguna_m_ready_d = 1'b0;
    (* USER_SLL_REG="true", keep="true" *)  reg laguna_s_ready_i = 1'b0;
    (* keep="true" *)  reg [P_PIPE_WIDTH-1:0] ready_d = {P_PIPE_WIDTH{1'b0}};
    wire [(C_PIPELINES+2)*C_DATA_WIDTH-1:0] payload_i;
    wire [(C_PIPELINES+2)-1:0] handshake_i;
    genvar p;
    
    assign laguna_m_payload = laguna_m_payload_i;
    assign laguna_s_ready = laguna_s_ready_i;
        
    always @(posedge ACLK) begin
      laguna_m_ready_d <= laguna_m_ready; 
      laguna_s_ready_i <= (C_PIPELINES==0) ? laguna_m_ready_d : ready_d[P_PIPE_WIDTH-1];
      ready_d <= {ready_d, laguna_m_ready_d}; 
    end

    for (p=0; p<=(C_PIPELINES+1); p=p+1) begin : pipe
      (* shreg_extract="no" *) reg [C_DATA_WIDTH-1:0]  payload_data;
      wire payload_valid_d;
      wire payload_valid_q;
      
      assign payload_i[p*C_DATA_WIDTH +: C_DATA_WIDTH] = (p==0) ? laguna_s_payload_d : payload_data;
      assign handshake_i[p] = (p==0) ? laguna_s_handshake_q : payload_valid_q;
      assign payload_valid_d = handshake_i[((p>0)?(p-1):0)];
      
      always @(posedge ACLK) begin
        if (p==0) begin
          laguna_s_payload_d <= laguna_s_payload;
        end else if (p==C_PIPELINES+1) begin
          laguna_m_payload_i <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
        end else begin
          payload_data <= payload_i[((p>0)?(p-1):0)*C_DATA_WIDTH +: C_DATA_WIDTH];
        end
      end

      FDCE #(
          .INIT(1'b0)
       ) payload_valid_asyncclear_inst (
          .Q   (payload_valid_q),
          .C   (ACLK), 
          .CE  (1'b1),
          .CLR (ACLEAR),
          .D   (payload_valid_d)
       );
    end  // loop p
    
    assign m_handshake_d = handshake_i[C_PIPELINES];
    
    (* USER_SLL_REG="true" *)
    FDCE #(
        .INIT(1'b0)
     ) laguna_m_handshake_asyncclear_inst (
        .Q   (laguna_m_handshake),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (ACLEAR),
        .D   (m_handshake_d)
     );
    
    (* USER_SLL_REG="true" *)
    FDCE #(
        .INIT(1'b0)
     ) laguna_s_handshake_asyncclear_inst (
        .Q   (laguna_s_handshake_q),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (ACLEAR),
        .D   (laguna_s_handshake)
     );
    
  end // gen_slr
  endgenerate
endmodule  // middle_region_slr

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_source_region_slr #
  (
   parameter C_FAMILY     = "virtex6",
   parameter integer C_REG_CONFIG = 12,
   parameter integer C_CHANNEL = 0,  // 0=Forward, 1=Response
   parameter integer C_DATA_WIDTH = 32,
   parameter integer C_SLR_WIDTH = 32,
   parameter integer C_PIPELINES = 0
   )
  (
   // System Signals
   input wire ACLK,
   input wire ACLK2X,
   input wire ARESETN,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
   input  wire S_VALID,
   output wire S_READY,

   // Master side
   input  wire laguna_m_reset_in,
   output wire laguna_m_reset_out,
   output wire [C_SLR_WIDTH-1:0] laguna_m_payload,
   output wire laguna_m_handshake,
   input  wire laguna_m_ready
   );

  generate

  if (C_REG_CONFIG == 13) begin : tdm
    (* keep="true" *) reg areset_d = 1'b0;
    always @(posedge ACLK) begin
      areset_d <= ~ARESETN;
    end
    assign laguna_m_reset_out = 1'b0;
  
    localparam integer P_EVEN_WIDTH = C_DATA_WIDTH[0] ? (C_DATA_WIDTH+1) : C_DATA_WIDTH;
    
    (* shreg_extract = "no" *) reg [P_EVEN_WIDTH-1:0] payload_d1;
    (* shreg_extract = "no" *) reg [C_SLR_WIDTH-1:0]  laguna_m_payload_i;
    (* keep="true" *)    reg laguna_m_handshake_i = 1'b0;
    (* shreg_extract = "no" *) reg laguna_m_ready_d = 1'b0;
    wire sample_cycle;
    integer i;

    assign laguna_m_payload = laguna_m_payload_i;
    assign laguna_m_handshake = laguna_m_handshake_i;
    assign S_READY = laguna_m_ready_d;
        
    always @(posedge ACLK) begin
      if (laguna_m_ready_d) begin
        payload_d1 <= S_PAYLOAD_DATA;  // ACLK cycle 1
      end
    end

    always @(posedge ACLK2X) begin
      for (i=0;i<C_SLR_WIDTH;i=i+1) begin  
        if (laguna_m_ready_d) begin
          if (~sample_cycle) begin  // First (high) phase of ACLK cycle 2
            laguna_m_payload_i[i] <= payload_d1[2*i+1];  // Mux odd bits
          end else begin  // Second (low) phase of ACLK cycle 2
            laguna_m_payload_i[i] <= payload_d1[2*i];  // Mux even bits
          end
        end
      end
    end

    always @(posedge ACLK) begin
      if (areset_d) begin
        laguna_m_handshake_i <= 1'b0;
        laguna_m_ready_d <= 1'b0;
      end else begin
        if (laguna_m_ready_d) begin
          laguna_m_handshake_i <= S_VALID;
        end
        laguna_m_ready_d <= laguna_m_ready;  // Half-cycle setup from dest_region.laguna_s_ready_i
      end
    end

    axi_register_slice_v2_1_22_tdm_sample tdm_sample_inst (
      .slow_clk     (ACLK),
      .fast_clk     (ACLK2X),
      .sample_cycle (sample_cycle)
    );
    
  end else begin : common

    localparam integer P_FANOUT = 256;
    localparam integer P_REPLICATION = (C_DATA_WIDTH>P_FANOUT) ? (C_DATA_WIDTH/P_FANOUT + 1) : 1;
    localparam integer P_PIPE_WIDTH = (C_PIPELINES>0) ? C_PIPELINES : 1;
    localparam integer P_FORWARD = 0;
    localparam integer P_RESPONSE = 1;
     
    (* keep="true" *)    reg aresetn_d = 1'b1;
    (* keep="true" *) reg areset_d = 1'b0;
    (* USER_SLL_REG="true", keep="true" *) reg laguna_m_reset_in_d = 1'b0;
    (* USER_SLL_REG="true", keep="true" *) reg laguna_m_reset_out_i = 1'b0;
                               reg [15:0] areset_dly = 16'b0;
    
    assign laguna_m_reset_out = laguna_m_reset_out_i;
    
    always @(posedge ACLK) begin
      laguna_m_reset_in_d <= laguna_m_reset_in;
      aresetn_d <= C_CHANNEL==P_FORWARD ? ARESETN : 1'b1;
      areset_dly <= {16{~aresetn_d}} | (areset_dly<<1);
      areset_d <= C_REG_CONFIG == 12 ? ~ARESETN : C_CHANNEL==P_FORWARD ? areset_dly[15]  : laguna_m_reset_in_d;
      laguna_m_reset_out_i <= areset_d;  // For resp channels, reflect laguna_m_reset_in_d to avoid tie-off laguna routing errors, but it doesn't get used.
    end
  
    wire ACLEAR;
    assign ACLEAR = C_REG_CONFIG == 12 ? 1'b0 : ~ARESETN;
  
    (* USER_SLL_REG="true", shreg_extract="no" *) reg [C_DATA_WIDTH-1:0] laguna_m_payload_i;
    wire m_handshake_d;
    (* USER_SLL_REG="true", keep="true" *)  reg laguna_m_ready_d = 1'b0;
    (* keep="true" *)  reg s_ready_i = 1'b0;
    (* keep="true" *)  reg [P_PIPE_WIDTH-1:0] ready_d = {P_PIPE_WIDTH{1'b0}};
    wire [(C_PIPELINES+1)*C_DATA_WIDTH-1:0] payload_i;
    wire [(C_PIPELINES+1)-1:0] handshake_i;
    genvar p;
    
    assign laguna_m_payload = laguna_m_payload_i;
    assign S_READY = s_ready_i;
        
    always @(posedge ACLK) begin
      laguna_m_ready_d <= laguna_m_ready; 
      ready_d <= {ready_d, laguna_m_ready_d}; 
      if (areset_d) begin
        s_ready_i <= 1'b0; 
      end else begin
        s_ready_i <= (C_PIPELINES==0) ? laguna_m_ready_d : ready_d[P_PIPE_WIDTH-1]; 
      end
    end
    
    for (p=0; p<=C_PIPELINES; p=p+1) begin : pipe
      (* shreg_extract="no" *) reg [C_DATA_WIDTH-1:0] payload_data;
      wire payload_valid_d;
      wire payload_valid_q;
      
      assign payload_i[p*C_DATA_WIDTH +: C_DATA_WIDTH] = payload_data;
      assign handshake_i[p] = payload_valid_q;
      assign payload_valid_d = (p==0) ? (S_VALID & s_ready_i) : handshake_i[((p>0)?(p-1):0)];
      
      always @(posedge ACLK) begin
        if (p==C_PIPELINES) begin
          laguna_m_payload_i <= C_PIPELINES==0 ? S_PAYLOAD_DATA : payload_i[(P_PIPE_WIDTH-1)*C_DATA_WIDTH +: C_DATA_WIDTH];
        end else if (p==0) begin
          payload_data <= S_PAYLOAD_DATA;
        end else begin
          payload_data <= payload_i[((p>0)?(p-1):0)*C_DATA_WIDTH +: C_DATA_WIDTH];
        end
      end
      
      FDCE #(
          .INIT(1'b0)
       ) payload_valid_asyncclear_inst (
          .Q   (payload_valid_q),
          .C   (ACLK), 
          .CE  (1'b1),
          .CLR (ACLEAR),
          .D   (payload_valid_d)
       );
    end  // loop p
    
    assign m_handshake_d = C_PIPELINES==0 ? (S_VALID & s_ready_i) : handshake_i[P_PIPE_WIDTH-1];
    
    (* USER_SLL_REG="true" *)
    FDCE #(
        .INIT(1'b0)
     ) laguna_m_handshake_asyncclear_inst (
        .Q   (laguna_m_handshake),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (ACLEAR),
        .D   (m_handshake_d)
     );
    
  end // gen_slr
  endgenerate
endmodule  // source_region_slr

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *)
module axi_register_slice_v2_1_22_dest_region_slr #
  (
   parameter C_FAMILY     = "virtex6",
   parameter integer C_REG_CONFIG = 12,
   parameter integer C_CHANNEL = 0,  // 0=Forward, 1=Response
   parameter integer C_DATA_WIDTH = 32,
   parameter integer C_SLR_WIDTH = 32,
   parameter integer C_PIPELINES = 0,
   parameter integer C_SOURCE_LATENCY = 1
      // Number of cycles to wait after laguna_s_ready output to enable shifting internal pipeline stages, to stay in sync with pipeline enables in source slr .
   )
  (
   // System Signals
   input wire ACLK,
   input wire ACLK2X,
   input wire ARESETN,

   // Slave side
   input  wire laguna_s_reset_in,
   output wire laguna_s_reset_out,
   input  wire [C_SLR_WIDTH-1:0] laguna_s_payload,
   input  wire laguna_s_handshake,
   output wire laguna_s_ready,

   // Master side
   output wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA,
   output wire M_VALID,
   input  wire M_READY
   );

  generate

  if (C_REG_CONFIG == 13) begin : tdm
    (* keep="true" *) reg areset_d = 1'b0;
    always @(posedge ACLK) begin
      areset_d <= ~ARESETN;
    end
    assign laguna_s_reset_out = 1'b0;
  
    localparam integer P_EVEN_WIDTH = C_DATA_WIDTH[0] ? (C_DATA_WIDTH+1) : C_DATA_WIDTH;
    
    (* shreg_extract = "no" *) reg [C_SLR_WIDTH-1:0]  laguna_s_payload_d;
    (* shreg_extract = "no" *) reg [C_SLR_WIDTH-1:0]  payload_tdm_d4;
    (* shreg_extract = "no" *) reg [C_DATA_WIDTH-1:0] fifo_out;
    (* shreg_extract = "no" *) reg [C_DATA_WIDTH-1:0] fifo_out_n1;
    (* shreg_extract = "no" *) reg laguna_s_handshake_d = 1'b0;
    (* keep="true" *)    reg laguna_s_ready_i = 1'b0;
    (* shreg_extract = "no" *) reg s_ready_d2 = 1'b0;
    reg [P_EVEN_WIDTH-1:0] payload_demux;
    reg m_valid_r = 1'b0;
    wire push;
    wire pop;
    reg [1:0] fifo_cnt = 2'h0;
    integer i;
    
    assign laguna_s_ready = laguna_s_ready_i;
    assign M_VALID = m_valid_r;
    assign M_PAYLOAD_DATA = fifo_out;  // Registered outputs
    assign pop = M_READY & m_valid_r;
    assign push = laguna_s_handshake_d & s_ready_d2;      

    always @(posedge ACLK) begin
      if (areset_d) begin
        laguna_s_handshake_d <= 1'b0;
      end else if (s_ready_d2) begin
        laguna_s_handshake_d <= laguna_s_handshake;
      end
    end

    always @(posedge ACLK2X) begin
      if (s_ready_d2) begin
        payload_tdm_d4 <= laguna_s_payload_d;
        laguna_s_payload_d <= laguna_s_payload;
      end
    end
    
    always @ * begin
      for (i=0;i<C_SLR_WIDTH;i=i+1) begin
        payload_demux[2*i+1] = payload_tdm_d4[i];       // Odd bits captured during second (low) phase of ACLK cycle 2
        payload_demux[2*i] = laguna_s_payload_d[i];  // Even bits captured during first (high) phase of ACLK cycle 3
          // Complete payload_demux signal is stable during second (low) phase of ACLK cycle 3 (gets clobbered after each ACLK active edge)
      end
    end

    always @(posedge ACLK) begin
      if (areset_d) begin
        fifo_cnt <= 2'h0;
        m_valid_r <=  1'b0;
        s_ready_d2 <= 1'b0;
      end else begin
        s_ready_d2 <= laguna_s_ready_i;  // Half-cycle setup from laguna_s_ready_i
        if (push & ~pop) begin
          fifo_cnt <= fifo_cnt + 2'h1;
          m_valid_r <=  1'b1;
        end else if (~push & pop) begin
          fifo_cnt <= fifo_cnt - 2'h1;
          m_valid_r <= fifo_cnt[1];  // fifo_cnt >= 2
        end
      end
    end

    always @(negedge ACLK) begin
      if (areset_d) begin
        laguna_s_ready_i <= 1'b0;
      end else begin
        laguna_s_ready_i <= M_READY | ~m_valid_r;  // Half-cycle setup
      end
    end

    always @(posedge ACLK) begin
      case (fifo_cnt)
        2'h0: begin  // EMPTY
          fifo_out <= payload_demux;
        end
        
        2'h1: begin
          fifo_out_n1 <= payload_demux;
          if (pop) begin
            fifo_out <= payload_demux;
          end
        end
        
        default: begin  // fifo_cnt == 2
          if (pop) begin
            fifo_out <= fifo_out_n1;
            fifo_out_n1 <= payload_demux;
          end
        end
      endcase
    end

  end else begin : common

    localparam integer P_PIPE_WIDTH = C_PIPELINES>0 ? C_PIPELINES : 1;
    localparam integer P_PIPE_LATENCY = ((C_SOURCE_LATENCY>0)?C_SOURCE_LATENCY:1) + C_PIPELINES;
    localparam integer P_FANOUT = 256;
    localparam integer P_REPLICATION = (C_DATA_WIDTH>P_FANOUT) ? (C_DATA_WIDTH/P_FANOUT + 1) : 1;
    localparam integer P_FORWARD = 0;
    localparam integer P_RESPONSE = 1;
     
    (* keep="true" *)    reg aresetn_d = 1'b1;
    (* keep="true" *) reg areset_d = 1'b0;
    (* USER_SLL_REG="true", keep="true" *) reg laguna_s_reset_in_d = 1'b0;
    (* USER_SLL_REG="true", keep="true" *) reg laguna_s_reset_out_i = 1'b0;
                               reg [15:0] areset_dly = 16'b0;
    
    assign laguna_s_reset_out = laguna_s_reset_out_i;
    
    always @(posedge ACLK) begin
      laguna_s_reset_in_d <= laguna_s_reset_in;
      aresetn_d <= C_CHANNEL==P_RESPONSE ? ARESETN : 1'b1;
      areset_dly <= {16{~aresetn_d}} | (areset_dly<<1);
      areset_d <= C_REG_CONFIG == 12 ? ~ARESETN : C_CHANNEL==P_FORWARD ? laguna_s_reset_in_d : areset_dly[15];
      laguna_s_reset_out_i <= areset_d;  // For forward channels, reflect laguna_s_reset_in_d to avoid tie-off laguna routing errors, but it doesn't get used.
    end

    wire ACLEAR;
    assign ACLEAR = C_REG_CONFIG == 12 ? 1'b0 : ~ARESETN;
  
    (* USER_SLL_REG="true", shreg_extract="no" *) reg [C_DATA_WIDTH-1:0] laguna_s_payload_d;
    wire laguna_s_handshake_q;
    (* USER_SLL_REG="true", keep="true" *)  reg laguna_s_ready_i = 1'b0;
    (* keep="true" *)  reg [P_PIPE_WIDTH-1:0] ready_d = {P_PIPE_WIDTH{1'b0}};
    wire [(C_PIPELINES+1)*C_DATA_WIDTH-1:0] payload_i;
    wire [(C_PIPELINES+1)-1:0] handshake_i;
    wire m_valid_i;
    wire push;
    wire pop;
    genvar p;
    
    assign laguna_s_ready = laguna_s_ready_i;
    assign pop = M_READY & m_valid_i;
    assign push = handshake_i[C_PIPELINES];      
    assign M_VALID = m_valid_i;

    always @(posedge ACLK) begin
      laguna_s_ready_i <= (C_PIPELINES==0) ? (M_READY | ~m_valid_i) : ready_d[P_PIPE_WIDTH-1];
      ready_d <= {ready_d, (M_READY | ~m_valid_i)}; 
    end
    
    for (p=0; p<=C_PIPELINES; p=p+1) begin : pipe
      (* shreg_extract="no" *) reg [C_DATA_WIDTH-1:0]  payload_data;
      wire payload_valid_d;
      wire payload_valid_q;
      
      assign payload_i[p*C_DATA_WIDTH +: C_DATA_WIDTH] = (p==0) ? laguna_s_payload_d : payload_data;
      assign handshake_i[p] = (p==0) ? laguna_s_handshake_q : payload_valid_q;
      assign payload_valid_d = handshake_i[((p>0)?(p-1):0)];
      
      always @(posedge ACLK) begin
        if (p==0) begin
          laguna_s_payload_d <= laguna_s_payload;
        end else begin
          payload_data <= payload_i[((p>0)?(p-1):0)*C_DATA_WIDTH +: C_DATA_WIDTH];
        end
      end
        
      FDCE #(
          .INIT(1'b0)
       ) payload_valid_asyncclear_inst (
          .Q   (payload_valid_q),
          .C   (ACLK), 
          .CE  (1'b1),
          .CLR (ACLEAR),
          .D   (payload_valid_d)
       );
    end  // loop p
    
    (* USER_SLL_REG="true" *)
    FDCE #(
        .INIT(1'b0)
     ) laguna_s_handshake_asyncclear_inst (
        .Q   (laguna_s_handshake_q),
        .C   (ACLK), 
        .CE  (1'b1),
        .CLR (ACLEAR),
        .D   (laguna_s_handshake)
     );
        
    axi_register_slice_v2_1_22_axic_reg_srl_fifo #
      (
       .C_FIFO_WIDTH (C_DATA_WIDTH), 
       .C_FIFO_SIZE  ((C_PIPELINES+C_SOURCE_LATENCY>14) ? 6 : (C_PIPELINES+C_SOURCE_LATENCY>6) ? 5 : 4)  
      )
      srl_fifo_0
      (
       .aclk    (ACLK),    
       .areset  (areset_d),  
       .aclear  (ACLEAR),
       .s_mesg  (payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH]),  
       .s_valid (push), 
       .m_mesg  (M_PAYLOAD_DATA),  
       .m_valid (m_valid_i), 
       .m_ready (pop)
      ); 
  
  end // gen_slr
  endgenerate
endmodule  // dest_region_slr

`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings="yes" *)
module axi_register_slice_v2_1_22_single_slr #
  (
   parameter C_FAMILY     = "virtex6",
   parameter integer C_DATA_WIDTH = 32,
   parameter integer C_PIPELINES = 0
   )
  (
   // System Signals
   input wire ACLK,
   input wire ARESETN,

   // Slave side
   input  wire [C_DATA_WIDTH-1:0] S_PAYLOAD_DATA,
   input  wire S_VALID,
   output wire S_READY,

   // Master side
   output wire [C_DATA_WIDTH-1:0] M_PAYLOAD_DATA,
   output wire M_VALID,
   input  wire M_READY
   );

  generate

  localparam integer P_PIPE_WIDTH = (C_PIPELINES>0) ? C_PIPELINES : 1;
  localparam integer P_FANOUT = 256;
  localparam integer P_REPLICATION = (C_DATA_WIDTH>P_FANOUT) ? (C_DATA_WIDTH/P_FANOUT + 1) : 1;
   
  reg areset_d = 1'b0;
  reg [3:0] areset_dly = 4'b0;
  always @(posedge ACLK) begin
    areset_dly <= {4{~ARESETN}} | (areset_dly<<1);
    areset_d <= areset_dly[3];
  end
  
  if (1) begin : common
    reg s_ready_i = 1'b0;
    (* keep="true" *)  reg [P_PIPE_WIDTH-1:0] ready_d = {P_PIPE_WIDTH{1'b0}};
    wire [(C_PIPELINES+1)*C_DATA_WIDTH-1:0] payload_i;
    wire [(C_PIPELINES+1)-1:0] handshake_i;
    wire m_valid_i;
    wire push;
    wire pop;
    genvar p;
    
    assign pop = M_READY & m_valid_i;
    assign push = handshake_i[C_PIPELINES];      
    assign M_VALID = m_valid_i;
    assign S_READY = s_ready_i;
        
    always @(posedge ACLK) begin
      ready_d <= {ready_d, (M_READY | ~m_valid_i)}; 
      if (areset_d) begin
        s_ready_i <= 1'b0; 
      end else begin
        s_ready_i <= (C_PIPELINES==0) ? (M_READY | ~m_valid_i) : ready_d[P_PIPE_WIDTH-1]; 
      end
    end
    
    assign payload_i[0 +: C_DATA_WIDTH] = S_PAYLOAD_DATA;
    assign handshake_i[0] = S_VALID & s_ready_i;
    
    for (p=1; p<=C_PIPELINES; p=p+1) begin : pipe
      (* shreg_extract="no" *) reg [C_DATA_WIDTH-1:0]  payload_data;
      (* keep="true" *)  reg payload_valid = 1'b0;
      
      assign payload_i[p*C_DATA_WIDTH +: C_DATA_WIDTH] = payload_data;
      assign handshake_i[p] = payload_valid;
      
      always @(posedge ACLK) begin
        if (p==1) begin
          payload_data <= S_PAYLOAD_DATA;
          payload_valid <= S_VALID & s_ready_i & ~areset_d;
        end else begin
          payload_data <= payload_i[((p>0)?(p-1):0)*C_DATA_WIDTH +: C_DATA_WIDTH];
          payload_valid <= handshake_i[((p>0)?(p-1):0)];
        end
      end
    end
    
    if (C_PIPELINES==0) begin : ff_fifo

      (* shreg_extract = "no" *) reg [C_DATA_WIDTH-1:0] fifo_out;
      (* shreg_extract = "no" *) reg [C_DATA_WIDTH-1:0] fifo_out_n1;
      (* shreg_extract = "no" *) reg [C_DATA_WIDTH-1:0] fifo_out_n2;
      reg [1:0] fifo_cnt = 2'h0;
      reg m_valid_r = 1'b0;
      
      assign M_PAYLOAD_DATA = fifo_out; 
      assign m_valid_i = m_valid_r;
      
      always @(posedge ACLK) begin
        if (areset_d) begin
          fifo_cnt <= 2'h0;
          m_valid_r <=  1'b0;
        end else begin
          if (push & ~pop) begin
            fifo_cnt <= fifo_cnt + 2'h1;
            m_valid_r <=  1'b1;
          end else if (~push & pop) begin
            fifo_cnt <= fifo_cnt - 2'h1;
            m_valid_r <= fifo_cnt[1];  // fifo_cnt >= 2
          end
        end
      end

      always @(posedge ACLK) begin
        case (fifo_cnt)
          2'h0: begin  // EMPTY
            fifo_out <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
          end
          
          2'h1: begin
            fifo_out_n1 <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
            if (pop) begin
              fifo_out <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
            end
          end
          
          2'h2: begin
            fifo_out_n2 <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
            if (pop) begin
              fifo_out <= fifo_out_n1;
              fifo_out_n1 <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
            end
          end
          
          default: begin  // fifo_cnt == 3
            if (pop) begin
              fifo_out <= fifo_out_n1;
              fifo_out_n1 <= fifo_out_n2;
              fifo_out_n2 <= payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH];
            end
          end
        endcase
      end
    
    end else begin : srl_fifo
    
      axi_register_slice_v2_1_22_axic_reg_srl_fifo #
        (
         .C_FIFO_WIDTH (C_DATA_WIDTH), 
         .C_FIFO_SIZE  ((C_PIPELINES>12) ? 5 : 4)  
        )
        srl_fifo_0
        (
         .aclk    (ACLK),    
         .areset  (areset_d),
         .aclear  (1'b0),  
         .s_mesg  (payload_i[C_PIPELINES*C_DATA_WIDTH +: C_DATA_WIDTH]),  
         .s_valid (push), 
         .m_mesg  (M_PAYLOAD_DATA),  
         .m_valid (m_valid_i), 
         .m_ready (pop)
        );

    end // gen_fifo
  end // gen_slr
  endgenerate
endmodule  // single_slr

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_axic_reg_srl_fifo #
  // FIFO with no s_ready back-pressure; must guarantee parent will never push beyond full
  (
   parameter integer C_FIFO_WIDTH  = 1,      // Width of s_mesg/m_mesg.
   parameter integer C_FIFO_SIZE = 5        // Depth of FIFO is 2**C_FIFO_SIZE.  
   )
  (
   input  wire                        aclk,    // Clock
   input  wire                        areset,  // Reset
   input  wire                        aclear,  // Async clear
   input  wire [C_FIFO_WIDTH-1:0]     s_mesg,  // Input data
   input  wire                        s_valid, // Input data valid
   output wire [C_FIFO_WIDTH-1:0]     m_mesg,  // Output data
   output wire                        m_valid, // Output data valid
   input  wire                        m_ready  // Output data ready
   );
  
  genvar i;

  generate
  
    localparam integer P_FIFO_DEPTH            = 2**C_FIFO_SIZE;
    localparam [C_FIFO_SIZE-1:0] P_EMPTY       = {C_FIFO_SIZE{1'b1}};
    localparam [C_FIFO_SIZE-1:0] P_ALMOSTEMPTY = {C_FIFO_SIZE{1'b0}};
    
    localparam M_VALID_0   = 1'b0;
    localparam M_VALID_1   = 1'b1;
    localparam SRL_VALID_0 = 1'b0;
    localparam SRL_VALID_1 = 1'b1;
    localparam S_VALID_0   = 1'b0;
    localparam S_VALID_1   = 1'b1;
    localparam M_READY_0   = 1'b0;
    localparam M_READY_1   = 1'b1;
    
    localparam [1:0] K_EMPTY   = {SRL_VALID_0, M_VALID_0};
    localparam [1:0] K_HAS1    = {SRL_VALID_0, M_VALID_1};
    localparam [1:0] K_MIN2    = {SRL_VALID_1, M_VALID_1};

    reg  push;       // SRL push
    reg  pop;        // SRL pop
    wire [C_FIFO_WIDTH-1:0] srl_reg;
    reg [C_FIFO_SIZE-1:0]  fifoaddr = P_EMPTY;
    
    wire [1:0] state;  // State vector register
    reg  [1:0] next;           // Next state value
    wire [1:0] next_qual;           // Next state value
    
    reg  load_mesg;  // Load output register
    reg  srl2mesg;   // Output reg loads from SRL (else from s_mesg)
    reg  [C_FIFO_WIDTH-1:0] mesg_reg;  // No initial state
    reg  m_valid_d;
    wire m_valid_q;
    
    assign m_valid = m_valid_q;
    assign next_qual = areset ? K_EMPTY : next;
    assign m_mesg  = mesg_reg;

    FDCE #(
        .INIT(1'b0)
     ) asyncclear_mvalid_inst (
        .Q   (m_valid_q),
        .C   (aclk), 
        .CE  (1'b1),
        .CLR (aclear),
        .D   (m_valid_d)
     );

    FDCE #(
        .INIT(1'b0)
     ) asyncclear_state0_inst (
        .Q   (state[0]),
        .C   (aclk), 
        .CE  (1'b1),
        .CLR (aclear),
        .D   (next_qual[0])
     );

    FDCE #(
        .INIT(1'b0)
     ) asyncclear_state1_inst (
        .Q   (state[1]),
        .C   (aclk), 
        .CE  (1'b1),
        .CLR (aclear),
        .D   (next_qual[1])
     );

    always @ * begin
      next = state;  // Default: hold state unless re-assigned
      m_valid_d = m_valid_q & ~areset;
      load_mesg = 1'b1;
      srl2mesg = 1'b0;
      push = 1'b0;
      pop = 1'b0;
      case (state)
        K_EMPTY: begin  // FIFO Empty; pre-assert s_ready
          load_mesg = s_valid;
          srl2mesg = 1'b0;
          push = 1'b0;
          pop = 1'b0;
          if (s_valid & ~areset) begin
            next = K_HAS1;
            m_valid_d = 1'b0;
          end
        end  // EMPTY
        
        K_HAS1: begin  // FIFO contains 1 item in the output register (SRL empty)
          srl2mesg = 1'b0;
          pop = 1'b0;
          casex ({s_valid,m_ready})
            {S_VALID_1,M_READY_0}: begin  // Receive a 2nd item, push into SRL
              next = K_MIN2;
              load_mesg = 1'b0;
              push = 1'b1;
              m_valid_d = 1'b1;
            end
            
            {S_VALID_0,M_READY_1}: begin  // Pop to empty
              next = K_EMPTY;
              load_mesg = 1'b1;  // Inconsequential
              push = 1'b0;
              m_valid_d = 1'b0;
            end
            
            {S_VALID_1,M_READY_1}: begin  // Push a new item while popping; replace contents of output reg
              next = K_HAS1;
              load_mesg = 1'b1;
              push = 1'b0;
              m_valid_d = 1'b1;
            end
            
            default: begin  // s_valid=0, m_ready=0: hold state
              next = K_HAS1;
              load_mesg = 1'b0;
              push = 1'b0;
              m_valid_d = 1'b1;
            end
          endcase
        end  // HAS1
        
        K_MIN2: begin  // FIFO contains >1 item, some in SRL
          srl2mesg = 1'b1;
          m_valid_d = 1'b1;
          casex ({s_valid,m_ready})
            {S_VALID_1,M_READY_0}: begin  // Receive a new item, push into SRL
              next = K_MIN2;
              load_mesg = 1'b0;
              push = 1'b1;
              pop = 1'b0;
            end
            
            {S_VALID_0,M_READY_1}: begin  // Pop SRL to replace output reg
              next = (fifoaddr == P_ALMOSTEMPTY) ? K_HAS1 : K_MIN2;
              load_mesg = 1'b1;
              push = 1'b0;
              pop = 1'b1;
            end
            
            {S_VALID_1,M_READY_1}: begin  // Push a new item while popping
              next = K_MIN2;
              load_mesg = 1'b1;
              push = 1'b1;
              pop = 1'b1;
            end
            
            default: begin  // s_valid=0, m_ready=0: hold state
              next = K_MIN2;
              load_mesg = 1'b0;
              push = 1'b0;
              pop = 1'b0;
            end
          endcase
        end  // MIN2
        
        default: begin  // Same as RESET
          next = K_EMPTY;
        end  // default
      endcase
    end
    
    always @(posedge aclk) begin  // Payload reg needs no reset
      if (load_mesg) begin
        mesg_reg <= srl2mesg ? srl_reg : s_mesg;
      end
    end
        
    // SRL FIFO address pointer
    always @(posedge aclk) begin
      if (areset) begin
        fifoaddr <= P_EMPTY;
      end else begin
        if (push & ~pop) begin
          fifoaddr <= fifoaddr + 1;
        end else if (~push & pop) begin
          fifoaddr <= fifoaddr - 1;
        end
      end
    end
        
    //---------------------------------------------------------------------------
    // Instantiate SRLs
    //---------------------------------------------------------------------------
    for (i=0;i<C_FIFO_WIDTH;i=i+1) begin : srl
      (* keep_hierarchy = "yes" *) axi_register_slice_v2_1_22_srl_rtl #
        (
         .C_A_WIDTH (C_FIFO_SIZE)
        )
        srl_nx1
        (
         .clk (aclk),
         .a   (fifoaddr),
         .ce  (s_valid),
         .d   (s_mesg[i]),
         .q   (srl_reg[i])
        );
    end      
  endgenerate
  
endmodule  // axic_reg_srl_fifo


//  (c) Copyright 2010-2017 Xilinx, Inc. All rights reserved.
//
//  This file contains confidential and proprietary information
//  of Xilinx, Inc. and is protected under U.S. and
//  international copyright and other intellectual property
//  laws.
//
//  DISCLAIMER
//  This disclaimer is not a license and does not grant any
//  rights to the materials distributed herewith. Except as
//  otherwise provided in a valid license issued to you by
//  Xilinx, and to the maximum extent permitted by applicable
//  law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
//  WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
//  AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
//  BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
//  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
//  (2) Xilinx shall not be liable (whether in contract or tort,
//  including negligence, or under any other theory of
//  liability) for any loss or damage of any kind or nature
//  related to, arising under or in connection with these
//  materials, including for any direct, or any indirect,
//  special, incidental, or consequential loss or damage
//  (including loss of data, profits, goodwill, or any type of
//  loss or damage suffered as a result of any action brought
//  by a third party) even if such damage or loss was
//  reasonably foreseeable or Xilinx had been advised of the
//  possibility of the same.
//
//  CRITICAL APPLICATIONS
//  Xilinx products are not designed or intended to be fail-
//  safe, or for use in any application requiring fail-safe
//  performance, such as life-support or safety devices or
//  systems, Class III medical devices, nuclear facilities,
//  applications related to the deployment of airbags, or any
//  other applications that could lead to death, personal
//  injury, or severe property or environmental damage
//  (individually and collectively, "Critical
//  Applications"). Customer assumes the sole risk and
//  liability of any use of Xilinx products in Critical
//  Applications, subject only to applicable laws and
//  regulations governing limitations on product liability.
//
//  THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
//  PART OF THIS FILE AT ALL TIMES. 
//-----------------------------------------------------------------------------
//
// AXI Register Slice
//   Register selected channels on the forward and/or reverse signal paths.
//   5-channel memory-mapped AXI4 interfaces.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   axi_register_slice
//      axic_register_slice
//
//--------------------------------------------------------------------------

`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module axi_register_slice_v2_1_22_axi_register_slice #
  (
   parameter C_FAMILY                            = "virtex6",
   parameter C_AXI_PROTOCOL                      = 0,
   parameter integer C_AXI_ID_WIDTH              = 1,
   parameter integer C_AXI_ADDR_WIDTH            = 32,
   parameter integer C_AXI_DATA_WIDTH            = 32,
   parameter integer C_AXI_SUPPORTS_USER_SIGNALS = 0,
   parameter integer C_AXI_AWUSER_WIDTH          = 1,
   parameter integer C_AXI_ARUSER_WIDTH          = 1,
   parameter integer C_AXI_WUSER_WIDTH           = 1,
   parameter integer C_AXI_RUSER_WIDTH           = 1,
   parameter integer C_AXI_BUSER_WIDTH           = 1,
   // C_REG_CONFIG_*:
   //   0 => BYPASS    = The channel is just wired through the module.
   //   1 => FWD_REV   = Both FWD and REV (fully-registered)
   //   2 => FWD       = The master VALID and payload signals are registrated. 
   //   3 => REV       = The slave ready signal is registrated
   //   4 => SLAVE_FWD = All slave side signals and master VALID and payload are registrated.
   //   5 => SLAVE_RDY = All slave side signals and master READY are registrated.
   //   6 => INPUTS    = Slave and Master side inputs are registrated.
   //   7 => LIGHT_WT  = 1-stage pipeline register with bubble cycle, both FWD and REV pipelining
   //   9 => SI/MI_REG = Source side completely registered (including S_VALID input)
   //   12 => SLR Crossing (source->dest flops, full-width payload, single clock)
   //   13 => TDM SLR Crossing (source->dest flops, half-width payload, dual clock)
   //   15 => Variable SLR Crossings (single clock)
   //   16 -> Auto-pipelining
   parameter integer C_REG_CONFIG_AW = 7,
   parameter integer C_REG_CONFIG_W  = 1,
   parameter integer C_REG_CONFIG_B  = 7,
   parameter integer C_REG_CONFIG_AR = 7,
   parameter integer C_REG_CONFIG_R  = 1,
   parameter integer C_RESERVE_MODE = 0,
   parameter integer C_NUM_SLR_CROSSINGS = 0,
   parameter integer C_PIPELINES_MASTER_AW = 0,
   parameter integer C_PIPELINES_MASTER_W  = 0,
   parameter integer C_PIPELINES_MASTER_B  = 0,
   parameter integer C_PIPELINES_MASTER_AR = 0,
   parameter integer C_PIPELINES_MASTER_R  = 0,
   parameter integer C_PIPELINES_SLAVE_AW = 0,
   parameter integer C_PIPELINES_SLAVE_W  = 0,
   parameter integer C_PIPELINES_SLAVE_B  = 0,
   parameter integer C_PIPELINES_SLAVE_AR = 0,
   parameter integer C_PIPELINES_SLAVE_R  = 0,
   parameter integer C_PIPELINES_MIDDLE_AW = 0,
   parameter integer C_PIPELINES_MIDDLE_W  = 0,
   parameter integer C_PIPELINES_MIDDLE_B  = 0,
   parameter integer C_PIPELINES_MIDDLE_AR = 0,
   parameter integer C_PIPELINES_MIDDLE_R  = 0
   )   
  (
   // System Signals
   input wire aclk,
   input wire aclk2x,
   input wire aresetn,

   // Slave Interface Write Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     s_axi_awid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]  s_axi_awlen,
   input  wire [3-1:0]                  s_axi_awsize,
   input  wire [2-1:0]                  s_axi_awburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]  s_axi_awlock,
   input  wire [4-1:0]                  s_axi_awcache,
   input  wire [3-1:0]                  s_axi_awprot,
   input  wire [4-1:0]                  s_axi_awregion,
   input  wire [4-1:0]                  s_axi_awqos,
   input  wire [C_AXI_AWUSER_WIDTH-1:0] s_axi_awuser,
   input  wire                          s_axi_awvalid,
   output wire                          s_axi_awready,

   // Slave Interface Write Data Ports
   input wire [C_AXI_ID_WIDTH-1:0]      s_axi_wid,
   input  wire [C_AXI_DATA_WIDTH-1:0]   s_axi_wdata,
   input  wire [C_AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
   input  wire                          s_axi_wlast,
   input  wire [C_AXI_WUSER_WIDTH-1:0]  s_axi_wuser,
   input  wire                          s_axi_wvalid,
   output wire                          s_axi_wready,

   // Slave Interface Write Response Ports
   output wire [C_AXI_ID_WIDTH-1:0]    s_axi_bid,
   output wire [2-1:0]                 s_axi_bresp,
   output wire [C_AXI_BUSER_WIDTH-1:0] s_axi_buser,
   output wire                         s_axi_bvalid,
   input  wire                         s_axi_bready,

   // Slave Interface Read Address Ports
   input  wire [C_AXI_ID_WIDTH-1:0]     s_axi_arid,
   input  wire [C_AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
   input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]  s_axi_arlen,
   input  wire [3-1:0]                  s_axi_arsize,
   input  wire [2-1:0]                  s_axi_arburst,
   input  wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]  s_axi_arlock,
   input  wire [4-1:0]                  s_axi_arcache,
   input  wire [3-1:0]                  s_axi_arprot,
   input  wire [4-1:0]                  s_axi_arregion,
   input  wire [4-1:0]                  s_axi_arqos,
   input  wire [C_AXI_ARUSER_WIDTH-1:0] s_axi_aruser,
   input  wire                          s_axi_arvalid,
   output wire                          s_axi_arready,

   // Slave Interface Read Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]    s_axi_rid,
   output wire [C_AXI_DATA_WIDTH-1:0]  s_axi_rdata,
   output wire [2-1:0]                 s_axi_rresp,
   output wire                         s_axi_rlast,
   output wire [C_AXI_RUSER_WIDTH-1:0] s_axi_ruser,
   output wire                         s_axi_rvalid,
   input  wire                         s_axi_rready,
   
   // Master Interface Write Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_awid,
   output wire [C_AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]  m_axi_awlen,
   output wire [3-1:0]                  m_axi_awsize,
   output wire [2-1:0]                  m_axi_awburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]  m_axi_awlock,
   output wire [4-1:0]                  m_axi_awcache,
   output wire [3-1:0]                  m_axi_awprot,
   output wire [4-1:0]                  m_axi_awregion,
   output wire [4-1:0]                  m_axi_awqos,
   output wire [C_AXI_AWUSER_WIDTH-1:0] m_axi_awuser,
   output wire                          m_axi_awvalid,
   input  wire                          m_axi_awready,
   
   // Master Interface Write Data Ports
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_wid,
   output wire [C_AXI_DATA_WIDTH-1:0]   m_axi_wdata,
   output wire [C_AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
   output wire                          m_axi_wlast,
   output wire [C_AXI_WUSER_WIDTH-1:0]  m_axi_wuser,
   output wire                          m_axi_wvalid,
   input  wire                          m_axi_wready,
   
   // Master Interface Write Response Ports
   input  wire [C_AXI_ID_WIDTH-1:0]    m_axi_bid,
   input  wire [2-1:0]                 m_axi_bresp,
   input  wire [C_AXI_BUSER_WIDTH-1:0] m_axi_buser,
   input  wire                         m_axi_bvalid,
   output wire                         m_axi_bready,
   
   // Master Interface Read Address Port
   output wire [C_AXI_ID_WIDTH-1:0]     m_axi_arid,
   output wire [C_AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
   output wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0]  m_axi_arlen,
   output wire [3-1:0]                  m_axi_arsize,
   output wire [2-1:0]                  m_axi_arburst,
   output wire [((C_AXI_PROTOCOL == 1) ? 2 : 1)-1:0]  m_axi_arlock,
   output wire [4-1:0]                  m_axi_arcache,
   output wire [3-1:0]                  m_axi_arprot,
   output wire [4-1:0]                  m_axi_arregion,
   output wire [4-1:0]                  m_axi_arqos,
   output wire [C_AXI_ARUSER_WIDTH-1:0] m_axi_aruser,
   output wire                          m_axi_arvalid,
   input  wire                          m_axi_arready,
   
   // Master Interface Read Data Ports
   input  wire [C_AXI_ID_WIDTH-1:0]    m_axi_rid,
   input  wire [C_AXI_DATA_WIDTH-1:0]  m_axi_rdata,
   input  wire [2-1:0]                 m_axi_rresp,
   input  wire                         m_axi_rlast,
   input  wire [C_AXI_RUSER_WIDTH-1:0] m_axi_ruser,
   input  wire                         m_axi_rvalid,
   output wire                         m_axi_rready
  );

  wire reset;

  localparam integer C_AXI_SUPPORTS_REGION_SIGNALS = (C_AXI_PROTOCOL == 0) ? 1 : 0;
  localparam integer P_FORWARD = 0;
  localparam integer P_RESPONSE = 1;
  `include "axi_infrastructure_v1_1_0.vh"

  wire [G_AXI_AWPAYLOAD_WIDTH-1:0] s_awpayload;
  wire [G_AXI_AWPAYLOAD_WIDTH-1:0] m_awpayload;
  wire [G_AXI_WPAYLOAD_WIDTH-1:0] s_wpayload;
  wire [G_AXI_WPAYLOAD_WIDTH-1:0] m_wpayload;
  wire [G_AXI_BPAYLOAD_WIDTH-1:0] s_bpayload;
  wire [G_AXI_BPAYLOAD_WIDTH-1:0] m_bpayload;
  wire [G_AXI_ARPAYLOAD_WIDTH-1:0] s_arpayload;
  wire [G_AXI_ARPAYLOAD_WIDTH-1:0] m_arpayload;
  wire [G_AXI_RPAYLOAD_WIDTH-1:0] s_rpayload;
  wire [G_AXI_RPAYLOAD_WIDTH-1:0] m_rpayload;

  assign reset = ~aresetn;
  
  generate
  
  if (C_RESERVE_MODE==1) begin : gen_reserve_si
  
    axi_register_slice_v2_1_22_test_slave #(
      .C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
      .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
      .C_AXI_PROTOCOL(C_AXI_PROTOCOL),
      .C_AXI_AWUSER_WIDTH(C_AXI_AWUSER_WIDTH),
      .C_AXI_ARUSER_WIDTH(C_AXI_ARUSER_WIDTH),
      .C_AXI_WUSER_WIDTH(C_AXI_WUSER_WIDTH),
      .C_AXI_RUSER_WIDTH(C_AXI_RUSER_WIDTH),
      .C_AXI_BUSER_WIDTH(C_AXI_BUSER_WIDTH)
    ) inst (
      .s_axi_awaddr(s_axi_awaddr),
      .s_axi_awprot(s_axi_awprot),
      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awready(s_axi_awready),
      .s_axi_awsize(s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awcache(s_axi_awcache),
      .s_axi_awlen(s_axi_awlen),
      .s_axi_awlock(s_axi_awlock),
      .s_axi_awqos(s_axi_awqos),
      .s_axi_awregion(s_axi_awregion),
      .s_axi_awid(s_axi_awid),
      .s_axi_awuser(s_axi_awuser),
      .s_axi_wdata(s_axi_wdata),
      .s_axi_wstrb(s_axi_wstrb),
      .s_axi_wvalid(s_axi_wvalid),
      .s_axi_wready(s_axi_wready),
      .s_axi_wlast(s_axi_wlast),
      .s_axi_wid(s_axi_wid),
      .s_axi_wuser(s_axi_wuser),
      .s_axi_bresp(s_axi_bresp),
      .s_axi_bvalid(s_axi_bvalid),
      .s_axi_bready(s_axi_bready),
      .s_axi_buser(s_axi_buser),
      .s_axi_bid(s_axi_bid),
      .s_axi_araddr(s_axi_araddr),
      .s_axi_arprot(s_axi_arprot),
      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arready(s_axi_arready),
      .s_axi_arsize(s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arcache(s_axi_arcache),
      .s_axi_arlock(s_axi_arlock),
      .s_axi_arlen(s_axi_arlen),
      .s_axi_arqos(s_axi_arqos),
      .s_axi_arregion(s_axi_arregion),
      .s_axi_aruser(s_axi_aruser),
      .s_axi_arid(s_axi_arid),
      .s_axi_rdata(s_axi_rdata),
      .s_axi_rresp(s_axi_rresp),
      .s_axi_rvalid(s_axi_rvalid),
      .s_axi_rready(s_axi_rready),
      .s_axi_rlast(s_axi_rlast),
      .s_axi_ruser(s_axi_ruser),
      .s_axi_rid(s_axi_rid),
      .aclk(aclk),
      .aresetn(aresetn)
    );
    
     assign m_axi_awid     = 0;
     assign m_axi_awaddr   = 0;
     assign m_axi_awlen    = 0;
     assign m_axi_awsize   = 0;
     assign m_axi_awburst  = 0;
     assign m_axi_awlock   = 0;
     assign m_axi_awcache  = 0;
     assign m_axi_awprot   = 0;
     assign m_axi_awregion = 0;
     assign m_axi_awqos    = 0;
     assign m_axi_awuser   = 0;
     assign m_axi_awvalid  = 0;
     assign m_axi_wid      = 0;
     assign m_axi_wdata    = 0;
     assign m_axi_wstrb    = 0;
     assign m_axi_wlast    = 0;
     assign m_axi_wuser    = 0;
     assign m_axi_wvalid   = 0;
     assign m_axi_bready   = 0;
     assign m_axi_arid     = 0;
     assign m_axi_araddr   = 0;
     assign m_axi_arlen    = 0;
     assign m_axi_arsize   = 0;
     assign m_axi_arburst  = 0;
     assign m_axi_arlock   = 0;
     assign m_axi_arcache  = 0;
     assign m_axi_arprot   = 0;
     assign m_axi_arregion = 0;
     assign m_axi_arqos    = 0;
     assign m_axi_aruser   = 0;
     assign m_axi_arvalid  = 0;
     assign m_axi_rready   = 0;
      
  end else if (C_RESERVE_MODE==2) begin : gen_reserve_mi
    
    axi_register_slice_v2_1_22_test_master #(
    .C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
    .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
    .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
    .C_AXI_PROTOCOL(C_AXI_PROTOCOL),
    .C_AXI_AWUSER_WIDTH(C_AXI_AWUSER_WIDTH),
    .C_AXI_ARUSER_WIDTH(C_AXI_ARUSER_WIDTH),
    .C_AXI_WUSER_WIDTH(C_AXI_WUSER_WIDTH),
    .C_AXI_RUSER_WIDTH(C_AXI_RUSER_WIDTH),
    .C_AXI_BUSER_WIDTH(C_AXI_BUSER_WIDTH)
    ) inst (
      .m_axi_awaddr(m_axi_awaddr),
      .m_axi_awprot(m_axi_awprot),
      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awready(m_axi_awready),
      .m_axi_awsize(m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awcache(m_axi_awcache),
      .m_axi_awlen(m_axi_awlen),
      .m_axi_awlock(m_axi_awlock),
      .m_axi_awqos(m_axi_awqos),
      .m_axi_awid(m_axi_awid),
      .m_axi_awuser(m_axi_awuser),
      .m_axi_wid(m_axi_wid),
      .m_axi_wdata(m_axi_wdata),
      .m_axi_wstrb(m_axi_wstrb),
      .m_axi_wvalid(m_axi_wvalid),
      .m_axi_wready(m_axi_wready),
      .m_axi_wlast(m_axi_wlast),
      .m_axi_wuser(m_axi_wuser),
      .m_axi_bresp(m_axi_bresp),
      .m_axi_bvalid(m_axi_bvalid),
      .m_axi_bready(m_axi_bready),
      .m_axi_buser(m_axi_buser),
      .m_axi_bid(m_axi_bid),
      .m_axi_araddr(m_axi_araddr),
      .m_axi_arprot(m_axi_arprot),
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arready(m_axi_arready),
      .m_axi_arsize(m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arcache(m_axi_arcache),
      .m_axi_arlen(m_axi_arlen),
      .m_axi_arlock(m_axi_arlock),
      .m_axi_arqos(m_axi_arqos),
      .m_axi_arid(m_axi_arid),
      .m_axi_aruser(m_axi_aruser),
      .m_axi_rdata(m_axi_rdata),
      .m_axi_rresp(m_axi_rresp),
      .m_axi_rvalid(m_axi_rvalid),
      .m_axi_rready(m_axi_rready),
      .m_axi_rlast(m_axi_rlast),
      .m_axi_ruser(m_axi_ruser),
      .m_axi_rid(m_axi_rid),
      .aclk(aclk),
      .aresetn(aresetn)
    );
    
     assign s_axi_awready = 0;
     assign s_axi_wready  = 0;
     assign s_axi_bid     = 0;
     assign s_axi_bresp   = 0;
     assign s_axi_buser   = 0;
     assign s_axi_bvalid  = 0;
     assign s_axi_arready = 0;
     assign s_axi_rid     = 0;
     assign s_axi_rdata   = 0;
     assign s_axi_rresp   = 0;
     assign s_axi_rlast   = 0;
     assign s_axi_ruser   = 0;
     assign s_axi_rvalid  = 0;

  end else begin : gen_reg_slice  // Any normal reg-slice mode

    axi_infrastructure_v1_1_0_axi2vector #( 
      .C_AXI_PROTOCOL                ( C_AXI_PROTOCOL                ) ,
      .C_AXI_ID_WIDTH                ( C_AXI_ID_WIDTH                ) ,
      .C_AXI_ADDR_WIDTH              ( C_AXI_ADDR_WIDTH              ) ,
      .C_AXI_DATA_WIDTH              ( C_AXI_DATA_WIDTH              ) ,
      .C_AXI_SUPPORTS_USER_SIGNALS   ( C_AXI_SUPPORTS_USER_SIGNALS   ) ,
      .C_AXI_SUPPORTS_REGION_SIGNALS ( C_AXI_SUPPORTS_REGION_SIGNALS ) ,
      .C_AXI_AWUSER_WIDTH            ( C_AXI_AWUSER_WIDTH            ) ,
      .C_AXI_ARUSER_WIDTH            ( C_AXI_ARUSER_WIDTH            ) ,
      .C_AXI_WUSER_WIDTH             ( C_AXI_WUSER_WIDTH             ) ,
      .C_AXI_RUSER_WIDTH             ( C_AXI_RUSER_WIDTH             ) ,
      .C_AXI_BUSER_WIDTH             ( C_AXI_BUSER_WIDTH             ) ,
      .C_AWPAYLOAD_WIDTH             ( G_AXI_AWPAYLOAD_WIDTH         ) ,
      .C_WPAYLOAD_WIDTH              ( G_AXI_WPAYLOAD_WIDTH          ) ,
      .C_BPAYLOAD_WIDTH              ( G_AXI_BPAYLOAD_WIDTH          ) ,
      .C_ARPAYLOAD_WIDTH             ( G_AXI_ARPAYLOAD_WIDTH         ) ,
      .C_RPAYLOAD_WIDTH              ( G_AXI_RPAYLOAD_WIDTH          ) 
    )
    axi2vector_0 ( 
      .s_axi_awid      ( s_axi_awid      ) ,
      .s_axi_awaddr    ( s_axi_awaddr    ) ,
      .s_axi_awlen     ( s_axi_awlen     ) ,
      .s_axi_awsize    ( s_axi_awsize    ) ,
      .s_axi_awburst   ( s_axi_awburst   ) ,
      .s_axi_awlock    ( s_axi_awlock    ) ,
      .s_axi_awcache   ( s_axi_awcache   ) ,
      .s_axi_awprot    ( s_axi_awprot    ) ,
      .s_axi_awqos     ( s_axi_awqos     ) ,
      .s_axi_awuser    ( s_axi_awuser    ) ,
      .s_axi_awregion  ( s_axi_awregion  ) ,
      .s_axi_wid       ( s_axi_wid       ) ,
      .s_axi_wdata     ( s_axi_wdata     ) ,
      .s_axi_wstrb     ( s_axi_wstrb     ) ,
      .s_axi_wlast     ( s_axi_wlast     ) ,
      .s_axi_wuser     ( s_axi_wuser     ) ,
      .s_axi_bid       ( s_axi_bid       ) ,
      .s_axi_bresp     ( s_axi_bresp     ) ,
      .s_axi_buser     ( s_axi_buser     ) ,
      .s_axi_arid      ( s_axi_arid      ) ,
      .s_axi_araddr    ( s_axi_araddr    ) ,
      .s_axi_arlen     ( s_axi_arlen     ) ,
      .s_axi_arsize    ( s_axi_arsize    ) ,
      .s_axi_arburst   ( s_axi_arburst   ) ,
      .s_axi_arlock    ( s_axi_arlock    ) ,
      .s_axi_arcache   ( s_axi_arcache   ) ,
      .s_axi_arprot    ( s_axi_arprot    ) ,
      .s_axi_arqos     ( s_axi_arqos     ) ,
      .s_axi_aruser    ( s_axi_aruser    ) ,
      .s_axi_arregion  ( s_axi_arregion  ) ,
      .s_axi_rid       ( s_axi_rid       ) ,
      .s_axi_rdata     ( s_axi_rdata     ) ,
      .s_axi_rresp     ( s_axi_rresp     ) ,
      .s_axi_rlast     ( s_axi_rlast     ) ,
      .s_axi_ruser     ( s_axi_ruser     ) ,
      .s_awpayload ( s_awpayload ) ,
      .s_wpayload  ( s_wpayload  ) ,
      .s_bpayload  ( s_bpayload  ) ,
      .s_arpayload ( s_arpayload ) ,
      .s_rpayload  ( s_rpayload  ) 
    );
    
    axi_infrastructure_v1_1_0_vector2axi #( 
      .C_AXI_PROTOCOL                ( C_AXI_PROTOCOL                ) ,
      .C_AXI_ID_WIDTH                ( C_AXI_ID_WIDTH                ) ,
      .C_AXI_ADDR_WIDTH              ( C_AXI_ADDR_WIDTH              ) ,
      .C_AXI_DATA_WIDTH              ( C_AXI_DATA_WIDTH              ) ,
      .C_AXI_SUPPORTS_USER_SIGNALS   ( C_AXI_SUPPORTS_USER_SIGNALS   ) ,
      .C_AXI_SUPPORTS_REGION_SIGNALS ( C_AXI_SUPPORTS_REGION_SIGNALS ) ,
      .C_AXI_AWUSER_WIDTH            ( C_AXI_AWUSER_WIDTH            ) ,
      .C_AXI_ARUSER_WIDTH            ( C_AXI_ARUSER_WIDTH            ) ,
      .C_AXI_WUSER_WIDTH             ( C_AXI_WUSER_WIDTH             ) ,
      .C_AXI_RUSER_WIDTH             ( C_AXI_RUSER_WIDTH             ) ,
      .C_AXI_BUSER_WIDTH             ( C_AXI_BUSER_WIDTH             ) ,
      .C_AWPAYLOAD_WIDTH             ( G_AXI_AWPAYLOAD_WIDTH         ) ,
      .C_WPAYLOAD_WIDTH              ( G_AXI_WPAYLOAD_WIDTH          ) ,
      .C_BPAYLOAD_WIDTH              ( G_AXI_BPAYLOAD_WIDTH          ) ,
      .C_ARPAYLOAD_WIDTH             ( G_AXI_ARPAYLOAD_WIDTH         ) ,
      .C_RPAYLOAD_WIDTH              ( G_AXI_RPAYLOAD_WIDTH          ) 
    )
    vector2axi_0 ( 
      .m_awpayload    ( m_awpayload    ) ,
      .m_wpayload     ( m_wpayload     ) ,
      .m_bpayload     ( m_bpayload     ) ,
      .m_arpayload    ( m_arpayload    ) ,
      .m_rpayload     ( m_rpayload     ) ,
      .m_axi_awid     ( m_axi_awid     ) ,
      .m_axi_awaddr   ( m_axi_awaddr   ) ,
      .m_axi_awlen    ( m_axi_awlen    ) ,
      .m_axi_awsize   ( m_axi_awsize   ) ,
      .m_axi_awburst  ( m_axi_awburst  ) ,
      .m_axi_awlock   ( m_axi_awlock   ) ,
      .m_axi_awcache  ( m_axi_awcache  ) ,
      .m_axi_awprot   ( m_axi_awprot   ) ,
      .m_axi_awqos    ( m_axi_awqos    ) ,
      .m_axi_awuser   ( m_axi_awuser   ) ,
      .m_axi_awregion ( m_axi_awregion ) ,
      .m_axi_wid      ( m_axi_wid      ) ,
      .m_axi_wdata    ( m_axi_wdata    ) ,
      .m_axi_wstrb    ( m_axi_wstrb    ) ,
      .m_axi_wlast    ( m_axi_wlast    ) ,
      .m_axi_wuser    ( m_axi_wuser    ) ,
      .m_axi_bid      ( m_axi_bid      ) ,
      .m_axi_bresp    ( m_axi_bresp    ) ,
      .m_axi_buser    ( m_axi_buser    ) ,
      .m_axi_arid     ( m_axi_arid     ) ,
      .m_axi_araddr   ( m_axi_araddr   ) ,
      .m_axi_arlen    ( m_axi_arlen    ) ,
      .m_axi_arsize   ( m_axi_arsize   ) ,
      .m_axi_arburst  ( m_axi_arburst  ) ,
      .m_axi_arlock   ( m_axi_arlock   ) ,
      .m_axi_arcache  ( m_axi_arcache  ) ,
      .m_axi_arprot   ( m_axi_arprot   ) ,
      .m_axi_arqos    ( m_axi_arqos    ) ,
      .m_axi_aruser   ( m_axi_aruser   ) ,
      .m_axi_arregion ( m_axi_arregion ) ,
      .m_axi_rid      ( m_axi_rid      ) ,
      .m_axi_rdata    ( m_axi_rdata    ) ,
      .m_axi_rresp    ( m_axi_rresp    ) ,
      .m_axi_rlast    ( m_axi_rlast    ) ,
      .m_axi_ruser    ( m_axi_ruser    ) 
    );
    
  end  // Reserve SI/MI branch

  if ((C_REG_CONFIG_AW <= 9) && (C_RESERVE_MODE==0)) begin : aw
    axi_register_slice_v2_1_22_axic_register_slice # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_AWPAYLOAD_WIDTH ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AW       ) 
    )
    aw_pipe (
      // System Signals
      .ACLK(aclk),
      .ARESET(reset),

      // Slave side
      .S_PAYLOAD_DATA(s_awpayload),
      .S_VALID(s_axi_awvalid),
      .S_READY(s_axi_awready),

      // Master side
      .M_PAYLOAD_DATA(m_awpayload),
      .M_VALID(m_axi_awvalid),
      .M_READY(m_axi_awready)
    );
    
  end else if ((C_REG_CONFIG_AW == 15) && (C_RESERVE_MODE==0)) begin : aw15
    
    axi_register_slice_v2_1_22_multi_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_AWPAYLOAD_WIDTH ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_NUM_SLR_CROSSINGS (C_NUM_SLR_CROSSINGS) ,
      .C_PIPELINES_MASTER  (C_PIPELINES_MASTER_AW) ,
      .C_PIPELINES_SLAVE   (C_PIPELINES_SLAVE_AW) ,
      .C_PIPELINES_MIDDLE  (C_PIPELINES_MIDDLE_AW) 
    )
    aw_multi (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_awpayload),
      .S_VALID(s_axi_awvalid),
      .S_READY(s_axi_awready),

      // Master side
      .M_PAYLOAD_DATA(m_awpayload),
      .M_VALID(m_axi_awvalid),
      .M_READY(m_axi_awready)
    );
    
  end else if ((C_REG_CONFIG_AW == 16) && (C_RESERVE_MODE==0)) begin : aw16
    
    axi_register_slice_v2_1_22_auto_slr # (
      .C_DATA_WIDTH ( G_AXI_AWPAYLOAD_WIDTH ) 
    )
    aw_auto (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_awpayload),
      .S_VALID(s_axi_awvalid),
      .S_READY(s_axi_awready),

      // Master side
      .M_PAYLOAD_DATA(m_awpayload),
      .M_VALID(m_axi_awvalid),
      .M_READY(m_axi_awready)
    );
    
  end else if (C_RESERVE_MODE==0) begin : aw12
    
    localparam integer P_AW_EVEN_WIDTH = G_AXI_AWPAYLOAD_WIDTH[0] ? (G_AXI_AWPAYLOAD_WIDTH+1) : G_AXI_AWPAYLOAD_WIDTH;
    localparam integer P_AW_TDM_WIDTH = P_AW_EVEN_WIDTH/2;
    localparam integer P_AW_SLR_WIDTH = (C_REG_CONFIG_AW == 13) ? P_AW_TDM_WIDTH : G_AXI_AWPAYLOAD_WIDTH;
    
    wire [P_AW_SLR_WIDTH-1:0] slr_awpayload;
    wire slr_awhandshake;
    wire slr_awready;
        
    axi_register_slice_v2_1_22_source_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AW       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_AWPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_AW_SLR_WIDTH ),
      .C_PIPELINES  (0)
    )
    slr_master_aw (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .S_PAYLOAD_DATA ( s_awpayload ) ,
      .S_VALID        ( s_axi_awvalid   ) ,
      .S_READY        ( s_axi_awready   ) ,
      .laguna_m_reset_in  ( 1'b0 ) ,
      .laguna_m_reset_out  (  ) ,
      .laguna_m_payload   ( slr_awpayload ) , 
      .laguna_m_handshake ( slr_awhandshake   ) ,
      .laguna_m_ready     ( slr_awready   )
    );

    axi_register_slice_v2_1_22_dest_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AW       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_AWPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_AW_SLR_WIDTH ),
      .C_PIPELINES  (0),
      .C_SOURCE_LATENCY (2)
    )
    slr_slave_aw (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .laguna_s_reset_in  ( 1'b0 ) ,
      .laguna_s_reset_out  (  ) ,
      .laguna_s_payload   ( slr_awpayload ) ,
      .laguna_s_handshake ( slr_awhandshake   ) ,
      .laguna_s_ready     ( slr_awready   ) ,
      .M_PAYLOAD_DATA ( m_awpayload ) , 
      .M_VALID        ( m_axi_awvalid   ) ,
      .M_READY        ( m_axi_awready   )
    );
  end  // gen_aw
    
  if ((C_REG_CONFIG_W <= 9) && (C_RESERVE_MODE==0)) begin : w
    axi_register_slice_v2_1_22_axic_register_slice # (
      .C_FAMILY     ( C_FAMILY             ) ,
      .C_DATA_WIDTH ( G_AXI_WPAYLOAD_WIDTH ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_W       ) 
    )
    w_pipe (
      // System Signals
      .ACLK(aclk),
      .ARESET(reset),

      // Slave side
      .S_PAYLOAD_DATA(s_wpayload),
      .S_VALID(s_axi_wvalid),
      .S_READY(s_axi_wready),

      // Master side
      .M_PAYLOAD_DATA(m_wpayload),
      .M_VALID(m_axi_wvalid),
      .M_READY(m_axi_wready)
    );
    
  end else if ((C_REG_CONFIG_W == 15) && (C_RESERVE_MODE==0)) begin : w15
    
    axi_register_slice_v2_1_22_multi_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_WPAYLOAD_WIDTH ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_NUM_SLR_CROSSINGS (C_NUM_SLR_CROSSINGS) ,
      .C_PIPELINES_MASTER  (C_PIPELINES_MASTER_W) ,
      .C_PIPELINES_SLAVE   (C_PIPELINES_SLAVE_W) ,
      .C_PIPELINES_MIDDLE  (C_PIPELINES_MIDDLE_W) 
    )
    w_multi (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_wpayload),
      .S_VALID(s_axi_wvalid),
      .S_READY(s_axi_wready),

      // Master side
      .M_PAYLOAD_DATA(m_wpayload),
      .M_VALID(m_axi_wvalid),
      .M_READY(m_axi_wready)
    );
    
  end else if ((C_REG_CONFIG_W == 16) && (C_RESERVE_MODE==0)) begin : w16
    
    axi_register_slice_v2_1_22_auto_slr # (
      .C_DATA_WIDTH ( G_AXI_WPAYLOAD_WIDTH ) 
    )
    w_auto (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_wpayload),
      .S_VALID(s_axi_wvalid),
      .S_READY(s_axi_wready),

      // Master side
      .M_PAYLOAD_DATA(m_wpayload),
      .M_VALID(m_axi_wvalid),
      .M_READY(m_axi_wready)
    );
    
  end else if (C_RESERVE_MODE==0) begin : w12
    
    localparam integer P_W_EVEN_WIDTH = G_AXI_WPAYLOAD_WIDTH[0] ? (G_AXI_WPAYLOAD_WIDTH+1) : G_AXI_WPAYLOAD_WIDTH;
    localparam integer P_W_TDM_WIDTH = P_W_EVEN_WIDTH/2;
    localparam integer P_W_SLR_WIDTH = (C_REG_CONFIG_W == 13) ? P_W_TDM_WIDTH : G_AXI_WPAYLOAD_WIDTH;
    
    wire [P_W_SLR_WIDTH-1:0] slr_wpayload;
    wire slr_whandshake;
    wire slr_wready;
        
    axi_register_slice_v2_1_22_source_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_W       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_WPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_W_SLR_WIDTH ),
      .C_PIPELINES  (0)
    )
    slr_master_w (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .S_PAYLOAD_DATA ( s_wpayload ) ,
      .S_VALID        ( s_axi_wvalid   ) ,
      .S_READY        ( s_axi_wready   ) ,
      .laguna_m_reset_in  ( 1'b0 ) ,
      .laguna_m_reset_out  (  ) ,
      .laguna_m_payload   ( slr_wpayload ) , 
      .laguna_m_handshake ( slr_whandshake   ) ,
      .laguna_m_ready     ( slr_wready   )
    );

    axi_register_slice_v2_1_22_dest_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_W       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_WPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_W_SLR_WIDTH ),
      .C_PIPELINES  (0),
      .C_SOURCE_LATENCY (2)
    )
    slr_slave_w (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .laguna_s_reset_in  ( 1'b0 ) ,
      .laguna_s_reset_out  (  ) ,
      .laguna_s_payload   ( slr_wpayload ) ,
      .laguna_s_handshake ( slr_whandshake   ) ,
      .laguna_s_ready     ( slr_wready   ) ,
      .M_PAYLOAD_DATA ( m_wpayload ) , 
      .M_VALID        ( m_axi_wvalid   ) ,
      .M_READY        ( m_axi_wready   )
    );
  end  // gen_w

  if ((C_REG_CONFIG_B <= 9) && (C_RESERVE_MODE==0)) begin : b
    axi_register_slice_v2_1_22_axic_register_slice # (
      .C_FAMILY     ( C_FAMILY             ) ,
      .C_DATA_WIDTH ( G_AXI_BPAYLOAD_WIDTH ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_B       ) 
    )
    b_pipe (
      // System Signals
      .ACLK(aclk),
      .ARESET(reset),

      // Slave side
      .S_PAYLOAD_DATA(m_bpayload),
      .S_VALID(m_axi_bvalid),
      .S_READY(m_axi_bready),

      // Master side
      .M_PAYLOAD_DATA(s_bpayload),
      .M_VALID(s_axi_bvalid),
      .M_READY(s_axi_bready)
    );
 
  end else if ((C_REG_CONFIG_B == 15) && (C_RESERVE_MODE==0)) begin : b15
    
    axi_register_slice_v2_1_22_multi_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_BPAYLOAD_WIDTH ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_NUM_SLR_CROSSINGS (C_NUM_SLR_CROSSINGS) ,
      .C_PIPELINES_MASTER  (C_PIPELINES_MASTER_B) ,
      .C_PIPELINES_SLAVE   (C_PIPELINES_SLAVE_B) ,
      .C_PIPELINES_MIDDLE  (C_PIPELINES_MIDDLE_B) 
    )
    b_multi (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(m_bpayload),
      .S_VALID(m_axi_bvalid),
      .S_READY(m_axi_bready),

      // Master side
      .M_PAYLOAD_DATA(s_bpayload),
      .M_VALID(s_axi_bvalid),
      .M_READY(s_axi_bready)
    );
    
  end else if ((C_REG_CONFIG_B == 16) && (C_RESERVE_MODE==0)) begin : b16
    
    axi_register_slice_v2_1_22_auto_slr # (
      .C_DATA_WIDTH ( G_AXI_BPAYLOAD_WIDTH ) 
    )
    b_auto (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(m_bpayload),
      .S_VALID(m_axi_bvalid),
      .S_READY(m_axi_bready),

      // Master side
      .M_PAYLOAD_DATA(s_bpayload),
      .M_VALID(s_axi_bvalid),
      .M_READY(s_axi_bready)
    );
    
  end else if (C_RESERVE_MODE==0) begin : b12
    
    localparam integer P_B_EVEN_WIDTH = G_AXI_BPAYLOAD_WIDTH[0] ? (G_AXI_BPAYLOAD_WIDTH+1) : G_AXI_BPAYLOAD_WIDTH;
    localparam integer P_B_TDM_WIDTH = P_B_EVEN_WIDTH/2;
    localparam integer P_B_SLR_WIDTH = (C_REG_CONFIG_B == 13) ? P_B_TDM_WIDTH : G_AXI_BPAYLOAD_WIDTH;
    
    wire [P_B_SLR_WIDTH-1:0] slr_bpayload;
    wire slr_bhandshake;
    wire slr_bready;
        
    axi_register_slice_v2_1_22_source_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_B       ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_DATA_WIDTH ( G_AXI_BPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_B_SLR_WIDTH ),
      .C_PIPELINES  (0)
    )
    slr_slave_b (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .S_PAYLOAD_DATA ( m_bpayload ) ,
      .S_VALID        ( m_axi_bvalid   ) ,
      .S_READY        ( m_axi_bready   ) ,
      .laguna_m_reset_in  ( 1'b0 ) ,
      .laguna_m_reset_out  (  ) ,
      .laguna_m_payload   ( slr_bpayload ) , 
      .laguna_m_handshake ( slr_bhandshake   ) ,
      .laguna_m_ready     ( slr_bready   )
    );

    axi_register_slice_v2_1_22_dest_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_B       ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_DATA_WIDTH ( G_AXI_BPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_B_SLR_WIDTH ),
      .C_PIPELINES  (0),
      .C_SOURCE_LATENCY (2)
    )
    slr_master_b (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .laguna_s_reset_in  ( 1'b0 ) ,
      .laguna_s_reset_out  (  ) ,
      .laguna_s_payload   ( slr_bpayload ) ,
      .laguna_s_handshake ( slr_bhandshake   ) ,
      .laguna_s_ready     ( slr_bready   ) ,
      .M_PAYLOAD_DATA ( s_bpayload ) , 
      .M_VALID        ( s_axi_bvalid   ) ,
      .M_READY        ( s_axi_bready   )
    );
  end  // gen_b

  if ((C_REG_CONFIG_AR <= 9) && (C_RESERVE_MODE==0)) begin : ar
    axi_register_slice_v2_1_22_axic_register_slice # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_ARPAYLOAD_WIDTH ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AR       ) 
    )
    ar_pipe (
      // System Signals
      .ACLK(aclk),
      .ARESET(reset),

      // Slave side
      .S_PAYLOAD_DATA(s_arpayload),
      .S_VALID(s_axi_arvalid),
      .S_READY(s_axi_arready),

      // Master side
      .M_PAYLOAD_DATA(m_arpayload),
      .M_VALID(m_axi_arvalid),
      .M_READY(m_axi_arready)
    );
    
  end else if ((C_REG_CONFIG_AR == 15) && (C_RESERVE_MODE==0)) begin : ar15
    
    axi_register_slice_v2_1_22_multi_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_ARPAYLOAD_WIDTH ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_NUM_SLR_CROSSINGS (C_NUM_SLR_CROSSINGS) ,
      .C_PIPELINES_MASTER  (C_PIPELINES_MASTER_AR) ,
      .C_PIPELINES_SLAVE   (C_PIPELINES_SLAVE_AR) ,
      .C_PIPELINES_MIDDLE  (C_PIPELINES_MIDDLE_AR) 
    )
    ar_multi (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_arpayload),
      .S_VALID(s_axi_arvalid),
      .S_READY(s_axi_arready),

      // Master side
      .M_PAYLOAD_DATA(m_arpayload),
      .M_VALID(m_axi_arvalid),
      .M_READY(m_axi_arready)
    );
    
  end else if ((C_REG_CONFIG_AR == 16) && (C_RESERVE_MODE==0)) begin : ar16
    
    axi_register_slice_v2_1_22_auto_slr # (
      .C_DATA_WIDTH ( G_AXI_ARPAYLOAD_WIDTH ) 
    )
    ar_auto (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(s_arpayload),
      .S_VALID(s_axi_arvalid),
      .S_READY(s_axi_arready),

      // Master side
      .M_PAYLOAD_DATA(m_arpayload),
      .M_VALID(m_axi_arvalid),
      .M_READY(m_axi_arready)
    );
    
  end else if (C_RESERVE_MODE==0) begin : ar12
    
    localparam integer P_AR_EVEN_WIDTH = G_AXI_ARPAYLOAD_WIDTH[0] ? (G_AXI_ARPAYLOAD_WIDTH+1) : G_AXI_ARPAYLOAD_WIDTH;
    localparam integer P_AR_TDM_WIDTH = P_AR_EVEN_WIDTH/2;
    localparam integer P_AR_SLR_WIDTH = (C_REG_CONFIG_AR == 13) ? P_AR_TDM_WIDTH : G_AXI_ARPAYLOAD_WIDTH;
    
    wire [P_AR_SLR_WIDTH-1:0] slr_arpayload;
    wire slr_arhandshake;
    wire slr_arready;
        
    axi_register_slice_v2_1_22_source_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AR       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_ARPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_AR_SLR_WIDTH ),
      .C_PIPELINES  (0)
    )
    slr_master_ar (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .S_PAYLOAD_DATA ( s_arpayload ) ,
      .S_VALID        ( s_axi_arvalid   ) ,
      .S_READY        ( s_axi_arready   ) ,
      .laguna_m_reset_in  ( 1'b0 ) ,
      .laguna_m_reset_out  (  ) ,
      .laguna_m_payload   ( slr_arpayload ) , 
      .laguna_m_handshake ( slr_arhandshake   ) ,
      .laguna_m_ready     ( slr_arready   )
    );

    axi_register_slice_v2_1_22_dest_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_AR       ) ,
      .C_CHANNEL    ( P_FORWARD ),
      .C_DATA_WIDTH ( G_AXI_ARPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_AR_SLR_WIDTH ),
      .C_PIPELINES  (0),
      .C_SOURCE_LATENCY (2)
    )
    slr_slave_ar (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .laguna_s_reset_in  ( 1'b0 ) ,
      .laguna_s_reset_out  (  ) ,
      .laguna_s_payload   ( slr_arpayload ) ,
      .laguna_s_handshake ( slr_arhandshake   ) ,
      .laguna_s_ready     ( slr_arready   ) ,
      .M_PAYLOAD_DATA ( m_arpayload ) , 
      .M_VALID        ( m_axi_arvalid   ) ,
      .M_READY        ( m_axi_arready   )
    );
  end  // gen_ar
        
  if ((C_REG_CONFIG_R <= 9) && (C_RESERVE_MODE==0)) begin : r
    axi_register_slice_v2_1_22_axic_register_slice # (
      .C_FAMILY     ( C_FAMILY             ) ,
      .C_DATA_WIDTH ( G_AXI_RPAYLOAD_WIDTH ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_R       ) 
    )
    r_pipe (
      // System Signals
      .ACLK(aclk),
      .ARESET(reset),

      // Slave side
      .S_PAYLOAD_DATA(m_rpayload),
      .S_VALID(m_axi_rvalid),
      .S_READY(m_axi_rready),

      // Master side
      .M_PAYLOAD_DATA(s_rpayload),
      .M_VALID(s_axi_rvalid),
      .M_READY(s_axi_rready)
    );
    
  end else if ((C_REG_CONFIG_R == 15) && (C_RESERVE_MODE==0)) begin : r15
    
    axi_register_slice_v2_1_22_multi_slr # (
      .C_FAMILY     ( C_FAMILY              ) ,
      .C_DATA_WIDTH ( G_AXI_RPAYLOAD_WIDTH ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_NUM_SLR_CROSSINGS (C_NUM_SLR_CROSSINGS) ,
      .C_PIPELINES_MASTER  (C_PIPELINES_MASTER_R) ,
      .C_PIPELINES_SLAVE   (C_PIPELINES_SLAVE_R) ,
      .C_PIPELINES_MIDDLE  (C_PIPELINES_MIDDLE_R) 
    )
    r_multi (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(m_rpayload),
      .S_VALID(m_axi_rvalid),
      .S_READY(m_axi_rready),

      // Master side
      .M_PAYLOAD_DATA(s_rpayload),
      .M_VALID(s_axi_rvalid),
      .M_READY(s_axi_rready)
    );
    
  end else if ((C_REG_CONFIG_R == 16) && (C_RESERVE_MODE==0)) begin : r16
    
    axi_register_slice_v2_1_22_auto_slr # (
      .C_DATA_WIDTH ( G_AXI_RPAYLOAD_WIDTH ) 
    )
    r_auto (
      // System Signals
      .ACLK(aclk),
      .ARESETN(aresetn),

      // Slave side
      .S_PAYLOAD_DATA(m_rpayload),
      .S_VALID(m_axi_rvalid),
      .S_READY(m_axi_rready),

      // Master side
      .M_PAYLOAD_DATA(s_rpayload),
      .M_VALID(s_axi_rvalid),
      .M_READY(s_axi_rready)
    );
    
  end else if (C_RESERVE_MODE==0) begin : r12
    
    localparam integer P_R_EVEN_WIDTH = G_AXI_RPAYLOAD_WIDTH[0] ? (G_AXI_RPAYLOAD_WIDTH+1) : G_AXI_RPAYLOAD_WIDTH;
    localparam integer P_R_TDM_WIDTH = P_R_EVEN_WIDTH/2;
    localparam integer P_R_SLR_WIDTH = (C_REG_CONFIG_R == 13) ? P_R_TDM_WIDTH : G_AXI_RPAYLOAD_WIDTH;
    
    wire [P_R_SLR_WIDTH-1:0] slr_rpayload;
    wire slr_rhandshake;
    wire slr_rready;
        
    axi_register_slice_v2_1_22_source_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_R       ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_DATA_WIDTH ( G_AXI_RPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_R_SLR_WIDTH ),
      .C_PIPELINES  (0)
    )
    slr_slave_r (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .S_PAYLOAD_DATA ( m_rpayload ) ,
      .S_VALID        ( m_axi_rvalid   ) ,
      .S_READY        ( m_axi_rready   ) ,
      .laguna_m_reset_in  ( 1'b0 ) ,
      .laguna_m_reset_out  (  ) ,
      .laguna_m_payload   ( slr_rpayload ) , 
      .laguna_m_handshake ( slr_rhandshake   ) ,
      .laguna_m_ready     ( slr_rready   )
    );

    axi_register_slice_v2_1_22_dest_region_slr #(
      .C_FAMILY     ( C_FAMILY         ) ,
      .C_REG_CONFIG ( C_REG_CONFIG_R       ) ,
      .C_CHANNEL    ( P_RESPONSE ),
      .C_DATA_WIDTH ( G_AXI_RPAYLOAD_WIDTH ) ,
      .C_SLR_WIDTH  ( P_R_SLR_WIDTH ),
      .C_PIPELINES  (0),
      .C_SOURCE_LATENCY (2)
    )
    slr_master_r (
      .ACLK           ( aclk            ) ,
      .ACLK2X         ( aclk2x            ) ,
      .ARESETN        ( aresetn        ) ,
      .laguna_s_reset_in  ( 1'b0 ) ,
      .laguna_s_reset_out  (  ) ,
      .laguna_s_payload   ( slr_rpayload ) ,
      .laguna_s_handshake ( slr_rhandshake   ) ,
      .laguna_s_ready     ( slr_rready   ) ,
      .M_PAYLOAD_DATA ( s_rpayload ) , 
      .M_VALID        ( s_axi_rvalid   ) ,
      .M_READY        ( s_axi_rready   )
    );
  end  // gen_r

endgenerate
endmodule // axi_register_slice


