// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
// ============================================================================


//=====================================================================================
// AXI-L to CFG bus convertor
// ---------------------------
// Description:
// * This block can be used to convert AXIL transaction into a simple CFG bus
// * Simple CFG bus has a single addr, wr, rd and ack signals.
//
//=====================================================================================

module axil_to_cfg_cnv
  #(
    parameter ADDR_WIDTH   = 32,
    parameter DATA_WIDTH   = 32
    )
   (
    input logic              clk,
    input logic              rst_n,
    axil_bus_t.slave         s_axil_bus,
    cfg_bus_t.master         m_cfg_bus,
    output logic             o_fsm_busy = '0
    );

   //=====================================================================================
   // AXI-L State Machine
   //=====================================================================================
   typedef enum logic [1:0] {
                             AXL_FSM_IDLE  = 2'd0,
                             AXL_FSM_ADDR  = 2'd1,
                             AXL_FSM_WDATA = 2'd2,
                             AXL_FSM_RESP  = 2'd3
                             } axl_fsm_t;

   axl_fsm_t              axl_fsm_state_q = AXL_FSM_IDLE;
   axl_fsm_t              axl_fsm_next;
   logic                  awvalid_q = '0;
   logic                  cfg_wr_q = '0;
   logic                  cfg_rd_q = '0;
   logic [ADDR_WIDTH-1:0] cfg_addr_q = '0;
   logic                  arvalid_q  = '0;

   // Next state logic
   always_comb begin : NEXT_STATE
      axl_fsm_next = axl_fsm_state_q;
      unique case (axl_fsm_state_q) //{
        AXL_FSM_IDLE :
          if (s_axil_bus.awvalid || s_axil_bus.arvalid)
            axl_fsm_next = AXL_FSM_ADDR;

        AXL_FSM_ADDR :
          if (awvalid_q)
            axl_fsm_next = AXL_FSM_WDATA;
          else
            axl_fsm_next = AXL_FSM_RESP;

        AXL_FSM_WDATA :
          if (cfg_wr_q && m_cfg_bus.ack)
            axl_fsm_next = AXL_FSM_RESP;

        AXL_FSM_RESP :
          if ((s_axil_bus.bvalid && s_axil_bus.bready) ||
              (s_axil_bus.rvalid && s_axil_bus.rready))
              // (s_axil_bus.rvalid && s_axil_bus.rlast && s_axil_bus.rready))
            axl_fsm_next = AXL_FSM_IDLE;
      endcase // unique case (axl_fsm_state_q) //}
   end : NEXT_STATE

   // FSM sequencer
   always_ff @(posedge clk)
     if (!rst_n)
       axl_fsm_state_q <= AXL_FSM_IDLE;
     else
       axl_fsm_state_q <= axl_fsm_next;

   // FSM busy indicator
   always_ff @(posedge clk)
     o_fsm_busy <= (axl_fsm_next != AXL_FSM_IDLE);

   //=====================================================================================
   // CFG Addr
   //=====================================================================================
   // cfg_addr, identify whether write or read.
   always_ff @(posedge clk)
     if (!rst_n) begin
        {awvalid_q, arvalid_q} <= '0;
     end
     else if ((axl_fsm_state_q == AXL_FSM_IDLE) && s_axil_bus.awvalid) begin //{
        cfg_addr_q <= s_axil_bus.awaddr;
        awvalid_q  <= '1;
        arvalid_q  <= '0;
     end //}
     else if ((axl_fsm_state_q == AXL_FSM_IDLE) && s_axil_bus.arvalid) begin //{
        cfg_addr_q <= s_axil_bus.araddr;
        awvalid_q  <= '0;
        arvalid_q  <= '1;
     end //}

   // AWREADY, ARREADY
   always_ff @(posedge clk)
     if (!rst_n) begin //{
        s_axil_bus.awready <= '0;
        s_axil_bus.arready <= '0;
     end //}
     else begin //{
        s_axil_bus.awready <= ((axl_fsm_state_q == AXL_FSM_IDLE) && s_axil_bus.awvalid);
        s_axil_bus.arready <= ((axl_fsm_state_q == AXL_FSM_IDLE) && s_axil_bus.arvalid && !s_axil_bus.awvalid);
     end //}

   //=====================================================================================
   // CFG WR/RD requests
   //=====================================================================================
   always_ff @(posedge clk)
     if (!rst_n) begin
        cfg_wr_q <= '0;
        cfg_rd_q <= '0;
     end
     else begin //{
        if ((axl_fsm_next == AXL_FSM_WDATA) && s_axil_bus.wvalid)
          cfg_wr_q <= '1;
        else if (cfg_wr_q && m_cfg_bus.ack)
          cfg_wr_q <= '0;

        if ((axl_fsm_state_q == AXL_FSM_ADDR) && arvalid_q)
          cfg_rd_q <= '1;
        else if (cfg_rd_q && m_cfg_bus.ack)
          cfg_rd_q <= '0;
     end //}

   // WREADY
   always_ff @(posedge clk)
     if (!rst_n)
       s_axil_bus.wready <= '0;
     else
       s_axil_bus.wready <= (cfg_wr_q && m_cfg_bus.ack);

   //=====================================================================================
   // AXIL BRESP, RDATA
   //=====================================================================================
   always_ff @(posedge clk)
     if (!rst_n || (s_axil_bus.bvalid && s_axil_bus.bready))
       s_axil_bus.bvalid <= '0;
     else if (s_axil_bus.wready && s_axil_bus.wvalid)
       s_axil_bus.bvalid <= '1;

   assign s_axil_bus.bresp = '0; //NOTE: always OKAY response

   // CFG-RDATA to AXIL-RDATA
   logic [DATA_WIDTH-1:0] axil_bus_rdata_q = '0; // prevents X's in simulation at time 0;

   always_ff @(posedge clk)
     if (!rst_n || (s_axil_bus.rvalid && s_axil_bus.rready)) begin //{
        s_axil_bus.rvalid <= '0;
        // s_axil_bus.rlast  <= '0;
     end //}
     else if (cfg_rd_q && m_cfg_bus.ack) begin //{
        s_axil_bus.rvalid <= '1;
        // s_axil_bus.rlast  <= '1;
        axil_bus_rdata_q  <= m_cfg_bus.rdata;
     end //}

   assign s_axil_bus.rdata = axil_bus_rdata_q;
   assign s_axil_bus.rresp = '0; // NOTE: Always OKAY response

   //=====================================================================================
   // Drive CFG bus
   //=====================================================================================
   always_comb begin : DRIVE_CFG_BUS //{
      m_cfg_bus.addr  = cfg_addr_q;
      m_cfg_bus.wdata = s_axil_bus.wdata;
      m_cfg_bus.wr    = cfg_wr_q;
      m_cfg_bus.rd    = cfg_rd_q;
      m_cfg_bus.user  = '0;
   end : DRIVE_CFG_BUS //}

endmodule // axil_to_cfg_cnv
