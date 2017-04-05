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


module mem_scrb
  #(ADDR_WIDTH = 64,
    DATA_WIDTH = 512,
    ID_WIDTH = 10,
    USER_WIDTH = 10,
    BURST_LEN_MINUS1 = 15,
    MAX_ADDR = 64'h3FFFFF
    )

   (
   input                             clk,
   input                             rst_n,
  
   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   output logic [ID_WIDTH-1:0]       awid,
   output logic [ADDR_WIDTH-1:0]     awaddr,
   output logic [7:0]                awlen,
   output logic [USER_WIDTH-1:0]     awuser,
   output logic                      awvalid,
   input                             awready,

   output logic [ID_WIDTH-1:0]       wid,
   output logic [DATA_WIDTH-1:0]     wdata,
   output logic [(DATA_WIDTH/8)-1:0] wstrb,
   output logic                      wlast,
   output logic                      wvalid,
   input                             wready,

   input                             bvalid,
   output logic                      bready,

   output logic [ID_WIDTH-1:0]       arid,
   output logic [ADDR_WIDTH-1:0]     araddr,
   output logic [7:0]                arlen,
   output logic [USER_WIDTH-1:0]     aruser,
   output logic                      arvalid,
   input                             arready,

   output logic                      rready,

   input                             scrb_enable,

   output logic                      scrb_done,

   output logic [2:0]                dbg_state,
   output logic [ADDR_WIDTH-1:0]     dbg_addr                     

    );

   localparam DATA_WIDTH_BYTES = DATA_WIDTH/8;
   
   typedef enum logic [2:0] {FSM_IDLE = 3'd0,
                             FSM_START = 3'd1,
                             FSM_AW = 3'd2,
                             FSM_W = 3'd3,
                             FSM_B = 3'd4,
                             FSM_DONE = 3'd5} fsm_state_t;
   
   fsm_state_t curr_state;
   fsm_state_t next_state;
   logic [ADDR_WIDTH-1:0] curr_addr;
   logic [15:0]           num_txn;
   logic                  scrb_enable_q;
   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n)
       scrb_enable_q <= 1'b0;
     else
       scrb_enable_q <= scrb_enable;
   
   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n)
       curr_state <= FSM_IDLE;
     else 
       curr_state <= ~scrb_enable_q ? FSM_IDLE : next_state;
   
   always_comb
     case (curr_state)
       FSM_IDLE : next_state = scrb_enable_q ? FSM_START : FSM_IDLE;
       FSM_START : next_state = FSM_AW;
       FSM_AW : next_state = awready ? FSM_W : FSM_AW;
       FSM_W  : next_state = wready && (num_txn == BURST_LEN_MINUS1) ? FSM_B : FSM_W;
       FSM_B  : next_state = bvalid && (curr_addr >= MAX_ADDR) ? FSM_DONE :
                             bvalid ? FSM_AW : FSM_B;
       FSM_DONE : next_state = FSM_DONE;
       default : next_state = FSM_IDLE;
     endcase // case (curr_state)

   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n)
       curr_addr <= {ADDR_WIDTH{1'b0}};
     else
       curr_addr <= (curr_state == FSM_START) ? ({ADDR_WIDTH{1'b0}}) : 
         (curr_state == FSM_W) && wready ? curr_addr + DATA_WIDTH_BYTES : curr_addr;

   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n)
       num_txn <= 16'd0;
     else
       num_txn <= (curr_state == FSM_AW) ? 16'd0 :
                  (curr_state == FSM_W) && wready ? num_txn + 16'd1 : num_txn;
   
   assign awvalid = (curr_state == FSM_AW);
   assign awaddr = curr_addr;
   assign awid = {ID_WIDTH{1'b0}};
   assign awlen = BURST_LEN_MINUS1;
   assign awuser = {USER_WIDTH{1'b0}};

   assign wvalid = (curr_state == FSM_W);
   assign wid = {ID_WIDTH{1'b0}};
   assign wstrb = {(DATA_WIDTH/8){1'b1}};
   assign wdata = {DATA_WIDTH{1'b0}};
   assign wlast = (num_txn == BURST_LEN_MINUS1);
                          
   assign arvalid = 1'b0;
   assign araddr = {ADDR_WIDTH{1'b0}};
   assign arid = {ID_WIDTH{1'b0}};
   assign arlen = 8'd0;
   assign aruser = {USER_WIDTH{1'b0}};

   assign bready = 1'b1;
   assign rready = 1'b1;

   always_ff @(posedge clk or negedge rst_n)
     if (!rst_n)
       scrb_done <= 1'b0;
     else
       scrb_done <= (curr_state == FSM_IDLE) ? 1'b0: 
                    (curr_state == FSM_DONE) ? 1'b1 : scrb_done;

   // Debug outputs
   assign dbg_state = curr_state;
   assign dbg_addr = curr_addr;
   
endmodule // mem_scrb


   
   
   
   
   
   
