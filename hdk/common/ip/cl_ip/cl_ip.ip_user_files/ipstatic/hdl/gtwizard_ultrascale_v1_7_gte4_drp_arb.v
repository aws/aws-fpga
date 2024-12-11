// (c) Copyright 2013-2015, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
////////////////////////////////////////////////////////////

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

module gtwizard_ultrascale_v1_7_18_gte4_drp_arb 

#(
  parameter [9:0]  ADDR_TX_PROGCLK_SEL = 10'h00C,
  parameter [9:0]  ADDR_TX_PROGDIV_CFG = 10'h03E, //GTY /GTH addresses are different  (003E in GTH; 0057 in GTY)
  parameter [9:0]  ADDR_RX_PROGDIV_CFG = 10'h0C6,
  parameter [9:0]  ADDR_X0E1 = 10'h0E1,
  parameter [9:0]  ADDR_X079 = 10'h079,
  parameter [9:0]  ADDR_X114 = 10'h114,
  parameter C_NUM_CLIENTS = 2,
  parameter C_ADDR_WIDTH = 9,
  parameter C_DATA_WIDTH = 16
)
(

  input  wire                                     DCLK_I,

  input  wire                                     RESET_I,
  
  input wire                                      TX_CAL_DONE_I, 
  input wire                                      RX_CAL_DONE_I,

  input  wire [C_NUM_CLIENTS-1:0]                 DEN_USR_I,

  input  wire [C_NUM_CLIENTS-1:0]                 DWE_USR_I,

  input  wire [(C_ADDR_WIDTH*C_NUM_CLIENTS)-1:0]  DADDR_USR_I,

  input  wire [(C_DATA_WIDTH*C_NUM_CLIENTS)-1:0]  DI_USR_I,

  output reg  [(C_DATA_WIDTH*C_NUM_CLIENTS)-1:0]  DO_USR_O = 'h0,

  output reg  [C_NUM_CLIENTS-1:0]                 DRDY_USR_O = 'h0,



  output reg                                      DEN_O = 1'b0,

  output reg                                      DWE_O = 1'b0,

  output reg  [C_ADDR_WIDTH-1:0]                  DADDR_O = 1'b0,

  output reg  [C_DATA_WIDTH-1:0]                  DI_O = 'h0,

  input  wire [C_DATA_WIDTH-1:0]                  DO_I,

  input  wire                                     DRDY_I

);

  //

  //  log base 2

  //

  function integer clogb2;

    input integer depth;

    integer d;

    begin

      if (depth == 0)

        clogb2 = 1;

      else

      begin

        d = depth;

        for (clogb2=0; d > 0; clogb2 = clogb2+1)

          d = d >> 1;

      end

    end

  endfunction



  

  reg [clogb2(C_NUM_CLIENTS)-1:0]         idx = 'b0;

  reg                                     done = 1'b0;

  

  reg                                     rd = 1'b0;

  reg                                     wr = 1'b0;

  

  reg [C_NUM_CLIENTS-1:0]                 en = 'h0;

  reg [C_NUM_CLIENTS-1:0]                 we = 'h0;

  reg [(C_DATA_WIDTH*C_NUM_CLIENTS)-1:0]  data_i = 'h0;

  reg [(C_ADDR_WIDTH*C_NUM_CLIENTS)-1:0]  addr_i = 'h0;

  

  

  reg [C_DATA_WIDTH-1:0]                  di = 'h0;

  reg [C_ADDR_WIDTH-1:0]                  daddr = 'h0;

  reg [C_DATA_WIDTH-1:0]                  do_r = 'h0;

  

  //

  // Arbitration state machine encodings

  //

  localparam [3:0] ARB_START    = 4'd1;

  localparam [3:0] ARB_WAIT     = 4'd2;

  localparam [3:0] ARB_REPORT   = 4'd4;

  localparam [3:0] ARB_INC      = 4'd8;

  

  reg [3:0] arb_state = ARB_START;

  

  //

  // DRP state machine encodings

  //

  localparam [6:0] DRP_WAIT      = 7'd1;

  localparam [6:0] DRP_READ      = 7'd2;

  localparam [6:0] DRP_READ_ACK  = 7'd4;

  localparam [6:0] DRP_MODIFY    = 7'd8;

  localparam [6:0] DRP_WRITE     = 7'd16;

  localparam [6:0] DRP_WRITE_ACK = 7'd32;

  localparam [6:0] DRP_DONE      = 7'd64;

  

  reg [6:0] drp_state = DRP_WAIT;

  

  reg [7:0] timeout_cntr = 0;

  

  integer i;

  

  //

  // Register incoming transactions: grab data, address, write enable when DEN is high

  // Clear internal enable when transaction is (eventually) finished

  //

  always @(posedge DCLK_I)

  begin

    if (RESET_I)

    begin

      en <= 'b0;

      we <= 'b0;

      data_i <= 'b0;

      addr_i <= 'b0;

    end

    else

    begin

      if (DEN_USR_I[0]) begin 
      
        en[0] <= 1'b1;  // this means this client wants to do a transaction

        we[0] <= DWE_USR_I[0];

        //data_i[(i*C_DATA_WIDTH) +: C_DATA_WIDTH] <= DI_USR_I[(i*C_DATA_WIDTH) +: C_DATA_WIDTH];
        //addr_i[(i*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= DADDR_USR_I[(i*C_ADDR_WIDTH) +: C_ADDR_WIDTH];      
        
        // if cpll cal not done (mask) from cpll cal, if user tries to write, always save progdiv to temp holding place. 
        if (!TX_CAL_DONE_I && DADDR_USR_I[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] == ADDR_TX_PROGDIV_CFG && DWE_USR_I[0]) begin  
            addr_i[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= ADDR_X079;
            data_i[(0*C_DATA_WIDTH) +: C_DATA_WIDTH] <= {1'b1,DI_USR_I[(0*C_DATA_WIDTH) +: C_DATA_WIDTH-1]};
        end
        else if (!TX_CAL_DONE_I && DADDR_USR_I[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] == ADDR_TX_PROGCLK_SEL && DWE_USR_I[0]) begin 
            addr_i[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= ADDR_X0E1;
            data_i[(0*C_DATA_WIDTH) +: C_DATA_WIDTH] <= {1'b1,DI_USR_I[(0*C_DATA_WIDTH) +: C_DATA_WIDTH-1]};
        end
        else if (!RX_CAL_DONE_I && DADDR_USR_I[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] == ADDR_RX_PROGDIV_CFG && DWE_USR_I[0]) begin 
            addr_i[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= ADDR_X114;
            data_i[(0*C_DATA_WIDTH) +: C_DATA_WIDTH] <= {1'b1,DI_USR_I[(0*C_DATA_WIDTH) +: C_DATA_WIDTH-1]};
        end
        else begin
            //behave normal
            addr_i[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= DADDR_USR_I[(0*C_ADDR_WIDTH) +: C_ADDR_WIDTH];
            data_i[(0*C_DATA_WIDTH) +: C_DATA_WIDTH] <= DI_USR_I[(0*C_DATA_WIDTH) +: C_DATA_WIDTH];
        end
        
      end

      for (i = 1; i < C_NUM_CLIENTS; i= i+1) 

      begin

        if (DEN_USR_I[i])

        begin

          en[i] <= 1'b1;  // this means this client wants to do a transaction

          we[i] <= DWE_USR_I[i];

          data_i[(i*C_DATA_WIDTH) +: C_DATA_WIDTH] <= DI_USR_I[(i*C_DATA_WIDTH) +: C_DATA_WIDTH];

          addr_i[(i*C_ADDR_WIDTH) +: C_ADDR_WIDTH] <= DADDR_USR_I[(i*C_ADDR_WIDTH) +: C_ADDR_WIDTH];

        end

      end

      if (done)

      begin

        en[idx] <= 1'b0;

        we[idx] <= 1'b0;

      end  

    end     

  end

           

  

  //

  // Arbitration FSM - does a round-robin arbritration scheme

  //

  always @(posedge DCLK_I)

  begin

    if (RESET_I) 

    begin

      idx <= 'b0;

      di <= 'b0;

      daddr <= 'b0;

      rd <= 1'b0;

      wr <= 1'b0;

      arb_state <= ARB_START;

      DRDY_USR_O <= 'b0;

      DO_USR_O <= 'b0;

    end

    else

    begin

      case (arb_state)

        ARB_START: begin

          if (en[idx] == 1'b1) 

          begin

            di    <= data_i[idx*C_DATA_WIDTH +: C_DATA_WIDTH];

            daddr <= addr_i[idx*C_ADDR_WIDTH +: C_ADDR_WIDTH];

            rd    <= !we[idx];

            wr    <= we[idx];

            arb_state <= ARB_WAIT;

          end

          else

          begin 

            rd    <= 1'b0;

            wr    <= 1'b0;

            arb_state <= ARB_INC;

          end 

        end

        ARB_WAIT: begin

          rd <= 1'b0;

          wr <= 1'b0;

          if (done == 1'b1)  

            arb_state <= ARB_REPORT;

          else

            arb_state <= ARB_WAIT;

        end

        ARB_REPORT: begin

          DRDY_USR_O[idx] <= 1'b1;

          DO_USR_O[idx*C_DATA_WIDTH +: C_DATA_WIDTH] <= do_r;

          arb_state <= ARB_INC;

        end

        ARB_INC : begin

          DRDY_USR_O[idx] <= 1'b0;

          if (idx == C_NUM_CLIENTS-1)

            idx <= 1'b0;

          else

            idx <= idx + 1;

          arb_state <= ARB_START;

        end

        default: arb_state <= ARB_START;

        

      endcase

    end

  end  

  

  

  //

  // DRP FSM - does the actual DRP read or write

  //

  always @(posedge DCLK_I) 

  begin

    if (RESET_I) 

    begin

      DEN_O <=  1'b0;

      DWE_O <=  1'b0;

      DI_O <=  16'h0000;

      DADDR_O <= 'b0;

      do_r <= 'b0;

      drp_state <=  DRP_WAIT;

      done <=  1'b0;

    end

    else 

    begin

      case (drp_state)

        DRP_WAIT: begin

          timeout_cntr <= 8'h0;

          if (rd) drp_state <=  DRP_READ;

          else if (wr) drp_state <=  DRP_WRITE;

          else         drp_state <=  DRP_WAIT;

        end

        DRP_READ: begin

          DEN_O <=  1'b1;

          DWE_O <=  1'b0;

          DADDR_O <= daddr;

          timeout_cntr <= 8'h0;

          done <= 1'b0;

          drp_state <=  DRP_READ_ACK;

        end

        DRP_READ_ACK: begin

          DEN_O <=  1'b0;

          DWE_O <=  1'b0;

          timeout_cntr <= timeout_cntr + 1;

          if (DRDY_I == 1'b1 || timeout_cntr == 8'hFF) 

          begin

            do_r <= DO_I;

            done <= 1'b1;

            drp_state <=  DRP_DONE;

          end  

          else      

            drp_state <=  DRP_READ_ACK; 

        end

        DRP_WRITE: begin

          DEN_O <=  1'b1;

          DWE_O <=  1'b1;

          DADDR_O <=  daddr;

          DI_O <=  di;

          timeout_cntr <= 8'h0;

          done <= 1'b0;

          drp_state <=  DRP_WRITE_ACK;

        end

        DRP_WRITE_ACK: begin

          DEN_O <=  1'b0;

          DWE_O <=  1'b0;

          timeout_cntr <= timeout_cntr + 1;

          if (DRDY_I == 1'b1 || timeout_cntr == 8'hFF) 

          begin
          
            do_r <= DO_I;

            done <= 1'b1;

            drp_state <=  DRP_DONE;

          end  

          else              

            drp_state <=  DRP_WRITE_ACK;

        end

        DRP_DONE: begin

          timeout_cntr <= 8'h0;

          done <= 1'b0; // done was asserted in the previous state

          drp_state <=  DRP_WAIT;

        end

          default: drp_state <=  DRP_WAIT;

      endcase

    end

  end

  

endmodule  

