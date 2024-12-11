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

module gtwizard_ultrascale_v1_7_18_gthe4_delay_powergood # (
  parameter C_USER_GTPOWERGOOD_DELAY_EN = 0,
  parameter C_PCIE_ENABLE = "FALSE"
)(
  input wire GT_RXOUTCLKPCS,

  input wire GT_GTPOWERGOOD,
  input wire [2:0] USER_RXRATE,
  input wire USER_RXRATEMODE,
  input wire USER_GTRXRESET,
  input wire USER_RXPMARESET,
  input wire [1:0] USER_RXPD,

  output wire USER_GTPOWERGOOD,
  output wire [2:0] GT_RXRATE,
  output wire GT_RXRATEMODE,
  output wire GT_GTRXRESET,
  output wire GT_RXPMARESET,
  output wire [1:0] GT_RXPD
);

generate if (C_PCIE_ENABLE || (C_USER_GTPOWERGOOD_DELAY_EN == 0))
begin : gen_powergood_nodelay
  assign GT_RXPD          = USER_RXPD;
  assign GT_GTRXRESET     = USER_GTRXRESET;
  assign GT_RXPMARESET    = USER_RXPMARESET;
  assign GT_RXRATE        = USER_RXRATE;
  assign GT_RXRATEMODE    = USER_RXRATEMODE;
  assign USER_GTPOWERGOOD = GT_GTPOWERGOOD;
end
else
begin: gen_powergood_delay
  (*  ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) reg [4:0] intclk_rrst_n_r = 5'd0;
  (*  ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) reg [8:0] wait_cnt;
  (*  ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* KEEP = "TRUE" *) reg int_pwr_on_fsm = 1'b0;
  (*  ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* KEEP = "TRUE" *) reg pwr_on_fsm = 1'b0;
  wire intclk_rrst_n;
  
  //--------------------------------------------------------------------------
  //  POWER ON FSM Encoding
  //-------------------------------------------------------------------------- 
  localparam PWR_ON_WAIT_CNT           = 4'd0;
  localparam PWR_ON_DONE               = 4'd1; 
  
  //--------------------------------------------------------------------------------------------------
  //  Reset Synchronizer
  //--------------------------------------------------------------------------------------------------
  always @ (posedge GT_RXOUTCLKPCS or negedge GT_GTPOWERGOOD)
  begin
      if (!GT_GTPOWERGOOD)
          intclk_rrst_n_r <= 5'd0;
      else if(!int_pwr_on_fsm)
          intclk_rrst_n_r <= {intclk_rrst_n_r[3:0], 1'd1}; 
  end

  assign intclk_rrst_n = intclk_rrst_n_r[4];

  //--------------------------------------------------------------------------------------------------
  //  Wait counter 
  //--------------------------------------------------------------------------------------------------
  always @ (posedge GT_RXOUTCLKPCS)
  begin
    if (!intclk_rrst_n)
    	wait_cnt <= 9'd0;
    else begin
    	if (int_pwr_on_fsm == PWR_ON_WAIT_CNT)
    		wait_cnt <= {wait_cnt[7:0],1'b1};
    	else
    		wait_cnt <= wait_cnt;
    end
  end

  //--------------------------------------------------------------------------------------------------
  // Power On FSM
  //--------------------------------------------------------------------------------------------------

  always @ (posedge GT_RXOUTCLKPCS or negedge GT_GTPOWERGOOD)
  begin
    if (!GT_GTPOWERGOOD)
    begin
      int_pwr_on_fsm <= PWR_ON_WAIT_CNT;
    end
    else begin
      case (int_pwr_on_fsm)
        PWR_ON_WAIT_CNT :
          begin
            int_pwr_on_fsm <= (wait_cnt[7] == 1'b1) ? PWR_ON_DONE : PWR_ON_WAIT_CNT;
          end 

        PWR_ON_DONE :
          begin
            int_pwr_on_fsm <= PWR_ON_DONE;
          end

        default :
        begin
          int_pwr_on_fsm <= PWR_ON_WAIT_CNT;
        end
      endcase
    end
  end

  always @(posedge GT_RXOUTCLKPCS)
    pwr_on_fsm <= int_pwr_on_fsm;

  assign GT_RXPD          = pwr_on_fsm ? USER_RXPD : 2'b11;
  assign GT_GTRXRESET     = pwr_on_fsm ? USER_GTRXRESET : !GT_GTPOWERGOOD;
  assign GT_RXPMARESET    = pwr_on_fsm ? USER_RXPMARESET : 1'b0;
  assign GT_RXRATE        = pwr_on_fsm ? USER_RXRATE : 3'b001;
  assign GT_RXRATEMODE    = pwr_on_fsm ? USER_RXRATEMODE : 1'b1;
  assign USER_GTPOWERGOOD = pwr_on_fsm; 

end
endgenerate

endmodule
