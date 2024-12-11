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

module gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_rx # (
  parameter C_SIM_CPLL_CAL_BYPASS = 1'b1,
  parameter SIM_RESET_SPEEDUP     = "TRUE",
  parameter CPLL_CAL_ONLY_TX      = 1,
  parameter C_FREERUN_FREQUENCY   = 100
)(
  // control signals
  input   wire  [17:0]  RXOUTCLK_PERIOD_IN,
  input   wire  [17:0]  CNT_TOL_IN,
  input   wire  [15:0]  FREQ_COUNT_WINDOW_IN,
  // User Interface
  input   wire          RESET_IN,
  input   wire          CLK_IN,
  
  input   wire          USER_RXPROGDIVRESET_IN,
  output  wire          USER_RXPRGDIVRESETDONE_OUT,
  output  wire          USER_RXPMARESETDONE_OUT,
  input   wire  [2:0]   USER_RXOUTCLKSEL_IN,
  input   wire          USER_RXOUTCLK_BUFG_CE_IN,
  input   wire          USER_RXOUTCLK_BUFG_CLR_IN,
  output  reg           USER_CPLLLOCK_OUT,
  input   wire          USER_GTRXRESET_IN, 
  input   wire          USER_RXCDRHOLD_IN,
  input   wire          USER_RXPMARESET_IN,
  // Debug Interface
  output  wire          CPLL_CAL_FAIL,
  output  wire          CPLL_CAL_DONE,
  output  wire  [15:0]  DEBUG_OUT,
  output  wire  [17:0]  CAL_FREQ_CNT,
  input         [3:0]   REPEAT_RESET_LIMIT,
  // GT Interface
  input   wire          GTHE4_RXOUTCLK_IN,
  input   wire          GTHE4_CPLLLOCK_IN,
  output  wire          GTHE4_CPLLRESET_OUT,
  output  wire          GTHE4_CPLLPD_OUT,
  output  wire          GTHE4_RXPROGDIVRESET_OUT,
  output  wire   [2:0]  GTHE4_RXOUTCLKSEL_OUT,
  input   wire          GTHE4_RXPRGDIVRESETDONE_IN,
  output  wire  [9:0]   GTHE4_CHANNEL_DRPADDR_OUT,
  output  wire  [15:0]  GTHE4_CHANNEL_DRPDI_OUT,
  output  wire          GTHE4_CHANNEL_DRPEN_OUT,
  output  wire          GTHE4_CHANNEL_DRPWE_OUT,
  input   wire          GTHE4_CHANNEL_DRPRDY_IN,
  input   wire  [15:0]  GTHE4_CHANNEL_DRPDO_IN, 
  output  wire          GTHE4_GTRXRESET_OUT,
  output  wire          GTHE4_RXPMARESET_OUT,
  output  wire          GTHE4_RXCDRHOLD_OUT,
  input   wire          GTHE4_RXPMARESETDONE_IN,
  output  wire          DONE
);

generate if (CPLL_CAL_ONLY_TX == 1)
begin: gen_cal_rx_dis
  assign GTHE4_RXPROGDIVRESET_OUT   =   USER_RXPROGDIVRESET_IN;
  assign GTHE4_GTRXRESET_OUT        =   USER_GTRXRESET_IN; 
  assign GTHE4_RXOUTCLKSEL_OUT      =   USER_RXOUTCLKSEL_IN;
  assign GTHE4_RXCDRHOLD_OUT        =   USER_RXCDRHOLD_IN;
  assign GTHE4_RXPMARESET_OUT       =   USER_RXPMARESET_IN; 
  assign USER_RXPRGDIVRESETDONE_OUT =   GTHE4_RXPRGDIVRESETDONE_IN;
  assign USER_RXPMARESETDONE_OUT    =   GTHE4_RXPMARESETDONE_IN; 
  assign  CPLL_CAL_DONE              =  1'd0;
  assign  CPLL_CAL_FAIL              =  1'd0;
  assign  DONE                       =  1'd1;
  assign  GTHE4_CHANNEL_DRPEN_OUT    =  1'd0;
  assign  GTHE4_CHANNEL_DRPWE_OUT    =  1'd0;
  assign  GTHE4_CPLLPD_OUT           =  1'd0;
  assign  GTHE4_CPLLRESET_OUT        =  1'd0;
  assign  DEBUG_OUT                  = 16'd0;
  assign  GTHE4_CHANNEL_DRPDI_OUT    = 16'd0;
  assign  CAL_FREQ_CNT               = 18'd0;
  assign  GTHE4_CHANNEL_DRPADDR_OUT  = 10'd0;

  always @(posedge CLK_IN) begin
    if(RESET_IN)
    	USER_CPLLLOCK_OUT <= 1'b0;
    else
    	USER_CPLLLOCK_OUT <= 1'b0;
  end

end
else
begin: gen_cal_rx_en

  //DRP FSM
  localparam DRP_WAIT      = 0;
  localparam DRP_READ      = 1;
  localparam DRP_READ_ACK  = 2;
  localparam DRP_MODIFY    = 3;
  localparam DRP_WRITE     = 4;
  localparam DRP_WRITE_ACK = 5;
  localparam DRP_DONE      = 6;

  localparam RESET                = 0;
  localparam READ_X114            = 1;
  localparam CHECK_X114_STATUS    = 2;
  localparam READ_PROGDIV_CFG     = 3;
  localparam SAVE_PROGDIV_CFG     = 4;
  localparam MODIFY_PROGDIV       = 5; 
  localparam MODIFY_RXOUTCLK_SEL  = 6;
  localparam ASSERT_RXCDRHOLD     = 7;
  localparam ASSERT_CPLLPD        = 8;
  localparam DEASSERT_CPLLPD      = 9;
  localparam ASSERT_CPLLRESET     = 10;
  localparam DEASSERT_CPLLRESET   = 11;
  localparam WAIT_GTCPLLLOCK      = 12;
  localparam ASSERT_GTRXRESET     = 13;
  localparam WAIT_RXPMARESETDONE  = 14;
  localparam WAIT_RXPMARESETDONE_DEASSERT = 15; 
  localparam WAIT_RXPMARESETDONE_2        = 16;
  localparam ASSERT_PROGDIVRESET  = 17;
  localparam WAIT_PRGDIVRESETDONE = 18;
  localparam CHECK_FREQ           = 19;
  localparam RESTORE_READ_X114    = 20; 
  localparam RESTORE_PROGDIV      = 21;
  localparam CLEAR_FLAG_x114      = 22;
  localparam WAIT_GTCPLLLOCK2     = 23;
  localparam ASSERT_PROGDIVRESET2 = 24;
  localparam WAIT_PRGDIVRESETDONE2= 25;
  localparam CAL_FAIL             = 26;
  localparam CAL_DONE             = 27;
  
  reg [31:0] cpll_cal_state = 31'd0;
  wire [4:0] cpll_cal_state_bin;
  reg [6:0] drp_state = 7'd1;
  wire drp_done;
  reg [9:0] daddr = 10'd0;
  reg [15:0] di = 16'd0;
  wire drdy;
  wire [15:0] dout;
  reg den = 1'b0;
  reg dwe = 1'b0;
  reg wr = 1'b0;
  reg rd = 1'b0;
  reg [15:0] di_msk;
  reg [15:0] mask;
  reg [24:0] wait_ctr;
  reg [3:0] repeat_ctr;
  reg [15:0] progdiv_cfg_store = 16'd0;
  reg mask_user_in = 1'b0;
  reg cpllreset_int = 1'b0;
  reg cpllpd_int = 1'b0;
  reg rxprogdivreset_int = 1'b0;
  reg rxcdrhold_int = 1'b0; 
  reg gtrxreset_int = 1'b0;
  reg [2:0] rxoutclksel_int = 3'b000;
  reg cal_fail_store = 1'b0;
  reg status_store = 1'b0;
  wire den_i; 
  wire dwe_i;
  
  //All these need to be based on CLK_IN frequency (free_run) 
  localparam [24:0] SYNTH_WAIT_ASSERT_CPLLRESET = (1000 * C_FREERUN_FREQUENCY );  // 1 ms
  localparam [24:0] SYNTH_WAIT_CPLLLOCK = (1000 * C_FREERUN_FREQUENCY );         // 1 ms 
  localparam [24:0] SYNTH_WAIT_DEASSERT_CPLLRESET = (100 * C_FREERUN_FREQUENCY );   // 100 us 
  localparam [24:0] SYNTH_WAIT_ASSERT_PROGDIVRESET = C_FREERUN_FREQUENCY ;   // 1 us 

  localparam [24:0] SIM_WAIT_ASSERT_CPLLRESET = SYNTH_WAIT_ASSERT_CPLLRESET/10; 
  localparam [24:0] SIM_WAIT_CPLLLOCK = SYNTH_WAIT_CPLLLOCK/10;
  localparam [24:0] SIM_WAIT_DEASSERT_CPLLRESET = SYNTH_WAIT_DEASSERT_CPLLRESET/10;  
  localparam [24:0] SIM_WAIT_ASSERT_PROGDIVRESET = SYNTH_WAIT_ASSERT_PROGDIVRESET/10;
  
  localparam [40:1] SIM_RESET_SPEEDUP_REG = SIM_RESET_SPEEDUP;
  localparam [4:0]  WAIT_WIDTH_PROGDIVRESET = 5'd25; // >= 100 ns
  localparam [24:0] WAIT_ASSERT_CPLLRESET =
    //pragma translate_off
    (SIM_RESET_SPEEDUP_REG == "TRUE") ? SIM_WAIT_ASSERT_CPLLRESET :
    //pragma translate_on
                                        SYNTH_WAIT_ASSERT_CPLLRESET;
  localparam [4:0]  WAIT_ASSERT_CPLLPD = 5'd25;  // >= 100 ns
  localparam [24:0] WAIT_DEASSERT_CPLLRESET =  
    //pragma translate_off
    (SIM_RESET_SPEEDUP_REG == "TRUE") ? SIM_WAIT_DEASSERT_CPLLRESET :
    //pragma translate_on
                                        SYNTH_WAIT_DEASSERT_CPLLRESET;
  localparam [24:0] WAIT_CPLLLOCK = 
    //pragma translate_off
    (SIM_RESET_SPEEDUP_REG == "TRUE") ? SIM_WAIT_CPLLLOCK :
    //pragma translate_on
                                        SYNTH_WAIT_CPLLLOCK;
  
  localparam [24:0] WAIT_ASSERT_PROGDIVRESET = 
    //pragma translate_off
    (SIM_RESET_SPEEDUP_REG == "TRUE") ? SIM_WAIT_ASSERT_PROGDIVRESET :
    //pragma translate_on
                                        SYNTH_WAIT_ASSERT_PROGDIVRESET;  


  localparam [15:0] MOD_PROGDIV_CFG = 16'hE062; //divider 20
  localparam [2:0]  MOD_RXOUTCLK_SEL = 3'b101;
  localparam [9:0]  ADDR_RX_PROGDIV_CFG = 10'h0C6; 
  localparam [9:0]  ADDR_X114 = 10'h114;

  // Drive RXOUTCLK with BUFG_GT-buffered source clock, divider = 1
  wire rxoutclkmon;
  //assign rxoutclkmon = GTHE4_RXOUTCLK_IN;
  BUFG_GT bufg_gt_rxoutclkmon_inst (
    .CE      (USER_RXOUTCLK_BUFG_CE_IN),
    .CEMASK  (1'b1),
    .CLR     (USER_RXOUTCLK_BUFG_CLR_IN),
    .CLRMASK (1'b1),
    .DIV     (3'b000),
    .I       (GTHE4_RXOUTCLK_IN),
    .O       (rxoutclkmon)
  );

  wire gthe4_cplllock_sync;
  gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_cplllock_inst (
    .clk_in (CLK_IN),
    .i_in   (GTHE4_CPLLLOCK_IN),
    .o_out  (gthe4_cplllock_sync)
  );

  wire gthe4_rxpmaresetdone_sync; 
  gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_rxpmaresetdone_inst (
    .clk_in (CLK_IN),
    .i_in   (GTHE4_RXPMARESETDONE_IN),
    .o_out  (gthe4_rxpmaresetdone_sync)
  );
  
  wire gthe4_rxprgdivresetdone_sync; 
  gtwizard_ultrascale_v1_7_18_bit_synchronizer bit_synchronizer_rxprgdivresetdone_inst (
    .clk_in (CLK_IN),
    .i_in   (GTHE4_RXPRGDIVRESETDONE_IN),
    .o_out  (gthe4_rxprgdivresetdone_sync)
  );  

  assign GTHE4_CPLLRESET_OUT = cpllreset_int;
  assign GTHE4_CPLLPD_OUT = cpllpd_int;

  always @(posedge CLK_IN) begin
    if (mask_user_in | cpll_cal_state[CAL_FAIL] | cpll_cal_state[RESET] | RESET_IN)
      USER_CPLLLOCK_OUT <= 1'b0;
    else
      USER_CPLLLOCK_OUT <= gthe4_cplllock_sync;
  end

  assign GTHE4_RXPROGDIVRESET_OUT = mask_user_in ? rxprogdivreset_int : USER_RXPROGDIVRESET_IN;
  assign GTHE4_GTRXRESET_OUT = mask_user_in ? gtrxreset_int : USER_GTRXRESET_IN; 
  assign GTHE4_RXOUTCLKSEL_OUT = mask_user_in ? rxoutclksel_int : USER_RXOUTCLKSEL_IN;
  assign GTHE4_RXCDRHOLD_OUT = mask_user_in ? rxcdrhold_int : USER_RXCDRHOLD_IN;
  assign GTHE4_RXPMARESET_OUT = mask_user_in ? 1'b0 : USER_RXPMARESET_IN; 
  assign USER_RXPRGDIVRESETDONE_OUT = mask_user_in ? 1'b0 : GTHE4_RXPRGDIVRESETDONE_IN;
  assign USER_RXPMARESETDONE_OUT = mask_user_in ? 1'b0 : GTHE4_RXPMARESETDONE_IN; 

  // frequency counter for rxoutclk
  wire [17:0] rxoutclk_freq_cnt;
  reg freq_counter_rst = 1'b1;
  wire freq_cnt_done;
  gtwizard_ultrascale_v1_7_18_gthe4_cpll_cal_freq_counter U_RXOUTCLK_FREQ_COUNTER
  (
    .freq_cnt_o(rxoutclk_freq_cnt),
    .done_o(freq_cnt_done),
    .rst_i(freq_counter_rst),
    .test_term_cnt_i(FREQ_COUNT_WINDOW_IN),
    .ref_clk_i(CLK_IN),
    .test_clk_i(rxoutclkmon)
  );

  //Debug signals
  assign DEBUG_OUT = {cpllreset_int,cpllpd_int,gthe4_cplllock_sync,1'b0,freq_cnt_done,freq_counter_rst,mask_user_in,cpll_cal_state_bin,repeat_ctr};
  assign CPLL_CAL_FAIL = cpll_cal_state[CAL_FAIL];
  assign CPLL_CAL_DONE = cpll_cal_state[CAL_DONE];
  assign CAL_FREQ_CNT = rxoutclk_freq_cnt;
  assign DONE = cpll_cal_state[CAL_DONE] | cpll_cal_state[RESET];

  //pragma translate_off
  if (C_SIM_CPLL_CAL_BYPASS == 1'b1)
  begin: gen_sim_cpll_cal_bypass_gthe4
    //CPLL CAL FSM for simulation
    always @(posedge CLK_IN) begin
      if (RESET_IN) begin
        cpll_cal_state <= 0;
        cpll_cal_state[RESET] <= 1'b1;
        cpllreset_int <= 1'b0;
        cpllpd_int <= 1'b0;
        rxprogdivreset_int <= 1'b0;
        mask_user_in <= 1'b0;
        wr <= 1'b0;
        rd <= 1'b0;
        rxcdrhold_int <= 1'b0;
        gtrxreset_int <= 1'b0;
      end
      else begin
        cpll_cal_state <= 0;
        case(1'b1) // synthesis parallel_case full_case
          cpll_cal_state[RESET]: 
          begin
            wait_ctr <= 25'd0;
            repeat_ctr <= 4'd0;
            mask_user_in <= 1'b1;
            di_msk <= 16'b0000_0000_0000_0000;
            cpll_cal_state[READ_X114] <= 1'b1;
          end
          
          cpll_cal_state[READ_X114]:
          begin
            mask_user_in <= 1'b1;
            rd <= 1'b1;
            if (drp_done) begin
              rd <= 1'b0;
              status_store <= dout[15];
              cpll_cal_state[CHECK_X114_STATUS] <= 1'b1;
            end
            else
              cpll_cal_state[READ_X114] <= 1'b1;
          end
          
          cpll_cal_state[CHECK_X114_STATUS]:
          begin 
            if (status_store)
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1;
            else 
              cpll_cal_state[READ_PROGDIV_CFG] <= 1'b1;  
          end
          
          cpll_cal_state[READ_PROGDIV_CFG]:
          begin
            rd <= 1'b1;
            if (drp_done) begin
              rd <= 1'b0;
              progdiv_cfg_store <= {1'b1,dout[14:0]};
              cpll_cal_state[SAVE_PROGDIV_CFG] <= 1'b1;
            end
            else begin
              cpll_cal_state[READ_PROGDIV_CFG] <= 1'b1;
            end
          end
          
          cpll_cal_state[SAVE_PROGDIV_CFG]:
          begin 
            wr <= 1'b1;
            if (drp_done) begin
              wr <= 1'b0;
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1; 
            end
            else begin
              cpll_cal_state[SAVE_PROGDIV_CFG] <= 1'b1;
            end
            di_msk <= progdiv_cfg_store;
          end          
          
          cpll_cal_state[MODIFY_PROGDIV]:
          begin
            wr <= 1'b1;
            if (drp_done) begin
              wr <= 1'b0;
              cpll_cal_state[MODIFY_RXOUTCLK_SEL] <= 1'b1;
            end
            else begin
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1;
              wait_ctr <= 25'd0;
            end
            di_msk<= MOD_PROGDIV_CFG;
          end
          
          cpll_cal_state[MODIFY_RXOUTCLK_SEL]:
          begin
            cpll_cal_state[ASSERT_RXCDRHOLD] <= 1'b1;
          end
          
          cpll_cal_state[ASSERT_RXCDRHOLD]:
          begin
            rxcdrhold_int <= 1'b1;
            cpll_cal_state[ASSERT_CPLLRESET] <= 1'b1;
          end
          
          cpll_cal_state[ASSERT_CPLLRESET]:
          begin
            cpllreset_int <= 1'b1;
            freq_counter_rst <= 1'b1;
            cpll_cal_state[DEASSERT_CPLLRESET] <= 1'b1;
            wait_ctr <= 25'd0;
          end
          
          cpll_cal_state[DEASSERT_CPLLRESET]:
          begin
            if (wait_ctr < WAIT_DEASSERT_CPLLRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              cpll_cal_state[DEASSERT_CPLLRESET] <= 1'b1;
            end
            else begin
              cpllreset_int <= 1'b0;
              cpll_cal_state[WAIT_GTCPLLLOCK] <= 1'b1;
              wait_ctr <= 16'd0;
            end
          end
          
          cpll_cal_state[WAIT_GTCPLLLOCK]:
          begin
            if(!gthe4_cplllock_sync) begin
              cpll_cal_state[WAIT_GTCPLLLOCK] <= 1'b1;
            end
            else begin
              cpll_cal_state[ASSERT_GTRXRESET] <= 1'b1;
            end
          end
          
          cpll_cal_state[ASSERT_GTRXRESET]:
          begin
            if (wait_ctr < WAIT_WIDTH_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              gtrxreset_int <= 1'b1;
              cpll_cal_state[ASSERT_GTRXRESET] <= 1'b1;
            end
            else begin
              gtrxreset_int <= 1'b0;
              cpll_cal_state[WAIT_RXPMARESETDONE] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end

          cpll_cal_state[WAIT_RXPMARESETDONE]:
          begin
            if (gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE] <= 1'b1;
            end 
          end  

          cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT]:
          begin
            if (!gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[WAIT_RXPMARESETDONE_2] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT] <= 1'b1;
            end 
          end  
          
          cpll_cal_state[WAIT_RXPMARESETDONE_2]:
          begin
            if (gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[ASSERT_PROGDIVRESET] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE_2] <= 1'b1;
            end 
          end    
          
          cpll_cal_state[ASSERT_PROGDIVRESET]:
          begin
            if (wait_ctr < WAIT_ASSERT_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              rxprogdivreset_int <= 1'b1;
              cpll_cal_state[ASSERT_PROGDIVRESET] <= 1'b1;
            end
            else begin
              rxprogdivreset_int <= 1'b0;
              cpll_cal_state[WAIT_PRGDIVRESETDONE] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[WAIT_PRGDIVRESETDONE]:
          begin
            if (gthe4_rxprgdivresetdone_sync) begin
              cpll_cal_state[CHECK_FREQ] <= 1'b1;
              freq_counter_rst <= 1'b0;
            end
            else begin
              cpll_cal_state[WAIT_PRGDIVRESETDONE] <= 1'b1;
            end
          end
          
          cpll_cal_state[CHECK_FREQ]:
          begin
            if(freq_cnt_done) begin
              if ((rxoutclk_freq_cnt >= (RXOUTCLK_PERIOD_IN - CNT_TOL_IN)) & (rxoutclk_freq_cnt <= (RXOUTCLK_PERIOD_IN + CNT_TOL_IN))) begin
                cpll_cal_state[RESTORE_READ_X114] <= 1'b1;
                cal_fail_store <= 1'b0;
              end
              else begin
                if (repeat_ctr < REPEAT_RESET_LIMIT) begin
                  cpll_cal_state[ASSERT_CPLLRESET] <= 1'b1;
                  repeat_ctr <= repeat_ctr + 1'b1;
                end
                else begin
                  cpll_cal_state[RESTORE_READ_X114] <= 1'b1;
                  cal_fail_store <= 1'b1;
                end
              end
            end
            else
              cpll_cal_state[CHECK_FREQ] <= 1'b1;
          end
          
          cpll_cal_state[RESTORE_READ_X114]: 
          begin
            rd <= 1'b1; 
            if (drp_done) begin
              rd <= 1'b0; 
              progdiv_cfg_store <= dout; 
              cpll_cal_state[RESTORE_PROGDIV] <= 1'b1; 
            end else begin
              cpll_cal_state[RESTORE_READ_X114] <= 1'b1; 
            end 
          end
          
          cpll_cal_state[RESTORE_PROGDIV]:
          begin
            wr <= 1'b1; 
            if (drp_done) begin
              wr <= 1'b0; 
              cpll_cal_state[CLEAR_FLAG_x114] <= 1'b1;
            end
            else begin
              cpll_cal_state[RESTORE_PROGDIV] <= 1'b1;
            end
            di_msk <= progdiv_cfg_store;
          end
          
          cpll_cal_state[CLEAR_FLAG_x114]: 
          begin
            //set [15] to 0
            wr <= 1'b1; 
            if (drp_done) begin 
              wr <= 1'b0; 
              cpll_cal_state[WAIT_GTCPLLLOCK2] <= 1'b1; 
            end 
            else begin 
              cpll_cal_state[CLEAR_FLAG_x114] <= 1'b1; 
            end
            // clear
            di_msk <= 16'h0000;
          end 
         
          cpll_cal_state[WAIT_GTCPLLLOCK2]:
          begin
            cpll_cal_state[ASSERT_PROGDIVRESET2] <= 1'b1;
            if(!gthe4_cplllock_sync)
              cal_fail_store <= 1'b1;
            else
              cal_fail_store <= cal_fail_store;
          end
          
          cpll_cal_state[ASSERT_PROGDIVRESET2]:
          begin
            if (wait_ctr < WAIT_WIDTH_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              rxprogdivreset_int <= 1'b1;
              cpll_cal_state[ASSERT_PROGDIVRESET2] <= 1'b1;
            end
            else begin
              rxprogdivreset_int <= 1'b0;
              cpll_cal_state[WAIT_PRGDIVRESETDONE2] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[WAIT_PRGDIVRESETDONE2]:
          begin
            if (gthe4_rxprgdivresetdone_sync) begin
              if (cal_fail_store)
                cpll_cal_state[CAL_FAIL] <= 1'b1;
              else
                cpll_cal_state[CAL_DONE] <= 1'b1;
              end
            else begin
              cpll_cal_state[WAIT_PRGDIVRESETDONE2] <= 1'b1;
            end
          end
          
          cpll_cal_state[CAL_FAIL]:
          begin
            cpll_cal_state[CAL_FAIL] <= 1'b1;
            mask_user_in <= 1'b0;
          end
          
          cpll_cal_state[CAL_DONE]:
          begin
            cpll_cal_state[CAL_DONE] <= 1'b1;
            mask_user_in <= 1'b0;
          end
        endcase
      end
    end // always block

  end
  else
  begin: gen_cpll_cal_gthe4_rx
  //pragma translate_on
    //CPLL CAL FSM
    always @(posedge CLK_IN) begin
      if (RESET_IN) begin
        cpll_cal_state <= 0;
        cpll_cal_state[RESET] <= 1'b1;
        cpllreset_int <= 1'b0;
        cpllpd_int <= 1'b0;
        rxprogdivreset_int <= 1'b0;
        mask_user_in <= 1'b0;
        wr <= 1'b0;
        rd <= 1'b0;
        rxcdrhold_int <= 1'b0;
        gtrxreset_int <= 1'b0;        
      end
      else begin
        cpll_cal_state <= 0;
        case(1'b1) // synthesis parallel_case full_case
          cpll_cal_state[RESET]: 
          begin
            wait_ctr <= 25'd0;
            repeat_ctr <= 4'd0;
            mask_user_in <= 1'b1;
            di_msk <= 16'b0000_0000_0000_0000;
            cpll_cal_state[READ_X114] <= 1'b1;
          end
          
          cpll_cal_state[READ_X114]:
          begin
            mask_user_in <= 1'b1;
            rd <= 1'b1;
            if (drp_done) begin
              rd <= 1'b0;
              status_store <= dout[15];
              cpll_cal_state[CHECK_X114_STATUS] <= 1'b1;
            end
            else
              cpll_cal_state[READ_X114] <= 1'b1;
          end
          
          cpll_cal_state[CHECK_X114_STATUS]:
          begin 
            if (status_store)
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1;
            else 
              cpll_cal_state[READ_PROGDIV_CFG] <= 1'b1;  
          end
          
          cpll_cal_state[READ_PROGDIV_CFG]:
          begin
            rd <= 1'b1;
            if (drp_done) begin
              rd <= 1'b0;
              progdiv_cfg_store <= {1'b1,dout[14:0]};
              cpll_cal_state[SAVE_PROGDIV_CFG] <= 1'b1;
            end
            else begin
              cpll_cal_state[READ_PROGDIV_CFG] <= 1'b1;
            end
          end
          
          cpll_cal_state[SAVE_PROGDIV_CFG]:
          begin 
            wr <= 1'b1;
            if (drp_done) begin
              wr <= 1'b0;
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1; 
            end
            else begin
              cpll_cal_state[SAVE_PROGDIV_CFG] <= 1'b1;
            end
            di_msk <= progdiv_cfg_store;
          end          
          
          cpll_cal_state[MODIFY_PROGDIV]:
          begin
            wr <= 1'b1;
            if (drp_done) begin
              wr <= 1'b0;
              cpll_cal_state[MODIFY_RXOUTCLK_SEL] <= 1'b1;
            end
            else begin
              cpll_cal_state[MODIFY_PROGDIV] <= 1'b1;
              wait_ctr <= 25'd0;
            end
            di_msk<= MOD_PROGDIV_CFG;
          end
          
          cpll_cal_state[MODIFY_RXOUTCLK_SEL]:
          begin
            cpll_cal_state[ASSERT_RXCDRHOLD] <= 1'b1;
          end
          
          cpll_cal_state[ASSERT_RXCDRHOLD]:
          begin
            rxcdrhold_int <= 1'b1;
            cpll_cal_state[ASSERT_CPLLPD] <= 1'b1;
          end
          
          cpll_cal_state[ASSERT_CPLLPD]:
          begin
            if (wait_ctr < WAIT_ASSERT_CPLLPD) begin
              wait_ctr <= wait_ctr + 1'b1;
              cpll_cal_state[ASSERT_CPLLPD] <= 1'b1;                 
            end
            else begin
              cpllpd_int <= 1'b1;
              cpll_cal_state[DEASSERT_CPLLPD] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[DEASSERT_CPLLPD]:
          begin
            if (wait_ctr < SYNTH_WAIT_DEASSERT_CPLLRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              cpll_cal_state[DEASSERT_CPLLPD] <= 1'b1;
            end
            else begin
              cpllpd_int <= 1'b0;
              cpll_cal_state[ASSERT_CPLLRESET] <= 1'b1;
              wait_ctr <= 16'd0;
              freq_counter_rst <= 1'b1;
            end
          end 
          
          cpll_cal_state[ASSERT_CPLLRESET]:
          begin
            if (wait_ctr < WAIT_ASSERT_CPLLRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              cpll_cal_state[ASSERT_CPLLRESET] <= 1'b1;
            end
            else begin
              cpllreset_int <= 1'b1;
              freq_counter_rst <= 1'b1;
              cpll_cal_state[DEASSERT_CPLLRESET] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[DEASSERT_CPLLRESET]:
          begin
            if (wait_ctr < WAIT_DEASSERT_CPLLRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              cpll_cal_state[DEASSERT_CPLLRESET] <= 1'b1;
            end
            else begin
              cpllreset_int <= 1'b0;
              cpll_cal_state[WAIT_GTCPLLLOCK] <= 1'b1;
              wait_ctr <= 16'd0;
            end
          end
          
          cpll_cal_state[WAIT_GTCPLLLOCK]:
          begin
            if(wait_ctr < WAIT_CPLLLOCK) begin
              cpll_cal_state[WAIT_GTCPLLLOCK] <= 1'b1;
              wait_ctr <= wait_ctr + 1'b1;
            end
            else begin
              cpll_cal_state[ASSERT_GTRXRESET] <= 1'b1;
              wait_ctr <= 16'd0;
            end
          end
          
          cpll_cal_state[ASSERT_GTRXRESET]:
          begin
            if (wait_ctr < WAIT_WIDTH_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              gtrxreset_int <= 1'b1;
              cpll_cal_state[ASSERT_GTRXRESET] <= 1'b1;
            end
            else begin
              gtrxreset_int <= 1'b0;
              cpll_cal_state[WAIT_RXPMARESETDONE] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end

          cpll_cal_state[WAIT_RXPMARESETDONE]:
          begin
            if (gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE] <= 1'b1;
            end 
          end  
          
          cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT]:
          begin
            if (!gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[WAIT_RXPMARESETDONE_2] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE_DEASSERT] <= 1'b1;
            end 
          end  
          
          cpll_cal_state[WAIT_RXPMARESETDONE_2]:
          begin
            if (gthe4_rxpmaresetdone_sync) begin
              cpll_cal_state[ASSERT_PROGDIVRESET] <= 1'b1;
            end
            else begin 
              cpll_cal_state[WAIT_RXPMARESETDONE_2] <= 1'b1;
            end 
          end    
          
          cpll_cal_state[ASSERT_PROGDIVRESET]:
          begin
            if (wait_ctr < WAIT_ASSERT_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              rxprogdivreset_int <= 1'b1;
              cpll_cal_state[ASSERT_PROGDIVRESET] <= 1'b1;
            end
            else begin
              rxprogdivreset_int <= 1'b0;
              cpll_cal_state[WAIT_PRGDIVRESETDONE] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[WAIT_PRGDIVRESETDONE]:
          begin
            if (gthe4_rxprgdivresetdone_sync) begin
              cpll_cal_state[CHECK_FREQ] <= 1'b1;
              freq_counter_rst <= 1'b0;
            end
            else begin
              cpll_cal_state[WAIT_PRGDIVRESETDONE] <= 1'b1;
            end
          end
          
          cpll_cal_state[CHECK_FREQ]:
          begin
            if(freq_cnt_done) begin
              if ((rxoutclk_freq_cnt >= (RXOUTCLK_PERIOD_IN - CNT_TOL_IN)) & (rxoutclk_freq_cnt <= (RXOUTCLK_PERIOD_IN + CNT_TOL_IN))) begin
                cpll_cal_state[RESTORE_READ_X114] <= 1'b1;
                cal_fail_store <= 1'b0;
              end
              else begin
                if (repeat_ctr < REPEAT_RESET_LIMIT) begin
                  cpll_cal_state[ASSERT_CPLLPD] <= 1'b1;
                  repeat_ctr <= repeat_ctr + 1'b1;
                end
                else begin
                  cpll_cal_state[RESTORE_READ_X114] <= 1'b1;
                  cal_fail_store <= 1'b1;
                end
              end
            end
            else
              cpll_cal_state[CHECK_FREQ] <= 1'b1;
          end
          
          cpll_cal_state[RESTORE_READ_X114]: 
          begin
            rd <= 1'b1; 
            if (drp_done) begin
              rd <= 1'b0; 
              progdiv_cfg_store <= dout; 
              cpll_cal_state[RESTORE_PROGDIV] <= 1'b1; 
            end else begin
              cpll_cal_state[RESTORE_READ_X114] <= 1'b1; 
            end 
          end
          
          cpll_cal_state[RESTORE_PROGDIV]:
          begin
            wr <= 1'b1; 
            if (drp_done) begin
              wr <= 1'b0; 
              cpll_cal_state[CLEAR_FLAG_x114] <= 1'b1;
            end
            else begin
              cpll_cal_state[RESTORE_PROGDIV] <= 1'b1;
            end
            di_msk <= progdiv_cfg_store;
          end
          
          cpll_cal_state[CLEAR_FLAG_x114]: 
          begin
            //set [15] to 0
            wr <= 1'b1; 
            if (drp_done) begin 
              wr <= 1'b0; 
              cpll_cal_state[WAIT_GTCPLLLOCK2] <= 1'b1; 
            end 
            else begin 
              cpll_cal_state[CLEAR_FLAG_x114] <= 1'b1; 
            end
            // clear
            di_msk <= 16'h0000;
          end 
          
          cpll_cal_state[WAIT_GTCPLLLOCK2]:
          begin
            cpll_cal_state[ASSERT_PROGDIVRESET2] <= 1'b1;
            if(!gthe4_cplllock_sync)
              cal_fail_store <= 1'b1;
            else
              cal_fail_store <= cal_fail_store;
          end
          
          cpll_cal_state[ASSERT_PROGDIVRESET2]:
          begin
            if (wait_ctr < WAIT_WIDTH_PROGDIVRESET) begin
              wait_ctr <= wait_ctr + 1'b1;
              rxprogdivreset_int <= 1'b1;
              cpll_cal_state[ASSERT_PROGDIVRESET2] <= 1'b1;
            end
            else begin
              rxprogdivreset_int <= 1'b0;
              cpll_cal_state[WAIT_PRGDIVRESETDONE2] <= 1'b1;
              wait_ctr <= 25'd0;
            end
          end
          
          cpll_cal_state[WAIT_PRGDIVRESETDONE2]:
          begin
            if (gthe4_rxprgdivresetdone_sync) begin
              if (cal_fail_store)
                cpll_cal_state[CAL_FAIL] <= 1'b1;
              else
                cpll_cal_state[CAL_DONE] <= 1'b1;
              end
            else begin
              cpll_cal_state[WAIT_PRGDIVRESETDONE2] <= 1'b1;
            end
          end
          
          cpll_cal_state[CAL_FAIL]:
          begin
            rxcdrhold_int <= 1'b0;
            cpll_cal_state[CAL_FAIL] <= 1'b1;
            mask_user_in <= 1'b0;
          end
          
          cpll_cal_state[CAL_DONE]:
          begin
            rxcdrhold_int <= 1'b0;          
            cpll_cal_state[CAL_DONE] <= 1'b1;
            mask_user_in <= 1'b0;
          end
        endcase
      end
    end // always block
  
  //pragma translate_off
  end
  //pragma translate_on

  always @(posedge CLK_IN) begin
    if (cpll_cal_state[RESET])
      rxoutclksel_int <= 3'b0;
    else if (cpll_cal_state[MODIFY_RXOUTCLK_SEL])
      rxoutclksel_int <= MOD_RXOUTCLK_SEL;
    else 
      rxoutclksel_int <= rxoutclksel_int;
  end

  always @(posedge CLK_IN) begin
    if (cpll_cal_state[RESET]) begin
      daddr <= 10'h000;
      mask  <= 16'b1111_1111_1111_1111;
    end
    else if (cpll_cal_state[READ_X114] | cpll_cal_state[SAVE_PROGDIV_CFG] | cpll_cal_state[RESTORE_READ_X114] | cpll_cal_state[CLEAR_FLAG_x114]) begin 
      daddr <= ADDR_X114;
    end
    else if (cpll_cal_state[READ_PROGDIV_CFG] | cpll_cal_state[MODIFY_PROGDIV] | cpll_cal_state[RESTORE_PROGDIV]) begin
      daddr <= ADDR_RX_PROGDIV_CFG;
    end
  end

  assign drp_done = drp_state[DRP_DONE];
  assign GTHE4_CHANNEL_DRPEN_OUT = den;
  assign GTHE4_CHANNEL_DRPWE_OUT = dwe;
  assign GTHE4_CHANNEL_DRPADDR_OUT = daddr;
  assign GTHE4_CHANNEL_DRPDI_OUT = di;
  assign drdy = GTHE4_CHANNEL_DRPRDY_IN; 
  assign dout = GTHE4_CHANNEL_DRPDO_IN; 
  
  always @(posedge CLK_IN) begin
  if (RESET_IN) begin
    den <= 1'b0;
    dwe <= 1'b0;
    di <= 16'h0000;
    drp_state <= 0;
    drp_state[DRP_WAIT] <= 1'b1;
  end
  else begin
    drp_state <= 0;
    case (1'b1) // synthesis parallel_case full_case
        drp_state[DRP_WAIT]:
        begin
          if (rd) drp_state[DRP_READ] <= 1'b1;
          else if (wr) drp_state[DRP_WRITE] <= 1'b1;
          else         drp_state[DRP_WAIT] <= 1'b1;
        end
        drp_state[DRP_READ]:
        begin
          den <= 1'b1;
          drp_state[DRP_READ_ACK] <= 1'b1;
        end
        drp_state[DRP_READ_ACK]:
        begin
          den <= 1'b0;
          if (drdy == 1'b1) begin
            if (rd) drp_state[DRP_DONE] <= 1'b1;
            else    drp_state[DRP_MODIFY] <= 1'b1;
          end
          else      drp_state[DRP_READ_ACK] <= 1'b1;
        end
        drp_state[DRP_MODIFY]:
        begin
          drp_state[DRP_WRITE] <= 1'b1;
        end
        drp_state[DRP_WRITE]:
        begin
          den <= 1'b1;
          dwe <= 1'b1;
          di <= di_msk;
          drp_state[DRP_WRITE_ACK] <= 1'b1;
        end
        drp_state[DRP_WRITE_ACK]:
        begin
          den <= 1'b0;
          dwe <= 1'b0;
          if (drdy == 1'b1) drp_state[DRP_DONE] <= 1'b1;
          else              drp_state[DRP_WRITE_ACK] <= 1'b1;
        end
        drp_state[DRP_DONE]:
        begin
          drp_state[DRP_WAIT] <= 1'b1;
        end
    endcase
  end
  end 

    //debug logic - convert one hot state to binary
  genvar i,j;
    for (j=0; j<5; j=j+1)
    begin : jl
      wire [32-1:0] tmp_mask;
      for (i=0; i<32; i=i+1)
      begin : il
        assign tmp_mask[i] = i[j];
      end
      assign cpll_cal_state_bin[j] = |(tmp_mask & cpll_cal_state);
    end
  
end
endgenerate
endmodule //CPLL_CAL  
