//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_rc_pcie4c_ip_gt_cdr_ctrl_on_eidle.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper
//  Module :  CDR Control Upon EIDLE Detection
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  CDR Control Upon EIDLE Detection Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_gt_cdr_ctrl_on_eidle #
(
    parameter         PHY_GEN12_CDR_CTRL_ON_EIDLE = "FALSE",
    parameter         PHY_GEN34_CDR_CTRL_ON_EIDLE = "FALSE",
    parameter integer PHY_REFCLK_MODE            = 0,
    parameter integer SYNC_STAGE                 = 3,
    parameter integer PHY_REFCLK_FREQ            = 0
)
(
    //-------------------------------------------------------------------------- 
    //  Input Ports
    //-------------------------------------------------------------------------- 
    input                               CDRCTRL_PCLK,
    input                               CDRCTRL_PCLK_RST_N,
    input                               CDRCTRL_CLK,
    input                               CDRCTRL_RST_N,
    input     [ 1:0]                    CDRCTRL_RATE,
    input                               CDRCTRL_RXELECIDLE,
    input                               CDRCTRL_GEN34_EIOS_DET,
    input                               CDRCTRL_RXCDRHOLD_IN,    
    input                               CDRCTRL_RXCDRFREQRESET_IN,
    input                               CDRCTRL_RXRATEDONE,
    
    //-------------------------------------------------------------------------- 
    //  Output Ports
    //-------------------------------------------------------------------------- 
    output                              CDRCTRL_RXCDRFREQRESET_OUT,
    output                              CDRCTRL_RXCDRHOLD_OUT,
    output                              CDRCTRL_RESETOVRD_OUT
);
    //--------------------------------------------------------------------------
    //  Synchronized Signals
    //--------------------------------------------------------------------------                                     
    wire                                gen3or4;
    reg         [ 1:0]                  rate_r;     
    reg         [ 1:0]                  rate_r2;
    wire                                rxelecidle_a;
    reg         [ 1:0]                  rxelecidle_r;
    wire                                gen34_eios_det_a;
    reg         [ 1:0]                  gen34_eios_det_r;
    wire                                rxcdrhold_in_r;
    reg                                 rate_change;
    wire                                rate_change_a;
    
    reg        [6:0]    rxelecidle_cycle_count;
    wire        ctrl_fsm_not_in_solid_deassert;
    //-------------------------------------------------------------------------- 
    //  FSM Signals
    //-------------------------------------------------------------------------- 
    reg [ 2:0] fsm;
    
    reg                                 rxcdrhold = 1'd1;     
    reg        [ 7:0]                   counter_max = 8'd0;
    reg        [ 7:0]                   wait_ctr = 8'd0;
    reg                                 resetovrd = 1'd0;
    reg                                 rxcdrfreqreset = 1'd0;
    
    reg                                 exit = 1'd0;
    wire                                rst_n;

    localparam MAX_COUNT_ENTER = (PHY_REFCLK_FREQ == 2) ? 8'd9 : 
                                 (PHY_REFCLK_FREQ == 1) ? 8'd4  : 8'd3;
    
    localparam MAX_COUNT_EXIT = (PHY_REFCLK_FREQ == 2)  ? 8'd75 : 
                                 (PHY_REFCLK_FREQ == 1) ? 8'd38 : 8'd30;
    
    localparam RXELECIDLE_CYCLE_CNT_MAX = (PHY_REFCLK_MODE == 2)  ? 16 : 
                                          (PHY_REFCLK_MODE == 1) ? 16 : 64;

    assign rst_n = CDRCTRL_RST_N;

    reg [3:0] gen34_eios_det_extend;
    reg [7:0] rate_change_extend = 8'd0;
    reg rxelecidle_int = 0;
    reg gen34_eios_det_pclk;
    reg rate_change_extend_pclk;
    
    always @(posedge CDRCTRL_PCLK) 
    begin
      if (!CDRCTRL_PCLK_RST_N) begin
        gen34_eios_det_extend <= 4'd0;
        gen34_eios_det_pclk <= 1'd0;
      end 
      else begin
        gen34_eios_det_extend <= {gen34_eios_det_extend[2:0],CDRCTRL_GEN34_EIOS_DET};
        gen34_eios_det_pclk <= |gen34_eios_det_extend;
      end
    end
    
    //--------------------------------------------------------------------------------------------------
    //  Input Synchronizer or Pipeline
    //--------------------------------------------------------------------------------------------------
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_gen34          (.CLK (CDRCTRL_CLK), .D (CDRCTRL_RATE[1]),         .Q (gen3or4));
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rxelecidle     (.CLK (CDRCTRL_CLK), .D (CDRCTRL_RXELECIDLE),      .Q (rxelecidle_a));
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_gen34_eios_det (.CLK (CDRCTRL_CLK), .D (gen34_eios_det_pclk),     .Q (gen34_eios_det_a));
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rxcdrreset_in  (.CLK (CDRCTRL_CLK), .D (CDRCTRL_RXCDRHOLD_IN),    .Q (rxcdrhold_in_r));
    
    always @ (posedge CDRCTRL_CLK) 
    begin
      if (!rst_n) begin
        rxelecidle_r <= 2'd3;
        gen34_eios_det_r <= 2'd0;
      end 
      else begin 
        rxelecidle_r <= {rxelecidle_r[0], rxelecidle_a}; 
        gen34_eios_det_r <= {gen34_eios_det_r[0], gen34_eios_det_a}; 
      end
    end 
    
generate
    if (PHY_REFCLK_MODE <= 1) 
    begin : non_sris
    //--------------------------------------------------------------------------
    //  FSM Encoding
    //-------------------------------------------------------------------------- 
    localparam FSM_IDLE                  = 3'd0;
    localparam FSM_GEN12_RXELECIDLE_EXIT = 3'd1;
    localparam FSM_GEN34_RXELECIDLE_EXIT = 3'd2;

  assign ctrl_fsm_not_in_solid_deassert = (fsm == FSM_IDLE);
    
      always @ (posedge CDRCTRL_CLK) 
      begin 
        if (ctrl_fsm_not_in_solid_deassert) begin
          rxelecidle_cycle_count <= 7'd0;
        end 
        else begin
          if (!rxelecidle_r[1])
            rxelecidle_cycle_count <= rxelecidle_cycle_count + 7'd1;        
          else 
            rxelecidle_cycle_count <= 7'd0;
        end
      end
      
      always @(posedge CDRCTRL_CLK)
      begin 
        if (ctrl_fsm_not_in_solid_deassert) begin
          rxelecidle_int <= 1'b0;
        end 
        else begin
          if (rxelecidle_cycle_count > RXELECIDLE_CYCLE_CNT_MAX)
            rxelecidle_int <= 1'b1;
          else 
            rxelecidle_int <= rxelecidle_int;
        end
      end
    
    //--------------------------------------------------------------------------------------------------
    //  Hold CDR upon EIOS/EIDLE detection FSM
    //--------------------------------------------------------------------------------------------------
      always @ (posedge CDRCTRL_CLK)
      begin

          if (!rst_n)
              begin
              fsm        <= FSM_IDLE;
              rxcdrhold  <= 1'd1;
              end
          else
              begin
              
              case (fsm)
                  
              //------------------------------------------------------------------------------------------
              //  Stay in IDLE state until EIOS/EIDLE rising edge is detected
              //------------------------------------------------------------------------------------------
              FSM_IDLE :
              
                  begin
                 if ((PHY_GEN12_CDR_CTRL_ON_EIDLE == "TRUE") && (!gen3or4) && rxelecidle_r[0])//(!rxelecidle_r[1]&rxelecidle_r[0]))
                      begin
                      fsm       <= FSM_GEN12_RXELECIDLE_EXIT;
                      rxcdrhold <= 1'd1;
                      end
                 else if ((PHY_GEN34_CDR_CTRL_ON_EIDLE == "TRUE") && (gen3or4) && (!gen34_eios_det_r[1]&gen34_eios_det_r[0]))
                      begin
                      fsm       <= FSM_GEN34_RXELECIDLE_EXIT;
                      rxcdrhold <= 1'd1;
                      end
                  else
                      begin
                      fsm       <= FSM_IDLE;
                      rxcdrhold <= 1'd0;
                      end
                  end     
                  
              //------------------------------------------------------------------------------------------
              //  Gen1/Gen2:  Hold RXCDRRESET until RXELECIDLE exit
              //------------------------------------------------------------------------------------------
              FSM_GEN12_RXELECIDLE_EXIT:
              
                  begin
                  if (rxelecidle_int)
                      begin
                      fsm        <= FSM_IDLE;
                      rxcdrhold  <= 1'd0;
                      end
                  else
                      begin
                      fsm        <= FSM_GEN12_RXELECIDLE_EXIT;
                      rxcdrhold  <= 1'd1;
                      end
                  end    
                  
              //------------------------------------------------------------------------------------------
              //  Gen3/Gen4:  Hold RXCDRRESET until RXELECIDLE exit
              //------------------------------------------------------------------------------------------
              FSM_GEN34_RXELECIDLE_EXIT:
              
                  begin
                  if ((!gen34_eios_det_r[0]) & rxelecidle_int)
                      begin
                      fsm        <= FSM_IDLE;
                      rxcdrhold  <= 1'd0;
                      end
                  else
                      begin
                      fsm        <= FSM_GEN34_RXELECIDLE_EXIT;
                      rxcdrhold  <= 1'd1;
                      end
                  end    
                  
              //------------------------------------------------------------------------------------------
              //  Default State
              //------------------------------------------------------------------------------------------
              default :
              
                  begin
                  fsm        <= FSM_IDLE;
                  rxcdrhold <= 1'd0;
                  end

              endcase
              
              end
              
      end
    end 
endgenerate

generate
  if (PHY_REFCLK_MODE == 2) begin : sris
  
    reg [7:0]rx_rate_done_extend = 8'd0;
    reg rx_rate_done_extend_pclk = 1'd0;
    wire rate_done_a;
    reg rate_change_in_prog = 1'd0;
  
    always @(posedge CDRCTRL_PCLK)
    begin
      if (!CDRCTRL_PCLK_RST_N) begin
        rate_r <= 2'd0;
        rate_r2 <= 2'd0;
        rate_change <= 1'b0;
        rate_change_extend_pclk <= 1'd0;
        rate_change_extend <= 7'd0;
        rx_rate_done_extend_pclk <= 1'd0;
        rx_rate_done_extend <= 7'd0;        
      end
      else begin
        rate_r <= CDRCTRL_RATE;
        rate_r2 <= rate_r;

        if (rate_r2 != rate_r) 
          rate_change <= 1'b1;
        else
          rate_change <= 1'b0;
          
        rate_change_extend <= {rate_change_extend[6:0],rate_change};
        rate_change_extend_pclk <= |rate_change_extend;  

        rx_rate_done_extend <= {rx_rate_done_extend[6:0],CDRCTRL_RXRATEDONE};
        rx_rate_done_extend_pclk <= |rx_rate_done_extend;          
        
      end  
    end
    
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rate_change    (.CLK (CDRCTRL_CLK), .D (rate_change_extend_pclk), .Q (rate_change_a));
    pcie_bridge_rc_pcie4c_ip_sync #(.WIDTH (1), .STAGE (SYNC_STAGE)) sync_rate_done      (.CLK (CDRCTRL_CLK), .D (rx_rate_done_extend_pclk), .Q (rate_done_a));
    
    //--------------------------------------------------------------------------
    //  FSM Encoding
    //-------------------------------------------------------------------------- 
    localparam FSM_IDLE                                 = 3'd0;
    localparam FSM_COUNTER                              = 3'd1;
    localparam FSM_GEN12_RXELECIDLE_EXIT_OR_RATE_CHANGE = 3'd2;
    localparam FSM_GEN34_RXELECIDLE_EXIT_OR_RATE_CHANGE = 3'd3;
    localparam FSM_WAIT_RATE_DONE                       = 3'd4;
    
    //--------------------------------------------------------------------------------------------------
    //  Reset CDR upon EIOS/EIDLE detection FSM
    //--------------------------------------------------------------------------------------------------
      always @ (posedge CDRCTRL_CLK)
      begin

          if (!rst_n)
              begin
              fsm            <= FSM_IDLE;
              resetovrd      <= 1'd0;
              rxcdrfreqreset <= 1'd0;
              wait_ctr       <= 8'd0;
              counter_max    <= 8'd0;
              exit           <= 1'd0;
              rate_change_in_prog <= 1'd0;
              end
          else
              begin
              
              case (fsm)
                  
              //------------------------------------------------------------------------------------------
              //  Stay in IDLE state until EIOS/EIDLE rising edge is detected
              //------------------------------------------------------------------------------------------
              FSM_IDLE :
              
                begin
                exit           <= 1'd0;
                
                counter_max <= MAX_COUNT_ENTER;
                
                 if ((PHY_GEN12_CDR_CTRL_ON_EIDLE == "TRUE") && ((!gen3or4) && (!rxelecidle_r[1]&rxelecidle_r[0])) || (rate_change_in_prog && !rxelecidle_r[0]) )
                      begin
                      fsm        <= FSM_COUNTER;
                      resetovrd  <= 1'd1;
                      rxcdrfreqreset <= 1'd0;
                      end
                 else if ((PHY_GEN34_CDR_CTRL_ON_EIDLE == "TRUE") && (gen3or4) && (!gen34_eios_det_r[1]&gen34_eios_det_r[0]) || (rate_change_in_prog && !rxelecidle_r[0]))
                      begin
                      fsm        <= FSM_COUNTER;
                      resetovrd  <= 1'd1;
                      rxcdrfreqreset <= 1'd0;
                      end
                  else
                      begin
                      fsm       <= FSM_IDLE;
                      resetovrd <= 1'd0;
                      rxcdrfreqreset <= 1'd0;
                      end
                      
                  end     
              
              FSM_COUNTER : 
              
                begin
                  if (wait_ctr < counter_max)
                  begin
                    wait_ctr <= wait_ctr + 1'b1;
                    fsm <= FSM_COUNTER;
                  end
                  else begin
                    wait_ctr <= 8'd0;
                    
                    if (!exit && !gen3or4) begin
                      rxcdrfreqreset <= 1'd1;
                      fsm <= FSM_GEN12_RXELECIDLE_EXIT_OR_RATE_CHANGE;
                    end
                    else if (!exit && gen3or4) begin
                      rxcdrfreqreset <= 1'd1;
                      fsm <= FSM_GEN34_RXELECIDLE_EXIT_OR_RATE_CHANGE;
                    end
                    else if (exit && rate_change_in_prog) begin
                      fsm <= FSM_WAIT_RATE_DONE;
                      resetovrd <= 1'd0;
                    end
                    else begin
                      fsm <= FSM_IDLE;
                      resetovrd <= 1'd0;
                    end
                  end
                end
              
              //------------------------------------------------------------------------------------------
              //  Gen1/Gen2:  Hold RXCDRREQRESET until RXELECIDLE exit or rate change detected
              //------------------------------------------------------------------------------------------
              FSM_GEN12_RXELECIDLE_EXIT_OR_RATE_CHANGE:
              
                  begin
                  
                  exit <= 1'd1;
                  
                  counter_max <= 8'd30;
                  
                  if (!rxelecidle_r[0] || rate_change_a)
                      begin
                      rate_change_in_prog <= rate_change_a;
                      fsm            <= FSM_COUNTER;
                      rxcdrfreqreset <= 1'd0;
                      end
                  else
                      begin
                      fsm        <= FSM_GEN12_RXELECIDLE_EXIT_OR_RATE_CHANGE;
                      end
                  end
                  
              //------------------------------------------------------------------------------------------
              //  Gen3/Gen4:  Hold RXCDRREQRESET until RXELECIDLE exit or rate change detected
              //------------------------------------------------------------------------------------------
              FSM_GEN34_RXELECIDLE_EXIT_OR_RATE_CHANGE:
                  begin 
 
                  exit <= 1'd1;
 
                  counter_max <= MAX_COUNT_EXIT;
                  
                  if (((!gen34_eios_det_r[0]) & (!rxelecidle_r[0])) || rate_change_a)
                      begin
                      rate_change_in_prog <= rate_change_a;
                      fsm            <= FSM_COUNTER;
                      rxcdrfreqreset <= 1'd0;
                      end
                  else
                      begin
                      fsm            <= FSM_GEN34_RXELECIDLE_EXIT_OR_RATE_CHANGE;
                      end
                  end    

              FSM_WAIT_RATE_DONE:
                begin 
                  
                  if (rate_done_a) 
                    fsm <= FSM_IDLE;
                  else 
                    fsm <= FSM_WAIT_RATE_DONE;
               
                end                  
              
              //------------------------------------------------------------------------------------------
              //  Default State
              //------------------------------------------------------------------------------------------
              default :
              
                  begin
                  fsm            <= FSM_IDLE;
                  resetovrd      <= 1'd0;
                  rxcdrfreqreset <= 1'd0;
                  wait_ctr       <= 8'd0;
                  counter_max    <= 8'd0;         
                  exit           <= 1'd0;
                  end

              endcase
              
              end
        end      
      end
endgenerate

//--------------------------------------------------------------------------------------------------
//  HOLD CDR upon EIOS/EIDLE Detection Outputs
//--------------------------------------------------------------------------------------------------
assign CDRCTRL_RXCDRHOLD_OUT = rxcdrhold;

//--------------------------------------------------------------------------------------------------
//  RESET CDR upon EIOS/EIDLE Detection Outputs
//--------------------------------------------------------------------------------------------------
assign CDRCTRL_RXCDRFREQRESET_OUT = rxcdrfreqreset;
assign CDRCTRL_RESETOVRD_OUT = resetovrd;


endmodule
