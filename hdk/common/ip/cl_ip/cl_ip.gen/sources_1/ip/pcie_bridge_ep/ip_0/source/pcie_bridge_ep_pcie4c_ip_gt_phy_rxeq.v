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
// File       : pcie_bridge_ep_pcie4c_ip_gt_phy_rxeq.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper                                                             
//  Module :  RX Equalization                                                                   
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps
 
//--------------------------------------------------------------------------------------------------
//  RX Equalization Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_gt_phy_rxeq #
(
    parameter         PHY_SIM_EN      = "FALSE",   
    parameter integer PHY_LP_TXPRESET = 4,
    parameter integer SYNC_STAGE      = 3                        
)
(
    //-------------------------------------------------------------------------- 
    //  Input Ports
    //-------------------------------------------------------------------------- 
    input                               RXEQ_CLK,                            
    input                               RXEQ_RST_N,
    
    input       [ 1:0]                  RXEQ_CTRL,    
    input       [ 2:0]                  RXEQ_PRESET,
    input       [ 3:0]                  RXEQ_TXPRESET,
    input       [ 5:0]                  RXEQ_TXCOEFF,
    input       [ 5:0]                  RXEQ_LFFS,
    
    //-------------------------------------------------------------------------- 
    //  Output Ports
    //-------------------------------------------------------------------------- 
    output      [2:0]                   phy_rxeq_fsm,
    output                              RXEQ_LFFS_SEL, 
    output      [17:0]                  RXEQ_NEW_TXCOEFF,
    output                              RXEQ_ADAPT_DONE,
    output                              RXEQ_DONE 
);          
    //--------------------------------------------------------------------------
    //  Synchronized Signals
    //--------------------------------------------------------------------------   
    wire        [ 1:0]                  ctrl_r;
    wire        [ 2:0]                  preset_r;
    wire        [ 3:0]                  txpreset_r;
    wire        [ 5:0]                  txcoeff_r;
    wire        [ 5:0]                  lffs_r;

    //--------------------------------------------------------------------------
    //  Internal Signals
    //--------------------------------------------------------------------------
    reg         [ 21:0]                 adapt_cnt;

    //--------------------------------------------------------------------------
    //  FSM Signals                                                            
    //--------------------------------------------------------------------------    
    reg         [ 2:0]                  fsm;
    reg         [ 3:0]                  txpreset;
    reg         [17:0]                  txcoeff;
    reg         [ 1:0]                  txcoeff_cnt;
    reg                                 lffs_sel;
    reg                                 adapt_done;
    reg                                 adapt_2nd;
    reg                                 done;
   
    //----------------------------------------------------------------------------------------------  
    //  FSM Encoding                                                                                  
    //----------------------------------------------------------------------------------------------                                            
    localparam FSM_IDLE    = 3'd0; 
    localparam FSM_PRESET  = 3'd1;                                     
    localparam FSM_TXCOEFF = 3'd2;
    localparam FSM_ADAPT   = 3'd3;
    localparam FSM_DONE    = 3'd4;                                  

    //--------------------------------------------------------------------------
    //  New TX Coefficient
    //--------------------------------------------------------------------------
    localparam NEW_TXCOEFF = (PHY_LP_TXPRESET == 10) ? 18'd10 :
                             (PHY_LP_TXPRESET ==  9) ? 18'd9  :
                             (PHY_LP_TXPRESET ==  8) ? 18'd8  :
                             (PHY_LP_TXPRESET ==  7) ? 18'd7  :
                             (PHY_LP_TXPRESET ==  6) ? 18'd6  :                                                                     
                             (PHY_LP_TXPRESET ==  5) ? 18'd5  :
                             (PHY_LP_TXPRESET ==  4) ? 18'd4  :
                             (PHY_LP_TXPRESET ==  3) ? 18'd3  :
                             (PHY_LP_TXPRESET ==  2) ? 18'd2  :           
                             (PHY_LP_TXPRESET ==  1) ? 18'd1  :
                             (PHY_LP_TXPRESET ==  0) ? 18'd0  : 18'd0;   

    //--------------------------------------------------------------------------
    //  Counters (Simulation vs. Silicon)
    //--------------------------------------------------------------------------
    localparam ADAPT_MAX = (PHY_SIM_EN == "TRUE") ? 22'd1000 : 22'd2000000;
  
    
    
//--------------------------------------------------------------------------------------------------
//  Input Synchronizer
//--------------------------------------------------------------------------------------------------
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (2), .STAGE (SYNC_STAGE)) sync_ctrl     (.CLK (RXEQ_CLK), .D (RXEQ_CTRL),     .Q (ctrl_r));
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (3), .STAGE (SYNC_STAGE)) sync_preset   (.CLK (RXEQ_CLK), .D (RXEQ_PRESET),   .Q (preset_r));
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (4), .STAGE (SYNC_STAGE)) sync_txpreset (.CLK (RXEQ_CLK), .D (RXEQ_TXPRESET), .Q (txpreset_r));    
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (6), .STAGE (SYNC_STAGE)) sync_txcoeff  (.CLK (RXEQ_CLK), .D (RXEQ_TXCOEFF),  .Q (txcoeff_r));
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (6), .STAGE (SYNC_STAGE)) sync_lffs     (.CLK (RXEQ_CLK), .D (RXEQ_LFFS),     .Q (lffs_r));            



//--------------------------------------------------------------------------------------------------
//  Adaptation Counter
//--------------------------------------------------------------------------------------------------
always @ (posedge RXEQ_CLK)
begin

    if (!RXEQ_RST_N)
        begin
        adapt_cnt <= 22'd0;
        end
    else
        begin
        
        //----------------------------------------------------------------------
        //  Increment Counter
        //----------------------------------------------------------------------
        if (fsm == FSM_ADAPT)
            begin
            adapt_cnt <= adapt_cnt + 22'd1;
            end
            
        //----------------------------------------------------------------------
        //  Reset Counter
        //----------------------------------------------------------------------
        else
            begin
            adapt_cnt <= 22'd0;
            end

        end
        
end



//-------------------------------------------------------------------------------------------------- 
//  RX Equalization FSM                                                                              
//-------------------------------------------------------------------------------------------------- 
always @ (posedge RXEQ_CLK)
begin

    if (!RXEQ_RST_N)
        begin
        fsm         <= FSM_IDLE; 
        txpreset    <=  4'd0;
        txcoeff     <= 18'd0;
        txcoeff_cnt <=  2'd0;
        lffs_sel    <=  1'd0;
        adapt_done  <=  1'd0;
        adapt_2nd   <=  1'd1;
        done        <=  1'd0;
        end                    
    else
        begin
        
        case (fsm)
        
        //------------------------------------------------------------------------------------------
        //  Wait until RXEQ_CTRL != 2'b00
        //------------------------------------------------------------------------------------------
        FSM_IDLE :
        
            begin
            
            case (ctrl_r)
                
            //------------------------------------------------------------------
            //  Idle
            //------------------------------------------------------------------
            2'd0 :
            
                begin
                fsm         <= FSM_IDLE; 
                txpreset    <=  4'd0;
                txcoeff     <= 18'd0;
                txcoeff_cnt <=  2'd0;
                lffs_sel    <=  1'd0;
                adapt_done  <=  1'd0;
                adapt_2nd   <= adapt_2nd;
                done        <=  1'd0;
                end      
                
            //------------------------------------------------------------------
            //  Preset
            //------------------------------------------------------------------
            2'd1 :
            
                begin
                fsm         <= FSM_PRESET; 
                txpreset    <=  4'd0;
                txcoeff     <= 18'd0;
                txcoeff_cnt <=  2'd0;
                lffs_sel    <=  1'd0;
                adapt_done  <=  1'd0;
                adapt_2nd   <= adapt_2nd;
                done        <=  1'd0;
                end  
                
            //------------------------------------------------------------------
            //  Coeff : Latch C(-1) and TXPRESET
            //------------------------------------------------------------------
            2'd2 :
            
                begin
                fsm         <= FSM_TXCOEFF; 
                txpreset    <= txpreset_r;
                txcoeff     <= {txcoeff_r, txcoeff[17:6]};
                txcoeff_cnt <= 2'd1;
                lffs_sel    <= 1'd1;
                adapt_done  <= 1'd0;
                adapt_2nd   <= !adapt_2nd;                                      // Toggle adapt done
                done        <= 1'd0;
                end
                
            //------------------------------------------------------------------
            //  Bypass : Latch C(-1) and TXPRESET
            //------------------------------------------------------------------
            2'd3 :
            
                begin
                fsm         <= FSM_TXCOEFF; 
                txpreset    <= txpreset_r;
                txcoeff     <= {txcoeff_r, txcoeff[17:6]};
                txcoeff_cnt <= 2'd1;
                lffs_sel    <= 1'd1;
                adapt_done  <= 1'd0;
                adapt_2nd   <= 1'd1;
                done        <= 1'd0;
                end
                
            //------------------------------------------------------------------
            //  Default
            //------------------------------------------------------------------
            default :
            
                begin
                fsm         <= FSM_IDLE; 
                txpreset    <=  4'd0;
                txcoeff     <= 18'd0;
                txcoeff_cnt <=  2'd0;
                lffs_sel    <=  1'd0;
                adapt_done  <=  1'd0;
                adapt_2nd   <= adapt_2nd;
                done        <=  1'd0;
                end
                
            endcase
            
            end
            
        //------------------------------------------------------------------------------------------
        //  Go to DONE state (RXEQ preset not supported)
        //------------------------------------------------------------------------------------------
        FSM_PRESET :
        
            begin
            fsm         <= FSM_DONE;
            txpreset    <=  4'd0;
            txcoeff     <= 18'd0; 
            txcoeff_cnt <=  2'd0;
            lffs_sel    <=  1'd0;
            adapt_done  <=  1'd0;
            adapt_2nd   <= adapt_2nd;
            done        <=  1'd0; 
            end        
            
        //------------------------------------------------------------------------------------------
        //  Latch C(0) and C(+1)
        //------------------------------------------------------------------------------------------
        FSM_TXCOEFF :
        
            begin
            fsm         <= (txcoeff_cnt == 2'd2) ? FSM_ADAPT : FSM_TXCOEFF;
            txpreset    <= txpreset;
            txcoeff     <= {txcoeff_r, txcoeff[17:6]};
            txcoeff_cnt <= txcoeff_cnt + 2'd1;
            lffs_sel    <= 1'd0;
            adapt_done  <= 1'd0;
            adapt_2nd   <= adapt_2nd;
            done        <= 1'd0; 
            end
   
        //------------------------------------------------------------------------------------------
        //  Wait for adaptation timer 
        //------------------------------------------------------------------------------------------
        FSM_ADAPT :
        
            begin            
            fsm         <= (adapt_cnt == ADAPT_MAX) || (!adapt_2nd) ? FSM_DONE : FSM_ADAPT;
            txpreset    <= txpreset;
            txcoeff     <= txcoeff;
            txcoeff_cnt <= 2'd0;
            lffs_sel    <= 1'd0;
            adapt_done  <= 1'd0;
            adapt_2nd   <= adapt_2nd;
            done        <= 1'd0;
            end             
             
        //------------------------------------------------------------------------------------------
        //  Assert RXEQ_DONE until RXEQ_CTRL == 2'd0
        //------------------------------------------------------------------------------------------
        FSM_DONE :
        
            begin
            fsm         <= (ctrl_r == 2'd0) ? FSM_IDLE : FSM_DONE;
            txpreset    <= txpreset;
            txcoeff     <= txcoeff;
            txcoeff_cnt <= 2'd0;
            lffs_sel    <= ((ctrl_r == 2'd2) || (ctrl_r == 2'd3));
            adapt_done  <= ((ctrl_r == 2'd2) || (ctrl_r == 2'd3)) ? adapt_2nd : 1'd0;
            adapt_2nd   <= adapt_2nd;  
            done        <= 1'd1;
            end        
                          
        //------------------------------------------------------------------------------------------
        //  Default State
        //------------------------------------------------------------------------------------------
        default : 
        
            begin
            fsm         <= FSM_IDLE;
            txpreset    <=  4'd0;
            txcoeff     <= 18'd0;
            txcoeff_cnt <=  2'd0;
            lffs_sel    <=  1'd0;
            adapt_done  <=  1'd0; 
            adapt_2nd   <=  1'd1; 
            done        <=  1'd0; 
            end    
                    
        endcase
        
        end
        
end      



//-------------------------------------------------------------------------------------------------- 
//  RX Equalization Output                                                                           
//-------------------------------------------------------------------------------------------------- 
assign RXEQ_NEW_TXCOEFF = NEW_TXCOEFF;
assign RXEQ_LFFS_SEL    = lffs_sel;
assign RXEQ_ADAPT_DONE  = adapt_done;
assign RXEQ_DONE        = done;
assign phy_rxeq_fsm      = fsm;



endmodule
