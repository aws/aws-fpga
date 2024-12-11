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
// File       : pcie_bridge_ep_pcie4c_ip_gt_phy_txeq.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PCIe PHY Wrapper 
//  Module :  TX Equalization 
//--------------------------------------------------------------------------------------------------



`timescale 1ps / 1ps



//--------------------------------------------------------------------------------------------------
//  TX Equalization Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_gt_phy_txeq #
(
    parameter integer PHY_GT_TXPRESET = 0,
    parameter integer SYNC_STAGE    = 3
)
(
    //-------------------------------------------------------------------------- 
    //  Input Ports
    //-------------------------------------------------------------------------- 
    input                               TXEQ_CLK,                            
    input                               TXEQ_RST_N,

    input       [ 1:0]                  TXEQ_CTRL,    
    input       [ 3:0]                  TXEQ_PRESET,
    input       [ 5:0]                  TXEQ_COEFF,
    
    //-------------------------------------------------------------------------- 
    //  Output Ports
    //-------------------------------------------------------------------------- 
    output      [2:0]                   phy_txeq_fsm,
    output  reg [ 4:0]                  TXEQ_PRECURSOR, 
    output  reg [ 6:0]                  TXEQ_MAINCURSOR,
    output  reg [ 4:0]                  TXEQ_POSTCURSOR,
    output  reg [17:0]                  TXEQ_NEW_COEFF,
    output  reg                         TXEQ_DONE
);          
    //--------------------------------------------------------------------------
    //  Synchronized Signals
    //-------------------------------------------------------------------------- 
    wire        [ 1:0]                  ctrl_r; 
    wire        [ 3:0]                  preset_r;
    wire        [ 5:0]                  coeff_r;
  
    //--------------------------------------------------------------------------
    //  Internal Signals
    //--------------------------------------------------------------------------
    reg         [18:0]                  preset;          
    reg                                 preset_done;
    
    //--------------------------------------------------------------------------
    //  FSM Signals                                                            
    //--------------------------------------------------------------------------    
    reg         [ 2:0]                  fsm;
    reg         [18:0]                  coeff;
    reg         [ 1:0]                  coeff_cnt;
    reg                                 done;
   
    //----------------------------------------------------------------------------------------------                   
    //  FSM Encoding                                                                               
    //----------------------------------------------------------------------------------------------                   
    localparam FSM_IDLE   = 3'd0; 
    localparam FSM_PRESET = 3'd1;                                     
    localparam FSM_COEFF  = 3'd2;
    localparam FSM_REMAP  = 3'd3;
    localparam FSM_QUERY  = 3'd4;                                     
    localparam FSM_DONE   = 3'd5;

    //----------------------------------------------------------------------------------------------
    //  TX Equalization Preset 
    //----------------------------------------------------------------------------------------------
    //  Advertise FS = 40
    //  Advertise LF = 12
    //  Actual    FS = 80
    //  Actual    LF = 24
    //----------------------------------------------------------------------------------------------
    //  Coefficient Rules:
    //  * C(-1) < Floor(FS/4)
    //  * C(-1) + C(0) + C(+1) = FS
    //  * C(0) - C(-1) - C(+1) >= LF
    //----------------------------------------------------------------------------------------------
    //  TXPRECURSOR  or C(-1) should be 20 or less
    //  TXMAINCURSOR or C( 0) should be 52 or more (automatically calcuated in GT)
    //  TXPOSTCURSOR or C(+1) should be 28 or less
    //----------------------------------------------------------------------------------------------                           
    localparam TXPRECURSOR_00  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_00 = 7'd60;                     
    localparam TXPOSTCURSOR_00 = 6'd20;  // 6.0 dB
                                         
    localparam TXPRECURSOR_01  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_01 = 7'd66;                               
    localparam TXPOSTCURSOR_01 = 6'd14;  // 3.5 dB
                                         
    localparam TXPRECURSOR_02  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_02 = 7'd64;                     
    localparam TXPOSTCURSOR_02 = 6'd16;  // 4.5 dB
                                         
    localparam TXPRECURSOR_03  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_03 = 7'd70;                     
    localparam TXPOSTCURSOR_03 = 6'd10;  // 2.5 dB
                                         
    localparam TXPRECURSOR_04  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_04 = 7'd80;                     
    localparam TXPOSTCURSOR_04 = 6'd0;   // 0.0 dB
                                         
    localparam TXPRECURSOR_05  = 6'd8;   // 2.0 dB
    localparam TXMAINCURSOR_05 = 7'd72;                     
    localparam TXPOSTCURSOR_05 = 6'd0;   // 0.0 dB
                                         
    localparam TXPRECURSOR_06  = 6'd10;  // 2.5 dB
    localparam TXMAINCURSOR_06 = 7'd70;                     
    localparam TXPOSTCURSOR_06 = 6'd0;   // 0.0 dB
                                         
    localparam TXPRECURSOR_07  = 6'd8;   // 3.5 dB
    localparam TXMAINCURSOR_07 = 7'd56;                     
    localparam TXPOSTCURSOR_07 = 6'd16;  // 6.0 dB
                                         
    localparam TXPRECURSOR_08  = 6'd10;  // 3.5 dB
    localparam TXMAINCURSOR_08 = 7'd60;                     
    localparam TXPOSTCURSOR_08 = 6'd10;  // 3.5 dB
                                         
    localparam TXPRECURSOR_09  = 6'd14;  // 3.5 dB
    localparam TXMAINCURSOR_09 = 7'd66;                    
    localparam TXPOSTCURSOR_09 = 6'd0;   // 0.0 dB
                                         
    localparam TXPRECURSOR_10  = 6'd0;   // 0.0 dB
    localparam TXMAINCURSOR_10 = 7'd54;                      
    localparam TXPOSTCURSOR_10 = 6'd26;  // 9.5 dB
    
//--------------------------------------------------------------------------------------------------
//  Input Synchronizer
//--------------------------------------------------------------------------------------------------
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (2), .STAGE (SYNC_STAGE)) sync_ctrl   (.CLK (TXEQ_CLK), .D (TXEQ_CTRL),   .Q (ctrl_r));
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (4), .STAGE (SYNC_STAGE)) sync_preset (.CLK (TXEQ_CLK), .D (TXEQ_PRESET), .Q (preset_r));
pcie_bridge_ep_pcie4c_ip_sync #(.WIDTH (6), .STAGE (SYNC_STAGE)) sync_coeff  (.CLK (TXEQ_CLK), .D (TXEQ_COEFF),  .Q (coeff_r));



//--------------------------------------------------------------------------------------------------
//  TX Equalization Preset
//--------------------------------------------------------------------------------------------------
always @ (posedge TXEQ_CLK)
begin

    if (!TXEQ_RST_N)
        begin
        
        //------------------------------------------------------------------
        //  Default TX Equalization Preset                                 
        //------------------------------------------------------------------
        case (PHY_GT_TXPRESET)
            4'd0    : preset <= {TXPOSTCURSOR_00, TXMAINCURSOR_00, TXPRECURSOR_00};
            4'd1    : preset <= {TXPOSTCURSOR_01, TXMAINCURSOR_01, TXPRECURSOR_01};
            4'd2    : preset <= {TXPOSTCURSOR_02, TXMAINCURSOR_02, TXPRECURSOR_02};
            4'd3    : preset <= {TXPOSTCURSOR_03, TXMAINCURSOR_03, TXPRECURSOR_03};
            4'd4    : preset <= {TXPOSTCURSOR_04, TXMAINCURSOR_04, TXPRECURSOR_04};
            4'd5    : preset <= {TXPOSTCURSOR_05, TXMAINCURSOR_05, TXPRECURSOR_05};
            4'd6    : preset <= {TXPOSTCURSOR_06, TXMAINCURSOR_06, TXPRECURSOR_06};
            4'd7    : preset <= {TXPOSTCURSOR_07, TXMAINCURSOR_07, TXPRECURSOR_07};
            4'd8    : preset <= {TXPOSTCURSOR_08, TXMAINCURSOR_08, TXPRECURSOR_08};      
            4'd9    : preset <= {TXPOSTCURSOR_09, TXMAINCURSOR_09, TXPRECURSOR_09};   
            4'd10   : preset <= {TXPOSTCURSOR_10, TXMAINCURSOR_10, TXPRECURSOR_10};                 
            default : preset <= {TXPOSTCURSOR_00, TXMAINCURSOR_00, TXPRECURSOR_00};   
        endcase	       
        
        preset_done <= 1'd0;
        end                    
    else
        begin   
        if (fsm == FSM_PRESET)
            begin    
                
            //------------------------------------------------------------------
            //  Update TX Equalization Preset
            //------------------------------------------------------------------
            case (preset_r)
                4'd0    : preset <= {TXPOSTCURSOR_00, TXMAINCURSOR_00, TXPRECURSOR_00};
                4'd1    : preset <= {TXPOSTCURSOR_01, TXMAINCURSOR_01, TXPRECURSOR_01};
                4'd2    : preset <= {TXPOSTCURSOR_02, TXMAINCURSOR_02, TXPRECURSOR_02};
                4'd3    : preset <= {TXPOSTCURSOR_03, TXMAINCURSOR_03, TXPRECURSOR_03};
                4'd4    : preset <= {TXPOSTCURSOR_04, TXMAINCURSOR_04, TXPRECURSOR_04};
                4'd5    : preset <= {TXPOSTCURSOR_05, TXMAINCURSOR_05, TXPRECURSOR_05};
                4'd6    : preset <= {TXPOSTCURSOR_06, TXMAINCURSOR_06, TXPRECURSOR_06};
                4'd7    : preset <= {TXPOSTCURSOR_07, TXMAINCURSOR_07, TXPRECURSOR_07};
                4'd8    : preset <= {TXPOSTCURSOR_08, TXMAINCURSOR_08, TXPRECURSOR_08};      
                4'd9    : preset <= {TXPOSTCURSOR_09, TXMAINCURSOR_09, TXPRECURSOR_09}; 
                4'd10   : preset <= {TXPOSTCURSOR_10, TXMAINCURSOR_10, TXPRECURSOR_10};                   
                default : preset <= {TXPOSTCURSOR_00, TXMAINCURSOR_00, TXPRECURSOR_00};    
            endcase
              
            preset_done <= 1'd1;
            end
        else
            begin
            preset      <= preset;
            preset_done <= 1'd0;
            end
        end
        
end     



//--------------------------------------------------------------------------------------------------
//  TX Equalization FSM
//--------------------------------------------------------------------------------------------------
always @ (posedge TXEQ_CLK)
begin

    if (!TXEQ_RST_N)
        begin
        fsm       <= FSM_IDLE; 
        coeff     <= preset;
        coeff_cnt <= 2'd0;
        done      <= 1'd0;
        end                    
    else
        begin
        
        case (fsm)
        
        //------------------------------------------------------------------------------------------
        //  Wait until TXEQ_CTRL != 2'b00
        //------------------------------------------------------------------------------------------
        FSM_IDLE :
        
            begin
            done <= 1'd0;
            
            case (ctrl_r)
            
            //------------------------------------------------------------------
            //  Idle
            //------------------------------------------------------------------
            2'd0 :
            
                begin
                fsm       <= FSM_IDLE; 
                coeff     <= coeff;
                coeff_cnt <= 2'd0;
                end 
                
            //------------------------------------------------------------------
            //  Preset
            //------------------------------------------------------------------
            2'd1 :
            
                begin
                fsm       <= FSM_PRESET; 
                coeff     <= coeff;
                coeff_cnt <= 2'd0;
                end  
                
            //------------------------------------------------------------------
            //  Coeff : Latch C(-1) 
            //------------------------------------------------------------------
            2'd2 :
            
                begin
                fsm       <= FSM_COEFF; 
                coeff     <= {coeff_r, coeff[18:6]};
                coeff_cnt <= 2'd1;
                end
                
            //------------------------------------------------------------------
            //  Query
            //------------------------------------------------------------------
            2'd3 :
            
                begin
                fsm       <= FSM_QUERY; 
                coeff     <= coeff;
                coeff_cnt <= 2'd0;
                end
                
            //------------------------------------------------------------------
            //  Stay in IDLE state (Default)
            //------------------------------------------------------------------
            default :
            
                begin
                fsm       <= FSM_IDLE; 
                coeff     <= coeff;
                coeff_cnt <= 2'd0;
                end
                
            endcase
            
            end
            
        //------------------------------------------------------------------------------------------
        //  Wait for TXEQ preset done
        //------------------------------------------------------------------------------------------
        FSM_PRESET :
        
            begin
            fsm       <= preset_done ? FSM_DONE : FSM_PRESET;
            coeff     <= preset;
            coeff_cnt <= 2'd0;
            done      <= 1'd0;
            end    
            
        //------------------------------------------------------------------------------------------
        //  Latch C(0) and C(+1)
        //------------------------------------------------------------------------------------------
        FSM_COEFF :
        
            begin
            fsm <= (coeff_cnt == 2'd2) ? FSM_REMAP : FSM_COEFF;
            
            //------------------------------------------------------------------
            //  Shift in one extra bit for TXMAINCURSOR
            //------------------------------------------------------------------
            if (coeff_cnt == 2'd1)
                coeff <= {1'd0, coeff_r, coeff[18:7]};
            else
                coeff <= {coeff_r, coeff[18:6]};
                
            coeff_cnt <= coeff_cnt + 2'd1;
            done      <= 1'd0; 
            end
            
        //------------------------------------------------------------------------------------------
        //  Multiply coefficient by 2x
        //------------------------------------------------------------------------------------------
        FSM_REMAP :
        
            begin
            fsm       <= FSM_DONE;
            coeff     <= coeff << 1;        
            coeff_cnt <= 2'd0;
            done      <= 1'd0; 
            end
            
        //------------------------------------------------------------------------------------------
        //  Query to display current TXEQ_NEW_COEFF
        //------------------------------------------------------------------------------------------
        FSM_QUERY:
        
            begin
            fsm       <= FSM_DONE;
            coeff     <= coeff; 
            coeff_cnt <= 2'd0;
            done      <= 1'd0;
            end     
                  
        //------------------------------------------------------------------------------------------
        //  Assert TXEQ_DONE until TXEQ_CTRL == 2'd0
        //------------------------------------------------------------------------------------------
        FSM_DONE :
        
            begin
            fsm       <= (ctrl_r == 2'd0) ? FSM_IDLE : FSM_DONE;
            coeff     <= coeff;          
            coeff_cnt <= 2'd0;
            done      <= 1'd1;
            end        
                          
        //------------------------------------------------------------------------------------------
        //  Default State
        //------------------------------------------------------------------------------------------
        default : 
        
            begin
            fsm       <= FSM_IDLE;
            coeff     <= 19'd0; 
            coeff_cnt <=  2'd0;
            done      <=  1'd0;
            end    
                    
        endcase
        
        end
        
end  



//-------------------------------------------------------------------------------------------------- 
//  TX Equalization Output Register                                                                               
//-------------------------------------------------------------------------------------------------- 
always @ (posedge TXEQ_CLK)
begin

    if (!TXEQ_RST_N)
        begin
        TXEQ_PRECURSOR        <= coeff[ 4: 0];  
        TXEQ_MAINCURSOR       <= coeff[12: 6]; 
        TXEQ_POSTCURSOR       <= coeff[17:13];
        TXEQ_NEW_COEFF[17:12] <= {1'd0, coeff[18:14]};
        TXEQ_NEW_COEFF[11: 6] <= coeff[12:7]; 
        TXEQ_NEW_COEFF[ 5: 0] <= {1'd0, coeff[5:1]}; 
        TXEQ_DONE             <= 1'd0;
        end
    else           
        begin
        TXEQ_DONE <= done;
        
        //----------------------------------------------------------------------
        //  Divide TXEQ_NEW_COEFF by 2x and update output
        //----------------------------------------------------------------------
        if (fsm == FSM_DONE)
            begin
            TXEQ_PRECURSOR        <= coeff[ 4: 0]; 
            TXEQ_MAINCURSOR       <= coeff[12: 6]; 
            TXEQ_POSTCURSOR       <= coeff[17:13];
            TXEQ_NEW_COEFF[17:12] <= {1'd0, coeff[18:14]};
            TXEQ_NEW_COEFF[11: 6] <= coeff[12:7]; 
            TXEQ_NEW_COEFF[ 5: 0] <= {1'd0, coeff[5:1]}; 
            end
            
        //----------------------------------------------------------------------
        //  Hold output
        //----------------------------------------------------------------------    
        else
            begin
            TXEQ_PRECURSOR        <= TXEQ_PRECURSOR;  
            TXEQ_MAINCURSOR       <= TXEQ_MAINCURSOR; 
            TXEQ_POSTCURSOR       <= TXEQ_POSTCURSOR; 
            TXEQ_NEW_COEFF[17:12] <= TXEQ_NEW_COEFF[17:12];
            TXEQ_NEW_COEFF[11: 6] <= TXEQ_NEW_COEFF[11: 6];
            TXEQ_NEW_COEFF[ 5: 0] <= TXEQ_NEW_COEFF[ 5: 0];
            end
            
        end    
        
end


assign phy_txeq_fsm      = fsm;

endmodule
