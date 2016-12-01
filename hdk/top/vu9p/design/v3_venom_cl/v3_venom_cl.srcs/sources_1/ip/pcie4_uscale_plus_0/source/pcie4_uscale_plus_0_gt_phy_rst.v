//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : pcie4_uscale_plus_0_gt_phy_rst.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
//  Design :  PHY Wrapper
//  Module :  PHY Reset 
//--------------------------------------------------------------------------------------------------

`timescale 1ps / 1ps

//--------------------------------------------------------------------------------------------------
//  PHY Reset Module
//--------------------------------------------------------------------------------------------------
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie4_uscale_plus_0_gt_phy_rst #
(
    parameter integer PHY_LANE      = 16,   
    parameter integer PHY_MAX_SPEED = 4,
    parameter integer SYNC_STAGE    = 3
)
(
    //-------------------------------------------------------------------------- 
    //  Input Ports
    //-------------------------------------------------------------------------- 
    input                               RST_REFCLK,
    input                               RST_PCLK,
    input                               RST_N,
    input       [PHY_LANE-1:0]          RST_GTPOWERGOOD,
    input       [PHY_LANE-1:0]          RST_CPLLLOCK,
    input       [(PHY_LANE-1)>>2:0]     RST_QPLL0LOCK,   
    input       [(PHY_LANE-1)>>2:0]     RST_QPLL1LOCK,
    input       [PHY_LANE-1:0]          RST_TXPROGDIVRESETDONE,
    input       [PHY_LANE-1:0]          RST_TXRESETDONE,    
    input       [PHY_LANE-1:0]          RST_RXRESETDONE, 
    input       [PHY_LANE-1:0]          RST_TXSYNC_DONE,   
    input       [PHY_LANE-1:0]          RST_PHYSTATUS,
    
    //-------------------------------------------------------------------------- 
    //  Output Ports
    //-------------------------------------------------------------------------- 
    output      [3:0]                   phy_rst_fsm,
    output                              RST_RRST_N,
    output                              RST_PRST_N,
    output                              RST_CPLLPD,
    output                              RST_CPLLRESET,
    output                              RST_QPLLPD,
    output                              RST_QPLLRESET,
    output                              RST_TXPROGDIVRESET,
    output                              RST_GTRESET,
    output                              RST_USERRDY,
    output                              RST_TXSYNC_START,
    output                              RST_IDLE
);
    //-------------------------------------------------------------------------- 
    //  Reset Synchronized Signals
    //-------------------------------------------------------------------------- 
    (* ASYNC_REG = "TRUE", SHIFT_EXTRACT = "NO" *) reg [ 3:0] rrst_n_r;
    (* ASYNC_REG = "TRUE", SHIFT_EXTRACT = "NO" *) reg [ 3:0] prst_n_r;

    wire                                rrst_n;                                     
    wire                                prst_n;  
       
    //--------------------------------------------------------------------------
    //  Synchronized Signals
    //--------------------------------------------------------------------------                                     
    wire        [PHY_LANE-1:0]          gtpowergood_r;                                                                 
    wire        [PHY_LANE-1:0]          cplllock_r;
    wire        [(PHY_LANE-1)>>2:0]     qpll0lock_r;
    wire        [(PHY_LANE-1)>>2:0]     qpll1lock_r;
    wire        [PHY_LANE-1:0]          txprogdivresetdone_r;
    wire        [PHY_LANE-1:0]          txresetdone_r;  
    wire        [PHY_LANE-1:0]          rxresetdone_r;
    wire        [PHY_LANE-1:0]          txsync_done_r;
    wire        [PHY_LANE-1:0]          phystatus_r;
    
    //--------------------------------------------------------------------------
    //  Internal Signals
    //--------------------------------------------------------------------------
    wire                                gtpowergood_a;
    wire                                cplllock_a;
    wire                                qplllock_a;
    wire                                txprogdivresetdone_a;
    wire                                resetdone_a;
    wire                                txsync_done_a;
    wire                                phystatus_a;
    
    reg         [ 1:0]                  txsync_start_cnt;
    
    //--------------------------------------------------------------------------
    //  Output Delayed Signals
    //--------------------------------------------------------------------------     
    reg         [ 3:0]                  cpllpd_r;
    reg         [ 3:0]                  cpllreset_r;                                  
    reg         [ 3:0]                  qpllpd_r;
    reg         [ 3:0]                  qpllreset_r;                                
    reg         [ 3:0]                  txprogdivreset_r;
    reg         [ 3:0]                  gtreset_r;
    reg         [ 3:0]                  userrdy_r;
                
    wire                                cpllpd_dly;
    wire                                cpllreset_dly;                                    
    wire                                qpllpd_dly;
    wire                                qpllreset_dly;                        
    wire                                txprogdivreset_dly;
    wire                                gtreset_dly;
    wire                                userrdy_dly;
     
    //-------------------------------------------------------------------------- 
    //  FSM Signals
    //-------------------------------------------------------------------------- 
    reg [ 2:0] fsm;
    
    reg                                 idle;     
    reg                                 cpllpd;
    reg                                 cpllreset;
    reg                                 qpllpd;
    reg                                 qpllreset;
    reg                                 txprogdivreset;
    reg                                 gtreset;
    reg                                 userrdy; 
    reg                                 txsync_start;         
   
    //--------------------------------------------------------------------------
    //  FSM Encoding
    //-------------------------------------------------------------------------- 
    localparam FSM_IDLE               = 3'd0;
    localparam FSM_GTPOWERGOOD        = 3'd1;
    localparam FSM_PLLLOCK            = 3'd2;
    localparam FSM_TXPROGDIVRESETDONE = 3'd3;
    localparam FSM_RESETDONE          = 3'd4;
    localparam FSM_TXSYNC_START       = 3'd5;
    localparam FSM_TXSYNC_DONE        = 3'd6;
    localparam FSM_PHYSTATUS          = 3'd7;



//--------------------------------------------------------------------------------------------------
//  Reset Synchronizer for REFCLK
//--------------------------------------------------------------------------------------------------
always @ (posedge RST_REFCLK or negedge RST_N)
begin

    if (!RST_N) 
        rrst_n_r <= 4'd0;
    else
        rrst_n_r <= {rrst_n_r[2:0], 1'd1}; 
          
end   
 
assign rrst_n = rrst_n_r[3];



//--------------------------------------------------------------------------------------------------
//  Reset Synchronizer for PCLK
//--------------------------------------------------------------------------------------------------
always @ (posedge RST_PCLK or negedge RST_N)
begin

    if (!RST_N) 
        prst_n_r <= 4'd0;
    else
        prst_n_r <= {prst_n_r[2:0], 1'd1};
          
end   

assign prst_n = prst_n_r[3];



//--------------------------------------------------------------------------------------------------
//  Input Synchronizer or Pipeline
//--------------------------------------------------------------------------------------------------
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_gtpowergood        (.CLK (RST_REFCLK), .D (RST_GTPOWERGOOD),        .Q (gtpowergood_r));
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_cplllock           (.CLK (RST_REFCLK), .D (RST_CPLLLOCK),           .Q (cplllock_r));
pcie4_uscale_plus_0_sync #(.WIDTH (((PHY_LANE-1)>>2)+1), .STAGE (SYNC_STAGE)) sync_qpll0lock          (.CLK (RST_REFCLK), .D (RST_QPLL0LOCK),          .Q (qpll0lock_r));
pcie4_uscale_plus_0_sync #(.WIDTH (((PHY_LANE-1)>>2)+1), .STAGE (SYNC_STAGE)) sync_qpll1lock          (.CLK (RST_REFCLK), .D (RST_QPLL1LOCK),          .Q (qpll1lock_r));
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_txprogdivresetdone (.CLK (RST_REFCLK), .D (RST_TXPROGDIVRESETDONE), .Q (txprogdivresetdone_r));
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_txresetdone        (.CLK (RST_REFCLK), .D (RST_TXRESETDONE),        .Q (txresetdone_r));  
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_rxresetdone        (.CLK (RST_REFCLK), .D (RST_RXRESETDONE),        .Q (rxresetdone_r));
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_txsync_done        (.CLK (RST_REFCLK), .D (RST_TXSYNC_DONE),        .Q (txsync_done_r)); 
pcie4_uscale_plus_0_sync #(.WIDTH (PHY_LANE),            .STAGE (SYNC_STAGE)) sync_phystatus          (.CLK (RST_REFCLK), .D (RST_PHYSTATUS),          .Q (phystatus_r));



//--------------------------------------------------------------------------------------------------
//  Convert per-lane signals to per-design 
//--------------------------------------------------------------------------------------------------
assign gtpowergood_a        = &gtpowergood_r;
assign cplllock_a           = (PHY_MAX_SPEED  < 3) ? (&cplllock_r)  : cplllock_r[0];
assign qplllock_a           = (PHY_MAX_SPEED == 4) ? (&qpll0lock_r) : (&qpll1lock_r);
assign txprogdivresetdone_a = &txprogdivresetdone_r;
assign resetdone_a          = (&txresetdone_r) && (&rxresetdone_r);
assign txsync_done_a        = &txsync_done_r;
assign phystatus_a          = |phystatus_r;                 



//--------------------------------------------------------------------------------------------------
//  TX Sync Alignment Start Counter
//--------------------------------------------------------------------------------------------------
always @ (posedge RST_REFCLK)
begin

    if (!rrst_n)
        txsync_start_cnt <= 2'd0;
    else
        if (fsm == FSM_TXSYNC_START)
            txsync_start_cnt <= txsync_start_cnt + 2'd1; 
        else
            txsync_start_cnt <= 2'd0;
            
end



//--------------------------------------------------------------------------------------------------
//  Reset FSM
//--------------------------------------------------------------------------------------------------
always @ (posedge RST_REFCLK)
begin

    if (!rrst_n)
        begin
        fsm            <= FSM_GTPOWERGOOD;
        idle           <= 1'd0;
        cpllpd         <= 1'd1;                               
        cpllreset      <= 1'd1;
        qpllpd         <= 1'd1;
        qpllreset      <= 1'd1;
        txprogdivreset <= 1'd1;
        gtreset        <= 1'd1;
        userrdy        <= 1'd0;
        txsync_start   <= 1'd0;
        end
    else
        begin
        
        case (fsm)
            
        //------------------------------------------------------------------------------------------
        //  Stay in IDLE state until system reset is released
        //------------------------------------------------------------------------------------------
        FSM_IDLE :
        
            begin
            if (!rrst_n)
                begin
                fsm            <= FSM_GTPOWERGOOD;
                idle           <= 1'd0;
                cpllpd         <= 1'd1;
                cpllreset      <= 1'd1;
                qpllpd         <= 1'd1;
                qpllreset      <= 1'd1;
                txprogdivreset <= 1'd1;
                gtreset        <= 1'd1;
                userrdy        <= 1'd0;
                txsync_start   <= 1'd0;
                end
            else
                begin
                fsm            <= FSM_IDLE;
                idle           <= 1'd1;
                cpllpd         <= cpllpd;
                cpllreset      <= cpllreset;
                qpllpd         <= qpllpd;
                qpllreset      <= qpllreset;
                txprogdivreset <= txprogdivreset;
                gtreset        <= gtreset;
                userrdy        <= userrdy;
                txsync_start   <= txsync_start;
                end
            end   
            
        //------------------------------------------------------------------------------------------
        //  Release [CPLL/QPLL]PD and wait for GTPOWERGOOD to assert HIGH
        //------------------------------------------------------------------------------------------
        FSM_GTPOWERGOOD :
        
            begin
            fsm            <= (gtpowergood_a && (!cplllock_a) && (!qplllock_a || PHY_MAX_SPEED < 3)) ? FSM_PLLLOCK : FSM_GTPOWERGOOD;
            idle           <= idle;
            cpllpd         <= 1'd0;
            cpllreset      <= cpllreset;
            qpllpd         <= (PHY_MAX_SPEED < 3) ? 1'd1 : 1'd0;
            qpllreset      <= qpllreset;
            txprogdivreset <= txprogdivreset;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= txsync_start;
            end    
            
        //------------------------------------------------------------------------------------------
        //  Release [CPLL/QPLL]RESET and wait for [CPLL/QPLL]LOCK to assert HIGH
        //------------------------------------------------------------------------------------------
        FSM_PLLLOCK :
        
            begin
            fsm            <= (cplllock_a && (qplllock_a || PHY_MAX_SPEED < 3)) ? FSM_TXPROGDIVRESETDONE : FSM_PLLLOCK;
            idle           <= idle;
            cpllpd         <= cpllpd;
            cpllreset      <= 1'd0;
            qpllpd         <= qpllpd;
            qpllreset      <= (PHY_MAX_SPEED < 3) ? 1'd1 : 1'd0;
            txprogdivreset <= txprogdivreset;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= txsync_start;
            end

        //------------------------------------------------------------------------------------------
        //  Release TXPROGDIVRESET and wait for TXPROGDIVRESETDONE to assert HIGH
        //------------------------------------------------------------------------------------------
        FSM_TXPROGDIVRESETDONE :
        
            begin
            fsm            <= txprogdivresetdone_a ? FSM_RESETDONE : FSM_TXPROGDIVRESETDONE;  
            idle           <= idle;
            cpllpd         <= cpllpd;
            cpllreset      <= cpllreset;
            qpllpd         <= qpllpd;
            qpllreset      <= qpllreset;
            txprogdivreset <= 1'd0;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= txsync_start;
            end
            
        //------------------------------------------------------------------------------------------
        //  Release GT[TX/RX]RESET, assert [TX/RX]USERRDY, and wait for [TX/RX]RESETDONE to assert HIGH
        //------------------------------------------------------------------------------------------
        FSM_RESETDONE :
        
            begin
            fsm            <= resetdone_a ? FSM_TXSYNC_START : FSM_RESETDONE;  
            idle           <= idle;
            cpllpd         <= cpllpd;
            cpllreset      <= cpllreset;
            qpllpd         <= qpllpd;
            qpllreset      <= qpllreset;
            txprogdivreset <= txprogdivreset;
            gtreset        <= 1'd0;
            userrdy        <= 1'd1;
            txsync_start   <= txsync_start;
            end
        
        //------------------------------------------------------------------------------------------
        //  Start TX sync alignment.  Extend TXSYNC_START pulse by few REFCLK cycles
        //------------------------------------------------------------------------------------------
        FSM_TXSYNC_START :
        
            begin
            fsm            <= (!txsync_done_a && (txsync_start_cnt == 2'd3)) ? FSM_TXSYNC_DONE : FSM_TXSYNC_START;
            idle           <= idle;
            cpllpd         <= cpllpd;
            cpllreset      <= cpllreset;
            qpllpd         <= qpllpd;   
            qpllreset      <= qpllreset;
            txprogdivreset <= txprogdivreset;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= 1'd1;
            end
            
        //------------------------------------------------------------------------------------------
        //  Wait for TX sync alignment done
        //------------------------------------------------------------------------------------------
        FSM_TXSYNC_DONE :
        
            begin
            fsm            <= txsync_done_a ? FSM_PHYSTATUS : FSM_TXSYNC_DONE;
            idle           <= idle;
            cpllpd         <= cpllpd;
            cpllreset      <= cpllreset;
            qpllpd         <= qpllpd;
            qpllreset      <= qpllreset;
            txprogdivreset <= txprogdivreset;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= 1'd0;
            end    
            
        //------------------------------------------------------------------------------------------
        //  Wait for PHYSTATUS to de-assert LOW
        //------------------------------------------------------------------------------------------
        FSM_PHYSTATUS :
        
            begin
            fsm            <= !phystatus_a ? FSM_IDLE : FSM_PHYSTATUS;  
            idle           <= 1'd1;
            cpllpd         <= cpllpd;
            cpllreset      <= cpllreset;
            qpllpd         <= qpllpd;
            qpllreset      <= qpllreset;
            txprogdivreset <= txprogdivreset;
            gtreset        <= gtreset;
            userrdy        <= userrdy;
            txsync_start   <= txsync_start;
            end 
            
        //------------------------------------------------------------------------------------------
        //  Default State
        //------------------------------------------------------------------------------------------
        default :
        
            begin
            fsm            <= FSM_IDLE;
            idle           <= 1'd0;
            cpllpd         <= 1'd1;
            cpllreset      <= 1'd1;
            qpllpd         <= 1'd1;
            qpllreset      <= 1'd1;
            txprogdivreset <= 1'd1;
            gtreset        <= 1'd1;
            userrdy        <= 1'd0;
            txsync_start   <= 1'd0;
            end

        endcase
        
        end
        
end



//--------------------------------------------------------------------------------------------------
//  Delay Outputs
//--------------------------------------------------------------------------------------------------
always @ (posedge RST_REFCLK)
begin

    cpllpd_r         <= {cpllpd_r[2:0],         cpllpd}; 
    cpllreset_r      <= {cpllreset_r[2:0],      cpllreset}; 
    qpllpd_r         <= {qpllpd_r[2:0],         qpllpd}; 
    qpllreset_r      <= {qpllreset_r[2:0],      qpllreset}; 
    txprogdivreset_r <= {txprogdivreset_r[2:0], txprogdivreset}; 
    gtreset_r        <= {gtreset_r[2:0],        gtreset};    
    userrdy_r        <= {userrdy_r[2:0],        userrdy}; 
            
end

assign cpllpd_dly         = cpllpd_r[3];
assign cpllreset_dly      = cpllreset_r[3];
assign qpllpd_dly         = qpllpd_r[3];
assign qpllreset_dly      = qpllreset_r[3];
assign txprogdivreset_dly = txprogdivreset_r[3];
assign gtreset_dly        = gtreset_r[3];
assign userrdy_dly        = userrdy_r[3];



//--------------------------------------------------------------------------------------------------
//  PHY Reset Outputs
//--------------------------------------------------------------------------------------------------
assign RST_RRST_N         = rrst_n;
assign RST_PRST_N         = prst_n;

assign RST_CPLLPD         = cpllpd_dly;
assign RST_CPLLRESET      = cpllreset_dly; 
assign RST_QPLLPD         = qpllpd_dly;
assign RST_QPLLRESET      = qpllreset_dly;
assign RST_TXPROGDIVRESET = txprogdivreset_dly;
assign RST_GTRESET        = gtreset_dly;  
assign RST_USERRDY        = userrdy_dly;
assign RST_TXSYNC_START   = txsync_start;
assign RST_IDLE           = idle;
assign phy_rst_fsm      = {1'b0,fsm};



endmodule
