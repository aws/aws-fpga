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
// File       : pcie_bridge_ep_pcie4c_ip_cxs_remap.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

module pcie_bridge_ep_pcie4c_ip_cxs_remap #(
  parameter           AXIS_CCIX_RX_TDATA_WIDTH = 256,
  parameter           AXIS_CCIX_TX_TDATA_WIDTH = 256,
  parameter           AXIS_CCIX_RX_TUSER_WIDTH = 46,
  parameter           AXIS_CCIX_TX_TUSER_WIDTH = 46,
  parameter           AXIS_CCIX_RX_CNTL_WIDTH  = (AXIS_CCIX_RX_TDATA_WIDTH ==  512 ? 36 : 14), 
  parameter           AXIS_CCIX_TX_CNTL_WIDTH  = (AXIS_CCIX_TX_TDATA_WIDTH ==  512 ? 36 : 14) 
) (

   input [AXIS_CCIX_RX_TDATA_WIDTH-1:0]         ccix_rx_tdata,  
   input                                        ccix_rx_tvalid, 
   input [AXIS_CCIX_RX_TUSER_WIDTH-1:0]         ccix_rx_tuser,  
   output                                       ccix_rx_credit_grant,  
   input                                        ccix_rx_credit_return, 
   input [7:0]                                  ccix_rx_credit_av,     
   input                                        ccix_rx_active_req,    
   output                                       ccix_rx_active_ack,    
   output                                       ccix_rx_deact_hint,


   output  [AXIS_CCIX_TX_TDATA_WIDTH-1:0]       ccix_tx_tdata, 
   output                                       ccix_tx_tvalid,
   output  [AXIS_CCIX_TX_TUSER_WIDTH-1:0]       ccix_tx_tuser, 
   input                                        ccix_tx_credit_gnt,   
   output                                       ccix_tx_credit_rtn,   
   output                                       ccix_tx_active_req,  
   input                                        ccix_tx_active_ack, 
   input                                        ccix_tx_deact_hint,

   input                                        CXS0_ACTIVE_REQ_TX, 
   output                                       CXS0_ACTIVE_ACK_TX, 
   output                                       CXS0_DEACT_HINT_TX, 
   input                                        CXS0_VALID_TX,
   output                                       CXS0_CRDGNT_TX,
   input                                        CXS0_CRDRTN_TX,     
   input  [AXIS_CCIX_TX_CNTL_WIDTH-1:0]         CXS0_CNTL_TX,
   input  [AXIS_CCIX_TX_TDATA_WIDTH-1:0]        CXS0_DATA_TX,
   input                                        CXS0_VALID_CHK_TX,  
   output                                       CXS0_CRDGNT_CHK_TX,
   input                                        CXS0_CRDRTN_CHK_TX, 
   input                                        CXS0_CNTL_CHK_TX,   
   input  [AXIS_CCIX_TX_TDATA_WIDTH/8-1:0]      CXS0_DATA_CHK_TX, 
   output                                       CXS0_ACTIVE_REQ_RX, 
   input                                        CXS0_ACTIVE_ACK_RX, 
   input                                        CXS0_DEACT_HINT_RX, 
   output                                       CXS0_VALID_RX, 
   input                                        CXS0_CRDGNT_RX,
   output                                       CXS0_CRDRTN_RX,
   output [AXIS_CCIX_RX_CNTL_WIDTH-1:0]         CXS0_CNTL_RX,
   output [AXIS_CCIX_RX_TDATA_WIDTH-1:0]        CXS0_DATA_RX,
   output                                       CXS0_VALID_CHK_RX, 
   input                                        CXS0_CRDGNT_CHK_RX, 
   output                                       CXS0_CRDRTN_CHK_RX,
   output                                       CXS0_CNTL_CHK_RX,
   output [AXIS_CCIX_RX_TDATA_WIDTH/8-1:0]      CXS0_DATA_CHK_RX,

   input           cfg_vc1_en,
   input           cfg_vc1_neg_pend,

   input           ccix_rst, 
   input           ccix_clk 
  

);
//  reg   vc1_enabled = 1'b0;
//  //integer ii, jj;
//  wire [31:0] tx_parity, rx_parity;
//
//  //- First time ccix_tx_credit signal is asserted when VC1 is enabled
//  //    Use that to assert CXS activation on S$
//  always @(posedge ccix_clk)
//  begin
//    if (ccix_rst)
//      vc1_enabled <= 1'b0;
//    else if (cfg_vc1_en & ~cfg_vc1_neg_pend)  
//      vc1_enabled <= 1'b1;
//  end
//
//
//  assign ccix_rx_tdata          =   CXS0_DATA_TX;   
/*  
  //- Every DW byte reversal
  genvar ii, jj;
  generate 
  for (jj = 0; jj < 8; jj=jj+1)
  begin
    for (ii=0; ii<4; ii=ii+1)
    begin
      assign ccix_rx_tdata[((32*jj)+31-(8*ii)):((32*jj)+24-(8*ii))] = 
                        CXS0_DATA_TX[((32*jj)+(8*ii)+7):((32*jj)+(8*ii))];
      
      assign tx_parity[(4*jj)+3-ii] = CXS0_DATA_CHK_TX[(4*jj)+ii];

      assign CXS0_DATA_RX[((32*jj)+31-(8*ii)):((32*jj)+24-(8*ii))] = 
                        ccix_tx_tdata[((32*jj)+(8*ii)+7):((32*jj)+(8*ii))];

      assign CXS0_DATA_CHK_RX[(4*jj)+3-ii] = rx_parity[(4*jj)+ii];
    end
  end
  endgenerate
      //- PCIe TUSER doesn't provide parity
  //Logic to compute Parity for CXS-RX
  genvar aa;
  generate
    for (aa = 0; aa < 32; aa=aa+1)
      assign rx_parity[aa] = !(^ccix_tx_tdata[((8*(aa+1))-1):(8*aa)]);
  endgenerate

*/
/*
  assign ccix_rx_tvalid         =   CXS0_VALID_TX;
  assign ccix_rx_tuser[0]       =   CXS0_CNTL_TX[0];      //- is_sop0
  assign ccix_rx_tuser[1]       =   CXS0_CNTL_TX[2];      //- is_sop0_ptr
  assign ccix_rx_tuser[2]       =   CXS0_CNTL_TX[1];      //- is_sop1
  assign ccix_rx_tuser[3]       =   CXS0_CNTL_TX[3];      //- is_sop1_ptr
  assign ccix_rx_tuser[4]       =   CXS0_CNTL_TX[4];      //- is_eop0
  assign ccix_rx_tuser[7:5]     =   CXS0_CNTL_TX[10:8];   //- eop0_ptr
  assign ccix_rx_tuser[8]       =   CXS0_CNTL_TX[5];      //- is_eop1
  assign ccix_rx_tuser[11:9]    =   CXS0_CNTL_TX[13:11];  //- eop1_ptr
  assign ccix_rx_tuser[13:12]   =   CXS0_CNTL_TX[7:6];    //- error/discontinue
  assign ccix_rx_tuser[45:14]   =   CXS0_DATA_CHK_TX;     //- parity
  
  assign ccix_rx_credit         =   CXS0_CRDGNT_RX;
  
  assign CXS0_DATA_RX           =   ccix_tx_tdata;   
  assign CXS0_VALID_RX          =   ccix_tx_tvalid;
  assign CXS0_VALID_CHK_RX      =   ccix_tx_tvalid;
  assign CXS0_CNTL_RX[0]        =   ccix_tx_tuser[0];     //- sop0
  assign CXS0_CNTL_RX[1]        =   ccix_tx_tuser[2];     //- sop0_ptr
  assign CXS0_CNTL_RX[2]        =   ccix_tx_tuser[1];     //- sop1
  assign CXS0_CNTL_RX[3]        =   ccix_tx_tuser[3];     //- sop1_ptr
  assign CXS0_CNTL_RX[4]        =   ccix_tx_tuser[4];     //- eop0
  assign CXS0_CNTL_RX[5]        =   ccix_tx_tuser[8];     //- eop1
  assign CXS0_CNTL_RX[7:6]      =   ccix_tx_tuser[13:12]; //- discontinue
  assign CXS0_CNTL_RX[10:8]     =   ccix_tx_tuser[7:5];   //- eop0_ptr
  assign CXS0_CNTL_RX[13:11]    =   ccix_tx_tuser[11:9];  //- eop1_ptr
  assign CXS0_DATA_CHK_RX       =   ccix_tx_tuser[45:14]; //- parity
//  assign rx_parity              = ccix_tx_tuser[45:14];  

  assign CXS0_ACTIVE_REQ_RX     =   vc1_enabled;  //1'b1;
  assign CXS0_CRDRTN_RX         =   1'b0;
  assign CXS0_CNTL_CHK_RX       =   1'b0;
  assign CXS0_CRDRTN_CHK_RX     =   1'b0;
  assign CXS0_CRDGNT_TX         =   ccix_tx_credit; 
  assign CXS0_CRDGNT_CHK_TX     =   ccix_tx_credit;
  //- ACK the request from S$ only when VC1 is enabled
  assign CXS0_ACTIVE_ACK_TX     =   CXS0_ACTIVE_REQ_TX ? vc1_enabled : 1'b0;
  assign CXS0_DEACT_HINT_TX     =   1'b0;
*/
//-------------- With Latest CXS support in PCIe4c IP ----------------------
  assign ccix_tx_tdata          =   CXS0_DATA_TX;   
  assign ccix_tx_tvalid         =   CXS0_VALID_TX;
  assign ccix_tx_tuser          =   {CXS0_CNTL_CHK_TX,CXS0_DATA_CHK_TX,CXS0_CNTL_TX[AXIS_CCIX_RX_CNTL_WIDTH-1:0]};
  assign CXS0_CRDGNT_TX         =   ccix_tx_credit_gnt;
  assign CXS0_CRDGNT_CHK_TX     =   ccix_tx_credit_gnt;
  assign ccix_tx_credit_rtn     =   CXS0_CRDRTN_TX;
  assign ccix_tx_active_req     =   CXS0_ACTIVE_REQ_TX;
  assign CXS0_ACTIVE_ACK_TX     =   ccix_tx_active_ack;
  assign CXS0_DEACT_HINT_TX     =   ccix_tx_deact_hint; 
 
  assign CXS0_DATA_RX           = ccix_rx_tdata;  
  assign CXS0_VALID_RX          = ccix_rx_tvalid; 
  assign CXS0_VALID_CHK_RX      = ccix_rx_tvalid;
  assign CXS0_CNTL_CHK_RX       = ccix_rx_tuser[AXIS_CCIX_TX_TUSER_WIDTH-1]; 
  assign CXS0_CNTL_RX           = ccix_rx_tuser[AXIS_CCIX_RX_CNTL_WIDTH-1:0];  
  assign CXS0_DATA_CHK_RX       = ccix_rx_tuser[AXIS_CCIX_TX_TUSER_WIDTH-2:AXIS_CCIX_RX_CNTL_WIDTH];  
  assign ccix_rx_credit_grant   = CXS0_CRDGNT_RX; 
  assign CXS0_CRDRTN_RX         = ccix_rx_credit_return;
  assign CXS0_CRDRTN_CHK_RX     =   1'b0;
  //assign                        = ccix_rx_credit_av;    
  assign CXS0_ACTIVE_REQ_RX     = ccix_rx_active_req;   
  assign ccix_rx_active_ack     = CXS0_ACTIVE_ACK_RX;
  assign ccix_rx_deact_hint     = CXS0_DEACT_HINT_RX;


endmodule
