`ifndef AXI_BRIDGE_VH
`define AXI_BRIDGE_VH
`include "pciedmacoredefines.vh"
//-----------------------------------------------------------------------------
// $Id: 
//-----------------------------------------------------------------------------
// axi_bridge.vh
//-----------------------------------------------------------------------------
// (c) Copyright 2020-2023 AMD, Inc. All rights reserved.
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
//-----------------------------------------------------------------------------
// Filename:        axi_bridge.vh
//
// Description:     
//                  
// This file needs to be included in all modules so that all the modules can commonly 
// reference state_transitions
//                   
//                  
// VHDL-Standard:   VHDL'93
//-----------------------------------------------------------------------------
// Structure:   
//              Include file
//
//-----------------------------------------------------------------------------
// Revision:        v1.05.a
// Date:            06/28/12
//
//-----------------------------------------------------------------------------

`timescale 1 ps / 1 ps
`define XSRREG_AXIMM(clk, reset_n, q,d,rstval)        \
`ifdef SOFT_IP  \
`XSRREG_SYNC (clk, reset_n, q,d,rstval) \
`else   \
`XSRREG_ASYNC (clk, reset_n, q,d,rstval)  \
`endif 

`define XSRREG_EN_AXIMM(clk, reset_n, q,d,rstval, en)     \
`ifdef SOFT_IP \
`XSRREG_SYNC_EN(clk, reset_n, q,d,rstval, en) \
`else \
`XSRREG_ASYNC_EN(clk, reset_n, q,d,rstval, en) \
`endif

`define XSRREG_XDMA(clk, reset_n, q,d,rstval)        \
`ifdef SOFT_IP  \
`XSRREG_SYNC (clk, reset_n, q,d,rstval) \
`else   \
`XSRREG_ASYNC (clk, reset_n, q,d,rstval)  \
`endif

`define XSRREG_EN_XDMA(clk, reset_n, q,d,rstval, en)     \
`ifdef SOFT_IP \
`XSRREG_SYNC_EN(clk, reset_n, q,d,rstval, en) \
`else \
`XSRREG_ASYNC_EN(clk, reset_n, q,d,rstval, en) \
`endif

`define XLREG_AXIMM(clk, reset_n) \
`ifdef SOFT_IP \
`XLREGS_SYNC(clk, reset_n) \
`else \
`XLREGS_ASYNC(clk, reset_n)  \
`endif

`define XLREG_XDMA(clk, reset_n) \
`ifdef SOFT_IP \
`XLREGS_SYNC(clk, reset_n) \
`else \
`XLREGS_ASYNC(clk, reset_n)  \
`endif

`define XNRREG_AXIMM(clk,q,d)                            \
    always @(posedge clk)                            \
    begin                                            \
         `ifdef FOURVALCLKPROP                            \
            q <= #(TCQ) clk? d : q;                            \
          `else                                            \
            q <= #(TCQ) d;                                    \
          `endif                                    \
     end

`define XNRREG_EN_AXIMM(clk,q,d,en)     \
    always @(posedge clk)                            \
    begin                                            \
         `ifdef FOURVALCLKPROP                            \
            q <= #(TCQ) ((en & clk)  ? d : q);                    \
          `else                                            \
            q <= #(TCQ) (en ? d : q);                            \
          `endif                                    \
     end

// AXI Defines
`define SIZE64 0
`define SIZE128 1
`define SIZE256 2
`define SIZE512 3
`define CQ_USER_FBELO 0
`define CQ_USER_FBEHI 3
`define CQ_USER_LBELO 4
`define CQ_USER_LBEHI 7
`define CQ_USER_LBELO_512 8
`define CQ_USER_LBEHI_512 11
`define CQ_USER_BELO 8
`define CQ_USER_BEHI (CQ_USER_BELO +31)
`define CQ_USER_PARLO 53
`define CQ_USER_PARLO_512 119
`define CQ_USER_PARHI (CQ_USER_PARLO +31)
`define AXIS_MEM_READ 4'h0
`define AXIS_MEM_WRITE 4'h1
`define AXIS_IO_READ 4'h2
`define AXIS_IO_WRITE 4'h3
`define AXIS_IO_WRITE 4'h3
`define AXIS_FETCH_ADD 4'h4
`define AXIS_UCOND_SWAP 4'h5
`define AXIS_COMP_SWAP 4'h6
`define AXIS_READ_LCK 4'h7
`define AXIS_CFGRD_TYPE0 4'h8
`define AXIS_CFGRD_TYPE1 4'h9
`define AXIS_CFGWR_TYPE0 4'ha
`define AXIS_CFGWR_TYPE1 4'hb
`define AXIS_MSG_GEN 4'hc
`define AXIS_MSG_VNDDEF 4'hd
`define AXIS_MSG_ATS 4'he
`define AXIS_RSVD 4'hf


`define AXIMM_RRESP_OK 2'b00
`define AXIMM_RRESP_EXOK 2'b01
`define AXIMM_RRESP_SLVERR 2'b10
`define AXIMM_RRESP_DECERR 2'b11
//   typedef enum {IDLE_read_reqSM, CHECK_read_reqSM, SEND_REQ, WAIT_FOR_OPEN_SLOT} read_reqSM_STATES ;
   // Add these to the State machines
   //signal read_reqSM_cs : read_reqSM_STATES;
   //signal read_reqSM_ns : read_reqSM_STATES;

//   typedef enum {IDLE_read_dataSM,WAIT_FOR_CPLE, LOAD_READ_COUNTERE, FIRST_BRAM_READE, STR_DATAE, STR_DONEE, WAIT_SLOT_CLRE} read_dataSM_STATES ;
   // Add This to the appropriate file
   //signal read_dataSM_cs : read_dataSM_STATES;
   //signal read_dataSM_ns : read_dataSM_STATES;
   //signal read_dataSM_cs_d : read_dataSM_STATES;
   
//   typedef enum {IDLE_arid_dependencySM, FIND_HISTORY_MATCH, SET_DEPENDENCY, CLEAR_DEPENDENCY} arid_dependencySM_STATES ;
//   typedef enum {IDLE_write_reqSM, CHECK_write_reqSM, CHECK2, ONE_REQ_ACTIVE, TWO_REQ_ACTIVE} write_reqSM_STATES ;


//   typedef enum {IDLE_write_dataSM, FIRST_DATA_WORD, DATA_STREAM, DONE_write_dataSM, WAIT_TLP_START, WAIT_STR_DONE, FIRST_DATA_WORD_2, DATA_STREAM_2, DONE_2} write_dataSM_STATES ;

//function integer clog2;
//   input [0:7] value; // Input value
//    begin : dummy
//        reg [0:7] value_int;
//        value_int = value;
//        for (clog2 = 0; value_int > 0; clog2 = clog2 + 1)
//            value_int = value_int >> 1;
//   end
//endfunction
`endif // AXI_BRIDGE_VH
