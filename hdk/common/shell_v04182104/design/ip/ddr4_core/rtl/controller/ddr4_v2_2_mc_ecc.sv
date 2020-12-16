//*****************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
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
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor                : Xilinx
// \   \   \/     Version               : 1.1
//  \   \         Application           : MIG
//  /   /         Filename              : ddr4_v2_2_10_mc_ecc.sv
// /___/   /\     Date Last Modified    : $Date$
// \   \  /  \    Date Created          : Tue May 13 2014
//  \___\/\___\
//
//Device            : UltraScale
//Design Name       : DDR4 SDRAM & DDR3 SDRAM
//Purpose           :
//                   ddr4_v2_2_10_mc_ecc module
//Reference         :
//Revision History  :
//*****************************************************************************

`timescale 1ns/100ps

module ddr4_v2_2_10_mc_ecc # (parameter
    TCQ = 100
   ,PAYLOAD_WIDTH         = 64
   ,PAYLOAD_DM_WIDTH      = 8
   ,DATA_BUF_ADDR_WIDTH   = 5
   ,DQ_WIDTH              = 72
   ,DQS_WIDTH             = 9
   ,ECC_WIDTH             = 8
   ,ADDR_FIFO_WIDTH       = 30
   ,S_HEIGHT              = 1
   ,LR_WIDTH              = 1
   ,DM_WIDTH              = 9
   ,ECC                   = "OFF"
   ,MEM                   = "DDR4"
   ,COLBITS               = 10
   ,ABITS                 = 18
   ,RKBITS                = 2
   ,nCK_PER_CLK           = 4
   )
   (
    input                                   clk
   ,input                                   rst
    // error address
   ,input      [1:0]                        winPortEncC
   ,input                                   non_per_rd_cas
   ,input      [4*ABITS-1:0]                cmdRow
   ,input      [4*COLBITS-1:0]              cmdCol
   ,input      [3:0]                        cmdRmw
   ,input      [RKBITS*4-1:0]               cmdRank
   ,input      [4*LR_WIDTH-1:0]             cmdLRank
   ,input      [7:0]                        cmdBank
   ,input      [7:0]                        cmdGroup
    // NI write data
   ,input      [PAYLOAD_WIDTH*8-1:0]        wr_data_ni2mc
   ,input      [PAYLOAD_DM_WIDTH*8-1:0]     wr_data_mask_ni2mc
   ,input      [2*nCK_PER_CLK-1:0]          raw_not_ecc
   ,input                                   correct_en
   ,input                                   rmw_rd_done     
   ,input      [DATA_BUF_ADDR_WIDTH-1:0]    wr_data_addr_phy2mc
   // Phy read data
   ,input      [DQ_WIDTH*8-1:0]             rd_data_phy2mc_xif   // Xiphy format
   ,input      [DATA_BUF_ADDR_WIDTH-1:0]    rd_data_addr_phy2mc
   ,input                                   rd_data_en_phy2mc
   ,input                                   rd_data_end_phy2mc
   // Phy write data
   ,output reg [DQ_WIDTH*8-1:0]             wr_data_mc2phy
   ,output reg [DM_WIDTH*8-1:0]             wr_data_mask_mc2phy
   // NI read data
   ,output reg [PAYLOAD_WIDTH*8-1:0]        rd_data_mc2ni
   ,output     [DATA_BUF_ADDR_WIDTH-1:0]    rd_data_addr_mc2ni
   ,output                                  rd_data_en_mc2ni
   ,output                                  rd_data_end_mc2ni
   ,output     [ADDR_FIFO_WIDTH-1:0]        ecc_err_addr
   ,output     [2*nCK_PER_CLK-1:0]          eccSingle
   ,output     [2*nCK_PER_CLK-1:0]          eccMultiple
   ,output reg [DQ_WIDTH*8-1:0]             rd_data_phy2mc_cw_order // ecc log format
   ,input [DQS_WIDTH-1:0]                   fi_xor_we
   ,input [DQ_WIDTH-1:0]                    fi_xor_wrdata
   ,input                                   fi_xor_wrdata_en
  );

localparam DATA_WIDTH = ( ECC == "OFF" )              ?   PAYLOAD_WIDTH               :
                        ( PAYLOAD_WIDTH == DQ_WIDTH ) ? ( PAYLOAD_WIDTH - ECC_WIDTH ) : PAYLOAD_WIDTH;

wire [DQ_WIDTH*8-1:0]           wr_data_enc2xor;
wire [2*nCK_PER_CLK*DQ_WIDTH/8-1:0] mc_wrdata_mask;
wire [DATA_WIDTH*8-1:0]         rd_merge_data;
wire [DQ_WIDTH*ECC_WIDTH-1:0]   h_rows;
wire [PAYLOAD_WIDTH*8-1:0]      rd_data_fix2buf;
wire [2*nCK_PER_CLK-1:0]        ecc_single;
wire [2*nCK_PER_CLK-1:0]        ecc_multiple;
assign  eccSingle   = ecc_single;
assign  eccMultiple = ecc_multiple;

// Swizzle data into DDR bus burst order for ECC generation and error detection.
// Each burst on the DDR bus forms an ECC code word.
// =============================================================================

// NI interface order example:  4 byte data width
// wr_data_ni2mc          =  DDR bus burst/byte { 7/3 6/3 5/3 4/3  3/3 2/3 1/3 0/3
//                                                7/2 6/2 5/2 4/2  3/2 2/2 1/2 0/2
//                                                7/1 6/1 5/1 4/1  3/1 2/1 1/1 0/1
//                                                7/0 6/0 5/0 4/0  3/0 2/0 1/0 0/0 }
//
// wr_data_ni2mc_cw_order  = DDR bus burst/byte {  7/3 7/2 7/1 7/0
//                                                 6/3 6/2 6/1 6/0
//                                                 5/3 5/2 5/1 5/0
//                                                 4/3 4/2 4/1 4/0
//                                                 3/3 3/2 3/1 3/0
//                                                 2/3 2/2 2/1 2/0
//                                                 1/3 1/2 1/1 1/0
//                                                 0/3 0/2 0/1 0/0 }
//
// wr_data_mc2phy_cw_order = DDR bus burst/byte {  7/C 6/C 5/C 4/C
//                                                 3/C 2/C 1/C 0/C
//                                                 7/3 7/2 7/1 7/0
//                                                 6/3 6/2 6/1 6/0
//                                                 5/3 5/2 5/1 5/0
//                                                 4/3 4/2 4/1 4/0
//                                                 3/3 3/2 3/1 3/0
//                                                 2/3 2/2 2/1 2/0
//                                                 1/3 1/2 1/1 1/0
//                                                 0/3 0/2 0/1 0/0 }
//
// wr_data_ni2mc          =  DDR bus burst/byte { 7/C 6/C 5/C 4/C  3/C 2/C 1/C 0/C
//                                                7/3 6/3 5/3 4/3  3/3 2/3 1/3 0/3
//                                                7/2 6/2 5/2 4/2  3/2 2/2 1/2 0/2
//                                                7/1 6/1 5/1 4/1  3/1 2/1 1/1 0/1
//                                                7/0 6/0 5/0 4/0  3/0 2/0 1/0 0/0 }
//

integer pl_byte;
integer dq_byte;
integer burst;

reg  [DQ_WIDTH-1:0]            rd_data_phy2mc_burst[7:0];
wire [PAYLOAD_WIDTH*8-1:0]     rd_data_mc2ni_cw_order;
reg  [63:0]                    rd_data_mc2ni_byte[PAYLOAD_WIDTH/8-1:0];
reg  [PAYLOAD_WIDTH*8-1:0]     wr_data_ni2mc_cw_order;
reg  [PAYLOAD_WIDTH-1:0]       wr_data_ni2mc_burst[7:0];
wire [DQ_WIDTH*8-1:0]          wr_data_mc2phy_cw_order;
reg  [63:0]                    wr_data_mc2phy_byte[DQ_WIDTH/8-1:0];
reg  [PAYLOAD_DM_WIDTH*8-1:0]  wr_data_mask_ni2mc_cw_order;
reg  [PAYLOAD_DM_WIDTH-1:0]    wr_data_mask_ni2mc_burst[7:0];
wire [DM_WIDTH*8-1:0]          wr_data_mask_mc2phy_cw_order;
reg  [7:0]                     wr_data_mask_mc2phy_byte[DM_WIDTH-1:0];

// Swizzle read data from NI format to DDR bus codeword per burst format
always @(*) begin
   for (burst = 0; burst < 8; burst++) begin
     for (pl_byte = 0; pl_byte < DQ_WIDTH/8; pl_byte++) begin
        rd_data_phy2mc_burst     [burst][pl_byte*8 +: 8] = rd_data_phy2mc_xif [burst*8 + pl_byte*64 +: 8];
     end // for pl_byte
     rd_data_phy2mc_cw_order     [burst*DQ_WIDTH    +: DQ_WIDTH]    = rd_data_phy2mc_burst     [burst];
   end // for burst
end // always

// Swizzle read data from DDR bus codeword per burst format to NI format
always @(*) begin
   for (dq_byte = 0; dq_byte < PAYLOAD_WIDTH/8; dq_byte++) begin
     for (burst = 0; burst < 8; burst++) begin
        rd_data_mc2ni_byte     [dq_byte][burst*8 +: 8] = rd_data_mc2ni_cw_order     [dq_byte*8 + burst*PAYLOAD_WIDTH +: 8];
     end // for burst
     rd_data_mc2ni     [dq_byte*64 +: 64] = rd_data_mc2ni_byte     [dq_byte];
   end // for dq_byte
end // always

// Swizzle write data from NI format to DDR bus codeword per burst format
always @(*) begin
   for (burst = 0; burst < 8; burst++) begin
     for (pl_byte = 0; pl_byte < PAYLOAD_WIDTH/8; pl_byte++) begin
        wr_data_ni2mc_burst     [burst][pl_byte*8 +: 8] = wr_data_ni2mc     [burst*8 + pl_byte*64 +: 8];
        wr_data_mask_ni2mc_burst[burst][pl_byte]        = wr_data_mask_ni2mc[burst   + pl_byte*8];
     end // for pl_byte
     wr_data_ni2mc_cw_order     [burst*PAYLOAD_WIDTH    +: PAYLOAD_WIDTH]    = wr_data_ni2mc_burst     [burst];
     wr_data_mask_ni2mc_cw_order[burst*PAYLOAD_DM_WIDTH +: PAYLOAD_DM_WIDTH] = wr_data_mask_ni2mc_burst[burst];
   end // for burst
end // always


// Swizzle write data from DDR bus codeword per burst format to NI format
always @(*) begin
   // First swizzle back the payload
   for (dq_byte = 0; dq_byte < DATA_WIDTH/8; dq_byte++) begin
     for (burst = 0; burst < 8; burst++) begin
        wr_data_mc2phy_byte     [dq_byte][burst*8 +: 8] = wr_data_mc2phy_cw_order     [dq_byte*8 + burst*DATA_WIDTH +: 8];
        wr_data_mask_mc2phy_byte[dq_byte][burst]        = wr_data_mask_mc2phy_cw_order[dq_byte   + burst*PAYLOAD_DM_WIDTH];
     end // for burst
     wr_data_mc2phy     [dq_byte*64 +: 64] = wr_data_mc2phy_byte     [dq_byte];
     wr_data_mask_mc2phy[dq_byte*8  +:  8] = wr_data_mask_mc2phy_byte[dq_byte];
   end // for dq_byte
   // Now swizzle out the check bits
   for (dq_byte = DATA_WIDTH/8; dq_byte < DQ_WIDTH/8; dq_byte++) begin
     for (burst = 0; burst < 8; burst++) begin
        wr_data_mc2phy_byte     [dq_byte][burst*8 +: 8] = wr_data_mc2phy_cw_order     [(dq_byte-DATA_WIDTH/8)*8 + burst*ECC_WIDTH + 8*DATA_WIDTH +: 8];
        wr_data_mask_mc2phy_byte[dq_byte][burst]        = wr_data_mask_mc2phy_cw_order[(dq_byte-PAYLOAD_WIDTH/8)   + burst*(DM_WIDTH-PAYLOAD_DM_WIDTH) + 8*PAYLOAD_DM_WIDTH];
     end // for burst
     wr_data_mc2phy     [dq_byte*64 +: 64] = wr_data_mc2phy_byte     [dq_byte];
     wr_data_mask_mc2phy[dq_byte*8  +:  8] = wr_data_mask_mc2phy_byte[dq_byte];
   end // for dq_byte
end // always


reg  [4:0] rd_data_addr_dly;
reg        rd_data_en_dly;
reg        rmw_rd_done_dly;
reg        ecc_status_valid;

generate
if (ECC=="OFF") begin

assign  wr_data_mc2phy_cw_order      = wr_data_ni2mc_cw_order;
assign  wr_data_mask_mc2phy_cw_order = wr_data_mask_ni2mc_cw_order;
assign  rd_data_mc2ni_cw_order       = rd_data_phy2mc_cw_order;
assign  rd_data_addr_mc2ni           = rd_data_addr_phy2mc;
assign  rd_data_en_mc2ni             = rd_data_en_phy2mc;
assign  rd_data_end_mc2ni            = rd_data_end_phy2mc;
assign  ecc_err_addr                 = '0;
assign  ecc_single                   = '0;
assign  ecc_multiple                 = '0;

end else begin


// Check ECC on RMW underfill reads and regular reads, but not periodic reads
wire ecc_status_valid_nxt = rmw_rd_done | rd_data_en_phy2mc;

always @(posedge clk) begin
  rd_data_addr_dly     <= #TCQ rd_data_addr_phy2mc;
  rd_data_en_dly       <= #TCQ rd_data_en_phy2mc;
  rmw_rd_done_dly      <= #TCQ rmw_rd_done;
  ecc_status_valid     <= #TCQ ecc_status_valid_nxt;
end

assign  rd_data_addr_mc2ni  = rd_data_addr_dly;
assign  rd_data_en_mc2ni    = rd_data_en_dly;
assign  rd_data_end_mc2ni   = rd_data_end_phy2mc;


ddr4_v2_2_10_mc_ecc_dec_fix #(
    .PAYLOAD_WIDTH       (PAYLOAD_WIDTH)
   ,.DATA_WIDTH          (DATA_WIDTH)
   ,.CODE_WIDTH          (DQ_WIDTH)
   ,.ECC_WIDTH           (ECC_WIDTH)
   ,.ADDR_FIFO_WIDTH     (ADDR_FIFO_WIDTH)
   ,.S_HEIGHT            (S_HEIGHT)
   ,.LR_WIDTH            (LR_WIDTH)
   ,.DQ_WIDTH            (DQ_WIDTH)
   ,.nCK_PER_CLK         (nCK_PER_CLK)
   ,.MEM                 (MEM)
   ,.ABITS               (ABITS)
   ,.COLBITS             (COLBITS)
   ,.RKBITS              (RKBITS)
   ,.TCQ                 (TCQ)
)u_ddr_mc_ecc_dec_fix(
    .clk                  (clk)
   ,.rst                  (rst)
   ,.winPortEncC          (winPortEncC)
   ,.non_per_rd_cas       (non_per_rd_cas)
   ,.cmdRmw               (cmdRmw)
   ,.cmdRank              (cmdRank)
   ,.cmdLRank             (cmdLRank)
   ,.cmdRow               (cmdRow)
   ,.cmdCol               (cmdCol)
   ,.cmdBank              (cmdBank)
   ,.cmdGroup             (cmdGroup)
   ,.ecc_status_valid_nxt (ecc_status_valid_nxt)
   ,.rd_data              (rd_data_mc2ni_cw_order)
   ,.ecc_err_addr         (ecc_err_addr)
   ,.ecc_single           (ecc_single)
   ,.ecc_multiple         (ecc_multiple)
   ,.h_rows               (h_rows)
   ,.phy_rddata           (rd_data_phy2mc_cw_order)
   ,.correct_en           (correct_en)
   ,.ecc_status_valid     (ecc_status_valid)
);


ddr4_v2_2_10_mc_ecc_buf #(
    .PAYLOAD_WIDTH         (PAYLOAD_WIDTH)
   ,.DATA_WIDTH            (DATA_WIDTH)
   ,.DATA_BUF_ADDR_WIDTH   (DATA_BUF_ADDR_WIDTH)
   ,.DATA_BUF_OFFSET_WIDTH (1)
   ,.TCQ                   (TCQ)
   ,.nCK_PER_CLK           (nCK_PER_CLK)
)u_ddr_mc_ecc_buf(
    .clk                   (clk)
   ,.rst                   (rst)
   ,.rd_merge_data         (rd_merge_data)       // buf output port data
   ,.wr_data_addr          (wr_data_addr_phy2mc) // buf output port address
   ,.wr_data_offset        (1'b0)
   ,.rd_data_addr          (rd_data_addr_dly)    // buf input port address
   ,.rd_data               (rd_data_mc2ni_cw_order)       // buf input port data
   ,.wr_ecc_buf            (rmw_rd_done_dly)     // buf input port enable
   ,.rd_data_offset        (1'b0)
);

ddr4_v2_2_10_mc_ecc_merge_enc #(
    .PAYLOAD_WIDTH       (PAYLOAD_WIDTH)
   ,.DATA_WIDTH          (DATA_WIDTH)
   ,.CODE_WIDTH          (DQ_WIDTH)
   ,.PAYLOAD_DM_WIDTH    (PAYLOAD_DM_WIDTH)
   ,.ECC_WIDTH           (ECC_WIDTH)
   ,.DQ_WIDTH            (DQ_WIDTH)
   ,.DM_WIDTH            (DM_WIDTH)
   ,.nCK_PER_CLK         (nCK_PER_CLK)
   ,.DATA_BUF_ADDR_WIDTH (DATA_BUF_ADDR_WIDTH)
   ,.TCQ                 (TCQ)
)u_ddr_mc_ecc_merge_enc(
    .clk                 (clk)
   ,.rst                 (rst)
   ,.mc_wrdata           (wr_data_enc2xor)
   ,.mc_wrdata_mask      (wr_data_mask_mc2phy_cw_order)
   ,.wr_data             (wr_data_ni2mc_cw_order)
   ,.wr_data_mask        (wr_data_mask_ni2mc_cw_order)
   ,.rd_merge_data       (rd_merge_data)
   ,.h_rows              (h_rows)
   ,.raw_not_ecc         (raw_not_ecc)
);

ddr4_v2_2_10_mc_ecc_fi_xor #(
    .DQ_WIDTH            (DQ_WIDTH)
   ,.DQS_WIDTH           (DQS_WIDTH)
   ,.DATA_WIDTH          (DATA_WIDTH)
   ,.ECC_WIDTH           (ECC_WIDTH)
   ,.nCK_PER_CLK         (nCK_PER_CLK)
   ,.TCQ                 (TCQ)
)u_ddr_mc_ecc_ri_xor(
    .clk                 (clk)
   ,.rst                 (rst)
   ,.wrdata_out          (wr_data_mc2phy_cw_order)
   ,.wrdata_in           (wr_data_enc2xor)
   ,.wrdata_en           (fi_xor_wrdata_en)
   ,.fi_xor_we           (fi_xor_we)
   ,.fi_xor_wrdata       (fi_xor_wrdata)
);

ddr4_v2_2_10_mc_ecc_gen #(
    .DATA_WIDTH          (DATA_WIDTH)
   ,.CODE_WIDTH          (DQ_WIDTH)
   ,.ECC_WIDTH           (ECC_WIDTH)
)u_ddr_mc_ecc_gen(
    .h_rows              (h_rows)
);

end  // else branch of if (ECC=="OFF")
endgenerate 


//synopsys translate_off

`ifdef MEM_INTERNAL
// Events - When asserted high in a test that passes all verification checks, these coverage
//          properties indicate that a functional coverage event has been hit.
// ---------------------------------------------------------------------------------------------

//  Single bit error detected and corrected
wire   e_mc_ecc_000 = correct_en & ecc_status_valid & ( | ecc_single ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_000: if (~rst) cover property (e_mc_ecc_000);

//  Single bit error detected and not corrected
wire   e_mc_ecc_001 = ~correct_en & ecc_status_valid & ( | ecc_single ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_001: if (~rst) cover property (e_mc_ecc_001);

//  Uncorrectable error detected
wire   e_mc_ecc_002 = ecc_status_valid & ( | ecc_multiple ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_002: if (~rst) cover property (e_mc_ecc_002);

//  Single bit error detected in all burst positions
wire   e_mc_ecc_003 = correct_en & ecc_status_valid & ( & ecc_single ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_003: if (~rst) cover property (e_mc_ecc_003);

//  Single bit error detected in burst 0
wire   e_mc_ecc_004 = correct_en & ecc_status_valid & ( ecc_single == 8'h01 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_004: if (~rst) cover property (e_mc_ecc_004);

//  Single bit error detected in burst 1
wire   e_mc_ecc_005 = correct_en & ecc_status_valid & ( ecc_single == 8'h02 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_005: if (~rst) cover property (e_mc_ecc_005);

//  Single bit error detected in burst 2
wire   e_mc_ecc_006 = correct_en & ecc_status_valid & ( ecc_single == 8'h04 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_006: if (~rst) cover property (e_mc_ecc_006);

//  Single bit error detected in burst 3
wire   e_mc_ecc_007 = correct_en & ecc_status_valid & ( ecc_single == 8'h08 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_007: if (~rst) cover property (e_mc_ecc_007);

//  Single bit error detected in burst 4
wire   e_mc_ecc_008 = correct_en & ecc_status_valid & ( ecc_single == 8'h10 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_008: if (~rst) cover property (e_mc_ecc_008);

//  Single bit error detected in burst 5
wire   e_mc_ecc_009 = correct_en & ecc_status_valid & ( ecc_single == 8'h20 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_009: if (~rst) cover property (e_mc_ecc_009);

//  Single bit error detected in burst 6
wire   e_mc_ecc_010 = correct_en & ecc_status_valid & ( ecc_single == 8'h40 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_010: if (~rst) cover property (e_mc_ecc_010);

//  Single bit error detected in burst 7
wire   e_mc_ecc_011 = correct_en & ecc_status_valid & ( ecc_single == 8'h80 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_011: if (~rst) cover property (e_mc_ecc_011);

//  Multiple bit error detected in burst 0
wire   e_mc_ecc_012 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h01 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_012: if (~rst) cover property (e_mc_ecc_012);

//  Multiple bit error detected in burst 1
wire   e_mc_ecc_013 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h02 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_013: if (~rst) cover property (e_mc_ecc_013);

//  Multiple bit error detected in burst 2
wire   e_mc_ecc_014 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h04 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_014: if (~rst) cover property (e_mc_ecc_014);

//  Multiple bit error detected in burst 3
wire   e_mc_ecc_015 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h08 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_015: if (~rst) cover property (e_mc_ecc_015);

//  Multiple bit error detected in burst 4
wire   e_mc_ecc_016 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h10 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_016: if (~rst) cover property (e_mc_ecc_016);

//  Multiple bit error detected in burst 5
wire   e_mc_ecc_017 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h20 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_017: if (~rst) cover property (e_mc_ecc_017);

//  Multiple bit error detected in burst 6
wire   e_mc_ecc_018 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h40 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_018: if (~rst) cover property (e_mc_ecc_018);

//  Multiple bit error detected in burst 7
wire   e_mc_ecc_019 = correct_en & ecc_status_valid & ( ecc_multiple == 8'h80 ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_019: if (~rst) cover property (e_mc_ecc_019);

//  Mix of single and multiple bit errors detected
wire   e_mc_ecc_020 = correct_en & ecc_status_valid & ( | ecc_multiple ) & ( | ecc_single ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_020: if (~rst) cover property (e_mc_ecc_020);

//  Mix of single and multiple bit errors detected in all bursts
wire   e_mc_ecc_021 = correct_en & ecc_status_valid & ( & ( ecc_multiple | ecc_single ) ) & ( ECC == "ON" );
always @(posedge clk) mc_ecc_021: if (~rst) cover property (e_mc_ecc_021);

//  Mix of single and multiple bit errors detected in all bursts on a rmw
wire   e_mc_ecc_022 = correct_en & ecc_status_valid & ( & ( ecc_multiple | ecc_single ) ) & rmw_rd_done_dly & ( ECC == "ON" );
always @(posedge clk) mc_ecc_022: if (~rst) cover property (e_mc_ecc_022);

//  Single bit errors detected on a rmw
wire   e_mc_ecc_023 = correct_en & ecc_status_valid & ( | ecc_single ) & rmw_rd_done_dly & ( ECC == "ON" );
always @(posedge clk) mc_ecc_023: if (~rst) cover property (e_mc_ecc_023);

// Single bit error detected in 3ds part at LR other than 0
wire   e_mc_ecc_024 = (S_HEIGHT > 1) & ecc_status_valid & (|ecc_single ) & (ECC == "ON") & (|ecc_err_addr[51:48]);
always @(posedge clk) mc_ecc_024: if (~rst) cover property (e_mc_ecc_024);

// Multi bit error detected in 3ds part at LR other than 0
wire   e_mc_ecc_025 = (S_HEIGHT > 1) & ecc_status_valid & (|ecc_multiple ) & (ECC == "ON") & (|ecc_err_addr[51:48]);
always @(posedge clk) mc_ecc_025: if (~rst) cover property (e_mc_ecc_025);

// Asserts - When asserted high, an illegal condition has been detected and the test has failed.
// ---------------------------------------------------------------------------------------------

// Single and multiple errors detected in same burst
wire   a_mc_ecc_000 = correct_en & ecc_status_valid & ( | ( ecc_multiple & ecc_single ) ) & ( ECC == "ON" );
always @(posedge clk) if (~rst) assert property (~a_mc_ecc_000);


`endif

//synopsys translate_on


endmodule

