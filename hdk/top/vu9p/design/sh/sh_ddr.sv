// =============================================================================
// Copyright 2016 Amazon.com, Inc. or its affiliates.
// All Rights Reserved Worldwide.
// Amazon Confidential information
// Restricted NDA Material
// =============================================================================

//--------------------------------------------------------------------------------
// Stats interface registers
//Register MAP
// 0x00 - GPIO 0 - read/write scratchpad
// 0x04 - GPIO 1 - read/write scratchpad
// 0x08 - DDR is ready status (bit 0)
// 0x0c - DDR reset (bit 0).  Set to drive reset to the DDR core.
// 0x10 - AXI Address - AXI Address for accessing DDR core (refer to Xilinx DDR specification - pg150)
// 0x14 - AXI Data - AXI Data access for accessing DDR core.  Read or write this register
//                   to read or write the Xilinx DDR controller registers.
// 0x20 - Write Words Low - Stats, number of words written (512-bit words).  Write to clear.  note is 64-bit counter
// 0x24 - Write Words High - Note can write either register to clear entire 64-bits
// 0x28 - Read Words Low - Stats, number of read words writen (512-bit words).  Write to clear
// 0x2c - Read Words High
//
// Interrupt Status0 - bit0: AXI-Lite interrupt from DDR core (refer to Xilinx DDR specification - pg150)


//--------------------------------------------------------------------------------

module sh_ddr #( parameter NUM_DDR = 3)
   (

   //---------------------------
   // Main clock/reset
   //---------------------------
   input clk,
   input rst_n,

   //--------------------------
   // DDR Physical Interface
   //--------------------------

// ------------------- DDR4 x72 RDIMM 2100 Interface A ----------------------------------
    input                CLK_300M_DIMM0_DP,
    input                CLK_300M_DIMM0_DN,
    output logic         M_A_ACT_N,
    output logic[16:0]   M_A_MA,
    output logic[1:0]    M_A_BA,
    output logic[1:0]    M_A_BG,
    output logic[0:0]    M_A_CKE,
    output logic[0:0]    M_A_ODT,
    output logic[0:0]    M_A_CS_N,
    output logic[0:0]    M_A_CLK_DN,
    output logic[0:0]    M_A_CLK_DP,
    output logic         RST_DIMM_A_N,
    output logic         M_A_PAR,
    inout  [63:0]        M_A_DQ,
    inout  [7:0]         M_A_ECC,
    inout  [17:0]        M_A_DQS_DP,
    inout  [17:0]        M_A_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface B ----------------------------------
    input                CLK_300M_DIMM1_DP,
    input                CLK_300M_DIMM1_DN,
    output logic         M_B_ACT_N,
    output logic[16:0]   M_B_MA,
    output logic[1:0]    M_B_BA,
    output logic[1:0]    M_B_BG,
    output logic[0:0]    M_B_CKE,
    output logic[0:0]    M_B_ODT,
    output logic[0:0]    M_B_CS_N,
    output logic[0:0]    M_B_CLK_DN,
    output logic[0:0]    M_B_CLK_DP,
    output logic         RST_DIMM_B_N,
    output logic         M_B_PAR,
    inout  [63:0]        M_B_DQ,
    inout  [7:0]         M_B_ECC,
    inout  [17:0]        M_B_DQS_DP,
    inout  [17:0]        M_B_DQS_DN,

// // ------------------- DDR4 x72 RDIMM 2100 Interface C ----------------------------------
//     input                CLK_300M_DIMM2_DP,
//     input                CLK_300M_DIMM2_DN,
//     output logic         M_C_ACT_N,
//     output logic[16:0]   M_C_MA,
//     output logic[1:0]    M_C_BA,
//     output logic[1:0]    M_C_BG,
//     output logic[0:0]    M_C_CKE,
//     output logic[0:0]    M_C_ODT,
//     output logic[0:0]    M_C_CS_N,
//     output logic[0:0]    M_C_CLK_DN,
//     output logic[0:0]    M_C_CLK_DP,
//     output logic         RST_DIMM_C_N,
//     output logic         M_C_PAR,
//     inout  [63:0]        M_C_DQ,
//     inout  [7:0]         M_C_ECC,
//     inout  [17:0]        M_C_DQS_DP,
//     inout  [17:0]        M_C_DQS_DN,

// ------------------- DDR4 x72 RDIMM 2100 Interface D ----------------------------------
    input                CLK_300M_DIMM3_DP,
    input                CLK_300M_DIMM3_DN,
    output logic         M_D_ACT_N,
    output logic[16:0]   M_D_MA,
    output logic[1:0]    M_D_BA,
    output logic[1:0]    M_D_BG,
    output logic[0:0]    M_D_CKE,
    output logic[0:0]    M_D_ODT,
    output logic[0:0]    M_D_CS_N,
    output logic[0:0]    M_D_CLK_DN,
    output logic[0:0]    M_D_CLK_DP,
    output logic         RST_DIMM_D_N,
    output logic         M_D_PAR,
    inout  [63:0]        M_D_DQ,
    inout  [7:0]         M_D_ECC,
    inout  [17:0]        M_D_DQS_DP,
    inout  [17:0]        M_D_DQS_DN,


   //------------------------------------------------------
   // DDR-4 Interface from CL (AXI-4)
   //------------------------------------------------------
   input[5:0] cl_sh_ddr_awid[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_awaddr[NUM_DDR-1:0],
   input[7:0] cl_sh_ddr_awlen[NUM_DDR-1:0],
   //input[10:0] cl_sh_ddr_awuser[NUM_DDR-1:0],
   input cl_sh_ddr_awvalid[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_awready,

   input[5:0] cl_sh_ddr_wid[NUM_DDR-1:0],
   input[511:0] cl_sh_ddr_wdata[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_wstrb[NUM_DDR-1:0],
   input[NUM_DDR-1:0] cl_sh_ddr_wlast,
   input[NUM_DDR-1:0] cl_sh_ddr_wvalid,
   output logic[NUM_DDR-1:0] sh_cl_ddr_wready,

   output logic[5:0] sh_cl_ddr_bid[NUM_DDR-1:0],
   output logic[1:0] sh_cl_ddr_bresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_bvalid,
   input[NUM_DDR-1:0] cl_sh_ddr_bready,

   input[5:0] cl_sh_ddr_arid[NUM_DDR-1:0],
   input[63:0] cl_sh_ddr_araddr[NUM_DDR-1:0],
   input[7:0] cl_sh_ddr_arlen[NUM_DDR-1:0],
   //input[10:0] cl_sh_ddr_aruser[NUM_DDR-1:0],
   input[NUM_DDR-1:0] cl_sh_ddr_arvalid,
   output logic[NUM_DDR-1:0] sh_cl_ddr_arready,

   output logic[5:0] sh_cl_ddr_rid[NUM_DDR-1:0],
   output logic[511:0] sh_cl_ddr_rdata[NUM_DDR-1:0],
   output logic[1:0] sh_cl_ddr_rresp[NUM_DDR-1:0],
   output logic[NUM_DDR-1:0] sh_cl_ddr_rlast,
   output logic[NUM_DDR-1:0] sh_cl_ddr_rvalid,
   input[NUM_DDR-1:0] cl_sh_ddr_rready,

   output logic[NUM_DDR-1:0] sh_cl_ddr_is_ready,

   input[7:0] sh_ddr_stat_addr[2:0],
   input[2:0] sh_ddr_stat_wr,
   input[2:0] sh_ddr_stat_rd,
   input[31:0] sh_ddr_stat_wdata[2:0],

   output logic[2:0] ddr_sh_stat_ack,
   output logic[31:0] ddr_sh_stat_rdata[2:0],
   output logic[7:0] ddr_sh_stat_int[2:0]
   );


`pragma protect begin_protected
`pragma protect version = 1
`pragma protect encrypt_agent = "XILINX"
`pragma protect encrypt_agent_info = "Xilinx Encryption Tool 2015"
`pragma protect key_keyowner = "Xilinx", key_keyname = "xilinx_2014_03", key_method = "rsa"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 256)
`pragma protect key_block
pjTiGp9f7+I0+Gxu/nWkJlrbVzwHEy/3BR8Ft9QYATTpEaMFmI7GkqTY1kALB9mdZ3tui8++eT1q
FHDrTjG+rHFhFG5QjBs6NR9LZd7GdeKXfPQXbKoQ5+jCc+O/q0Sn49uhrSdQeAYVR9EwqNZ9D9Kn
TIDvlDv4BFk2hyNBjkPZRChvfM9L5+nKGuqp84b5IrBDdvHGuzmNDZEaMmfilne0pS15zo+ld0B6
w2P6ur6SPqA2Bnu65WvNMA50H+QvMXzGfJTitPZVKRChZCQ2sxGLP9EDiaG2qMuk/UmHfU3nkdRX
V/dBFSiHNUxGrZ+rEvU78o47bCqcuWV4x+WzWA==

`pragma protect key_keyowner = "Synopsys", key_keyname = "SNPS-VCS-RSA-1", key_method = "rsa"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 128)
`pragma protect key_block
3xHcA4YCV+mo6PYLl0R0a6v21PW0a3O9A3HiKdjUcDmnLcr+iJ35ZhMP/7tnWJ9FAzyUTay5Qot2
rZTjxMV472T1qV3bYAy506BxUChOgEuwZIS1ON/E3OpOiM3FFxmwS1snBKq92w9OxcRq6ih7ZqH1
dHAfmIC0s/BORlJDac0=

`pragma protect key_keyowner = "Mentor Graphics Corporation", key_keyname = "MGC-VERIF-SIM-RSA-1", key_method = "rsa"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 128)
`pragma protect key_block
g+ZD3lb8Ltyb1IM5ve1eLkO0ETPLFL5VBogX7BgBTgCbf1DvDhx+3ZQi5NjUhp8dbS7mKVuVdpo0
faLC2F+q7oTI5ucYQVjyw+++KpTdmFcDFuKbQR/ezrT5/UrhivH4qwfhK45C2tRldf4b4UhocX+0
x7Cm7f59WXa0+1mF+uk=

`pragma protect data_method = "AES128-CBC"
`pragma protect encoding = (enctype = "BASE64", line_length = 76, bytes = 35024)
`pragma protect data_block
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
5LNJxSG6B5l9AgJ6biT0o4hcB9/NP1vcTvA=
`pragma protect end_protected


endmodule
