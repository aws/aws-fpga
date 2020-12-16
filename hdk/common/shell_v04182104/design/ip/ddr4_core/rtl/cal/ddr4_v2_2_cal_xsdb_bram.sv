/******************************************************************************
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
******************************************************************************/
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor             : Xilinx
// \   \   \/     Version            : 2.0
//  \   \         Application        : MIG
//  /   /         Filename           : ddr4_v2_2_10_cal_xsdb_bram.sv
// /___/   /\     Date Last Modified : $Date: 2015/04/23 $
// \   \  /  \    Date Created       : Tue May 13 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_cal_xsdb_bram module
// Reference        :
// Revision History :
//*****************************************************************************
`timescale 1ns / 1ps

(* bram_map="yes" *)

module ddr4_v2_2_10_cal_xsdb_bram
    #(	
    
		parameter       	  MEM                        	  =  "DDR4"
		,parameter       	  DBYTES                     	  =  8 //4
		,parameter            START_ADDRESS                   =  18
		,parameter  		  SPREAD_SHEET_VERSION            =  2
		,parameter            RTL_VERSION                     =  0
		,parameter            MEM_CODE                        =  0
		,parameter  		  MEMORY_TYPE                     =  (MEM == "DDR4") ? 2 : 1
		,parameter            MEMORY_CONFIGURATION            =  1
		,parameter            MEMORY_VOLTAGE                  =  1
        ,parameter            CLKFBOUT_MULT_PLL               =  4
        ,parameter            DIVCLK_DIVIDE_PLL               =  1
        ,parameter            CLKOUT0_DIVIDE_PLL              =  1
        ,parameter            CLKFBOUT_MULT_MMCM              =  4
        ,parameter            DIVCLK_DIVIDE_MMCM              =  1
        ,parameter            CLKOUT0_DIVIDE_MMCM             =  4
		,parameter  		  DQBITS	                      =  64
		,parameter			  NIBBLE                          =  DQBITS/4
		,parameter  		  BITS_PER_BYTE                   =  8 //DQBITS/DBYTES
		,parameter  		  SLOTS                   =  1
		,parameter  		  ABITS                           =  10
		,parameter  		  BABITS                          =  2
		,parameter       	  BGBITS              	          =  2
		,parameter       	  CKEBITS                  		  =  4
		,parameter       	  CSBITS             	          =  4
		,parameter       	  ODTBITS                    	  =  4
		,parameter       	  DRAM_WIDTH                 	  =  8      // # of DQ per DQS
		,parameter       	  RANKS                      	  =  4 // 1      //1, 2, 3, or 4
		,parameter            S_HEIGHT                        =  1
		,parameter       	  nCK_PER_CLK                	  =  1      // # of memory CKs per fabric CLK
        ,parameter            tCK                             =  2000		
		,parameter       	  DM_DBI_SETTING             	  =  7     //// 3bits requried all 7
		,parameter            BISC_EN                         =  0
		,parameter       	  USE_CS_PORT             	      =  1     //// 1 bit
		,parameter            EXTRA_CMD_DELAY                 =  0     //// 1 bit
		,parameter            REG_CTRL_ON                     =  0     // RDIMM register control
		,parameter            CA_MIRROR                       =  0     //// 1 bit
		,parameter       	  DQS_GATE                   	  =  7
		,parameter       	  WRLVL                      	  =  7
		,parameter       	  RDLVL                      	  =  7
		,parameter       	  RDLVL_DBI                       =  7
		,parameter       	  WR_DQS_DQ                  	  =  7
		,parameter       	  WR_DQS_DM_DBI                   =  7
		,parameter            WRITE_LAT                       =  7
		,parameter       	  RDLVL_COMPLEX                   =  3     ///2 bits required all 3
		,parameter       	  WR_DQS_COMPLEX                  =  3     ///2 bits required all 3
		,parameter       	  DQS_TRACKING               	  =  3
		,parameter       	  RD_VREF                    	  =  3
		,parameter       	  RD_VREF_PATTERN                 =  3
		,parameter       	  WR_VREF                    	  =  3
		,parameter       	  WR_VREF_PATTERN                 =  3
		,parameter       	  DQS_SAMPLE_CNT             	  =  127
		,parameter       	  WRLVL_SAMPLE_CNT           	  =  255
		,parameter       	  RDLVL_SAMPLE_CNT           	  =  127
		,parameter       	  COMPLEX_LOOP_CNT           	  =  255
		,parameter       	  IODELAY_QTR_CK_TAP_CNT     	  =  255
		,parameter       	  DEBUG_MESSAGES     	          =  0
		,parameter         	  MR0                     		  =  13'b0000000110000
		,parameter         	  MR1                     		  =  13'b0000100000001 //RTT_NOM=RZQ/4 (60 Ohm)
		,parameter         	  MR2                     		  =  13'b0000000011000
		,parameter         	  MR3                     		  =  13'b0000000000000
		,parameter         	  MR4                     		  =  13'b0000000000000
		,parameter         	  MR5                     		  =  13'b0010000000000
		,parameter         	  MR6                     		  =  13'b0100000000000
		,parameter            ODTWR                           = 16'h0000
		,parameter            ODTRD                           = 16'h0000
		,parameter            SLOT0_CONFIG                    = 0     // all 9 bits
		,parameter            SLOT1_CONFIG                    = 0     // all 9 bits
		,parameter            SLOT0_FUNC_CS                   = 0     // all 9 bits
		,parameter            SLOT1_FUNC_CS                   = 0     // all 9 bits
		,parameter            SLOT0_ODD_CS                    = 0     // all 9 bits
		,parameter            SLOT1_ODD_CS                    = 0     // all 9 bits
		,parameter            DDR4_REG_RC03                   = 0     // all 9 bits
		,parameter            DDR4_REG_RC04                   = 0     // all 9 bits
		,parameter            DDR4_REG_RC05                   = 0     // all 9 bits
		,parameter            DDR4_REG_RC3X                   = 0     // all 9 bits
		
		,parameter         	  MR0_0                   		  =  MR0[8:0]
		,parameter         	  MR0_1                   		  =  {5'b0,MR0[12:9]}
		,parameter         	  MR1_0                   		  =  MR1[8:0]
		,parameter         	  MR1_1                   		  =  {5'b0,MR1[12:9]}
		,parameter         	  MR2_0                   	 	  =  MR2[8:0]
		,parameter         	  MR2_1                   		  =  {5'b0,MR2[12:9]}
		,parameter         	  MR3_0                   		  =  MR3[8:0]
		,parameter         	  MR3_1                   		  =  {5'b0,MR3[12:9]}
		,parameter         	  MR4_0                   		  =  MR4[8:0]
		,parameter         	  MR4_1                   		  =  {5'b0,MR4[12:9]}
		,parameter         	  MR5_0                   		  =  MR5[8:0]
		,parameter         	  MR5_1                   		  =  {5'b0,MR5[12:9]}
		,parameter         	  MR6_0                   		  =  MR6[8:0]
		,parameter         	  MR6_1                   		  =  {5'b0,MR6[12:9]}
  
       ,parameter NUM_BRAMS    = 1
	   ,parameter SIZE         = 36 * 1024 * NUM_BRAMS
    // Specify INITs as 9 bit blocks (256 locations per blockRAM)
       ,parameter ADDR_WIDTH   = 16
	   ,parameter DATA_WIDTH   = 9
       ,parameter PIPELINE_REG = 1 
    )
  (
	
		clka,
		clkb,
		ena,
		enb,
		addra,
		addrb,
		dina,
		dinb,
		douta,
		doutb,
		wea,
		web,
		rsta,
		rstb
);
input clka;
input clkb;
input ena;
input enb;
input [ADDR_WIDTH-1:0]addra;
input [ADDR_WIDTH-1:0]addrb;
input [DATA_WIDTH-1:0]dina;
input [DATA_WIDTH-1:0]dinb;
input wea;
input web;
input rsta;
input rstb;
output reg [DATA_WIDTH-1:0]douta;
output reg [DATA_WIDTH-1:0]doutb;


// Initial values to the BlockRam 0
localparam [8:0] mem0_init_0 = {4'b0,START_ADDRESS[4:0]};
localparam [8:0] mem0_init_1 = 9'b0;
localparam [8:0] mem0_init_2 = 9'b0;
localparam [8:0] mem0_init_3 = {5'b0,SPREAD_SHEET_VERSION[3:0]};
localparam [8:0] mem0_init_4 = {6'b0,MEMORY_TYPE[2:0]};
localparam [8:0] mem0_init_5 = RANKS;
localparam [8:0] mem0_init_6 = DBYTES[8:0]; // MAN - repeats DBYTES parameter (may hardwire to BYTES for initial SW compatability)
localparam [8:0] mem0_init_7 = NIBBLE[8:0];
localparam [8:0] mem0_init_8 = BITS_PER_BYTE[8:0];
localparam [8:0] mem0_init_9 = 9'b1;
localparam [8:0] mem0_init_10 = 9'b1;
localparam [8:0] mem0_init_11 = 9'b1;
localparam [8:0] mem0_init_12 = SLOTS;
localparam [8:0] mem0_init_13 = 9'b0;
localparam [8:0] mem0_init_14 = 9'b0;
localparam [8:0] mem0_init_15 = 9'b0;
localparam [8:0] mem0_init_16 = 9'b0;
localparam [8:0] mem0_init_17 = 9'b0;
localparam [8:0] mem0_init_18 = RTL_VERSION[8:0];
localparam [8:0] mem0_init_19 = 9'b0;
localparam [8:0] mem0_init_20 = NUM_BRAMS[8:0];
localparam [8:0] mem0_init_21 = {BGBITS[1:0],BABITS[1:0],ABITS[4:0]};
localparam [8:0] mem0_init_22 = {ODTBITS[2:0],CSBITS[2:0],CKEBITS[2:0]};
localparam [8:0] mem0_init_23 = DBYTES[8:0];
localparam [8:0] mem0_init_24 = DRAM_WIDTH[8:0];
localparam [8:0] mem0_init_25 = {CA_MIRROR[0],REG_CTRL_ON[0],EXTRA_CMD_DELAY[0],USE_CS_PORT[0],BISC_EN[0],DM_DBI_SETTING[2:0],nCK_PER_CLK[0]};
localparam [8:0] mem0_init_26 = {RDLVL[2:0],WRLVL[2:0],DQS_GATE[2:0]};
localparam [8:0] mem0_init_27 = {WR_DQS_DM_DBI[2:0],WR_DQS_DQ[2:0],RDLVL_DBI[2:0]};
localparam [8:0] mem0_init_28 = {WR_DQS_COMPLEX[2:0],RDLVL_COMPLEX[2:0],WRITE_LAT[2:0]};
localparam [8:0] mem0_init_29 = {DEBUG_MESSAGES[0],RD_VREF_PATTERN[1:0],WR_VREF_PATTERN[1:0],RD_VREF[1:0],WR_VREF[1:0]};
localparam [8:0] mem0_init_30 = {7'b0,DQS_TRACKING[1:0]};
localparam [8:0] mem0_init_31 = DQS_SAMPLE_CNT[8:0];
localparam [8:0] mem0_init_32 = WRLVL_SAMPLE_CNT[8:0];
localparam [8:0] mem0_init_33 = RDLVL_SAMPLE_CNT[8:0];
localparam [8:0] mem0_init_34 = COMPLEX_LOOP_CNT[8:0];
localparam [8:0] mem0_init_35 = IODELAY_QTR_CK_TAP_CNT[8:0];
localparam [8:0] mem0_init_36 = {5'b0,S_HEIGHT[3:0]};
localparam [8:0] mem0_init_37 = 9'b0;
localparam [8:0] mem0_init_38 = 9'b0;
localparam [8:0] mem0_init_39 = 9'b0;
localparam [8:0] mem0_init_40 = {1'b0, ODTWR[7:0]};
localparam [8:0] mem0_init_41 = {1'b0, ODTWR[15:8]};
localparam [8:0] mem0_init_42 = {1'b0, ODTRD[7:0]};
localparam [8:0] mem0_init_43 = {1'b0, ODTRD[15:8]};
localparam [8:0] mem0_init_44 = SLOT0_CONFIG;
localparam [8:0] mem0_init_45 = SLOT1_CONFIG;
localparam [8:0] mem0_init_46 = SLOT0_FUNC_CS;
localparam [8:0] mem0_init_47 = SLOT1_FUNC_CS;
localparam [8:0] mem0_init_48 = SLOT0_ODD_CS;
localparam [8:0] mem0_init_49 = SLOT1_ODD_CS;
localparam [8:0] mem0_init_50 = DDR4_REG_RC03;
localparam [8:0] mem0_init_51 = DDR4_REG_RC04;
localparam [8:0] mem0_init_52 = DDR4_REG_RC05;
localparam [8:0] mem0_init_53 = DDR4_REG_RC3X;
localparam [8:0] mem0_init_54 = MR0_0[8:0];
localparam [8:0] mem0_init_55 = MR0_1[8:0];
localparam [8:0] mem0_init_56 = MR1_0[8:0];
localparam [8:0] mem0_init_57 = MR1_1[8:0];
localparam [8:0] mem0_init_58 = MR2_0[8:0];
localparam [8:0] mem0_init_59 = MR2_1[8:0];
localparam [8:0] mem0_init_60 = MR3_0[8:0];
localparam [8:0] mem0_init_61 = MR3_1[8:0];
localparam [8:0] mem0_init_62 = MR4_0[8:0];
localparam [8:0] mem0_init_63 = MR4_1[8:0];
localparam [8:0] mem0_init_64 = MR5_0[8:0];
localparam [8:0] mem0_init_65 = MR5_1[8:0];
localparam [8:0] mem0_init_66 = MR6_0[8:0];
localparam [8:0] mem0_init_67 = MR6_1[8:0];
localparam [8:0] mem0_init_68 = 9'b0;
localparam [8:0] mem0_init_69 = tCK[8:0];
localparam [8:0] mem0_init_70 = tCK[16:9];
localparam [8:0] mem0_init_71 = MEMORY_CONFIGURATION[8:0];
localparam [8:0] mem0_init_72 = MEMORY_VOLTAGE[8:0];
localparam [8:0] mem0_init_73 = CLKFBOUT_MULT_PLL[8:0];
localparam [8:0] mem0_init_74 = DIVCLK_DIVIDE_PLL[8:0];
localparam [8:0] mem0_init_75 = CLKFBOUT_MULT_MMCM[8:0];
localparam [8:0] mem0_init_76 = DIVCLK_DIVIDE_MMCM[8:0];
localparam [8:0] mem0_init_77 = 9'b0;
localparam [8:0] mem0_init_78 = 9'b0;
localparam [8:0] mem0_init_79 = 9'b0;
localparam [8:0] mem0_init_80 = 9'b0;
localparam [8:0] mem0_init_81 = 9'b0;
localparam [8:0] mem0_init_82 = 9'b0;
localparam [8:0] mem0_init_83 = 9'b0;
localparam [8:0] mem0_init_84 = 9'b0;
localparam [8:0] mem0_init_85 = 9'b0;
localparam [8:0] mem0_init_86 = 9'b0;
localparam [8:0] mem0_init_87 = 9'b0;
localparam [8:0] mem0_init_88 = 9'b0;
localparam [8:0] mem0_init_89 = 9'b0;
localparam [8:0] mem0_init_90 = 9'b0;
localparam [8:0] mem0_init_91 = 9'b0;
localparam [8:0] mem0_init_92 = 9'b0;
localparam [8:0] mem0_init_93 = 9'b0;
localparam [8:0] mem0_init_94 = 9'b0;
localparam [8:0] mem0_init_95 = 9'b0;
localparam [8:0] mem0_init_96 = 9'b0;
localparam [8:0] mem0_init_97 = 9'b0;
localparam [8:0] mem0_init_98 = 9'b0;
localparam [8:0] mem0_init_99 = 9'b0;
localparam [8:0] mem0_init_100 = 9'b0;
localparam [8:0] mem0_init_101 = 9'b0;
localparam [8:0] mem0_init_102 = 9'b0;
localparam [8:0] mem0_init_103 = 9'b0;
localparam [8:0] mem0_init_104 = 9'b0;
localparam [8:0] mem0_init_105 = 9'b0;
localparam [8:0] mem0_init_106 = 9'b0;
localparam [8:0] mem0_init_107 = 9'b0;
localparam [8:0] mem0_init_108 = 9'b0;
localparam [8:0] mem0_init_109 = 9'b0;
localparam [8:0] mem0_init_110 = 9'b0;
localparam [8:0] mem0_init_111 = 9'b0;
localparam [8:0] mem0_init_112 = 9'b0;
localparam [8:0] mem0_init_113 = 9'b0;
localparam [8:0] mem0_init_114 = 9'b0;
localparam [8:0] mem0_init_115 = 9'b0;
localparam [8:0] mem0_init_116 = 9'b0;
localparam [8:0] mem0_init_117 = 9'b0;
localparam [8:0] mem0_init_118 = 9'b0;
localparam [8:0] mem0_init_119 = 9'b0;
localparam [8:0] mem0_init_120 = 9'b0;
localparam [8:0] mem0_init_121 = 9'b0;
localparam [8:0] mem0_init_122 = 9'b0;
localparam [8:0] mem0_init_123 = 9'b0;
localparam [8:0] mem0_init_124 = 9'b0;
localparam [8:0] mem0_init_125 = 9'b0;
localparam [8:0] mem0_init_126 = 9'b0;
localparam [8:0] mem0_init_127 = 9'b0;
localparam [8:0] mem0_init_128 = 9'b0;
localparam [8:0] mem0_init_129 = 9'b0;
localparam [8:0] mem0_init_130 = 9'b0;
localparam [8:0] mem0_init_131 = 9'b0;
localparam [8:0] mem0_init_132 = 9'b0;
localparam [8:0] mem0_init_133 = 9'b0;
localparam [8:0] mem0_init_134 = 9'b0;
localparam [8:0] mem0_init_135 = 9'b0;
localparam [8:0] mem0_init_136 = 9'b0;
localparam [8:0] mem0_init_137 = 9'b0;
localparam [8:0] mem0_init_138 = 9'b0;
localparam [8:0] mem0_init_139 = 9'b0;
localparam [8:0] mem0_init_140 = 9'b0;
localparam [8:0] mem0_init_141 = 9'b0;
localparam [8:0] mem0_init_142 = 9'b0;
localparam [8:0] mem0_init_143 = 9'b0;
localparam [8:0] mem0_init_144 = 9'b0;
localparam [8:0] mem0_init_145 = 9'b0;
localparam [8:0] mem0_init_146 = 9'b0;
localparam [8:0] mem0_init_147 = 9'b0;
localparam [8:0] mem0_init_148 = 9'b0;
localparam [8:0] mem0_init_149 = 9'b0;
localparam [8:0] mem0_init_150 = 9'b0;
localparam [8:0] mem0_init_151 = 9'b0;
localparam [8:0] mem0_init_152 = 9'b0;
localparam [8:0] mem0_init_153 = 9'b0;
localparam [8:0] mem0_init_154 = 9'b0;
localparam [8:0] mem0_init_155 = 9'b0;
localparam [8:0] mem0_init_156 = 9'b0;
localparam [8:0] mem0_init_157 = 9'b0;
localparam [8:0] mem0_init_158 = 9'b0;
localparam [8:0] mem0_init_159 = 9'b0;
localparam [8:0] mem0_init_160 = 9'b0;
localparam [8:0] mem0_init_161 = 9'b0;
localparam [8:0] mem0_init_162 = 9'b0;
localparam [8:0] mem0_init_163 = 9'b0;
localparam [8:0] mem0_init_164 = 9'b0;
localparam [8:0] mem0_init_165 = 9'b0;
localparam [8:0] mem0_init_166 = 9'b0;
localparam [8:0] mem0_init_167 = 9'b0;
localparam [8:0] mem0_init_168 = 9'b0;
localparam [8:0] mem0_init_169 = 9'b0;
localparam [8:0] mem0_init_170 = 9'b0;
localparam [8:0] mem0_init_171 = 9'b0;
localparam [8:0] mem0_init_172 = 9'b0;
localparam [8:0] mem0_init_173 = 9'b0;
localparam [8:0] mem0_init_174 = 9'b0;
localparam [8:0] mem0_init_175 = 9'b0;
localparam [8:0] mem0_init_176 = 9'b0;
localparam [8:0] mem0_init_177 = 9'b0;
localparam [8:0] mem0_init_178 = 9'b0;
localparam [8:0] mem0_init_179 = 9'b0;
localparam [8:0] mem0_init_180 = 9'b0;
localparam [8:0] mem0_init_181 = 9'b0;
localparam [8:0] mem0_init_182 = 9'b0;
localparam [8:0] mem0_init_183 = 9'b0;
localparam [8:0] mem0_init_184 = 9'b0;
localparam [8:0] mem0_init_185 = 9'b0;
localparam [8:0] mem0_init_186 = 9'b0;
localparam [8:0] mem0_init_187 = 9'b0;
localparam [8:0] mem0_init_188 = 9'b0;
localparam [8:0] mem0_init_189 = 9'b0;
localparam [8:0] mem0_init_190 = 9'b0;
localparam [8:0] mem0_init_191 = 9'b0;
localparam [8:0] mem0_init_192 = 9'b0;
localparam [8:0] mem0_init_193 = 9'b0;
localparam [8:0] mem0_init_194 = 9'b0;
localparam [8:0] mem0_init_195 = 9'b0;
localparam [8:0] mem0_init_196 = 9'b0;
localparam [8:0] mem0_init_197 = 9'b0;
localparam [8:0] mem0_init_198 = 9'b0;
localparam [8:0] mem0_init_199 = 9'b0;
localparam [8:0] mem0_init_200 = 9'b0;
localparam [8:0] mem0_init_201 = 9'b0;
localparam [8:0] mem0_init_202 = 9'b0;
localparam [8:0] mem0_init_203 = 9'b0;
localparam [8:0] mem0_init_204 = 9'b0;
localparam [8:0] mem0_init_205 = 9'b0;
localparam [8:0] mem0_init_206 = 9'b0;
localparam [8:0] mem0_init_207 = 9'b0;
localparam [8:0] mem0_init_208 = 9'b0;
localparam [8:0] mem0_init_209 = 9'b0;
localparam [8:0] mem0_init_210 = 9'b0;
localparam [8:0] mem0_init_211 = 9'b0;
localparam [8:0] mem0_init_212 = 9'b0;
localparam [8:0] mem0_init_213 = 9'b0;
localparam [8:0] mem0_init_214 = 9'b0;
localparam [8:0] mem0_init_215 = 9'b0;
localparam [8:0] mem0_init_216 = 9'b0;
localparam [8:0] mem0_init_217 = 9'b0;
localparam [8:0] mem0_init_218 = 9'b0;
localparam [8:0] mem0_init_219 = 9'b0;
localparam [8:0] mem0_init_220 = 9'b0;
localparam [8:0] mem0_init_221 = 9'b0;
localparam [8:0] mem0_init_222 = 9'b0;
localparam [8:0] mem0_init_223 = 9'b0;
localparam [8:0] mem0_init_224 = 9'b0;
localparam [8:0] mem0_init_225 = 9'b0;
localparam [8:0] mem0_init_226 = 9'b0;
localparam [8:0] mem0_init_227 = 9'b0;
localparam [8:0] mem0_init_228 = 9'b0;
localparam [8:0] mem0_init_229 = 9'b0;
localparam [8:0] mem0_init_230 = 9'b0;
localparam [8:0] mem0_init_231 = 9'b0;
localparam [8:0] mem0_init_232 = 9'b0;
localparam [8:0] mem0_init_233 = 9'b0;
localparam [8:0] mem0_init_234 = 9'b0;
localparam [8:0] mem0_init_235 = 9'b0;
localparam [8:0] mem0_init_236 = 9'b0;
localparam [8:0] mem0_init_237 = 9'b0;
localparam [8:0] mem0_init_238 = 9'b0;
localparam [8:0] mem0_init_239 = 9'b0;
localparam [8:0] mem0_init_240 = 9'b0;
localparam [8:0] mem0_init_241 = 9'b0;
localparam [8:0] mem0_init_242 = 9'b0;
localparam [8:0] mem0_init_243 = 9'b0;
localparam [8:0] mem0_init_244 = 9'b0;
localparam [8:0] mem0_init_245 = 9'b0;
localparam [8:0] mem0_init_246 = 9'b0;
localparam [8:0] mem0_init_247 = 9'b0;
localparam [8:0] mem0_init_248 = 9'b0;
localparam [8:0] mem0_init_249 = 9'b0;
localparam [8:0] mem0_init_250 = 9'b0;
localparam [8:0] mem0_init_251 = 9'b0;
localparam [8:0] mem0_init_252 = 9'b0;
localparam [8:0] mem0_init_253 = 9'b0;
localparam [8:0] mem0_init_254 = 9'b0;
localparam [8:0] mem0_init_255 = 9'b0;

localparam [256*9-1:0] INIT_BRAM0 = {mem0_init_255,mem0_init_254,mem0_init_253,mem0_init_252,mem0_init_251,mem0_init_250,mem0_init_249,mem0_init_248,mem0_init_247,mem0_init_246,mem0_init_245,mem0_init_244,mem0_init_243,mem0_init_242,mem0_init_241,mem0_init_240,mem0_init_239,mem0_init_238,mem0_init_237,mem0_init_236,mem0_init_235,mem0_init_234,mem0_init_233,mem0_init_232,mem0_init_231,mem0_init_230,mem0_init_229,mem0_init_228,mem0_init_227,mem0_init_226,mem0_init_225,mem0_init_224,mem0_init_223,mem0_init_222,mem0_init_221,mem0_init_220,mem0_init_219,mem0_init_218,mem0_init_217,mem0_init_216,mem0_init_215,mem0_init_214,mem0_init_213,mem0_init_212,mem0_init_211,mem0_init_210,mem0_init_209,mem0_init_208,mem0_init_207,mem0_init_206,mem0_init_205,mem0_init_204,mem0_init_203,mem0_init_202,mem0_init_201,mem0_init_200,mem0_init_199,mem0_init_198,mem0_init_197,mem0_init_196,mem0_init_195,mem0_init_194,mem0_init_193,mem0_init_192,mem0_init_191,mem0_init_190,mem0_init_189,mem0_init_188,mem0_init_187,mem0_init_186,mem0_init_185,mem0_init_184,mem0_init_183,mem0_init_182,mem0_init_181,mem0_init_180,mem0_init_179,mem0_init_178,mem0_init_177,mem0_init_176,mem0_init_175,mem0_init_174,mem0_init_173,mem0_init_172,mem0_init_171,mem0_init_170,mem0_init_169,mem0_init_168,mem0_init_167,mem0_init_166,mem0_init_165,mem0_init_164,mem0_init_163,mem0_init_162,mem0_init_161,mem0_init_160,mem0_init_159,mem0_init_158,mem0_init_157,mem0_init_156,mem0_init_155,mem0_init_154,mem0_init_153,mem0_init_152,mem0_init_151,mem0_init_150,mem0_init_149,mem0_init_148,mem0_init_147,mem0_init_146,mem0_init_145,mem0_init_144,mem0_init_143,mem0_init_142,mem0_init_141,mem0_init_140,mem0_init_139,mem0_init_138,mem0_init_137,mem0_init_136,mem0_init_135,mem0_init_134,mem0_init_133,mem0_init_132,mem0_init_131,mem0_init_130,mem0_init_129,mem0_init_128,mem0_init_127,mem0_init_126,mem0_init_125,mem0_init_124,mem0_init_123,mem0_init_122,mem0_init_121,mem0_init_120,mem0_init_119,mem0_init_118,mem0_init_117,mem0_init_116,mem0_init_115,mem0_init_114,mem0_init_113,mem0_init_112,mem0_init_111,mem0_init_110,mem0_init_109,mem0_init_108,mem0_init_107,mem0_init_106,mem0_init_105,mem0_init_104,mem0_init_103,mem0_init_102,mem0_init_101,mem0_init_100,mem0_init_99,mem0_init_98,mem0_init_97,mem0_init_96,mem0_init_95,mem0_init_94,mem0_init_93,mem0_init_92,mem0_init_91,mem0_init_90,mem0_init_89,mem0_init_88,mem0_init_87,mem0_init_86,mem0_init_85,mem0_init_84,mem0_init_83,mem0_init_82,mem0_init_81,mem0_init_80,mem0_init_79,mem0_init_78,mem0_init_77,mem0_init_76,mem0_init_75,mem0_init_74,mem0_init_73,mem0_init_72,mem0_init_71,mem0_init_70,mem0_init_69,mem0_init_68,mem0_init_67,mem0_init_66,mem0_init_65,mem0_init_64,mem0_init_63,mem0_init_62,mem0_init_61,mem0_init_60,mem0_init_59,mem0_init_58,mem0_init_57,mem0_init_56,mem0_init_55,mem0_init_54,mem0_init_53,mem0_init_52,mem0_init_51,mem0_init_50,mem0_init_49,mem0_init_48,mem0_init_47,mem0_init_46,mem0_init_45,mem0_init_44,mem0_init_43,mem0_init_42,mem0_init_41,mem0_init_40,mem0_init_39,mem0_init_38,mem0_init_37,mem0_init_36,mem0_init_35,mem0_init_34,mem0_init_33,mem0_init_32,mem0_init_31,mem0_init_30,mem0_init_29,mem0_init_28,mem0_init_27,mem0_init_26,mem0_init_25,mem0_init_24,mem0_init_23,mem0_init_22,mem0_init_21,mem0_init_20,mem0_init_19,mem0_init_18,mem0_init_17,mem0_init_16,mem0_init_15,mem0_init_14,mem0_init_13,mem0_init_12,mem0_init_11,mem0_init_10,mem0_init_9,mem0_init_8,mem0_init_7,mem0_init_6,mem0_init_5,mem0_init_4,mem0_init_3,mem0_init_2,mem0_init_1,mem0_init_0};

// Populate INIT's for rest of BlockRAMs if required
localparam [256*9*NUM_BRAMS-1:0] INIT = ( NUM_BRAMS == 1 ) ? INIT_BRAM0 : ( NUM_BRAMS == 2 ) ? {2304'b0 ,INIT_BRAM0} : {{2{2304'b0}} ,INIT_BRAM0};

ddr4_v2_2_10_cfg_mem_mod # (
               .SIZE(SIZE),
               .INIT(INIT),
               .ADDR_WIDTH(ADDR_WIDTH),
               .DATA_WIDTH(9),
               .PIPELINE_REG(PIPELINE_REG)
              )
     mem_inst (
                .clka(clka),
                .clkb(clkb),
                .ena(ena),
                .enb(enb),
                .addra(addra),
                .addrb(addrb),
                .dina(dina),
                .dinb(dinb),
                .wea(wea),
                .web(web),
                .rsta(rsta),
                .rstb(rstb),
                .douta(douta),
                .doutb(doutb)
               );

endmodule

