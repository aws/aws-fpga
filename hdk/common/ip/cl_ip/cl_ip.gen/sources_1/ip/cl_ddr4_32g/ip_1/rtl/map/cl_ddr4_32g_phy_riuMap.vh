 //DIRECT ACCESS to RIU (logical nibble order) 
 28'h???2???: begin 
   riu_addr_cal = io_address[5:0]; 
   riu_nibble = io_address[NIBBLE_CNT_WIDTH+6:6]; 
 end 
//========================================//
//===========Address ODELAYS=============//
//========================================//

28'h0010010: begin //c0_ddr4_adr[0] IO_L1P_T0L_N0_DBC_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h0;
end

28'h0010011: begin //c0_ddr4_adr[1] IO_L1N_T0L_N1_DBC_64
  riu_addr_cal = 6'hC;
  riu_nibble = 'h0;
end

28'h0010012: begin //c0_ddr4_adr[2] IO_L2P_T0L_N2_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h0;
end

28'h0010013: begin //c0_ddr4_adr[3] IO_L2N_T0L_N3_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h0;
end

28'h0010014: begin //c0_ddr4_adr[4] IO_L3P_T0L_N4_AD15P_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h0;
end

28'h0010015: begin //c0_ddr4_adr[5] IO_L3N_T0L_N5_AD15N_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h0;
end

28'h0010016: begin //c0_ddr4_adr[6] IO_L5P_T0U_N8_AD14P_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h1;
end

28'h0010017: begin //c0_ddr4_adr[7] IO_L5N_T0U_N9_AD14N_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h1;
end

28'h0010018: begin //c0_ddr4_adr[8] IO_L6P_T0U_N10_AD6P_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h1;
end

28'h0010019: begin //c0_ddr4_adr[9] IO_L6N_T0U_N11_AD6N_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h1;
end

28'h001001A: begin //c0_ddr4_adr[10] IO_L7P_T1L_N0_QBC_AD13P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h2;
end

28'h001001B: begin //c0_ddr4_adr[11] IO_L7N_T1L_N1_QBC_AD13N_64
  riu_addr_cal = 6'hC;
  riu_nibble = 'h2;
end

28'h001001C: begin //c0_ddr4_adr[12] IO_L8P_T1L_N2_AD5P_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h2;
end

28'h001001D: begin //c0_ddr4_adr[13] IO_L8N_T1L_N3_AD5N_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h2;
end

28'h001001E: begin //c0_ddr4_adr[14] IO_L9P_T1L_N4_AD12P_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h2;
end

28'h001001F: begin //c0_ddr4_adr[15] IO_L9N_T1L_N5_AD12N_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h2;
end

28'h0010020: begin //c0_ddr4_adr[16] IO_L10P_T1U_N6_QBC_AD4P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h3;
end

28'h0010080: begin //c0_ddr4_ba[0] IO_L10N_T1U_N7_QBC_AD4N_64
  riu_addr_cal = 6'hC;
  riu_nibble = 'h3;
end

28'h0010081: begin //c0_ddr4_ba[1] IO_L12P_T1U_N10_GC_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h3;
end

28'h0010100: begin //c0_ddr4_bg[0] IO_L12N_T1U_N11_GC_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h3;
end

28'h0010101: begin //c0_ddr4_bg[1] IO_T1U_N12_64
  riu_addr_cal = 6'h11;
  riu_nibble = 'h3;
end

28'h0010400: begin //c0_ddr4_cs_n[0] IO_L13P_T2L_N0_GC_QBC_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h4;
end

28'h0010401: begin //c0_ddr4_cs_n[1] IO_L13N_T2L_N1_GC_QBC_64
  riu_addr_cal = 6'hC;
  riu_nibble = 'h4;
end

28'h0010200: begin //c0_ddr4_cke[0] IO_L14P_T2L_N2_GC_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h4;
end

28'h0010201: begin //c0_ddr4_cke[1] IO_L14N_T2L_N3_GC_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h4;
end

28'h0010800: begin //c0_ddr4_odt[0] IO_L15P_T2L_N4_AD11P_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h4;
end

28'h0010801: begin //c0_ddr4_odt[1] IO_L15N_T2L_N5_AD11N_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h4;
end

28'h0010040: begin //c0_ddr4_act_n IO_L16P_T2U_N6_QBC_AD3P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h5;
end

28'h0011000: begin //c0_ddr4_parity IO_L17P_T2U_N8_AD10P_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h5;
end

//========================================//
//===========Address IDELAYS=============//
//========================================//

//========================================//
//===========Clock ODELAYS=============//
//========================================//

28'h0006100: begin //c0_ddr4_ck_t[0] IO_L4P_T0U_N6_DBC_AD7P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h1;
end

//========================================//
//===========Clock IDELAYS=============//
//========================================//

//========================================//
//===========Data ODELAYS=============//
//========================================//

28'h0004104: begin //c0_ddr4_dq[4] IO_L20P_T3L_N2_AD1P_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h6;
end

28'h0004105: begin //c0_ddr4_dq[5] IO_L20N_T3L_N3_AD1N_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h6;
end

28'h0004106: begin //c0_ddr4_dq[6] IO_L21P_T3L_N4_AD8P_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h6;
end

28'h0004107: begin //c0_ddr4_dq[7] IO_L21N_T3L_N5_AD8N_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h6;
end

28'h0004100: begin //c0_ddr4_dq[0] IO_L23P_T3U_N8_64
  riu_addr_cal = 6'hD;
  riu_nibble = 'h7;
end

28'h0004101: begin //c0_ddr4_dq[1] IO_L23N_T3U_N9_64
  riu_addr_cal = 6'hE;
  riu_nibble = 'h7;
end

28'h0004102: begin //c0_ddr4_dq[2] IO_L24P_T3U_N10_64
  riu_addr_cal = 6'hF;
  riu_nibble = 'h7;
end

28'h0004103: begin //c0_ddr4_dq[3] IO_L24N_T3U_N11_64
  riu_addr_cal = 6'h10;
  riu_nibble = 'h7;
end

28'h000410C: begin //c0_ddr4_dq[12] IO_L2P_T0L_N2_FOE_B_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'h8;
end

28'h000410D: begin //c0_ddr4_dq[13] IO_L2N_T0L_N3_FWE_FCS2_B_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'h8;
end

28'h000410E: begin //c0_ddr4_dq[14] IO_L3P_T0L_N4_AD15P_A26_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'h8;
end

28'h000410F: begin //c0_ddr4_dq[15] IO_L3N_T0L_N5_AD15N_A27_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'h8;
end

28'h0004108: begin //c0_ddr4_dq[8] IO_L5P_T0U_N8_AD14P_A22_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'h9;
end

28'h0004109: begin //c0_ddr4_dq[9] IO_L5N_T0U_N9_AD14N_A23_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'h9;
end

28'h000410A: begin //c0_ddr4_dq[10] IO_L6P_T0U_N10_AD6P_A20_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'h9;
end

28'h000410B: begin //c0_ddr4_dq[11] IO_L6N_T0U_N11_AD6N_A21_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'h9;
end

28'h0004114: begin //c0_ddr4_dq[20] IO_L8P_T1L_N2_AD5P_A16_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'ha;
end

28'h0004115: begin //c0_ddr4_dq[21] IO_L8N_T1L_N3_AD5N_A17_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'ha;
end

28'h0004116: begin //c0_ddr4_dq[22] IO_L9P_T1L_N4_AD12P_A14_D30_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'ha;
end

28'h0004117: begin //c0_ddr4_dq[23] IO_L9N_T1L_N5_AD12N_A15_D31_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'ha;
end

28'h0004110: begin //c0_ddr4_dq[16] IO_L11P_T1U_N8_GC_A10_D26_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'hb;
end

28'h0004111: begin //c0_ddr4_dq[17] IO_L11N_T1U_N9_GC_A11_D27_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'hb;
end

28'h0004112: begin //c0_ddr4_dq[18] IO_L12P_T1U_N10_GC_A08_D24_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'hb;
end

28'h0004113: begin //c0_ddr4_dq[19] IO_L12N_T1U_N11_GC_A09_D25_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'hb;
end

28'h000411C: begin //c0_ddr4_dq[28] IO_L14P_T2L_N2_GC_A04_D20_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'hc;
end

28'h000411D: begin //c0_ddr4_dq[29] IO_L14N_T2L_N3_GC_A05_D21_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'hc;
end

28'h000411E: begin //c0_ddr4_dq[30] IO_L15P_T2L_N4_AD11P_A02_D18_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'hc;
end

28'h000411F: begin //c0_ddr4_dq[31] IO_L15N_T2L_N5_AD11N_A03_D19_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'hc;
end

28'h0004118: begin //c0_ddr4_dq[24] IO_L17P_T2U_N8_AD10P_D14_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'hd;
end

28'h0004119: begin //c0_ddr4_dq[25] IO_L17N_T2U_N9_AD10N_D15_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'hd;
end

28'h000411A: begin //c0_ddr4_dq[26] IO_L18P_T2U_N10_AD2P_D12_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'hd;
end

28'h000411B: begin //c0_ddr4_dq[27] IO_L18N_T2U_N11_AD2N_D13_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'hd;
end

28'h0004124: begin //c0_ddr4_dq[36] IO_L20P_T3L_N2_AD1P_D08_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'he;
end

28'h0004125: begin //c0_ddr4_dq[37] IO_L20N_T3L_N3_AD1N_D09_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'he;
end

28'h0004126: begin //c0_ddr4_dq[38] IO_L21P_T3L_N4_AD8P_D06_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'he;
end

28'h0004127: begin //c0_ddr4_dq[39] IO_L21N_T3L_N5_AD8N_D07_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'he;
end

28'h0004120: begin //c0_ddr4_dq[32] IO_L23P_T3U_N8_I2C_SCLK_65
  riu_addr_cal = 6'hD;
  riu_nibble = 'hf;
end

28'h0004121: begin //c0_ddr4_dq[33] IO_L23N_T3U_N9_PERSTN1_I2C_SDA_65
  riu_addr_cal = 6'hE;
  riu_nibble = 'hf;
end

28'h0004122: begin //c0_ddr4_dq[34] IO_L24P_T3U_N10_EMCCLK_65
  riu_addr_cal = 6'hF;
  riu_nibble = 'hf;
end

28'h0004123: begin //c0_ddr4_dq[35] IO_L24N_T3U_N11_DOUT_CSO_B_65
  riu_addr_cal = 6'h10;
  riu_nibble = 'hf;
end

28'h000412C: begin //c0_ddr4_dq[44] IO_L2P_T0L_N2_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h10;
end

28'h000412D: begin //c0_ddr4_dq[45] IO_L2N_T0L_N3_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h10;
end

28'h000412E: begin //c0_ddr4_dq[46] IO_L3P_T0L_N4_AD15P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h10;
end

28'h000412F: begin //c0_ddr4_dq[47] IO_L3N_T0L_N5_AD15N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h10;
end

28'h0004128: begin //c0_ddr4_dq[40] IO_L5P_T0U_N8_AD14P_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h11;
end

28'h0004129: begin //c0_ddr4_dq[41] IO_L5N_T0U_N9_AD14N_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h11;
end

28'h000412A: begin //c0_ddr4_dq[42] IO_L6P_T0U_N10_AD6P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h11;
end

28'h000412B: begin //c0_ddr4_dq[43] IO_L6N_T0U_N11_AD6N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h11;
end

28'h0004134: begin //c0_ddr4_dq[52] IO_L8P_T1L_N2_AD5P_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h12;
end

28'h0004135: begin //c0_ddr4_dq[53] IO_L8N_T1L_N3_AD5N_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h12;
end

28'h0004136: begin //c0_ddr4_dq[54] IO_L9P_T1L_N4_AD12P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h12;
end

28'h0004137: begin //c0_ddr4_dq[55] IO_L9N_T1L_N5_AD12N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h12;
end

28'h0004130: begin //c0_ddr4_dq[48] IO_L11P_T1U_N8_GC_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h13;
end

28'h0004131: begin //c0_ddr4_dq[49] IO_L11N_T1U_N9_GC_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h13;
end

28'h0004132: begin //c0_ddr4_dq[50] IO_L12P_T1U_N10_GC_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h13;
end

28'h0004133: begin //c0_ddr4_dq[51] IO_L12N_T1U_N11_GC_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h13;
end

28'h000413C: begin //c0_ddr4_dq[60] IO_L14P_T2L_N2_GC_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h14;
end

28'h000413D: begin //c0_ddr4_dq[61] IO_L14N_T2L_N3_GC_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h14;
end

28'h000413E: begin //c0_ddr4_dq[62] IO_L15P_T2L_N4_AD11P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h14;
end

28'h000413F: begin //c0_ddr4_dq[63] IO_L15N_T2L_N5_AD11N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h14;
end

28'h0004138: begin //c0_ddr4_dq[56] IO_L17P_T2U_N8_AD10P_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h15;
end

28'h0004139: begin //c0_ddr4_dq[57] IO_L17N_T2U_N9_AD10N_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h15;
end

28'h000413A: begin //c0_ddr4_dq[58] IO_L18P_T2U_N10_AD2P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h15;
end

28'h000413B: begin //c0_ddr4_dq[59] IO_L18N_T2U_N11_AD2N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h15;
end

28'h0004144: begin //c0_ddr4_dq[68] IO_L20P_T3L_N2_AD1P_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h16;
end

28'h0004145: begin //c0_ddr4_dq[69] IO_L20N_T3L_N3_AD1N_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h16;
end

28'h0004146: begin //c0_ddr4_dq[70] IO_L21P_T3L_N4_AD8P_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h16;
end

28'h0004147: begin //c0_ddr4_dq[71] IO_L21N_T3L_N5_AD8N_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h16;
end

28'h0004140: begin //c0_ddr4_dq[64] IO_L23P_T3U_N8_66
  riu_addr_cal = 6'hD;
  riu_nibble = 'h17;
end

28'h0004141: begin //c0_ddr4_dq[65] IO_L23N_T3U_N9_66
  riu_addr_cal = 6'hE;
  riu_nibble = 'h17;
end

28'h0004142: begin //c0_ddr4_dq[66] IO_L24P_T3U_N10_66
  riu_addr_cal = 6'hF;
  riu_nibble = 'h17;
end

28'h0004143: begin //c0_ddr4_dq[67] IO_L24N_T3U_N11_66
  riu_addr_cal = 6'h10;
  riu_nibble = 'h17;
end

//========================================//
//===========Data IDELAYS=============//
//========================================//

28'h0004204: begin //c0_ddr4_dq[4] IO_L20P_T3L_N2_AD1P_64
  riu_addr_cal = 6'h14;
  riu_nibble = 'h6;
end

28'h0004205: begin //c0_ddr4_dq[5] IO_L20N_T3L_N3_AD1N_64
  riu_addr_cal = 6'h15;
  riu_nibble = 'h6;
end

28'h0004206: begin //c0_ddr4_dq[6] IO_L21P_T3L_N4_AD8P_64
  riu_addr_cal = 6'h16;
  riu_nibble = 'h6;
end

28'h0004207: begin //c0_ddr4_dq[7] IO_L21N_T3L_N5_AD8N_64
  riu_addr_cal = 6'h17;
  riu_nibble = 'h6;
end

28'h0004200: begin //c0_ddr4_dq[0] IO_L23P_T3U_N8_64
  riu_addr_cal = 6'h14;
  riu_nibble = 'h7;
end

28'h0004201: begin //c0_ddr4_dq[1] IO_L23N_T3U_N9_64
  riu_addr_cal = 6'h15;
  riu_nibble = 'h7;
end

28'h0004202: begin //c0_ddr4_dq[2] IO_L24P_T3U_N10_64
  riu_addr_cal = 6'h16;
  riu_nibble = 'h7;
end

28'h0004203: begin //c0_ddr4_dq[3] IO_L24N_T3U_N11_64
  riu_addr_cal = 6'h17;
  riu_nibble = 'h7;
end

28'h000420C: begin //c0_ddr4_dq[12] IO_L2P_T0L_N2_FOE_B_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'h8;
end

28'h000420D: begin //c0_ddr4_dq[13] IO_L2N_T0L_N3_FWE_FCS2_B_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'h8;
end

28'h000420E: begin //c0_ddr4_dq[14] IO_L3P_T0L_N4_AD15P_A26_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'h8;
end

28'h000420F: begin //c0_ddr4_dq[15] IO_L3N_T0L_N5_AD15N_A27_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'h8;
end

28'h0004208: begin //c0_ddr4_dq[8] IO_L5P_T0U_N8_AD14P_A22_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'h9;
end

28'h0004209: begin //c0_ddr4_dq[9] IO_L5N_T0U_N9_AD14N_A23_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'h9;
end

28'h000420A: begin //c0_ddr4_dq[10] IO_L6P_T0U_N10_AD6P_A20_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'h9;
end

28'h000420B: begin //c0_ddr4_dq[11] IO_L6N_T0U_N11_AD6N_A21_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'h9;
end

28'h0004214: begin //c0_ddr4_dq[20] IO_L8P_T1L_N2_AD5P_A16_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'ha;
end

28'h0004215: begin //c0_ddr4_dq[21] IO_L8N_T1L_N3_AD5N_A17_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'ha;
end

28'h0004216: begin //c0_ddr4_dq[22] IO_L9P_T1L_N4_AD12P_A14_D30_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'ha;
end

28'h0004217: begin //c0_ddr4_dq[23] IO_L9N_T1L_N5_AD12N_A15_D31_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'ha;
end

28'h0004210: begin //c0_ddr4_dq[16] IO_L11P_T1U_N8_GC_A10_D26_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'hb;
end

28'h0004211: begin //c0_ddr4_dq[17] IO_L11N_T1U_N9_GC_A11_D27_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'hb;
end

28'h0004212: begin //c0_ddr4_dq[18] IO_L12P_T1U_N10_GC_A08_D24_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'hb;
end

28'h0004213: begin //c0_ddr4_dq[19] IO_L12N_T1U_N11_GC_A09_D25_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'hb;
end

28'h000421C: begin //c0_ddr4_dq[28] IO_L14P_T2L_N2_GC_A04_D20_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'hc;
end

28'h000421D: begin //c0_ddr4_dq[29] IO_L14N_T2L_N3_GC_A05_D21_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'hc;
end

28'h000421E: begin //c0_ddr4_dq[30] IO_L15P_T2L_N4_AD11P_A02_D18_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'hc;
end

28'h000421F: begin //c0_ddr4_dq[31] IO_L15N_T2L_N5_AD11N_A03_D19_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'hc;
end

28'h0004218: begin //c0_ddr4_dq[24] IO_L17P_T2U_N8_AD10P_D14_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'hd;
end

28'h0004219: begin //c0_ddr4_dq[25] IO_L17N_T2U_N9_AD10N_D15_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'hd;
end

28'h000421A: begin //c0_ddr4_dq[26] IO_L18P_T2U_N10_AD2P_D12_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'hd;
end

28'h000421B: begin //c0_ddr4_dq[27] IO_L18N_T2U_N11_AD2N_D13_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'hd;
end

28'h0004224: begin //c0_ddr4_dq[36] IO_L20P_T3L_N2_AD1P_D08_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'he;
end

28'h0004225: begin //c0_ddr4_dq[37] IO_L20N_T3L_N3_AD1N_D09_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'he;
end

28'h0004226: begin //c0_ddr4_dq[38] IO_L21P_T3L_N4_AD8P_D06_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'he;
end

28'h0004227: begin //c0_ddr4_dq[39] IO_L21N_T3L_N5_AD8N_D07_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'he;
end

28'h0004220: begin //c0_ddr4_dq[32] IO_L23P_T3U_N8_I2C_SCLK_65
  riu_addr_cal = 6'h14;
  riu_nibble = 'hf;
end

28'h0004221: begin //c0_ddr4_dq[33] IO_L23N_T3U_N9_PERSTN1_I2C_SDA_65
  riu_addr_cal = 6'h15;
  riu_nibble = 'hf;
end

28'h0004222: begin //c0_ddr4_dq[34] IO_L24P_T3U_N10_EMCCLK_65
  riu_addr_cal = 6'h16;
  riu_nibble = 'hf;
end

28'h0004223: begin //c0_ddr4_dq[35] IO_L24N_T3U_N11_DOUT_CSO_B_65
  riu_addr_cal = 6'h17;
  riu_nibble = 'hf;
end

28'h000422C: begin //c0_ddr4_dq[44] IO_L2P_T0L_N2_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h10;
end

28'h000422D: begin //c0_ddr4_dq[45] IO_L2N_T0L_N3_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h10;
end

28'h000422E: begin //c0_ddr4_dq[46] IO_L3P_T0L_N4_AD15P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h10;
end

28'h000422F: begin //c0_ddr4_dq[47] IO_L3N_T0L_N5_AD15N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h10;
end

28'h0004228: begin //c0_ddr4_dq[40] IO_L5P_T0U_N8_AD14P_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h11;
end

28'h0004229: begin //c0_ddr4_dq[41] IO_L5N_T0U_N9_AD14N_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h11;
end

28'h000422A: begin //c0_ddr4_dq[42] IO_L6P_T0U_N10_AD6P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h11;
end

28'h000422B: begin //c0_ddr4_dq[43] IO_L6N_T0U_N11_AD6N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h11;
end

28'h0004234: begin //c0_ddr4_dq[52] IO_L8P_T1L_N2_AD5P_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h12;
end

28'h0004235: begin //c0_ddr4_dq[53] IO_L8N_T1L_N3_AD5N_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h12;
end

28'h0004236: begin //c0_ddr4_dq[54] IO_L9P_T1L_N4_AD12P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h12;
end

28'h0004237: begin //c0_ddr4_dq[55] IO_L9N_T1L_N5_AD12N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h12;
end

28'h0004230: begin //c0_ddr4_dq[48] IO_L11P_T1U_N8_GC_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h13;
end

28'h0004231: begin //c0_ddr4_dq[49] IO_L11N_T1U_N9_GC_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h13;
end

28'h0004232: begin //c0_ddr4_dq[50] IO_L12P_T1U_N10_GC_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h13;
end

28'h0004233: begin //c0_ddr4_dq[51] IO_L12N_T1U_N11_GC_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h13;
end

28'h000423C: begin //c0_ddr4_dq[60] IO_L14P_T2L_N2_GC_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h14;
end

28'h000423D: begin //c0_ddr4_dq[61] IO_L14N_T2L_N3_GC_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h14;
end

28'h000423E: begin //c0_ddr4_dq[62] IO_L15P_T2L_N4_AD11P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h14;
end

28'h000423F: begin //c0_ddr4_dq[63] IO_L15N_T2L_N5_AD11N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h14;
end

28'h0004238: begin //c0_ddr4_dq[56] IO_L17P_T2U_N8_AD10P_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h15;
end

28'h0004239: begin //c0_ddr4_dq[57] IO_L17N_T2U_N9_AD10N_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h15;
end

28'h000423A: begin //c0_ddr4_dq[58] IO_L18P_T2U_N10_AD2P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h15;
end

28'h000423B: begin //c0_ddr4_dq[59] IO_L18N_T2U_N11_AD2N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h15;
end

28'h0004244: begin //c0_ddr4_dq[68] IO_L20P_T3L_N2_AD1P_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h16;
end

28'h0004245: begin //c0_ddr4_dq[69] IO_L20N_T3L_N3_AD1N_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h16;
end

28'h0004246: begin //c0_ddr4_dq[70] IO_L21P_T3L_N4_AD8P_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h16;
end

28'h0004247: begin //c0_ddr4_dq[71] IO_L21N_T3L_N5_AD8N_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h16;
end

28'h0004240: begin //c0_ddr4_dq[64] IO_L23P_T3U_N8_66
  riu_addr_cal = 6'h14;
  riu_nibble = 'h17;
end

28'h0004241: begin //c0_ddr4_dq[65] IO_L23N_T3U_N9_66
  riu_addr_cal = 6'h15;
  riu_nibble = 'h17;
end

28'h0004242: begin //c0_ddr4_dq[66] IO_L24P_T3U_N10_66
  riu_addr_cal = 6'h16;
  riu_nibble = 'h17;
end

28'h0004243: begin //c0_ddr4_dq[67] IO_L24N_T3U_N11_66
  riu_addr_cal = 6'h17;
  riu_nibble = 'h17;
end

//========================================//
//===========Strobe ODELAYS=============//
//========================================//

28'h0008101: begin //c0_ddr4_dqs_t[1] IO_L19P_T3L_N0_DBC_AD9P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h6;
end

28'h0008100: begin //c0_ddr4_dqs_t[0] IO_L22P_T3U_N6_DBC_AD0P_64
  riu_addr_cal = 6'hB;
  riu_nibble = 'h7;
end

28'h0008103: begin //c0_ddr4_dqs_t[3] IO_L1P_T0L_N0_DBC_RS0_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'h8;
end

28'h0008102: begin //c0_ddr4_dqs_t[2] IO_L4P_T0U_N6_DBC_AD7P_A24_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'h9;
end

28'h0008105: begin //c0_ddr4_dqs_t[5] IO_L7P_T1L_N0_QBC_AD13P_A18_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'ha;
end

28'h0008104: begin //c0_ddr4_dqs_t[4] IO_L10P_T1U_N6_QBC_AD4P_A12_D28_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'hb;
end

28'h0008107: begin //c0_ddr4_dqs_t[7] IO_L13P_T2L_N0_GC_QBC_A06_D22_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'hc;
end

28'h0008106: begin //c0_ddr4_dqs_t[6] IO_L16P_T2U_N6_QBC_AD3P_A00_D16_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'hd;
end

28'h0008109: begin //c0_ddr4_dqs_t[9] IO_L19P_T3L_N0_DBC_AD9P_D10_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'he;
end

28'h0008108: begin //c0_ddr4_dqs_t[8] IO_L22P_T3U_N6_DBC_AD0P_D04_65
  riu_addr_cal = 6'hB;
  riu_nibble = 'hf;
end

28'h000810B: begin //c0_ddr4_dqs_t[11] IO_L1P_T0L_N0_DBC_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h10;
end

28'h000810A: begin //c0_ddr4_dqs_t[10] IO_L4P_T0U_N6_DBC_AD7P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h11;
end

28'h000810D: begin //c0_ddr4_dqs_t[13] IO_L7P_T1L_N0_QBC_AD13P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h12;
end

28'h000810C: begin //c0_ddr4_dqs_t[12] IO_L10P_T1U_N6_QBC_AD4P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h13;
end

28'h000810F: begin //c0_ddr4_dqs_t[15] IO_L13P_T2L_N0_GC_QBC_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h14;
end

28'h000810E: begin //c0_ddr4_dqs_t[14] IO_L16P_T2U_N6_QBC_AD3P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h15;
end

28'h0008111: begin //c0_ddr4_dqs_t[17] IO_L19P_T3L_N0_DBC_AD9P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h16;
end

28'h0008110: begin //c0_ddr4_dqs_t[16] IO_L22P_T3U_N6_DBC_AD0P_66
  riu_addr_cal = 6'hB;
  riu_nibble = 'h17;
end

//========================================//
//===========Strobe IDELAYS=============//
//========================================//

28'h0008201: begin //c0_ddr4_dqs_t[1] IO_L19P_T3L_N0_DBC_AD9P_64
  riu_addr_cal = 6'h12;
  riu_nibble = 'h6;
end

28'h0008200: begin //c0_ddr4_dqs_t[0] IO_L22P_T3U_N6_DBC_AD0P_64
  riu_addr_cal = 6'h12;
  riu_nibble = 'h7;
end

28'h0008203: begin //c0_ddr4_dqs_t[3] IO_L1P_T0L_N0_DBC_RS0_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'h8;
end

28'h0008202: begin //c0_ddr4_dqs_t[2] IO_L4P_T0U_N6_DBC_AD7P_A24_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'h9;
end

28'h0008205: begin //c0_ddr4_dqs_t[5] IO_L7P_T1L_N0_QBC_AD13P_A18_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'ha;
end

28'h0008204: begin //c0_ddr4_dqs_t[4] IO_L10P_T1U_N6_QBC_AD4P_A12_D28_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'hb;
end

28'h0008207: begin //c0_ddr4_dqs_t[7] IO_L13P_T2L_N0_GC_QBC_A06_D22_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'hc;
end

28'h0008206: begin //c0_ddr4_dqs_t[6] IO_L16P_T2U_N6_QBC_AD3P_A00_D16_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'hd;
end

28'h0008209: begin //c0_ddr4_dqs_t[9] IO_L19P_T3L_N0_DBC_AD9P_D10_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'he;
end

28'h0008208: begin //c0_ddr4_dqs_t[8] IO_L22P_T3U_N6_DBC_AD0P_D04_65
  riu_addr_cal = 6'h12;
  riu_nibble = 'hf;
end

28'h000820B: begin //c0_ddr4_dqs_t[11] IO_L1P_T0L_N0_DBC_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h10;
end

28'h000820A: begin //c0_ddr4_dqs_t[10] IO_L4P_T0U_N6_DBC_AD7P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h11;
end

28'h000820D: begin //c0_ddr4_dqs_t[13] IO_L7P_T1L_N0_QBC_AD13P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h12;
end

28'h000820C: begin //c0_ddr4_dqs_t[12] IO_L10P_T1U_N6_QBC_AD4P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h13;
end

28'h000820F: begin //c0_ddr4_dqs_t[15] IO_L13P_T2L_N0_GC_QBC_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h14;
end

28'h000820E: begin //c0_ddr4_dqs_t[14] IO_L16P_T2U_N6_QBC_AD3P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h15;
end

28'h0008211: begin //c0_ddr4_dqs_t[17] IO_L19P_T3L_N0_DBC_AD9P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h16;
end

28'h0008210: begin //c0_ddr4_dqs_t[16] IO_L22P_T3U_N6_DBC_AD0P_66
  riu_addr_cal = 6'h12;
  riu_nibble = 'h17;
end

