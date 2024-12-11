// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
`ifndef DDR4_PARAMS_PKG
 `define DDR4_PARAMS_PKG

package arch_package;
    timeunit 1ps;
    timeprecision 1ps;
`include "arch_defines.v"
    parameter int MAX_DM_BITS         = 2;
    parameter int MAX_DBI_BITS        = MAX_DM_BITS; // DM/DBI share pins in current spec.
    parameter int MAX_ADDR_BITS       = 21;
    parameter int MAX_ROW_ADDR_BITS   = 18;
    parameter int MAX_COL_ADDR_BITS   = 13; // Include AP/BLFLY
    parameter int MAX_BANK_BITS       = 2;
    parameter int MAX_RANK_BITS       = 3;
    parameter int MAX_DQ_BITS         = 16;
    parameter int MAX_DQS_BITS        = 2;
    parameter int MAX_CRC_EQUATION    = 8;
    parameter int MAX_CRC_TRANSFERS   = 2;
    parameter int MAX_BANK_GROUP_BITS = 2;
    parameter int MAX_BURST_LEN       = 8;
    parameter int AUTOPRECHARGEADDR   = 10;
    parameter int BLFLYSELECT         = 12;
    parameter int BANK_GROUP_SHIFT    = MAX_ADDR_BITS + MAX_BANK_BITS;
    parameter int BANK_SHIFT          = MAX_ADDR_BITS;
    parameter int MAX_MODEREGS        = 2**(MAX_BANK_BITS+MAX_BANK_GROUP_BITS);
    parameter int MODEREG_BITS        = MAX_ADDR_BITS + MAX_BANK_BITS + MAX_BANK_GROUP_BITS;
    parameter int MAX_MODEREG_SET_BITS = 14;
    parameter int MAX_BANKS_PER_GROUP = 2**(MAX_BANK_BITS);
    parameter int MAX_BANK_GROUPS     = 2**(MAX_BANK_GROUP_BITS);
    parameter int MAX_RANKS           = 2**(MAX_RANK_BITS);
    parameter int RTT_BITS = 16;
    typedef enum {
                  // Keep these in order of slowest to fastest for comparisons.
                  TS_1875, TS_1500, TS_1250, TS_1072, TS_938, TS_833, TS_750, TS_682, TS_625,
                  NUM_TS
    } UTYPE_TS;
    
    typedef enum {
        TCK_MIN, TCK_MAX, TCK_RANDOM
    } UTYPE_tCKMode;
    
    typedef struct packed {
        UTYPE_TS ts_loaded;
        UTYPE_tCKMode tck_mode;
        int ClockDutyCycle, tCHp_min, tCHp_max;
        int tCK, tCK_min, tCK_max, tCK_shmoo, tOffset;
        int tDQSQ, tQHp, tDS, tDH, tIPW;
        int tRPREp, tRPSTp, tQSHp, tQSLp;
        int tWPSTp, tWPREp;
        int tDQSCK, tDQSCK_min, tDQSCK_max, tDQSCK_dll_on, tDQSCK_dll_off, tDQSCK_dll_off_min, tDQSCK_dll_off_max;
        int tDQSLp, tDQSLp_min, tDQSLp_max, tDQSHp_min, tDQSHp_max, tDQSHp;
        int tDQSSp, tDQSSp_min, tDQSSp_max, tDQSSp_2tCK_min, tDQSSp_2tCK_max, tDQSSp_1tCK_min, tDQSSp_1tCK_max;
        int tDLLKc;
        int tRTP, tRTPc, tRTP_min, tRTPc_min;
        int tWTR_L, tWTRc_L, tWTR_L_CRC_DM, tWTRc_L_CRC_DM;
        int tWTR_S, tWTRc_S, tWTR_S_CRC_DM, tWTRc_S_CRC_DM;
        int tWR, tWRc, tWR_CRC_DMc, tWR_MPRc;
        int tCAL_min, tCALc_min;
        int tMRDc, tMOD, tMODc, tMPRRc;
        int tRCD, tRCDc, tRP, tRPc, tRAS, tRASc, tRC, tRCc;
        int tCCD_L, tCCDc_L, tCCD_S, tCCDc_S;
        int tRRD_L, tRRDc_L, tRRD_S, tRRDc_S, tRRDc_dlr, tFAW, tFAWc_dlr, tIS, tIH, tDIPW;
        int tZQinitc, tZQoperc, tZQCSc, tZQRTT, tZQRTTc;
        int tRFC, tRFCc, tRFC1, tRFC1c, tRFC2, tRFC2c, tRFC4, tRFC4c, tRFCc_dlr;
        int tXPR;
        int tXS, tXSc, tXS_Fast, tXS_Fastc, tXSDLLc, tCKESRc, tCKSRE, tCKSREc, tCKSRX, tCKSRXc, tXSR;
        int tXP, tXPc, tXPDLL, tXPDLLc, tCKE, tCKEc, tCPDEDc, tPD, tPDc;
        int tACTPDENc, tPREPDENc, tREFPDENc, tMRSPDENc, tMRSPDEN, tRDPDENc, tWRPDENc, tWRAPDENc;
        int tODTHc, tAON, tAON_min, tAON_max, tAOFp, tAOFp_min, tAOFp_max, tADCp, tADCp_min, tADCp_max;
        int tAONPD, tAONPDc, tAONPD_min, tAONPD_max, tAOF, tAOFPD, tAOFPDc, tAOFPD_min, tAOFPD_max, tAOFASp, tAONASp_min, tAONASp_max, tAOFASp_min, tAOFASp_max;
        int tWLMRDc, tWLDQSENc, tWLS, tWLS_nominal, tWLSc, tWLH, tWLHc;
        int tWLO_nominal, tWLO_min, tWLO_max, tWLOE_min, tWLOE_nominal, tWLOE_max, tWLOc_min, tWLOc_max, tWLOEc_min, tWLOEc_max;
        int tPAR_ALERT_ON_CYCLES, tPAR_ALERT_ON, tPAR_ALERT_ON_max, tPAR_ALERT_OFF, tPAR_CLOSE_BANKS, tPAR_tRP_tRAS_adjustment, tPAR_tRP_holdoff_adjustment;
        int tPAR_ALERT_PW, tPAR_ALERT_PW_min, tPAR_ALERT_PW_max, tPAR_ALERT_PWc, tPAR_ALERT_PWc_min, tPAR_ALERT_PWc_max;
        int tCRC_ALERT, tCRC_ALERT_min, tCRC_ALERT_max, tCRC_ALERT_PWc_min, tCRC_ALERT_PWc_max, tCRC_ALERT_PWc;
        int tSDO, tSDOc, tSDO_max, tSDOc_max;
        int tSYNC_GEARc, tCMD_GEARc, tGD_TRANSITIONc;
        int tMPED, tMPEDc, tCKMPE, tCKMPEc, tCKMPX, tCKMPXc, tMPX_H, tXMPDLLc, tXMPc;
        int tPWRUP, tRESET, tRESETCKE;
        int tBSCAN_Enable, tBSCAN_Valid;
        int tWLO_project, tRP_ref_internal, tRPc_ref_internal;
    } UTYPE_TimingParameters;
    parameter int FAW_DEPTH = 4;

    typedef enum{
        cmdACT, cmdPRE, cmdWR, cmdRD, cmdPREA,
        cmdNOP, cmdDES, cmdRDA, cmdWRA, cmdBST,
        cmdREF, cmdREFA, cmdSREFE, cmdSREFX,
        cmdNOCLK, cmdLMR, cmdPDX, cmdAPDE, cmdPPDE, cmdZQ
    } UTYPE_cmdtype;
    
    // Decoding table for commands pins.
    parameter     // {cs, act, ras, cas, we}
        LOAD_MODE_CMD = 5'b01000,
        REFRESH_CMD   = 5'b01001,
        PRECHARGE_CMD = 5'b01010,
        ACTIVATE_CMD  = 5'b00xxx,
        WRITE_CMD     = 5'b01100,
        READ_CMD      = 5'b01101,
        ZQ_CMD        = 5'b01110,
        NOP_CMD       = 5'b01111,
        SELF_REF_CMD  = 5'b01001,
        DESEL_CMD     = 5'b1xxxx
    ;
    
    class DDR4_cmd;
        UTYPE_cmdtype cmd;
        UTYPE_cmdtype raw_cmd;
        int rank;
        int bank_group;
        int bank;
        int addr;
        bit odt; // Defaults to 0.
        int sim_time; // Population optional.
        int cycle_count; // Population optional.
        int tCK = 10000;
        function new();
            cmd = cmdNOP;
            raw_cmd = cmdNOP;
            rank = -1;
            bank_group = -1;
            bank = -1;
            addr = -1;
            odt = 0;
            sim_time = 0;
            cycle_count = 0;
            tCK = 10000;
        endfunction
        function void Clone(DDR4_cmd rhs);
            this.cmd = rhs.cmd;
            this.raw_cmd = rhs.raw_cmd;
            this.rank = rhs.rank;
            this.bank_group = rhs.bank_group;
            this.bank = rhs.bank;
            this.addr = rhs.addr;
            this.odt = rhs.odt;
            this.sim_time= rhs.sim_time;
            this.cycle_count = rhs.cycle_count;
            this.tCK = rhs.tCK;
        endfunction
        function void Populate(UTYPE_cmdtype cmd_, int rank_, int bank_group_, int bank_, int addr_, int tCK_);
            cmd = cmd_;
            rank = rank_;
            bank_group = bank_group_;
            bank = bank_;
            addr = addr_;
            tCK = tCK_;
        endfunction
    endclass
    
    typedef enum {rBL8=0, rBLFLY=1, rBL4=2} UTYPE_blreg;
    typedef enum {rAL0=0, rALN1=1, rALN2=2, rALN3=3} UTYPE_alreg;
    typedef enum {SEQ=0, INT=1} UTYPE_bt;
    typedef enum {ODI_34=34, ODI_48=48, ODI_40=40, ODI_RES3=3} UTYPE_odi;
    typedef enum {RTTN_DIS=0, RTTN_60=60, RTTN_120=120, RTTN_40=40, RTTN_240=240, RTTN_48=48, RTTN_80=80, RTTN_34=34} UTYPE_rttn;
    typedef enum {RTTW_DIS=0, RTTW_120=120, RTTW_240=240, RTTW_Z=3, RTTW_80=80, RTTW_RES5=5, RTTW_RES6=6, RTTW_RES7=7} UTYPE_rttw;
    typedef enum {SERIAL=0, PARALLEL=1, STAGGERED=2, MPR_RES3=3} UTYPE_mpr;
    typedef enum {MPR_PATTERN=0, MPR_PARITY=1, MPR_MODEREG=2, MPR_PAGE3=3} UTYPE_mprpage;
    typedef enum {DELAY_WRITE_4=4, DELAY_WRITE_5=5, DELAY_WRITE_6=6, DELAY_WRITE_RES3=3} UTYPE_delay_write_crc_dm;
    typedef enum {LPASR_NORM=0, LPASR_REDUCED=1, LPASR_EXTENDED=2, LPASR_AUTO=3} UTYPE_lpasr;
    typedef enum {REF_1X=0, REF_2X=1, REF_4X=2, REF_RES3=3, REF_RES4=4, REF_FLY2X=5, REF_FLY4X=6, REF_RES7=7} UTYPE_refmode;
    typedef enum {CAPARITY_L0=0, CAPARITY_L4=4, CAPARITY_L5=5, CAPARITY_L6=6, CAPARITY_L8=8, CAPARITY_RES5, CAPARITY_RES6, CAPARITY_RES7} UTYPE_caparity_latency;
    typedef enum {RTTP_DIS=0, RTTP_60=60, RTTP_120=120, RTTP_40=40, RTTP_34=34, RTTP_48=48, RTTP_80=80, RTTP_240=240} UTYPE_rttp;
    typedef enum {VREF_DQ_RANGE1=0, VREF_DQ_RANGE2=1} UTYPE_vrefdqrange;
    
    typedef struct packed {
        UTYPE_blreg BL_reg; // BL value in the register.
        int BL; // Burst length.
        UTYPE_bt BT; // burst_type.
        int CL;
        bit DLL_reset;
        int write_recovery;
        bit DLL_enable;
        UTYPE_odi ODI;
        UTYPE_alreg AL_reg; // AL value in the register.
        int AL; // Actual AL in clks.
        bit write_levelization;
        UTYPE_rttn rtt_nominal;
        bit tDQS;
        bit qOff;
        int CWL; // cas_write_latency.
        UTYPE_lpasr LPASR;
        UTYPE_rttw rtt_write;
        bit write_crc_enable;
        bit trr_enable;
        int trr_ba;
        int trr_bg;
        UTYPE_mprpage MPR_page;
        bit MPR_enable;
        bit gear_down;
        bit perdram_addr;
        bit temp_sense_enable;
        UTYPE_refmode refresh_mode;
        UTYPE_delay_write_crc_dm delay_write_crc_dm;
        UTYPE_mpr MPR_mode;
        bit DCC;
        bit MPS;
        bit TCR_range;
        bit TCR_mode;
        bit vref_monitor;
        int CAL; // command_address_latency.
        bit fast_self_refresh;
        bit preamble_training;
        int rd_preamble_clocks;
        int wr_preamble_clocks;
        bit ppr_enable;
        UTYPE_caparity_latency CA_parity_latency;
        bit crc_error;
        bit CA_parity_error;
        bit odt_buffer_disable;
        UTYPE_rttp rtt_park;
        bit sticky_parity_error;
        bit dm_enable;
        bit latched_dm_enable;
        bit write_dbi;
        bit latched_write_dbi;
        bit read_dbi;
        bit latched_read_dbi;
        bit dll_frozen;
        int vref_training_offset;
        bit vref_training_range;
        bit vref_training;
        int tCCD_L;
        // Calculated values not directly tied to LMR bits.
        int RL, WL_calculated;
        } UTYPE_DutModeConfig;

    parameter int MIN_BL = 4;
    parameter int DEF_BL = 8;
    parameter int MAX_BL = MAX_BURST_LEN;
    parameter UTYPE_bt DEF_BT = INT;
    parameter int MIN_CL = 5;
    parameter int MAX_CL = 32;
    parameter int DEF_CL = 12;
    parameter int MIN_AL = 0;
    parameter int MAX_AL_REG = 2;
    parameter int MAX_AL_CLKS = MAX_CL - 1;
    parameter int MIN_CWL = 9;
    parameter int MAX_CWL = 20;
    parameter int DEF_CWL = 12;
    parameter int MIN_RL = MIN_CL - 1; // subtract one for the DLL disable mode.
    parameter int MAX_RL = MAX_CL + MAX_AL_CLKS;
    parameter int MIN_WL = 5;
    parameter int MAX_WL = MAX_CWL + MAX_AL_CLKS;
    parameter int MIN_WR = 10;
    parameter int MAX_WR = 28;
    parameter int DEF_WR = 12;
    parameter int MAX_CAL = 8;
    parameter int DEF_CAL = 0;
    parameter UTYPE_lpasr DEF_LPASR = LPASR_NORM;
    parameter UTYPE_rttw DEF_RTTW = RTTW_DIS;
    parameter UTYPE_mpr DEF_MPR_MODE = SERIAL;
    parameter UTYPE_delay_write_crc_dm DEF_DELAY_WRITE = DELAY_WRITE_4;
    parameter int MPR_DATA_BITS = 8;
    parameter int MPR_SELECT_BITS = 2;
    parameter int MAX_MPR_PATTERNS = 2**(MPR_SELECT_BITS);
    parameter int MPR_TEMP_BITS = 2;
    parameter int MAX_MPR_TEMPS = 2**(MPR_TEMP_BITS);
    parameter int MPR_TEMP0 = 'b0000_0000;
    parameter int MPR_TEMP1 = 'b0000_0001;
    parameter int MPR_TEMP2 = 'b0000_0010;
    parameter int MPR_TEMP3 = 'b0000_0011;
    parameter int MAX_MPR_DEFAULT_PATTERNS = 4;
    parameter int MPR_PAT_DEFAULT0 = 'b0101_0101;
    parameter int MPR_PAT_DEFAULT1 = 'b0011_0011;
    parameter int MPR_PAT_DEFAULT2 = 'b0000_1111;
    parameter int MPR_PAT_DEFAULT3 = 'b0000_0000;

    typedef enum {_2G=2, _4G=4, _8G=8, _16G=16} UTYPE_density;
    typedef enum {DDR4, PRE_DDR5} UTYPE_archtype;
    typedef struct packed{
        UTYPE_archtype arch_type;
        UTYPE_density density;
        int by_mode;
        int banks_per_group;
        int bank_mask;
        int bank_groups;
        int bank_group_mask;
        int ranks;
        int banks_per_rank;
        int rank_mask;
        int row_addr_bits;
        int row_cmd_bits;
        int row_bits; // Total row bits - WITH cmd pins.
        int row_mask; // Total row bit mask - WITH command pins.
        int row_addr_mask; // Mask for ONLY the addr lines - NOT INCLUDING cmd pins.
        int col_mask;
        logic[MAX_DQ_BITS-1:0] dq_mask;
        int num_dqs;
        logic[MAX_DQS_BITS-1:0] dqs_mask;
        int num_dqss;
        logic[MAX_DM_BITS-1:0] dm_mask;
        int num_dms;
        // Design specific limits.
        int min_CL, max_CL;
        int max_CL_dbi_enabled, max_CL_dbi_disabled, min_CL_dbi_enabled, min_CL_dbi_disabled;
        int min_CWL, max_CWL;
        int min_CL_dll_off, max_CL_dll_off;
        int min_CAL, max_CAL;
        // Design specific feature enables. (1 === feature_available)
        bit CAL_feature;
        bit tDQS_feature;
        bit LPASR_feature;
        bit gear_down_feature;
        bit trr_feature;
        bit ppr_feature;
        bit write_crc_feature;
        bit write_dbi_feature;
        bit read_dbi_feature;
        bit dm_enable_feature;
        bit rd_preamble_clocks_feature;
        bit wr_preamble_clocks_feature;
        bit preamble_training_feature;
        bit TCR_feature;
        bit MPS_feature;
        bit perdram_addr_feature;
        bit refresh_mode_feature;
        bit parity_error_feature;
        bit CA_parity_latency_feature;
        int max_CA_parity_latency;
        bit crc_error_feature;
        bit parity_alert_feature;
        bit sticky_parity_error_feature;
        bit temp_sense_feature;
        bit rtt_park_feature;
        bit dll_frozen_feature;
        bit cl_17_19_21_feature;
        bit cl_a12_feature;
        bit extended_wr;
        bit ignore_dbi_with_mpr;
    } UTYPE_dutconfig;

    function void dut_config_populate(inout UTYPE_dutconfig dut_config);
        dut_config.arch_type = DDR4;
        dut_config.col_mask = 16'b0000_0011_1111_1111;
        dut_config.row_addr_bits = 13;
        dut_config.row_addr_mask = 16'b0001_1111_1111_1111;
        if (4 == dut_config.by_mode) begin
            dut_config.dq_mask = 'b0000_0000_0000_0000_0000_0000_0000_1111;
            dut_config.dqs_mask = 'b0001;
            dut_config.dm_enable_feature = 0;
            dut_config.dm_mask = 'b0001;
            dut_config.num_dqs = 4;
            dut_config.num_dqss = 1;
            dut_config.num_dms = 1;
            dut_config.banks_per_group = 4;
            dut_config.bank_mask = 4'b0011;
            dut_config.bank_groups = 4;
            dut_config.bank_group_mask = 4'b0011;
        end else if (8 == dut_config.by_mode) begin
            dut_config.dq_mask = 'b0000_0000_0000_0000_0000_0000_1111_1111;
            dut_config.dqs_mask = 'b0001;
            dut_config.dm_enable_feature = 1;
            dut_config.dm_mask = 'b0001;
            dut_config.num_dqs = 8;
            dut_config.num_dqss = 1;
            dut_config.num_dms = 1;
            dut_config.banks_per_group = 4;
            dut_config.bank_mask = 4'b0011;
            dut_config.bank_groups = 4;
            dut_config.bank_group_mask = 4'b0011;
        end else if (16 == dut_config.by_mode) begin
            dut_config.dq_mask = 'b0000_0000_0000_0000_1111_1111_1111_1111;
            dut_config.dqs_mask = 'b0011;
            dut_config.dm_enable_feature = 1;
            dut_config.dm_mask = 'b0011;
            dut_config.num_dqs = 16;
            dut_config.num_dqss = 2;
            dut_config.num_dms = 2;
            dut_config.banks_per_group = 4;
            dut_config.bank_mask = 4'b0011;
            dut_config.bank_groups = 2;
            dut_config.bank_group_mask = 4'b0001;
        end else begin
            $display("ERROR: Unsupported DDR4 part width %0d", dut_config.by_mode);
            $finish;
        end
        dut_config.banks_per_rank = dut_config.banks_per_group * dut_config.bank_groups;
        if ((_2G == dut_config.density) && ((8 == dut_config.by_mode) || (16 == dut_config.by_mode))) begin
            dut_config.row_cmd_bits = 1;
            dut_config.row_bits = 14;
            dut_config.row_mask = 20'b0000_0011_1111_1111_1111;
        end else if (((_2G == dut_config.density) && (4 == dut_config.by_mode)) || 
                     ((_4G == dut_config.density) && ((8 == dut_config.by_mode) || (16 == dut_config.by_mode)))) begin
            dut_config.row_cmd_bits = 2;
            dut_config.row_bits = 15;
            dut_config.row_mask = 20'b0000_0111_1111_1111_1111;
        end else if (((_4G == dut_config.density) && (4 == dut_config.by_mode)) || 
                     ((_8G == dut_config.density) && ((8 == dut_config.by_mode) || (16 == dut_config.by_mode)))) begin
            dut_config.row_cmd_bits = 3;
            dut_config.row_bits = 16;
            dut_config.row_mask = 20'b0000_1111_1111_1111_1111;
        end else if (((_8G == dut_config.density) && (4 == dut_config.by_mode)) || 
                     ((_16G == dut_config.density) && ((8 == dut_config.by_mode) || (16 == dut_config.by_mode)))) begin
            dut_config.row_cmd_bits = 4;
            dut_config.row_bits = 17;
            dut_config.row_mask = 20'b0001_1111_1111_1111_1111;
        end else if ((_16G == dut_config.density) && (4 == dut_config.by_mode)) begin
            dut_config.row_cmd_bits = 5;
            dut_config.row_bits = 18;
            dut_config.row_mask = 20'b0011_1111_1111_1111_1111;
        end else begin
            $display("ERROR: Unsupported DDR4 density(%0d) and width(%0d) combination @%0t", 
                     dut_config.density, dut_config.by_mode, $time);
            $finish;
        end
        dut_config.min_CL = MIN_CL;
        dut_config.max_CL = MAX_CL;
        dut_config.max_CL_dbi_enabled = MAX_CL;
        dut_config.max_CL_dbi_disabled = MAX_CL;
        dut_config.min_CL_dbi_enabled = MIN_CL;
        dut_config.min_CL_dbi_disabled = MIN_CL;
        dut_config.min_CL_dll_off = MIN_CL;
        dut_config.max_CL_dll_off = MAX_CL;
        dut_config.min_CWL = MIN_CWL;
        dut_config.max_CWL = MAX_CWL;
        dut_config.min_CAL = 3;
        dut_config.max_CAL = MAX_CAL;
        dut_config.max_CA_parity_latency = 8;
        dut_config.CAL_feature = 1;
        dut_config.tDQS_feature = 1;
        dut_config.LPASR_feature = 1;
        dut_config.gear_down_feature = 1;
        dut_config.trr_feature = 0;
        dut_config.ppr_feature = 1;
        dut_config.write_crc_feature = 1;
        dut_config.write_dbi_feature = 1;
        dut_config.read_dbi_feature = 1;
        dut_config.rd_preamble_clocks_feature = 1;
        dut_config.wr_preamble_clocks_feature = 1;
        dut_config.preamble_training_feature = 1;
        dut_config.TCR_feature = 1;
        dut_config.MPS_feature = 1;
        dut_config.perdram_addr_feature = 1;
        dut_config.refresh_mode_feature = 1;
        dut_config.parity_error_feature = 1;
        dut_config.sticky_parity_error_feature = 1;
        dut_config.CA_parity_latency_feature = 1;
        dut_config.crc_error_feature = 1;
        dut_config.parity_alert_feature = 1;
        dut_config.temp_sense_feature = 1;
        dut_config.rtt_park_feature = 1;
        dut_config.dll_frozen_feature = 1;
        dut_config.cl_17_19_21_feature = 1;
        dut_config.cl_a12_feature = 1;
        dut_config.extended_wr = 1;
        dut_config.ignore_dbi_with_mpr = 1;
    endfunction

    // Mode Register Definitions
    parameter int MODE_REG_WIDTH = MODEREG_BITS;
    parameter reg[MODEREG_BITS:0] MR0 = '0;
    parameter reg[MODEREG_BITS:0] MR1 = MR0 | 2'b00 << BANK_GROUP_SHIFT | 2'b01 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR2 = MR0 | 2'b00 << BANK_GROUP_SHIFT | 2'b10 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR3 = MR0 | 2'b00 << BANK_GROUP_SHIFT | 2'b11 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR4 = MR0 | 2'b01 << BANK_GROUP_SHIFT | 2'b00 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR5 = MR0 | 2'b01 << BANK_GROUP_SHIFT | 2'b01 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR6 = MR0 | 2'b01 << BANK_GROUP_SHIFT | 2'b10 << BANK_SHIFT;
    parameter reg[MODEREG_BITS:0] MR7 = MR0 | 2'b01 << BANK_GROUP_SHIFT | 2'b11 << BANK_SHIFT;
    
    // VCS cannot use MRn in the parameter definitions below so use `MRn.
    `define MR0 '0;
    `define MR1 (2'b00 << BANK_GROUP_SHIFT | 2'b01 << BANK_SHIFT)
    `define MR2 (2'b00 << BANK_GROUP_SHIFT | 2'b10 << BANK_SHIFT)
    `define MR3 (2'b00 << BANK_GROUP_SHIFT | 2'b11 << BANK_SHIFT)
    `define MR4 (2'b01 << BANK_GROUP_SHIFT | 2'b00 << BANK_SHIFT)
    `define MR5 (2'b01 << BANK_GROUP_SHIFT | 2'b01 << BANK_SHIFT)
    `define MR6 (2'b01 << BANK_GROUP_SHIFT | 2'b10 << BANK_SHIFT)
    `define MR7 (2'b01 << BANK_GROUP_SHIFT | 2'b11 << BANK_SHIFT)
        
    // MR0 Codes
    parameter reg[MODEREG_BITS:0] MR0_RESERVED_BITS = 'b0011_1100_0000_1000_0000;
    
    parameter reg[MODEREG_BITS:0] MR0_BL8   = 'b0000_0000_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_BLFLY = 'b0000_0000_0000_0000_0001;
    parameter reg[MODEREG_BITS:0] MR0_BL4   = 'b0000_0000_0000_0000_0010;
    parameter reg[MODEREG_BITS:0] MR0_BLRES = 'b0000_0000_0000_0000_0011;
    parameter reg[MODEREG_BITS:0] MR0_DEF_BL = MR0_BLFLY;
    parameter reg[MODEREG_BITS:0] MR0_BL_MASK = 'b0000_0000_0000_0000_0011;
    parameter int NUM_BLMODE = 4;
    
    parameter reg[MODEREG_BITS:0] MR0_SEQ =   'b0000_0000_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_INTLV = 'b0000_0000_0000_0000_1000;
    parameter reg[MODEREG_BITS:0] MR0_DEF_BT = MR0_SEQ;
    parameter reg[MODEREG_BITS:0] MR0_BT_MASK = 'b0000_0000_0000_0000_1000;
    parameter reg[MODEREG_BITS:0] MR0_CL9     = 'b0000_0000_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL10    = 'b0000_0000_0000_0000_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL11    = 'b0000_0000_0000_0001_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL12    = 'b0000_0000_0000_0001_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL13    = 'b0000_0000_0000_0010_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL14    = 'b0000_0000_0000_0010_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL15    = 'b0000_0000_0000_0011_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL16    = 'b0000_0000_0000_0011_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL18    = 'b0000_0000_0000_0100_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL20    = 'b0000_0000_0000_0100_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL22    = 'b0000_0000_0000_0101_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL24    = 'b0000_0000_0000_0101_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL23    = 'b0000_0000_0000_0110_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL17    = 'b0000_0000_0000_0110_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL19    = 'b0000_0000_0000_0111_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL21    = 'b0000_0000_0000_0111_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL25    = 'b0000_0001_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL26    = 'b0000_0001_0000_0000_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL27    = 'b0000_0001_0000_0001_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL28    = 'b0000_0001_0000_0001_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL29    = 'b0000_0001_0000_0010_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL30    = 'b0000_0001_0000_0010_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL31    = 'b0000_0001_0000_0011_0000;
    parameter reg[MODEREG_BITS:0] MR0_CL32    = 'b0000_0001_0000_0011_0100;
    parameter reg[MODEREG_BITS:0] MR0_CL_MASK = 'b0000_0001_0000_0111_0100;
    parameter reg[MODEREG_BITS:0] MR0_DEF_CL = MR0_CL12;
    parameter reg[MODEREG_BITS:0] MR0_DLL_RESET = 'b0000_0000_0001_0000_0000;
    
    parameter reg[MODEREG_BITS:0] MR0_WR10    = 'b0000_0000_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR12    = 'b0000_0000_0010_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR14    = 'b0000_0000_0100_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR16    = 'b0000_0000_0110_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR18    = 'b0000_0000_1000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR20    = 'b0000_0000_1010_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR24    = 'b0000_0000_1100_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR22    = 'b0000_0000_1110_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR26    = 'b0000_0010_0000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR28    = 'b0000_0010_0010_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESA = 'b0000_0010_0100_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESB = 'b0000_0010_0110_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESC = 'b0000_0010_1000_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESD = 'b0000_0010_1010_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESE = 'b0000_0010_1100_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_RESF = 'b0000_0010_1110_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_WR_MASK = 'b0000_0010_1110_0000_0000;
    parameter reg[MODEREG_BITS:0] MR0_DEF_WR = MR0_WR12;
    
    // MR1 Codes
    parameter reg[MODEREG_BITS:0] MR1_RESERVED_BITS = 'b0011_1110_0000_0110_0000 | `MR1;
    
    parameter reg[MODEREG_BITS:0] MR1_DLL_DIS  = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_DLL_ENB  = 'b0000_0000_0000_0000_0001 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_DLL_MASK = 'b0000_0000_0000_0000_0001 | `MR1;
    
    parameter reg[MODEREG_BITS:0] MR1_ODI_34   = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ODI_48   = 'b0000_0000_0000_0000_0010 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ODI_40   = 'b0000_0000_0000_0000_0100 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ODI_RES3 = 'b0000_0000_0000_0000_0110 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ODI_MASK = 'b0000_0000_0000_0000_0110 | `MR1;
    
    parameter reg[MODEREG_BITS:0] MR1_AL0     = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ALCLN1  = 'b0000_0000_0000_0000_1000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ALCLN2  = 'b0000_0000_0000_0001_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ALCLN3  = 'b0000_0000_0000_0001_1000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_ALRES   = 'b0000_0000_0000_0001_1000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_AL_MASK = 'b0000_0000_0000_0001_1000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_DEF_AL = MR1_AL0;
    
    parameter reg[MODEREG_BITS:0] MR1_WL_DIS  = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_WL_ENB  = 'b0000_0000_0000_1000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_WL_MASK = 'b0000_0000_0000_1000_0000 | `MR1;
    
    parameter reg[MODEREG_BITS:0] MR1_RTTN_DIS   = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_60    = 'b0000_0000_0001_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_120   = 'b0000_0000_0010_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_40    = 'b0000_0000_0011_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_240   = 'b0000_0000_0100_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_48    = 'b0000_0000_0101_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_80    = 'b0000_0000_0110_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_34    = 'b0000_0000_0111_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_RTTN_MASK  = 'b0000_0000_0111_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_DEF_RTTN = MR1_RTTN_DIS;
    
    parameter reg[MODEREG_BITS:0] MR1_TDQS_DIS  = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_TDQS_ENB  = 'b0000_0000_1000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_TDQS_MASK = 'b0000_0000_1000_0000_0000 | `MR1;
    
    parameter reg[MODEREG_BITS:0] MR1_QOFF_ENB  = 'b0000_0000_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_QOFF_DIS  = 'b0000_0001_0000_0000_0000 | `MR1;
    parameter reg[MODEREG_BITS:0] MR1_QOFF_MASK = 'b0000_0001_0000_0000_0000 | `MR1;
    
    // MR2 Codes
    parameter reg[MODEREG_BITS:0] MR2_RESERVED_BITS = 'b0011_1100_0000_0000_0000 | `MR2;
    
    parameter reg[MODEREG_BITS:0] MR2_TRR_BA0     = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BA1     = 'b0000_0000_0000_0000_0001 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BA2     = 'b0000_0000_0000_0000_0010 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BA3     = 'b0000_0000_0000_0000_0011 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BA_MASK = 'b0000_0000_0000_0000_0011 | `MR2;
    
    parameter reg[MODEREG_BITS:0] MR2_TRR_BG0     = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BG1     = 'b0000_0000_0000_0000_0100 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BG2     = 'b0000_0000_0001_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BG3     = 'b0000_0000_0001_0000_0100 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_BG_MASK = 'b0000_0000_0001_0000_0100 | `MR2;
    
    parameter reg[MODEREG_BITS:0] MR2_CWL9     = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL10    = 'b0000_0000_0000_0000_1000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL11    = 'b0000_0000_0000_0001_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL12    = 'b0000_0000_0000_0001_1000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL14    = 'b0000_0000_0000_0010_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL16    = 'b0000_0000_0000_0010_1000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL18    = 'b0000_0000_0000_0011_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL20    = 'b0000_0000_0000_0011_1000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CWL_MASK = 'b0000_0000_0000_0011_1000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_DEF_CWL = MR2_CWL12;
    
    parameter reg[MODEREG_BITS:0] MR2_LPASR_NORM = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_LPASR_RED  = 'b0000_0000_0000_0100_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_LPASR_EXT  = 'b0000_0000_0000_1000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_LPASR_AUTO = 'b0000_0000_0000_1100_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_LPASR_MASK = 'b0000_0000_0000_1100_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_LPASR_DEF  = MR2_LPASR_NORM;
    
    parameter reg[MODEREG_BITS:0] MR2_RTTW_DIS  = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_120  = 'b0000_0000_0010_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_240  = 'b0000_0000_0100_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_Z    = 'b0000_0000_0110_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_80   = 'b0000_0000_1000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_RES5 = 'b0000_0000_1010_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_RES6 = 'b0000_0000_1100_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_RES7 = 'b0000_0000_1110_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_RTTW_MASK = 'b0000_0000_1110_0000_0000 | `MR2;
    
    parameter reg[MODEREG_BITS:0] MR2_CRC_WRITE_DATA_DIS  = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CRC_WRITE_DATA_ENB  = 'b0000_0001_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_CRC_WRITE_DATA_MASK = 'b0000_0001_0000_0000_0000 | `MR2;
    
    parameter reg[MODEREG_BITS:0] MR2_TRR_DIS      = 'b0000_0000_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_ENB      = 'b0000_0010_0000_0000_0000 | `MR2;
    parameter reg[MODEREG_BITS:0] MR2_TRR_ENB_MASK = 'b0000_0010_0000_0000_0000 | `MR2;
    
    // MR3 Codes
    parameter reg[MODEREG_BITS:0] MR3_RESERVED_BITS = 'b0011_1110_0000_0000_0000 | `MR3;
    
    parameter reg[MODEREG_BITS:0] MR3_MPR_PATTERN   = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_PARITY    = 'b0000_0000_0000_0000_0001 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_MODEREG   = 'b0000_0000_0000_0000_0010 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_PAGE3     = 'b0000_0000_0000_0000_0011 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_PAGE_MASK = 'b0000_0000_0000_0000_0011 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DEF_MPR_PAGE = MR3_MPR_PATTERN;
    
    parameter reg[MODEREG_BITS:0] MR3_MPR_DIS       = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_ENB       = 'b0000_0000_0000_0000_0100 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_ENB_MASK  = 'b0000_0000_0000_0000_0100 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DEF_MPR_ENB   = MR3_MPR_DIS;
    
    parameter reg[MODEREG_BITS:0] MR3_GEARDOWN_HALF    = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_GEARDOWN_QUARTER = 'b0000_0000_0000_0000_1000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_GEARDOWN_MASK    = 'b0000_0000_0000_0000_1000 | `MR3;
    
    parameter reg[MODEREG_BITS:0] MR3_PERDRAM_DIS  = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_PERDRAM_ENB  = 'b0000_0000_0000_0001_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_PERDRAM_MASK = 'b0000_0000_0000_0001_0000 | `MR3;
    
    parameter reg[MODEREG_BITS:0] MR3_TEMP_DIS  = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_TEMP_ENB  = 'b0000_0000_0000_0010_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_TEMP_MASK = 'b0000_0000_0000_0010_0000 | `MR3;
    
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_NORM  = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_2X    = 'b0000_0000_0000_0100_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_4X    = 'b0000_0000_0000_1000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_RES3  = 'b0000_0000_0000_1100_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_RES4  = 'b0000_0000_0001_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_FLY2X = 'b0000_0000_0001_0100_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_FLY4X = 'b0000_0000_0001_1000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_RES7  = 'b0000_0000_0001_1100_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_REFMODE_MASK  = 'b0000_0000_0001_1100_0000 | `MR3;

    parameter reg[MODEREG_BITS:0] MR3_DELAY_WRITE_4    = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DELAY_WRITE_5    = 'b0000_0000_0010_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DELAY_WRITE_6    = 'b0000_0000_0100_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DELAY_WRITE_RES3 = 'b0000_0000_0110_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DELAY_WRITE_MASK = 'b0000_0000_0110_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DEF_DELAY_WRITE = 'b0000_0000_0000_0000_0000 | `MR3;

    parameter reg[MODEREG_BITS:0] MR3_MPR_SERIAL    = 'b0000_0000_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_PARALLEL  = 'b0000_0000_1000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_STAGGERED = 'b0000_0001_0000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_RES3      = 'b0000_0001_1000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_MPR_MODE_MASK = 'b0000_0001_1000_0000_0000 | `MR3;
    parameter reg[MODEREG_BITS:0] MR3_DEF_MPR_MODE  = MR3_MPR_SERIAL;
    
    // MR4 Codes
    parameter reg[MODEREG_BITS:0] MR4_RESERVED_BITS = 'b0011_1100_0000_0010_0000 | `MR4;

    parameter reg[MODEREG_BITS:0] MR4_MPS_DIS  = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_MPS_ENB  = 'b0000_0000_0000_0000_0010 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_MPS_MASK = 'b0000_0000_0000_0000_0010 | `MR4;

    parameter reg[MODEREG_BITS:0] MR4_TCRR_NORM = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_TCRR_EXT  = 'b0000_0000_0000_0000_0100 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_TCRR_MASK = 'b0000_0000_0000_0000_0100 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_TCRM_DIS  = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_TCRM_ENB  = 'b0000_0000_0000_0000_1000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_TCRM_MASK = 'b0000_0000_0000_0000_1000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_VREFMON_DIS  = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_VREFMON_ENB  = 'b0000_0000_0000_0001_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_VREFMON_MASK = 'b0000_0000_0000_0001_0000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_CAL0     = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL3     = 'b0000_0000_0000_0100_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL4     = 'b0000_0000_0000_1000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL5     = 'b0000_0000_0000_1100_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL6     = 'b0000_0000_0001_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL8     = 'b0000_0000_0001_0100_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL_RES6 = 'b0000_0000_0001_1000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL_RES7 = 'b0000_0000_0001_1100_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_CAL_MASK = 'b0000_0000_0001_1100_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_DEF_CAL  = MR4_CAL0;
    parameter int MR4_CAL_SHIFT = 6;
    parameter int MR4_CAL_BITS = 3;

    parameter reg[MODEREG_BITS:0] MR4_SREF_SLOW = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_SREF_FAST = 'b0000_0000_0010_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_SREF_MASK = 'b0000_0000_0010_0000_0000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_PRETRAIN_DIS  = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_PRETRAIN_ENB  = 'b0000_0000_0100_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_PRETRAIN_MASK = 'b0000_0000_0100_0000_0000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_RDPRE_1CLK = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_RDPRE_2CLK = 'b0000_0000_1000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_RDPRE_MASK = 'b0000_0000_1000_0000_0000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_WRPRE_1CLK = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_WRPRE_2CLK = 'b0000_0001_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_WRPRE_MASK = 'b0000_0001_0000_0000_0000 | `MR4;
    
    parameter reg[MODEREG_BITS:0] MR4_PPR_DIS  = 'b0000_0000_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_PPR_ENB  = 'b0000_0010_0000_0000_0000 | `MR4;
    parameter reg[MODEREG_BITS:0] MR4_PPR_MASK = 'b0000_0010_0000_0000_0000 | `MR4;
    
    // MR5 Codes
    parameter reg[MODEREG_BITS:0] MR5_RESERVED_BITS = 'b0011_1100_0000_0000_0000 | `MR5;

    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_0    = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_4    = 'b0000_0000_0000_0000_0001 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_5    = 'b0000_0000_0000_0000_0010 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_6    = 'b0000_0000_0000_0000_0011 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_8    = 'b0000_0000_0000_0000_0100 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_RES5 = 'b0000_0000_0000_0000_0101 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_RES6 = 'b0000_0000_0000_0000_0110 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_RES7 = 'b0000_0000_0000_0000_0111 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_LATENCY_MASK = 'b0000_0000_0000_0000_0111 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_CRC_CLEAR = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_CRC_ERROR = 'b0000_0000_0000_0000_1000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_CRC_MASK  = 'b0000_0000_0000_0000_1000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_PARITY_ERROR_CLEAR = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_ERROR_ERROR = 'b0000_0000_0000_0001_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_PARITY_ERROR_MASK  = 'b0000_0000_0000_0001_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_ODT_BUFFER_ENB  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_ODT_BUFFER_DIS  = 'b0000_0000_0000_0010_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_ODT_BUFFER_MASK = 'b0000_0000_0000_0010_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_RTTP_DIS   = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_60    = 'b0000_0000_0000_0100_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_120   = 'b0000_0000_0000_1000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_40    = 'b0000_0000_0000_1100_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_240   = 'b0000_0000_0001_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_48    = 'b0000_0000_0001_0100_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_80    = 'b0000_0000_0001_1000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_34    = 'b0000_0000_0001_1100_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_RTTP_MASK  = 'b0000_0000_0001_1100_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_DEF_RTTP = MR5_RTTP_DIS;
    
    parameter reg[MODEREG_BITS:0] MR5_STICKY_PARITY_DIS  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_STICKY_PARITY_ENB  = 'b0000_0000_0010_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_STICKY_PARITY_MASK = 'b0000_0000_0010_0000_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_DM_DIS  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_DM_ENB  = 'b0000_0000_0100_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_DM_MASK = 'b0000_0000_0100_0000_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_WRITE_DBI_DIS  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_WRITE_DBI_ENB  = 'b0000_0000_1000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_WRITE_DBI_MASK = 'b0000_0000_1000_0000_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_READ_DBI_DIS  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_READ_DBI_ENB  = 'b0000_0001_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_READ_DBI_MASK = 'b0000_0001_0000_0000_0000 | `MR5;
    
    parameter reg[MODEREG_BITS:0] MR5_DLL_FROZEN_DIS  = 'b0000_0000_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_DLL_FROZEN_ENB  = 'b0000_0010_0000_0000_0000 | `MR5;
    parameter reg[MODEREG_BITS:0] MR5_DLL_FROZEN_MASK = 'b0000_0010_0000_0000_0000 | `MR5;
    
    // MR6 Codes
    parameter reg[MODEREG_BITS:0] MR6_RESERVED_BITS = 'b0011_1110_0000_0000_0000 | `MR6;
    
    parameter reg[MODEREG_BITS:0] MR6_VREF_OFFSET_MASK = 'b0000_0000_0000_0011_1111 | `MR6;
    parameter int MR6_VREF_OFFSET_SHIFT = 0;
    
    parameter reg[MODEREG_BITS:0] MR6_VREF_RANGE_1    = 'b0000_0000_0000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_VREF_RANGE_2    = 'b0000_0000_0000_0100_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_VREF_RANGE_MASK = 'b0000_0000_0000_0100_0000 | `MR6;
    
    parameter reg[MODEREG_BITS:0] MR6_VREF_DIS    = 'b0000_0000_0000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_VREF_ENB    = 'b0000_0000_0000_1000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_VREF_MASK   = 'b0000_0000_0000_1000_0000 | `MR6;


    parameter reg[MODEREG_BITS:0] MR6_tCCDL_4    = 'b0000_0000_0000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_5    = 'b0000_0000_0100_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_6    = 'b0000_0000_1000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_7    = 'b0000_0000_1100_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_8    = 'b0000_0001_0000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_RES5 = 'b0000_0001_0100_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_RES6 = 'b0000_0001_1000_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_RES7 = 'b0000_0001_1100_0000_0000 | `MR6;
    parameter reg[MODEREG_BITS:0] MR6_tCCDL_MASK = 'b0000_0001_1100_0000_0000 | `MR6;
    
    // MR7 Codes
    parameter reg[MODEREG_BITS:0] MR7_RESERVED_BITS = 'b0011_1111_1111_1111_1111 | `MR7;

    // Avoid name conflicts.
    class Class_CRC;
        bit _debug;
        int _by_mode;
        int _num_dms;
        
        function new(int by_mode, bit debug = 0);
            _by_mode = by_mode;
            if (16 == _by_mode)
                _num_dms = 2;
            else
                _num_dms = 1;
`ifdef DEBUG_CRC
            _debug = 1;
`else
            _debug = debug;
`endif
            if (_debug)
                Verify();
        endfunction
        function void BuildFrame(input logic[MAX_DQ_BITS*MAX_BURST_LEN-1:0] dq_in,
                                 input logic[MAX_DBI_BITS*MAX_BURST_LEN-1:0] dbi_in,
                                 output logic[MAX_DQ_BITS*(MAX_BURST_LEN+MAX_CRC_TRANSFERS)-1:0] dq_out,
                                 output logic[MAX_DBI_BITS*(MAX_BURST_LEN+MAX_CRC_EQUATION)-1:0] dbi_out);
            logic[(MAX_DQ_BITS+MAX_DBI_BITS)*MAX_BURST_LEN-1:0] d;
            logic[MAX_DQ_BITS-1:0] dq_crc;
            
            dq_crc = Calculate(dq_in, dbi_in);
            if (1'bx === &dq_crc)
                dq_crc = 'x;
            if (_debug)
                $display("BuildFrame() CRCs %0h @%0t", dq_crc, $time); 
            dbi_out = '1;
            dbi_out[MAX_DBI_BITS*MAX_BURST_LEN-1:0] = dbi_in[MAX_DBI_BITS*MAX_BURST_LEN-1:0];
            dq_out = AddCRC(dq_in, dq_crc);
        endfunction
        function logic[(MAX_DQ_BITS+MAX_DBI_BITS)*MAX_BURST_LEN-1:0] BitOrder(logic[MAX_DQ_BITS*MAX_BURST_LEN-1:0] dq_in, 
                                                                              logic[MAX_DBI_BITS*MAX_BURST_LEN-1:0] dbi_in);
            logic[(MAX_DQ_BITS+MAX_DBI_BITS)*MAX_BURST_LEN-1:0] d;
            int i;
            
            i = 0;
            d = '1;
            // Place bits in expected data map order.
            // All unused bits are 1 (check for dq/dm out of range for the given part width).
            for (int dbi=0;dbi<MAX_DBI_BITS;dbi++) begin
                for (int dq=0;dq<8;dq++) begin
                    for (int transfer=0;transfer<8;transfer++) begin
                        if ((dq < _by_mode) && (dbi < _num_dms))
                            d[i] = dq_in[transfer*MAX_DQ_BITS + dq + dbi*8];
                        i = i + 1;
                    end
                end
                for (int transfer=0;transfer<8;transfer++) begin
                    if (dbi < _num_dms)
                        d[i] = dbi_in[transfer*MAX_DBI_BITS + dbi];
                    i = i + 1;
                end
            end
            if (_debug) begin
                $display("CRCBitOrder - Input DQ:%0h DM:%0h @%0t", dq_in, dbi_in, $time);
                $display("CRCBitOrder - Output:(x16)%0h %0h @%0t", (d >> 72) & 72'hffffffffffffffffff, d & 72'hffffffffffffffffff, $time);
            end
            return d;
        endfunction
        function logic[MAX_DQ_BITS*(MAX_BURST_LEN+MAX_CRC_TRANSFERS)-1:0] AddCRC(logic[MAX_DQ_BITS*MAX_BURST_LEN-1:0] dq_in,
                                                                                 logic[MAX_DQ_BITS-1:0] crc_in);
            logic[MAX_DQ_BITS*(MAX_BURST_LEN+MAX_CRC_TRANSFERS)-1:0] dq_out;
            
            dq_out = '1;
            dq_out[MAX_DQ_BITS*MAX_BURST_LEN-1:0] = dq_in[MAX_DQ_BITS*MAX_BURST_LEN-1:0];
            for (int i=0;i<_by_mode;i++) begin
                dq_out[MAX_BURST_LEN*MAX_DQ_BITS + i] = crc_in[i];
            end
            if (4 == _by_mode) begin
                for (int i=4;i<8;i++) begin
                    dq_out[(MAX_BURST_LEN+1)*MAX_DQ_BITS + i%4] = crc_in[i];
                end
            end
            if (_debug) begin
//                 $display("AddCRC Input :%36h @%0t", dq_in, $time);
//                 $display("AddCRC Output:%36h @%0t", dq_out, $time);
            end
            return dq_out;
        endfunction
        function logic[MAX_DQ_BITS-1:0] GetCRC(logic[MAX_DQ_BITS*(MAX_BURST_LEN+MAX_CRC_TRANSFERS)-1:0] dq_in);
            logic[MAX_DQ_BITS-1:0] crc;
            
            for (int i=0;i<_by_mode;i++) begin
                crc[i] = dq_in[(MAX_DQ_BITS*(MAX_BURST_LEN)) + i];
            end
            if (4 == _by_mode) begin
                for (int i=4;i<8;i++) begin
                    crc[i] = dq_in[(MAX_DQ_BITS*(MAX_BURST_LEN+1))+i%4];
                end
            end
            return crc;
        endfunction
        function logic[MAX_DQ_BITS-1:0] Calculate(logic[MAX_DQ_BITS*MAX_BURST_LEN-1:0] dq_in, 
                                                logic[MAX_DBI_BITS*MAX_BURST_LEN-1:0] dbi_in);
            logic[(MAX_DQ_BITS+MAX_DBI_BITS)*MAX_BURST_LEN-1:0] d;
            logic[MAX_DQ_BITS-1:0] crc;
            
            d = BitOrder(dq_in, dbi_in);
            for (int i=0;i<MAX_DQ_BITS;i++) begin
                crc[i] = CalculatePerEquation(i, d);
            end
            return crc;
        endfunction
        function logic CalculatePerEquation(int eq_number, logic[(MAX_DQ_BITS+MAX_DBI_BITS)*MAX_BURST_LEN-1:0] d);
            int x16;
            logic result;
            
            x16 = 0;
            if (eq_number > 7) begin
                x16 = 72;
                eq_number = eq_number % 8;
            end
            result = 0;
            case (eq_number)
                0: begin
                    result = d[69+x16] ^ d[68+x16] ^ d[67+x16] ^ d[66+x16] ^ d[64+x16] ^ d[63+x16] ^ d[60+x16] ^
                             d[56+x16] ^ d[54+x16] ^ d[53+x16] ^ d[52+x16] ^ d[50+x16] ^ d[49+x16] ^ d[48+x16] ^
                             d[45+x16] ^ d[43+x16] ^ d[40+x16] ^ d[39+x16] ^ d[35+x16] ^ d[34+x16] ^ d[31+x16] ^
                             d[30+x16] ^ d[28+x16] ^ d[23+x16] ^ d[21+x16] ^ d[19+x16] ^ d[18+x16] ^ d[16+x16] ^
                             d[14+x16] ^ d[12+x16] ^ d[8+x16]  ^ d[7+x16]  ^ d[6+x16]  ^ d[0+x16];
                end
                1: begin
                    result = d[70+x16] ^ d[66+x16] ^ d[65+x16] ^ d[63+x16] ^ d[61+x16] ^ d[60+x16] ^ d[57+x16] ^
                             d[56+x16] ^ d[55+x16] ^ d[52+x16] ^ d[51+x16] ^ d[48+x16] ^ d[46+x16] ^ d[45+x16] ^
                             d[44+x16] ^ d[43+x16] ^ d[41+x16] ^ d[39+x16] ^ d[36+x16] ^ d[34+x16] ^ d[32+x16] ^
                             d[30+x16] ^ d[29+x16] ^ d[28+x16] ^ d[24+x16] ^ d[23+x16] ^ d[22+x16] ^ d[21+x16] ^
                             d[20+x16] ^ d[18+x16] ^ d[17+x16] ^ d[16+x16] ^ d[15+x16] ^ d[14+x16] ^ d[13+x16] ^
                             d[12+x16] ^ d[9+x16]  ^ d[6+x16]  ^ d[1+x16]  ^ d[0+x16];
                end
                2: begin
                    result = d[71+x16] ^ d[69+x16] ^ d[68+x16] ^ d[63+x16] ^ d[62+x16] ^ d[61+x16] ^ d[60+x16] ^
                             d[58+x16] ^ d[57+x16] ^ d[54+x16] ^ d[50+x16] ^ d[48+x16] ^ d[47+x16] ^ d[46+x16] ^
                             d[44+x16] ^ d[43+x16] ^ d[42+x16] ^ d[39+x16] ^ d[37+x16] ^ d[34+x16] ^ d[33+x16] ^
                             d[29+x16] ^ d[28+x16] ^ d[25+x16] ^ d[24+x16] ^ d[22+x16] ^ d[17+x16] ^ d[15+x16] ^
                             d[13+x16] ^ d[12+x16] ^ d[10+x16] ^ d[8+x16]  ^ d[6+x16]  ^ d[2+x16]  ^ d[1+x16]  ^ d[0+x16];
               end
                3: begin
                    result = d[70+x16] ^ d[69+x16] ^ d[64+x16] ^ d[63+x16] ^ d[62+x16] ^ d[61+x16] ^ d[59+x16] ^
                             d[58+x16] ^ d[55+x16] ^ d[51+x16] ^ d[49+x16] ^ d[48+x16] ^ d[47+x16] ^ d[45+x16] ^
                             d[44+x16] ^ d[43+x16] ^ d[40+x16] ^ d[38+x16] ^ d[35+x16] ^ d[34+x16] ^ d[30+x16] ^
                             d[29+x16] ^ d[26+x16] ^ d[25+x16] ^ d[23+x16] ^ d[18+x16] ^ d[16+x16] ^ d[14+x16] ^
                             d[13+x16] ^ d[11+x16] ^ d[9+x16]  ^ d[7+x16]  ^ d[3+x16]  ^ d[2+x16]  ^ d[1+x16];
                end
                4: begin
                    result = d[71+x16] ^ d[70+x16] ^ d[65+x16] ^ d[64+x16] ^ d[63+x16] ^ d[62+x16] ^ d[60+x16] ^
                             d[59+x16] ^ d[56+x16] ^ d[52+x16] ^ d[50+x16] ^ d[49+x16] ^ d[48+x16] ^ d[46+x16] ^
                             d[45+x16] ^ d[44+x16] ^ d[41+x16] ^ d[39+x16] ^ d[36+x16] ^ d[35+x16] ^ d[31+x16] ^
                             d[30+x16] ^ d[27+x16] ^ d[26+x16] ^ d[24+x16] ^ d[19+x16] ^ d[17+x16] ^ d[15+x16] ^
                             d[14+x16] ^ d[12+x16] ^ d[10+x16] ^ d[8+x16]  ^ d[4+x16]  ^ d[3+x16]  ^ d[2+x16];
                end
                5: begin
                    result = d[71+x16] ^ d[66+x16] ^ d[65+x16] ^ d[64+x16] ^ d[63+x16] ^ d[61+x16] ^ d[60+x16] ^
                             d[57+x16] ^ d[53+x16] ^ d[51+x16] ^ d[50+x16] ^ d[49+x16] ^ d[47+x16] ^ d[46+x16] ^
                             d[45+x16] ^ d[42+x16] ^ d[40+x16] ^ d[37+x16] ^ d[36+x16] ^ d[32+x16] ^ d[31+x16] ^
                             d[28+x16] ^ d[27+x16] ^ d[25+x16] ^ d[20+x16] ^ d[18+x16] ^ d[16+x16] ^ d[15+x16] ^
                             d[13+x16] ^ d[11+x16] ^ d[9+x16]  ^ d[5+x16]  ^ d[4+x16]  ^ d[3+x16];
                end
                6: begin
                    result = d[67+x16] ^ d[66+x16] ^ d[65+x16] ^ d[64+x16] ^ d[62+x16] ^ d[61+x16] ^ d[58+x16] ^
                             d[54+x16] ^ d[52+x16] ^ d[51+x16] ^ d[50+x16] ^ d[48+x16] ^ d[47+x16] ^ d[46+x16] ^
                             d[43+x16] ^ d[41+x16] ^ d[38+x16] ^ d[37+x16] ^ d[33+x16] ^ d[32+x16] ^ d[29+x16] ^
                             d[28+x16] ^ d[26+x16] ^ d[21+x16] ^ d[19+x16] ^ d[17+x16] ^ d[16+x16] ^ d[14+x16] ^
                             d[12+x16] ^ d[10+x16] ^ d[6+x16]  ^ d[5+x16]  ^ d[4+x16];
                end
                7: begin
                    result = d[68+x16] ^ d[67+x16] ^ d[66+x16] ^ d[65+x16] ^ d[63+x16] ^ d[62+x16] ^ d[59+x16] ^
                             d[55+x16] ^ d[53+x16] ^ d[52+x16] ^ d[51+x16] ^ d[49+x16] ^ d[48+x16] ^ d[47+x16] ^
                             d[44+x16] ^ d[42+x16] ^ d[39+x16] ^ d[38+x16] ^ d[34+x16] ^ d[33+x16] ^ d[30+x16] ^
                             d[29+x16] ^ d[27+x16] ^ d[22+x16] ^ d[20+x16] ^ d[18+x16] ^ d[17+x16] ^ d[15+x16] ^
                             d[13+x16] ^ d[11+x16] ^ d[7+x16]  ^ d[6+x16]  ^ d[5+x16];
                end
                default: begin
                    $display("ERROR: Invalid CRC equation:%0d @%0t", eq_number, $time);
                end
            endcase
            return result;
        endfunction
        function void Verify();
        endfunction
    endclass
    
endpackage
`endif
