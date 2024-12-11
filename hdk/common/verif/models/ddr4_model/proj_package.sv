// (c) Copyright 2023 Advanced Micro Devices, Inc. All rights reserved.
`ifndef DDR4_PROJ_PKG
`define DDR4_PROJ_PKG
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
package proj_package;
    timeunit 1ps;
    timeprecision 1ps;
    import arch_package::*;

    parameter DEF_CCD_L = 6;
        
    function void project_dut_config(inout UTYPE_dutconfig dut_config);
        dut_config.min_CL_dll_off = 5;
        dut_config.max_CL_dll_off = 10;
        dut_config.max_CL_dbi_enabled = 32;
        dut_config.max_CL_dbi_disabled = 30;
        dut_config.min_CL_dbi_enabled = 10;
        dut_config.min_CL_dbi_disabled = 9;
        dut_config.cl_17_19_21_feature = 1; // Add this line 0-off 1-on
        dut_config.cl_a12_feature = 1;      // Add this line 0-off 1-on
        dut_config.ppr_feature = 1;
        dut_config.min_CL  = 9;
        dut_config.max_CL  = 32;
        dut_config.max_CWL = 20;
        dut_config.min_CWL = MIN_CWL;
        dut_config.max_CAL = 8;
    endfunction
    
    function void GetCWLSpeedRange(input UTYPE_DutModeConfig dut_mode_config, input UTYPE_TS ts, 
                                   output int min, output int max, output int ideal);
        ideal = 9;
        min = 9;
        max = 9;
        case (ts)
            TS_1875,
            TS_1500: begin
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) begin
                    ideal = 10;
                    max = 10;
                end
            end
            TS_1250 : begin
                ideal = 9;
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down))
                    ideal = 10;
                min = ideal;
                max = 11;
            end 
            TS_1072 : begin
                ideal = 10;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = (1 == dut_mode_config.gear_down) ? 12 : 11;
                min = ideal;
                max = 12;
            end 
            TS_938 : begin
                ideal = 11;
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down))
                    ideal = 12;
                min = ideal;
                max = 14;
            end 
            TS_833 : begin
                ideal = 12;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 14;
                min = ideal;
                max = 16;
            end 
            TS_750 : begin
                ideal = 14;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 16;
                min = ideal;
                max = 18;
            end 
            TS_682, TS_625 : begin
                ideal = 16;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 18;
                min = ideal;
                max = 20;
            end 
        endcase
    endfunction
    
    function void GetCLSpeedRange(input UTYPE_DutModeConfig dut_mode_config, output UTYPE_TS slowest, output UTYPE_TS fastest, output UTYPE_TS ideal);
        UTYPE_TS default_tck;
        
        if (0 == dut_mode_config.read_dbi) begin
            case (dut_mode_config.CL)
                9: begin
                    ideal = TS_1500;
                    slowest = TS_1500; fastest = TS_1500;
                end
                10: begin
                    ideal = TS_1250;
                    slowest = TS_1500; fastest = TS_1250;
                end
                11: begin
                    ideal = TS_1250;
                    slowest = TS_1250; fastest = TS_1250;
                end
                12: begin
                    ideal = TS_1250;
                    slowest = TS_1250; fastest = TS_1072;
                end
                13: begin
                    ideal = TS_1072;
                    slowest = TS_1072; fastest = TS_1072;
                end
                14: begin
                    ideal = TS_1072;
                    slowest = TS_1072; fastest = TS_938;
                end
                15,16: begin
                    ideal = TS_938;
                    slowest = TS_938; fastest = TS_938;
                end
                17,18: begin
                    ideal = TS_833;
                    slowest = TS_833; fastest = TS_750;
                end
                19: begin
                    ideal = TS_750;
                    slowest = TS_750; fastest = TS_750;
                end
                20: begin
                    ideal = TS_750;
                    slowest = TS_750; fastest = TS_625;
                end
                // CL21 w/ DBI disabled is not in the spec!!
                21: begin
                    ideal = TS_750;
                    slowest = TS_750; fastest = TS_625;
                end
                22,24: begin
                    ideal = TS_625;
                    slowest = TS_625; fastest = TS_625;
                end
                23,25,26,27,28,29,30,31,32: begin
                    ideal = TS_625;
                    slowest = TS_625; fastest = TS_625;
                end
            endcase
        end else begin
            case (dut_mode_config.CL)
                5,9,10: begin
                    ideal = TS_1500;
                    slowest = TS_1500; fastest = TS_1500;
                end
                11: begin
                    ideal = TS_1500;
                    slowest = TS_1500; fastest = TS_1500;
                end
                12: begin
                    ideal = TS_1500;
                    slowest = TS_1500; fastest = TS_1250;
                end
                13: begin
                    ideal = TS_1250;
                    slowest = TS_1250; fastest = TS_1250;
                end
                14: begin
                    ideal = TS_1250;
                    slowest = TS_1250; fastest = TS_1072;
                end
                15,16: begin
                    ideal = TS_1072;
                    slowest = TS_1072; fastest = TS_1072;
                end
                17: begin
                    ideal = TS_938;
                    slowest = TS_938; fastest = TS_938;
                end
                18: begin
                    ideal = TS_938;
                    slowest = TS_938; fastest = TS_833;
                end
                19: begin
                    ideal = TS_833;
                    slowest = TS_833; fastest = TS_833;
                end
                20: begin
                    ideal = TS_833;
                    slowest = TS_833; fastest = TS_750;
                end
                21,22,23: begin
                    ideal = TS_750;
                    slowest = TS_750; fastest = TS_750;
                end
                24,25,26,27,28,29,30,31,32: begin
                    ideal = TS_625;
                    slowest = TS_625; fastest = TS_625;
                end
            endcase
        end
        `ifdef DDR4_STACK_X4_2H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        `ifdef DDR4_STACK_X8_2H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        `ifdef DDR4_STACK_X16_2H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        `ifdef DDR4_STACK_X4_4H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        `ifdef DDR4_STACK_X8_4H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        `ifdef DDR4_STACK_X16_4H
            GetCLSpeedRange3DS(.dut_mode_config(dut_mode_config), .slowest(slowest), .fastest(fastest), .ideal(ideal));
        `endif
        if (default_tck == ideal) begin
            $display("WARNING Missing CL in GetCLSpeedRange(). Default is %p", default_tck);
        end
    endfunction
    
    function void GetCLSpeedRange3DS(input UTYPE_DutModeConfig dut_mode_config, output UTYPE_TS slowest, output UTYPE_TS fastest, output UTYPE_TS ideal);
        UTYPE_TS default_tck;
        
        case (dut_mode_config.CL)
            9: begin
                ideal = TS_1500;
                slowest = TS_1500; fastest = TS_1500;
            end
            10, 11: begin
                ideal = TS_1250;
                slowest = TS_1500; fastest = TS_1250;
            end
            12, 13: begin
                ideal = TS_1250;
                slowest = TS_1250; fastest = TS_1250;
            end
            14: begin
                ideal = TS_1072;
                slowest = TS_1250; fastest = TS_1072;
            end
            15: begin
                ideal = TS_1072;
                slowest = TS_1072; fastest = TS_1072;
            end
            16, 17: begin
                ideal = TS_938;
                slowest = TS_1072; fastest = TS_938;
            end
            18, 19, 20: begin
                ideal = TS_833;
                slowest = TS_938; fastest = TS_833;
            end
            22,24,25,26,27,28,29,30,31,32: begin
                ideal = TS_833;
                slowest = TS_833; fastest = TS_833;
            end
        endcase
        if (default_tck == ideal) begin
            $display("WARNING Missing CL in GetCLSpeedRange(). Default is %p", default_tck);
        end
    endfunction
    
    function int GettCCD_LSpeed(input UTYPE_DutModeConfig dut_mode_config, input UTYPE_TS ts);
        int tCCD_L;
        
        tCCD_L = 4;
        case (ts)
            TS_1250,
            TS_1072 : begin
                tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 6 : 5;
            end 
            TS_938,
            TS_833 : begin
                tCCD_L = 6;
            end
            TS_750 : begin
                tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 8 : 7;
            end
            TS_682,
            TS_625 : begin
                tCCD_L = 8;
            end
        endcase
        return tCCD_L;
    endfunction
        
    function int GetMintWR(input UTYPE_DutModeConfig dut_mode_config, int tWRc, int tRTPc);
        int min_setting;
        
        min_setting = (tRTPc*2) > tWRc ? tRTPc*2 : tWRc;
        if (1 == dut_mode_config.gear_down)
            min_setting = min_setting + (min_setting % 4);
        else
            min_setting = min_setting + (min_setting % 2);
        if (min_setting < MIN_WR)
            min_setting = MIN_WR;
        else if (min_setting > MAX_WR)
            min_setting = MAX_WR;
        return min_setting;
    endfunction
    
    function UTYPE_delay_write_crc_dm GettWR_CRC_DMSpeed(input UTYPE_DutModeConfig dut_mode_config, input UTYPE_TS ts);
        UTYPE_delay_write_crc_dm tWR_CRC_DM;
        
        tWR_CRC_DM = DELAY_WRITE_5;
        case (ts)
            TS_1875,
            TS_1500,
            TS_1250 : begin
                tWR_CRC_DM = DELAY_WRITE_4;
            end
            TS_750,
            TS_682,
            TS_625 : begin
                tWR_CRC_DM = DELAY_WRITE_6;
            end
        endcase
        return tWR_CRC_DM;
    endfunction
    
    function void GetCWLSpeedRange_locked(input UTYPE_DutModeConfig dut_mode_config, input UTYPE_TS ts, input int tCK, 
                                   output int min, output int max, output int ideal);
        ideal = 9;
        min = 9;
        max = 9;
        case (ts)
            TS_1875,
            TS_1500: begin
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) begin
                    ideal = 10;
                    max = 10;
                end
            end
            TS_1250 : begin
                ideal = 9;
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down))
                    ideal = 10;
                min = ideal;
                max = 11;
            end 
            TS_1072 : begin
                ideal = 10;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = (1 == dut_mode_config.gear_down) ? 12 : 11;
                if (tCK >= 1250) begin
                    ideal = 9;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 11;
                end
                min = ideal;
                max = 12;
            end 
            TS_938 : begin
                ideal = 11;
                if ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down))
                    ideal = 12;
                if (tCK >= 1250) begin
                    ideal = 9;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 11;
                end else if (tCK >= 1071) begin
                    ideal = 10;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 12;
                end
                min = ideal;
                max = 14;
            end 
            TS_833 : begin
                ideal = 12;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 14;
                if (tCK >= 1250) begin
                    ideal = 9;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 11;
                end else if (tCK >= 1071) begin
                    ideal = 10;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 12;
                end else if (tCK >= 937) begin
                    ideal = 11;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 14;
                end
                min = ideal;
                max = 16;
            end 
            TS_750 : begin
                ideal = 14;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 16;
                if (tCK >= 1250) begin
                    ideal = 9;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 11;
                end else if (tCK >= 1071) begin
                    ideal = 10;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 12;
                end else if (tCK >= 937) begin
                    ideal = 11;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 14;
                end else if (tCK >= 833) begin
                    ideal = 12;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 16;
                end
                min = ideal;
                max = 18;
            end 
            TS_682, TS_625 : begin
                ideal = 16;
                if (2 == dut_mode_config.wr_preamble_clocks)
                    ideal = 18;
                if (tCK >= 1250) begin
                    ideal = 9;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 11;
                end else if (tCK >= 1071) begin
                    ideal = 10;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 12;
                end else if (tCK >= 937) begin
                    ideal = 11;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 14;
                end else if (tCK >= 833) begin
                    ideal = 12;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 16;
                end else if (tCK >= 750) begin
                    ideal = 14;
                    if (2 == dut_mode_config.wr_preamble_clocks)
                        ideal = 18;
                end
                min = ideal;
                max = 20;
            end 

        endcase
    endfunction
    
    function int GettCCD_LSpeed_locked(input UTYPE_DutModeConfig dut_mode_config, input UTYPE_TS ts, input int tCK);
        int tCCD_L;
        
        tCCD_L = 4;
        case (ts)
            TS_1250,
            TS_1072 : begin
                if (tCK >= 1500)
                    tCCD_L = 4;
            end 
            TS_938,
            TS_833  : begin
                if (tCK >= 1500)
                    tCCD_L = 4;
                else if (tCK >= 1071)
                    tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 6 : 5;
            end 
            TS_750  : begin
                if (tCK >= 1500)
                    tCCD_L = 4;
                else if (tCK >= 1071)
                    tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 6 : 5;
                else if (tCK >= 833)
                    tCCD_L = 6;
            end 
            TS_682  : begin
                if (tCK >= 1500)
                    tCCD_L = 4;
                else if (tCK >= 1071)
                    tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 6 : 5;
                else if (tCK >= 833)
                    tCCD_L = 6;
            end 
            TS_625  : begin
                if (tCK >= 1500)
                    tCCD_L = 4;
                else if (tCK >= 1071)
                    tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 6 : 5;
                else if (tCK >= 833)
                    tCCD_L = 6;
                else if (tCK >= 682)
                    tCCD_L = ((2 == dut_mode_config.wr_preamble_clocks) || (1 == dut_mode_config.gear_down)) ? 8 : 7;
            end
        endcase
        return tCCD_L;
    endfunction
        
    function bit ppr_available(input UTYPE_dutconfig dut_config);
        return 1;
    endfunction
   
    function bit sppr_available(input UTYPE_dutconfig dut_config);
        return 1;
    endfunction
endpackage
`endif
