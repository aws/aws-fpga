// file: system_management_wiz_0.v
// (c) Copyright 2013 - 2013 Xilinx, Inc. All rights reserved.
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
`timescale 1ns / 1 ps

(* CORE_GENERATION_INFO = "system_management_wiz_0,system_management_wiz_v1_3_2,{component_name=system_management_wiz_0,enable_axi=false,enable_axi4stream=false,dclk_frequency=125,enable_busy=true,enable_convst=false,enable_convstclk=false,enable_dclk=true,enable_drp=true,enable_eoc=true,enable_eos=true,enable_vbram_alaram=false,enable_vccpsaux_alaram=false,enable_Vccint_Alaram=true,enable_Vccaux_alaram=true,enable_vccpsintfp_alaram=false,enable_vccpsintlp_alaram=false,ot_alaram=true,user_temp_alaram=true,timing_mode=continuous,channel_averaging=None,sequencer_mode=on,startup_channel_selection=contineous_sequence}" *)

module system_management_wiz_0


          (
          daddr_in,            // Address bus for the dynamic reconfiguration port
          dclk_in,             // Clock input for the dynamic reconfiguration port
          den_in,              // Enable Signal for the dynamic reconfiguration port
          di_in,               // Input data bus for the dynamic reconfiguration port
          dwe_in,              // Write Enable for the dynamic reconfiguration port
          reset_in,            // Reset signal for the System Monitor control logic
          vp,
          vn,
          busy_out,            // ADC Busy signal
          channel_out,         // Channel Selection Outputs
          do_out,              // Output data bus for dynamic reconfiguration port
          drdy_out,            // Data ready signal for the dynamic reconfiguration port
          eoc_out,             // End of Conversion Signal
          eos_out,             // End of Sequence Signal
          ot_out,              // Over-Temperature alarm output
          i2c_sclk,
          i2c_sda,
          vccaux_alarm_out,    // VCCAUX-sensor alarm output
          vccint_alarm_out,    //  VCCINT-sensor alarm output
          user_temp_alarm_out, // Temperature-sensor alarm output
          alarm_out);

          input [7:0] daddr_in;
          input dclk_in;
          input den_in;
          input [15:0] di_in;
          input dwe_in;
          input reset_in;
          input vp; 
          input vn;
          output busy_out;
          output [5:0] channel_out;
          output [15:0] do_out;
          output drdy_out;
          output eoc_out;
          output eos_out;
          output ot_out;
          inout i2c_sclk;
          inout i2c_sda;
          output vccaux_alarm_out;
          output vccint_alarm_out;
          output user_temp_alarm_out;
          output alarm_out;

system_management_wiz_0_sysmon
inst (
      .daddr_in(daddr_in),
      .dclk_in(dclk_in),
      .den_in(den_in),
      .di_in(di_in),
      .dwe_in(dwe_in),
      .reset_in(reset_in),
      .vp (vp),
      .vn (vn),
 
      .vccaux_alarm_out(vccaux_alarm_out),
      .vccint_alarm_out(vccint_alarm_out),
      .user_temp_alarm_out(user_temp_alarm_out),
      .busy_out(busy_out),
      .channel_out(channel_out),
      .do_out(do_out[15:0]),
      .drdy_out(drdy_out),
      .eoc_out(eoc_out),
      .eos_out(eos_out),
      .ot_out(ot_out),
      .i2c_sclk(i2c_sclk),
      .i2c_sda(i2c_sda),
      .alarm_out(alarm_out)
      );


endmodule
