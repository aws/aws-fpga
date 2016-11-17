// file: system_management_wiz_0_sysmon.v
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


module system_management_wiz_0_sysmon
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
          wire GND_BIT;
          assign GND_BIT = 0;
          wire [15:0] aux_channel_p;
          wire [15:0] aux_channel_n;
          wire [15:0]  alm_int;
          reg jtag_sig;

          wire i2c_sclk_int;
          wire i2c_sda_int;
          wire i2c_sda_ts;
          wire i2c_sclk_ts;


          assign alarm_out = alm_int[7];
          assign vccaux_alarm_out = alm_int[2];
          assign vccint_alarm_out = alm_int[1];
          assign user_temp_alarm_out = alm_int[0];

// inout logic for i2c_sda and i2c_sclk ports
          IOBUF i2c_sda_iobuf
            (.O(i2c_sda_int), 
             .IO(i2c_sda),
             .I(1'b0),
             .T(i2c_sda_ts));
         
          IOBUF i2c_sclk_iobuf
            (.O(i2c_sclk_int), 
             .IO(i2c_sclk),
             .I(1'b0),
             .T(i2c_sclk_ts));

SYSMONE4 #(
        .COMMON_N_SOURCE(16'hFFFF),
        .INIT_40(16'h0000), // config reg 0
        .INIT_41(16'h2190), // config reg 1
        .INIT_42(16'h1900), // config reg 2
        .INIT_43(16'h208F), // config reg 3
        .INIT_44(16'h0000), // config reg 4
        .INIT_45(16'hCEDC), // Analog Bus Register
        .INIT_46(16'h0000), // Sequencer Channel selection (Vuser0-3)
        .INIT_47(16'h0000), // Sequencer Average selection (Vuser0-3)
        .INIT_48(16'h4F01), // Sequencer channel selection
        .INIT_49(16'h0000), // Sequencer channel selection
        .INIT_4A(16'h0000), // Sequencer Average selection
        .INIT_4B(16'h0000), // Sequencer Average selection
        .INIT_4C(16'h0000), // Sequencer Bipolar selection
        .INIT_4D(16'h0000), // Sequencer Bipolar selection
        .INIT_4E(16'h0000), // Sequencer Acq time selection
        .INIT_4F(16'h0000), // Sequencer Acq time selection
        .INIT_50(16'hBAA7), // Temp alarm trigger
        .INIT_51(16'h4E81), // Vccint upper alarm limit
        .INIT_52(16'hA147), // Vccaux upper alarm limit
        .INIT_53(16'hCF83),  // Temp alarm OT upper
        .INIT_54(16'hADA0), // Temp alarm reset
        .INIT_55(16'h4963), // Vccint lower alarm limit
        .INIT_56(16'h9555), // Vccaux lower alarm limit
        .INIT_57(16'hB2D6),  // Temp alarm OT reset
        .INIT_58(16'h4E81), // VCCBRAM upper alarm limit
        .INIT_5C(16'h4963), //  VCCBRAM lower alarm limit
        .INIT_59(16'h5555), // vccpsintlp upper alarm limit
        .INIT_5D(16'h5111), //  vccpsintlp lower alarm limit
        .INIT_5A(16'h9999), // vccpsintfp upper alarm limit
        .INIT_5E(16'h91EB), //  vccpsintfp lower alarm limit
        .INIT_5B(16'h6AAA), // vccpsaux upper alarm limit
        .INIT_5F(16'h6666), //  vccpsaux lower alarm limit
        .INIT_60(16'h9A74), // Vuser0 upper alarm limit
        .INIT_61(16'h4DA6), // Vuser1 upper alarm limit
        .INIT_62(16'h9A74), // Vuser2 upper alarm limit
        .INIT_63(16'h9A74), // Vuser3 upper alarm limit
        .INIT_68(16'h98BF), // Vuser0 lower alarm limit
        .INIT_69(16'h4BF2), // Vuser1 lower alarm limit
        .INIT_6A(16'h98BF), // Vuser2 lower alarm limit
        .INIT_6B(16'h98BF), // Vuser3 lower alarm limit
        .INIT_7A(16'h0000), // DUAL0 Register
        .INIT_7B(16'h0000), // DUAL1 Register
        .INIT_7C(16'h0000), // DUAL2 Register
        .INIT_7D(16'h0000), // DUAL3 Register
        .SIM_DEVICE("ULTRASCALE_PLUS_ES1"),
        .SIM_MONITOR_FILE("design.txt")
)

inst_sysmon (
       .ADC_DATA(),
        .CONVST(GND_BIT),
        .CONVSTCLK(GND_BIT),
        .DADDR(daddr_in[7:0]),
        .DCLK(dclk_in),
        .DEN(den_in),
        .DI(di_in[15:0]),
        .DWE(dwe_in),
        .RESET(reset_in),
        .VAUXN(aux_channel_n[15:0]),
        .VAUXP(aux_channel_p[15:0]),
        .ALM(alm_int),
       .BUSY(busy_out),
        .CHANNEL(channel_out[5:0]),
        .DO(do_out[15:0]),
        .DRDY(drdy_out),
        .EOC(eoc_out),
        .EOS(eos_out),
        .JTAGBUSY(),
        .JTAGLOCKED(),
        .JTAGMODIFIED(),
        .OT(ot_out),
        .I2C_SCLK(i2c_sclk_int),
        .I2C_SDA(i2c_sda_int),
        .I2C_SCLK_TS(i2c_sclk_ts),
        .I2C_SDA_TS(i2c_sda_ts),
        .SMBALERT_TS(),
        .MUXADDR(),
        .VP(vp),
        .VN(vn)
          );


endmodule
