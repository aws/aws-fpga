// (c) Copyright 2013-2015, 2023 Advanced Micro Devices, Inc. All rights reserved.
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

// ***************************
// * DO NOT MODIFY THIS FILE *
// ***************************

`timescale 1ps/1ps

module gtwizard_ultrascale_v1_7_18_gtwiz_userdata_tx #(

  parameter integer P_TX_USER_DATA_WIDTH       = 32,
  parameter integer P_TX_DATA_ENCODING         = 0,
  parameter integer P_TOTAL_NUMBER_OF_CHANNELS = 1

)(

  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS*P_TX_USER_DATA_WIDTH)-1:0] gtwiz_userdata_tx_in,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS*128)-1:0]                  txdata_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS* 16)-1:0]                  txctrl0_out,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS* 16)-1:0]                  txctrl1_out

);


  // -------------------------------------------------------------------------------------------------------------------
  // Transmitter user data width sizing conditional generation, based on parameter values in module instantiation
  // -------------------------------------------------------------------------------------------------------------------
  generate if (1) begin : gen_gtwiz_userdata_tx_main
    genvar ch_idx;

    // If transmitter data encoding is either not raw mode, or is raw mode but user data width is not modulus 10, then
    // simply assign the transceiver-facing TXDATA vector with data bits from the user-facing data vector, plus padding.
    if ((P_TX_DATA_ENCODING != 0) ||
       ((P_TX_DATA_ENCODING == 0) && (P_TX_USER_DATA_WIDTH % 10 != 0))) begin : gen_txdata

      for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_assign
        if (P_TX_USER_DATA_WIDTH < 128) begin : gen_less_128
          assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
            {{128-P_TX_USER_DATA_WIDTH{1'b0}},
             gtwiz_userdata_tx_in[(P_TX_USER_DATA_WIDTH*ch_idx)+P_TX_USER_DATA_WIDTH-1:
                                  (P_TX_USER_DATA_WIDTH*ch_idx)]};
        end
        else begin : gen_128
          assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
             gtwiz_userdata_tx_in[(P_TX_USER_DATA_WIDTH*ch_idx)+P_TX_USER_DATA_WIDTH-1:
                                  (P_TX_USER_DATA_WIDTH*ch_idx)];
        end
      end

      // Transceiver-facing TXCTRL0 and TXCTRL1 vectors are not driven by this helper block in this configuration
      assign txctrl0_out = {P_TOTAL_NUMBER_OF_CHANNELS*16{1'b0}};
      assign txctrl1_out = {P_TOTAL_NUMBER_OF_CHANNELS*16{1'b0}};
    end

    // If transmitter data encoding is raw mode and user data width is modulus 10, then assign the specified combination
    // of transceiver-facing TXDATA, TXCTRL0, and TXCTRL1 vectors with the user-facing data vector. The interleaving of
    // these vectors is always in a repeating 8-1-1 bit pattern, scaling with the user data width size.
    else begin : gen_txdata_txctrl

      case (P_TX_USER_DATA_WIDTH)
        20:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width20
            assign txctrl1_out[(16*ch_idx)+15:(16*ch_idx)] =
              {14'b0,
               gtwiz_userdata_tx_in[(ch_idx*20)+19],
               gtwiz_userdata_tx_in[(ch_idx*20)+9]};
            assign txctrl0_out[(16*ch_idx)+15:(16*ch_idx)] =
              {14'b0,
               gtwiz_userdata_tx_in[(ch_idx*20)+18],
               gtwiz_userdata_tx_in[(ch_idx*20)+8]};
            assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
              {112'b0,
               gtwiz_userdata_tx_in[(ch_idx*20)+17:(ch_idx*20)+10],
               gtwiz_userdata_tx_in[(ch_idx*20)+7:ch_idx*20]};
          end

        40:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width40
            assign txctrl1_out[(16*ch_idx)+15:(16*ch_idx)] =
              {12'b0,
               gtwiz_userdata_tx_in[(ch_idx*40)+39],
               gtwiz_userdata_tx_in[(ch_idx*40)+29],
               gtwiz_userdata_tx_in[(ch_idx*40)+19],
               gtwiz_userdata_tx_in[(ch_idx*40)+9]};
            assign txctrl0_out[(16*ch_idx)+15:(16*ch_idx)] =
              {12'b0,
               gtwiz_userdata_tx_in[(ch_idx*40)+38],
               gtwiz_userdata_tx_in[(ch_idx*40)+28],
               gtwiz_userdata_tx_in[(ch_idx*40)+18],
               gtwiz_userdata_tx_in[(ch_idx*40)+8]};
            assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
              {96'b0,
               gtwiz_userdata_tx_in[(ch_idx*40)+37:(ch_idx*40)+30],
               gtwiz_userdata_tx_in[(ch_idx*40)+27:(ch_idx*40)+20],
               gtwiz_userdata_tx_in[(ch_idx*40)+17:(ch_idx*40)+10],
               gtwiz_userdata_tx_in[(ch_idx*40)+7:ch_idx*40]};
          end

        80:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width80
            assign txctrl1_out[(16*ch_idx)+15:(16*ch_idx)] =
              {8'b0,
               gtwiz_userdata_tx_in[(ch_idx*80)+79],
               gtwiz_userdata_tx_in[(ch_idx*80)+69],
               gtwiz_userdata_tx_in[(ch_idx*80)+59],
               gtwiz_userdata_tx_in[(ch_idx*80)+49],
               gtwiz_userdata_tx_in[(ch_idx*80)+39],
               gtwiz_userdata_tx_in[(ch_idx*80)+29],
               gtwiz_userdata_tx_in[(ch_idx*80)+19],
               gtwiz_userdata_tx_in[(ch_idx*80)+9]};
            assign txctrl0_out[(16*ch_idx)+15:(16*ch_idx)] =
              {8'b0,
               gtwiz_userdata_tx_in[(ch_idx*80)+78],
               gtwiz_userdata_tx_in[(ch_idx*80)+68],
               gtwiz_userdata_tx_in[(ch_idx*80)+58],
               gtwiz_userdata_tx_in[(ch_idx*80)+48],
               gtwiz_userdata_tx_in[(ch_idx*80)+38],
               gtwiz_userdata_tx_in[(ch_idx*80)+28],
               gtwiz_userdata_tx_in[(ch_idx*80)+18],
               gtwiz_userdata_tx_in[(ch_idx*80)+8]};
            assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
              {64'b0,
               gtwiz_userdata_tx_in[(ch_idx*80)+77:(ch_idx*80)+70],
               gtwiz_userdata_tx_in[(ch_idx*80)+67:(ch_idx*80)+60],
               gtwiz_userdata_tx_in[(ch_idx*80)+57:(ch_idx*80)+50],
               gtwiz_userdata_tx_in[(ch_idx*80)+47:(ch_idx*80)+40],
               gtwiz_userdata_tx_in[(ch_idx*80)+37:(ch_idx*80)+30],
               gtwiz_userdata_tx_in[(ch_idx*80)+27:(ch_idx*80)+20],
               gtwiz_userdata_tx_in[(ch_idx*80)+17:(ch_idx*80)+10],
               gtwiz_userdata_tx_in[(ch_idx*80)+7:ch_idx*80]};
          end

        160:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width160
            assign txctrl1_out[(16*ch_idx)+15:(16*ch_idx)] =
              {gtwiz_userdata_tx_in[(ch_idx*160)+159],
               gtwiz_userdata_tx_in[(ch_idx*160)+149],
               gtwiz_userdata_tx_in[(ch_idx*160)+139],
               gtwiz_userdata_tx_in[(ch_idx*160)+129],
               gtwiz_userdata_tx_in[(ch_idx*160)+119],
               gtwiz_userdata_tx_in[(ch_idx*160)+109],
               gtwiz_userdata_tx_in[(ch_idx*160)+99],
               gtwiz_userdata_tx_in[(ch_idx*160)+89],
               gtwiz_userdata_tx_in[(ch_idx*160)+79],
               gtwiz_userdata_tx_in[(ch_idx*160)+69],
               gtwiz_userdata_tx_in[(ch_idx*160)+59],
               gtwiz_userdata_tx_in[(ch_idx*160)+49],
               gtwiz_userdata_tx_in[(ch_idx*160)+39],
               gtwiz_userdata_tx_in[(ch_idx*160)+29],
               gtwiz_userdata_tx_in[(ch_idx*160)+19],
               gtwiz_userdata_tx_in[(ch_idx*160)+9]};
            assign txctrl0_out[(16*ch_idx)+15:(16*ch_idx)] =
              {gtwiz_userdata_tx_in[(ch_idx*160)+158],
               gtwiz_userdata_tx_in[(ch_idx*160)+148],
               gtwiz_userdata_tx_in[(ch_idx*160)+138],
               gtwiz_userdata_tx_in[(ch_idx*160)+128],
               gtwiz_userdata_tx_in[(ch_idx*160)+118],
               gtwiz_userdata_tx_in[(ch_idx*160)+108],
               gtwiz_userdata_tx_in[(ch_idx*160)+98],
               gtwiz_userdata_tx_in[(ch_idx*160)+88],
               gtwiz_userdata_tx_in[(ch_idx*160)+78],
               gtwiz_userdata_tx_in[(ch_idx*160)+68],
               gtwiz_userdata_tx_in[(ch_idx*160)+58],
               gtwiz_userdata_tx_in[(ch_idx*160)+48],
               gtwiz_userdata_tx_in[(ch_idx*160)+38],
               gtwiz_userdata_tx_in[(ch_idx*160)+28],
               gtwiz_userdata_tx_in[(ch_idx*160)+18],
               gtwiz_userdata_tx_in[(ch_idx*160)+8]};
            assign txdata_out[(128*ch_idx)+127:(128*ch_idx)] =
              {gtwiz_userdata_tx_in[(ch_idx*160)+157:(ch_idx*160)+150],
               gtwiz_userdata_tx_in[(ch_idx*160)+147:(ch_idx*160)+140],
               gtwiz_userdata_tx_in[(ch_idx*160)+137:(ch_idx*160)+130],
               gtwiz_userdata_tx_in[(ch_idx*160)+127:(ch_idx*160)+120],
               gtwiz_userdata_tx_in[(ch_idx*160)+117:(ch_idx*160)+110],
               gtwiz_userdata_tx_in[(ch_idx*160)+107:(ch_idx*160)+100],
               gtwiz_userdata_tx_in[(ch_idx*160)+97:(ch_idx*160)+90],
               gtwiz_userdata_tx_in[(ch_idx*160)+87:(ch_idx*160)+80],
               gtwiz_userdata_tx_in[(ch_idx*160)+77:(ch_idx*160)+70],
               gtwiz_userdata_tx_in[(ch_idx*160)+67:(ch_idx*160)+60],
               gtwiz_userdata_tx_in[(ch_idx*160)+57:(ch_idx*160)+50],
               gtwiz_userdata_tx_in[(ch_idx*160)+47:(ch_idx*160)+40],
               gtwiz_userdata_tx_in[(ch_idx*160)+37:(ch_idx*160)+30],
               gtwiz_userdata_tx_in[(ch_idx*160)+27:(ch_idx*160)+20],
               gtwiz_userdata_tx_in[(ch_idx*160)+17:(ch_idx*160)+10],
               gtwiz_userdata_tx_in[(ch_idx*160)+7:ch_idx*160]};
          end

        default:
          begin : gen_default
            // The default case is a configuration error scenario should never be exercised
            assign txdata_out  = {P_TOTAL_NUMBER_OF_CHANNELS*128{1'b1}};
            assign txctrl0_out = {P_TOTAL_NUMBER_OF_CHANNELS*16{1'b1}};
            assign txctrl1_out = {P_TOTAL_NUMBER_OF_CHANNELS*16{1'b1}};
          end
      endcase

    end

  end
  endgenerate


endmodule
