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

module gtwizard_ultrascale_v1_7_18_gtwiz_userdata_rx #(

  parameter integer P_RX_USER_DATA_WIDTH       = 32,
  parameter integer P_RX_DATA_DECODING         = 0,
  parameter integer P_TOTAL_NUMBER_OF_CHANNELS = 1

)(

  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS*128)-1:0]                  rxdata_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS* 16)-1:0]                  rxctrl0_in,
  input  wire [(P_TOTAL_NUMBER_OF_CHANNELS* 16)-1:0]                  rxctrl1_in,
  output wire [(P_TOTAL_NUMBER_OF_CHANNELS*P_RX_USER_DATA_WIDTH)-1:0] gtwiz_userdata_rx_out

);


  // -------------------------------------------------------------------------------------------------------------------
  // Receiver user data width sizing conditional generation, based on parameter values in module instantiation
  // -------------------------------------------------------------------------------------------------------------------
  generate if (1) begin : gen_gtwiz_userdata_rx_main
    genvar ch_idx;

    // If receiver data decoding is either not raw mode, or is raw mode but user data width is not modulus 10, then
    // simply assign the user-facing data vector with the active data bits from the transceiver-facing RXDATA vector.
    if ((P_RX_DATA_DECODING != 0) ||
       ((P_RX_DATA_DECODING == 0) && (P_RX_USER_DATA_WIDTH % 10 != 0))) begin : gen_rxdata

      for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_assign
        assign gtwiz_userdata_rx_out[(P_RX_USER_DATA_WIDTH*ch_idx)+P_RX_USER_DATA_WIDTH-1:
                                     (P_RX_USER_DATA_WIDTH*ch_idx)] =
          rxdata_in[(128*ch_idx)+P_RX_USER_DATA_WIDTH-1:(128*ch_idx)];
      end

    end

    // If receiver data decoding is raw mode and user data width is modulus 10, then assign the user-facing data vector
    // with the specified combination of transceiver-facing RXDATA, RXCTRL0, and RXCTRL1 vectors. The interleaving of
    // these vectors is always in a repeating 8-1-1 bit pattern, scaling with the user data width size.
    else begin : gen_rxdata_rxctrl

      case (P_RX_USER_DATA_WIDTH)
        20:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width20
            assign gtwiz_userdata_rx_out [(ch_idx*20)+19:(ch_idx*20)] =
              {rxctrl1_in[(ch_idx* 16)+1],
               rxctrl0_in[(ch_idx* 16)+1],
               rxdata_in [(ch_idx*128)+15:(ch_idx*128)+8],
               rxctrl1_in[(ch_idx* 16)],
               rxctrl0_in[(ch_idx* 16)],
               rxdata_in [(ch_idx*128)+7:ch_idx*128]};
          end

        40:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width40
            assign gtwiz_userdata_rx_out [(ch_idx*40)+39:(ch_idx*40)] =
              {rxctrl1_in[(ch_idx* 16)+3],
               rxctrl0_in[(ch_idx* 16)+3],
               rxdata_in [(ch_idx*128)+31:(ch_idx*128)+24],
               rxctrl1_in[(ch_idx* 16)+2],
               rxctrl0_in[(ch_idx* 16)+2],
               rxdata_in [(ch_idx*128)+23:(ch_idx*128)+16],
               rxctrl1_in[(ch_idx* 16)+1],
               rxctrl0_in[(ch_idx* 16)+1],
               rxdata_in [(ch_idx*128)+15:(ch_idx*128)+8],
               rxctrl1_in[(ch_idx* 16)],
               rxctrl0_in[(ch_idx* 16)],
               rxdata_in [(ch_idx*128)+7:ch_idx*128]};
          end

        80:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width80
            assign gtwiz_userdata_rx_out [(ch_idx*80)+79:(ch_idx*80)] =
              {rxctrl1_in[(ch_idx* 16)+7],
               rxctrl0_in[(ch_idx* 16)+7],
               rxdata_in [(ch_idx*128)+63:(ch_idx*128)+56],
               rxctrl1_in[(ch_idx* 16)+6],
               rxctrl0_in[(ch_idx* 16)+6],
               rxdata_in [(ch_idx*128)+55:(ch_idx*128)+48],
               rxctrl1_in[(ch_idx* 16)+5],
               rxctrl0_in[(ch_idx* 16)+5],
               rxdata_in [(ch_idx*128)+47:(ch_idx*128)+40],
               rxctrl1_in[(ch_idx* 16)+4],
               rxctrl0_in[(ch_idx* 16)+4],
               rxdata_in [(ch_idx*128)+39:(ch_idx*128)+32],
               rxctrl1_in[(ch_idx* 16)+3],
               rxctrl0_in[(ch_idx* 16)+3],
               rxdata_in [(ch_idx*128)+31:(ch_idx*128)+24],
               rxctrl1_in[(ch_idx* 16)+2],
               rxctrl0_in[(ch_idx* 16)+2],
               rxdata_in [(ch_idx*128)+23:(ch_idx*128)+16],
               rxctrl1_in[(ch_idx* 16)+1],
               rxctrl0_in[(ch_idx* 16)+1],
               rxdata_in [(ch_idx*128)+15:(ch_idx*128)+8],
               rxctrl1_in[(ch_idx* 16)],
               rxctrl0_in[(ch_idx* 16)],
               rxdata_in [(ch_idx*128)+7:ch_idx*128]};
          end

        160:
          for (ch_idx = 0; ch_idx < P_TOTAL_NUMBER_OF_CHANNELS; ch_idx = ch_idx + 1) begin : gen_width160
            assign gtwiz_userdata_rx_out [(ch_idx*160)+159:(ch_idx*160)] =
              {rxctrl1_in[(ch_idx* 16)+15],
               rxctrl0_in[(ch_idx* 16)+15],
               rxdata_in [(ch_idx*128)+127:(ch_idx*128)+120],
               rxctrl1_in[(ch_idx* 16)+14],
               rxctrl0_in[(ch_idx* 16)+14],
               rxdata_in [(ch_idx*128)+119:(ch_idx*128)+112],
               rxctrl1_in[(ch_idx* 16)+13],
               rxctrl0_in[(ch_idx* 16)+13],
               rxdata_in [(ch_idx*128)+111:(ch_idx*128)+104],
               rxctrl1_in[(ch_idx* 16)+12],
               rxctrl0_in[(ch_idx* 16)+12],
               rxdata_in [(ch_idx*128)+103:(ch_idx*128)+96],
               rxctrl1_in[(ch_idx* 16)+11],
               rxctrl0_in[(ch_idx* 16)+11],
               rxdata_in [(ch_idx*128)+95:(ch_idx*128)+88],
               rxctrl1_in[(ch_idx* 16)+10],
               rxctrl0_in[(ch_idx* 16)+10],
               rxdata_in [(ch_idx*128)+87:(ch_idx*128)+80],
               rxctrl1_in[(ch_idx* 16)+9],
               rxctrl0_in[(ch_idx* 16)+9],
               rxdata_in [(ch_idx*128)+79:(ch_idx*128)+72],
               rxctrl1_in[(ch_idx* 16)+8],
               rxctrl0_in[(ch_idx* 16)+8],
               rxdata_in [(ch_idx*128)+71:(ch_idx*128)+64],
               rxctrl1_in[(ch_idx* 16)+7],
               rxctrl0_in[(ch_idx* 16)+7],
               rxdata_in [(ch_idx*128)+63:(ch_idx*128)+56],
               rxctrl1_in[(ch_idx* 16)+6],
               rxctrl0_in[(ch_idx* 16)+6],
               rxdata_in [(ch_idx*128)+55:(ch_idx*128)+48],
               rxctrl1_in[(ch_idx* 16)+5],
               rxctrl0_in[(ch_idx* 16)+5],
               rxdata_in [(ch_idx*128)+47:(ch_idx*128)+40],
               rxctrl1_in[(ch_idx* 16)+4],
               rxctrl0_in[(ch_idx* 16)+4],
               rxdata_in [(ch_idx*128)+39:(ch_idx*128)+32],
               rxctrl1_in[(ch_idx* 16)+3],
               rxctrl0_in[(ch_idx* 16)+3],
               rxdata_in [(ch_idx*128)+31:(ch_idx*128)+24],
               rxctrl1_in[(ch_idx* 16)+2],
               rxctrl0_in[(ch_idx* 16)+2],
               rxdata_in [(ch_idx*128)+23:(ch_idx*128)+16],
               rxctrl1_in[(ch_idx* 16)+1],
               rxctrl0_in[(ch_idx* 16)+1],
               rxdata_in [(ch_idx*128)+15:(ch_idx*128)+8],
               rxctrl1_in[(ch_idx* 16)],
               rxctrl0_in[(ch_idx* 16)],
               rxdata_in [(ch_idx*128)+7:ch_idx*128]};
          end

        default:
          begin : gen_default
            // The default case is a configuration error scenario should never be exercised
            assign gtwiz_userdata_rx_out = {P_TOTAL_NUMBER_OF_CHANNELS*P_RX_USER_DATA_WIDTH{1'b1}};
          end
      endcase

    end

  end
  endgenerate


endmodule
