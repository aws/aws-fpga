//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
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
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_rc_pcie4c_ip_bram_rep_int.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_rc_pcie4c_ip_bram_rep_int #(

  parameter EN_ECC_PIPE ="FALSE",
  parameter TCQ = 100

  ) (

  input  wire         clk_i,
  input  wire         reset_i,

  input  wire   [8:0] addr_i,
  input  wire   [0:0] wen_i,
  input  wire [255:0] wdata_i,
  input  wire   [0:0] ren_i,
  output wire [255:0] rdata_o,

  output wire   [3:0] err_cor_o,
  output wire   [3:0] err_uncor_o

  );

  genvar              i;

  wire [255:0]        rdata_w;
  wire [255:0]        wdata_w = wdata_i;

  generate begin : ECC_RAM

   for (i = 0; i < 4; i = i + 1)
   begin : RAMB36E2
        RAMB36E2 #(
          .DOA_REG (((EN_ECC_PIPE == "TRUE")? 0: 1)),
          .DOB_REG (((EN_ECC_PIPE == "TRUE")? 0: 1)),
          .EN_ECC_READ ("TRUE"),
          .EN_ECC_WRITE ("TRUE"),
          .EN_ECC_PIPE(EN_ECC_PIPE),
          .INIT_A (36'h000000000),
          .INIT_B (36'h000000000),
          .INIT_FILE ("NONE"),
          .READ_WIDTH_A (72),
          .READ_WIDTH_B (0),
          .RSTREG_PRIORITY_A ("REGCE"),
          .RSTREG_PRIORITY_B ("REGCE"),
          .SIM_COLLISION_CHECK ("ALL"),
          .SRVAL_A (36'h000000000),
          .SRVAL_B (36'h000000000),
          .WRITE_MODE_A ("WRITE_FIRST"),
          .WRITE_MODE_B ("WRITE_FIRST"),
          .WRITE_WIDTH_A (0),
          .WRITE_WIDTH_B (72))
        ramb36e2_inst (
          .ADDRENA (1'b1),
          .ADDRENB (1'b1),
          .CASDIMUXA (1'b0),
          .CASDIMUXB (1'b0),
          .CASDOMUXA (1'b0),
          .CASDOMUXB (1'b0),
          .CASDOMUXEN_A (1'b0),
          .CASDOMUXEN_B (1'b0),
          .CASINDBITERR (1'b0),
          .CASINSBITERR (1'b0),
          .CASOREGIMUXA (1'b0),
          .CASOREGIMUXB (1'b0),
          .CASOREGIMUXEN_A (1'b0),
          .CASOREGIMUXEN_B (1'b0),
          .ECCPIPECE (1'b1),
          .SLEEP (1'b0),
          .CASDINA (32'b0),
          .CASDINB (32'b0),
          .CASDINPA(4'b0),
          .CASDINPB(4'b0),
          .CASDOUTA (),
          .CASDOUTB (),
          .CASDOUTPA (),
          .CASDOUTPB (),
          .CASOUTDBITERR (),
          .CASOUTSBITERR (),
          .CLKARDCLK (clk_i),
          .CLKBWRCLK (clk_i),
          .DBITERR (err_uncor_o[i]),
          .ENARDEN (ren_i),
          .ENBWREN (wen_i),
          .INJECTDBITERR (1'b0),
          .INJECTSBITERR (1'b0),
          .REGCEAREGCE (1'b1),
          .REGCEB (1'b0),
          .RSTRAMARSTRAM (1'b0),
          .RSTRAMB (1'b0),
          .RSTREGARSTREG (1'b0),
          .RSTREGB (1'b0),
          .SBITERR (err_cor_o[i]),
          .ADDRARDADDR ({addr_i[8:0], 6'b0}),
          .ADDRBWRADDR ({addr_i[8:0], 6'b0}),
          .DINADIN (wdata_w[(2*32*i)+31:(2*32*i)+0]),
          .DINBDIN (wdata_w[(2*32*i)+63:(2*32*i)+32]),
          .DINPADINP (4'b0),
          .DINPBDINP (4'b0),
          .DOUTADOUT (rdata_w[(2*32*i)+31:(2*32*i)+0]),
          .DOUTBDOUT (rdata_w[(2*32*i)+63:(2*32*i)+32]),
          .DOUTPADOUTP (),
          .DOUTPBDOUTP (),
          .ECCPARITY (),
          .RDADDRECC (),
          .WEA (4'h0),
          .WEBWE (8'hFF)
        );
      end
    end
  endgenerate

  assign rdata_o =  rdata_w;

endmodule
