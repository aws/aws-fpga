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
// \   \  /  \    Date Created       : Dec 08 2014
//  \___\/\___\
//
// Device           : UltraScale
// Design Name      : DDR4 SDRAM & DDR3 SDRAM
// Purpose          :
//                   ddr4_v2_2_10_ddr_xsdb_bram module
// Reference        :
// Revision History :
//*****************************************************************************
`timescale 1ns / 1ps


module ddr4_v2_2_10_cfg_mem_mod # (
                        // Number of Memory Bits required. Based on this we calculate how many BRAMs are required
                        parameter SIZE         = 36 * 1024 * 1,
                        // You don't need to override this 
                        parameter NUM_BRAMS    = SIZE/36864 + (SIZE%36864 == 0 ? 0 : 1),
                        // Specify INITs as 9 bit blocks (256 locations per blockRAM)
                        parameter [256*9*NUM_BRAMS-1:0] INIT = 'd0,
                        parameter ADDR_WIDTH   = 16,
                        parameter DATA_WIDTH   = 9,
                        // Optional Pipeline Register Control
                        parameter PIPELINE_REG = 1 
                     )
                     (
                      input clka,
                      input clkb,
                      input ena,
                      input enb,
                      input [ADDR_WIDTH-1:0]addra,
                      input [ADDR_WIDTH-1:0]addrb,
                      input [DATA_WIDTH-1:0]dina,
                      input [DATA_WIDTH-1:0]dinb,
                      input wea,
                      input web,
                      input rsta,
                      input rstb,
                      output reg [DATA_WIDTH-1:0]douta,
                      output reg [DATA_WIDTH-1:0]doutb
                     );

localparam ADDR_WIDTH_INT = 12;
wire [DATA_WIDTH-1:0] douta_mem [NUM_BRAMS-1:0];
wire [DATA_WIDTH-1:0] doutb_mem [NUM_BRAMS-1:0];

genvar i;

function automatic integer logb2 (
                        input integer N
                       );

integer i;
integer calc_log=0;
begin
 for(i=0;2**i < N; i=i+1)
 begin
   calc_log = i;
 end
 logb2 = calc_log + 1;
end
endfunction 

localparam ADDR_MSB = logb2(NUM_BRAMS) + ADDR_WIDTH_INT;

generate
for(i=0;i<NUM_BRAMS;i=i+1)
begin: gen_mem
wire dec_ena = ADDR_WIDTH == ADDR_WIDTH_INT || NUM_BRAMS == 1 ? ena : ena & (i == addra[ADDR_MSB-1:ADDR_WIDTH_INT]);
wire dec_enb = ADDR_WIDTH == ADDR_WIDTH_INT || NUM_BRAMS == 1 ? enb : enb & (i == addrb[ADDR_MSB-1:ADDR_WIDTH_INT]);


  ddr4_v2_2_10_bram_tdp # (
              .INIT(INIT[256*9*(i+1)-1:256*9*i]),
              .PIPELINE_REG(PIPELINE_REG)
             )
         inst (
                .clka(clka),
                .clkb(clkb),
                .ena(dec_ena),
                .enb(dec_enb),
                .addra(addra[ADDR_WIDTH_INT-1:0]),
                .addrb(addrb[ADDR_WIDTH_INT-1:0]),
                .dina(dina),
                .dinb(dinb),
                .wea(wea),
                .web(web),
                .rsta(rsta),
                .rstb(rstb),
                .douta(douta_mem[i]),
                .doutb(doutb_mem[i])
              );
              
end
endgenerate

integer j;

always @ *
begin
if(ADDR_WIDTH == ADDR_WIDTH_INT || NUM_BRAMS == 1)
begin
 douta = douta_mem[0];
 doutb = doutb_mem[0];
end
else
begin
 douta = 0;
 doutb = 0;
 for(j=0;j<NUM_BRAMS;j=j+1)
 begin
   if(j == addra[ADDR_MSB-1:ADDR_WIDTH_INT])
    douta = douta_mem[j];
   if(j == addrb[ADDR_MSB-1:ADDR_WIDTH_INT])
    doutb = doutb_mem[j];
 end 
end
end

endmodule

module ddr4_v2_2_10_bram_tdp #(
                  parameter [256*9-1:0] INIT = 'd0,
                  parameter ADDR_WIDTH   = 12,
                  parameter DATA_WIDTH   = 9,
                  parameter PIPELINE_REG = 1 
                 )
                 (
                  input clka,
                  input clkb,
                  input ena,
                  input enb,
                  input [ADDR_WIDTH-1:0]addra,
                  input [ADDR_WIDTH-1:0]addrb,
                  input [DATA_WIDTH-1:0]dina,
                  input [DATA_WIDTH-1:0]dinb,
                  input wea,
                  input web,
                  input rsta,
                  input rstb,
                  output [DATA_WIDTH-1:0]douta,
                  output [DATA_WIDTH-1:0]doutb
                 );

reg [DATA_WIDTH-1:0] mem [2**ADDR_WIDTH-1:0]; // spyglass disable SYNTH_5273

integer i;
initial
begin
 for(i=0;i<256;i=i+1)
  mem[i] = INIT[9*i +: 9];
end

reg [DATA_WIDTH-1:0] dataa,datab;
reg [DATA_WIDTH-1:0] dataa_pipe,datab_pipe;

// True Dual Port RAM - Write first on both sides
 always @ (posedge clka)
 begin
  if(ena)
  begin
    if(wea)
    begin
      dataa <= dina;
      mem[addra] <= dina;
    end      
    else
      dataa <= mem[addra];

    dataa_pipe <= dataa;
  end
 end

 always @ (posedge clkb)
 begin
  if(enb)
  begin
    if(web)
    begin
      datab <= dinb;
      mem[addrb] <= dinb;
    end      
    else
      datab <= mem[addrb];

    datab_pipe <= datab;  
  end
 end

assign douta = PIPELINE_REG ? dataa_pipe : dataa;
assign doutb = PIPELINE_REG ? datab_pipe : datab;

endmodule




