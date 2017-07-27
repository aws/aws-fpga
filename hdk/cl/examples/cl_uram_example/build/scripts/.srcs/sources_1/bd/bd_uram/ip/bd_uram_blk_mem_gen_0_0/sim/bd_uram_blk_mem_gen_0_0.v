// (c) Copyright 1995-2017 Xilinx, Inc. All rights reserved.
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
// 
// DO NOT MODIFY THIS FILE.


// IP VLNV: xilinx.com:ip:blk_mem_gen:8.3
// IP Revision: 6

`timescale 1ns/1ps

(* DowngradeIPIdentifiedWarnings = "yes" *)
module bd_uram_blk_mem_gen_0_0 (
  clka,
  ena,
  wea,
  addra,
  dina,
  clkb,
  enb,
  addrb,
  doutb
);

(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTA CLK" *)
input wire clka;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTA EN" *)
input wire ena;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTA WE" *)
input wire [0 : 0] wea;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTA ADDR" *)
input wire [19 : 0] addra;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTA DIN" *)
input wire [31 : 0] dina;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTB CLK" *)
input wire clkb;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTB EN" *)
input wire enb;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTB ADDR" *)
input wire [19 : 0] addrb;
(* X_INTERFACE_INFO = "xilinx.com:interface:bram:1.0 BRAM_PORTB DOUT" *)
output wire [31 : 0] doutb;

  blk_mem_gen_v8_3_6 #(
    .C_FAMILY("virtexuplus"),
    .C_XDEVICEFAMILY("virtexuplus"),
    .C_ELABORATION_DIR("./"),
    .C_INTERFACE_TYPE(0),
    .C_AXI_TYPE(1),
    .C_AXI_SLAVE_TYPE(0),
    .C_USE_BRAM_BLOCK(0),
    .C_ENABLE_32BIT_ADDRESS(0),
    .C_CTRL_ECC_ALGO("NONE"),
    .C_HAS_AXI_ID(0),
    .C_AXI_ID_WIDTH(4),
    .C_MEM_TYPE(1),
    .C_BYTE_SIZE(9),
    .C_ALGORITHM(1),
    .C_PRIM_TYPE(1),
    .C_LOAD_INIT_FILE(0),
    .C_INIT_FILE_NAME("no_coe_file_loaded"),
    .C_INIT_FILE("NONE"),
    .C_USE_DEFAULT_DATA(0),
    .C_DEFAULT_DATA("0"),
    .C_HAS_RSTA(0),
    .C_RST_PRIORITY_A("CE"),
    .C_RSTRAM_A(0),
    .C_INITA_VAL("0"),
    .C_HAS_ENA(1),
    .C_HAS_REGCEA(0),
    .C_USE_BYTE_WEA(0),
    .C_WEA_WIDTH(1),
    .C_WRITE_MODE_A("READ_FIRST"),
    .C_WRITE_WIDTH_A(32),
    .C_READ_WIDTH_A(32),
    .C_WRITE_DEPTH_A(819200),
    .C_READ_DEPTH_A(819200),
    .C_ADDRA_WIDTH(20),
    .C_HAS_RSTB(0),
    .C_RST_PRIORITY_B("CE"),
    .C_RSTRAM_B(0),
    .C_INITB_VAL("0"),
    .C_HAS_ENB(1),
    .C_HAS_REGCEB(0),
    .C_USE_BYTE_WEB(0),
    .C_WEB_WIDTH(1),
    .C_WRITE_MODE_B("READ_FIRST"),
    .C_WRITE_WIDTH_B(32),
    .C_READ_WIDTH_B(32),
    .C_WRITE_DEPTH_B(819200),
    .C_READ_DEPTH_B(819200),
    .C_ADDRB_WIDTH(20),
    .C_HAS_MEM_OUTPUT_REGS_A(0),
    .C_HAS_MEM_OUTPUT_REGS_B(0),
    .C_HAS_MUX_OUTPUT_REGS_A(0),
    .C_HAS_MUX_OUTPUT_REGS_B(0),
    .C_MUX_PIPELINE_STAGES(0),
    .C_HAS_SOFTECC_INPUT_REGS_A(0),
    .C_HAS_SOFTECC_OUTPUT_REGS_B(0),
    .C_USE_SOFTECC(0),
    .C_USE_ECC(0),
    .C_EN_ECC_PIPE(0),
    .C_HAS_INJECTERR(0),
    .C_SIM_COLLISION_CHECK("ALL"),
    .C_COMMON_CLK(1),
    .C_DISABLE_WARN_BHV_COLL(0),
    .C_EN_SLEEP_PIN(0),
    .C_USE_URAM(1),
    .C_EN_RDADDRA_CHG(0),
    .C_EN_RDADDRB_CHG(0),
    .C_EN_DEEPSLEEP_PIN(0),
    .C_EN_SHUTDOWN_PIN(0),
    .C_EN_SAFETY_CKT(0),
    .C_DISABLE_WARN_BHV_RANGE(0),
    .C_COUNT_36K_BRAM("600"),
    .C_COUNT_18K_BRAM("250"),
    .C_EST_POWER_SUMMARY("Estimated Power for IP     :     211.933392 mW")
  ) inst (
    .clka(clka),
    .rsta(1'D0),
    .ena(ena),
    .regcea(1'D0),
    .wea(wea),
    .addra(addra),
    .dina(dina),
    .douta(),
    .clkb(clkb),
    .rstb(1'D0),
    .enb(enb),
    .regceb(1'D0),
    .web(1'B0),
    .addrb(addrb),
    .dinb(32'B0),
    .doutb(doutb),
    .injectsbiterr(1'D0),
    .injectdbiterr(1'D0),
    .eccpipece(1'D0),
    .sbiterr(),
    .dbiterr(),
    .rdaddrecc(),
    .sleep(1'D0),
    .deepsleep(1'D0),
    .shutdown(1'D0),
    .rsta_busy(),
    .rstb_busy(),
    .s_aclk(1'H0),
    .s_aresetn(1'D0),
    .s_axi_awid(4'B0),
    .s_axi_awaddr(32'B0),
    .s_axi_awlen(8'B0),
    .s_axi_awsize(3'B0),
    .s_axi_awburst(2'B0),
    .s_axi_awvalid(1'D0),
    .s_axi_awready(),
    .s_axi_wdata(32'B0),
    .s_axi_wstrb(1'B0),
    .s_axi_wlast(1'D0),
    .s_axi_wvalid(1'D0),
    .s_axi_wready(),
    .s_axi_bid(),
    .s_axi_bresp(),
    .s_axi_bvalid(),
    .s_axi_bready(1'D0),
    .s_axi_arid(4'B0),
    .s_axi_araddr(32'B0),
    .s_axi_arlen(8'B0),
    .s_axi_arsize(3'B0),
    .s_axi_arburst(2'B0),
    .s_axi_arvalid(1'D0),
    .s_axi_arready(),
    .s_axi_rid(),
    .s_axi_rdata(),
    .s_axi_rresp(),
    .s_axi_rlast(),
    .s_axi_rvalid(),
    .s_axi_rready(1'D0),
    .s_axi_injectsbiterr(1'D0),
    .s_axi_injectdbiterr(1'D0),
    .s_axi_sbiterr(),
    .s_axi_dbiterr(),
    .s_axi_rdaddrecc()
  );
endmodule
