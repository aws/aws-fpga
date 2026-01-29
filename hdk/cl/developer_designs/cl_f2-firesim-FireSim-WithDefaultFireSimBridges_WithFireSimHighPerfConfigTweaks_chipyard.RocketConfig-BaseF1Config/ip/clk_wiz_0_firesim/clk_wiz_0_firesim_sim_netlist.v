// Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// Copyright 2022-2024 Advanced Micro Devices, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2024.2 (lin64) Build 5239630 Fri Nov 08 22:34:34 MST 2024
// Date        : Mon Dec 29 04:36:14 2025
// Host        : ip-192-168-0-221 running 64-bit Ubuntu 24.04.1 LTS
// Command     : write_verilog -force -mode funcsim
//               /home/ubuntu/chipyard-bitstream/sims/firesim/platforms/f2/aws-fpga-firesim-f2/hdk/cl/developer_designs/cl_f2-firesim-FireSim-WithDefaultFireSimBridges_WithFireSimHighPerfConfigTweaks_chipyard.RocketConfig-BaseF1Config/ip/clk_wiz_0_firesim/clk_wiz_0_firesim_sim_netlist.v
// Design      : clk_wiz_0_firesim
// Purpose     : This verilog netlist is a functional simulation representation of the design and should not be modified
//               or synthesized. This netlist cannot be used for SDF annotated simulation.
// Device      : xcvu47p-fsvh2892-2-e
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* NotValidForBitStream *)
module clk_wiz_0_firesim
   (clk_out1,
    clk_out2,
    clk_out3,
    clk_out4,
    clk_out5,
    clk_out6,
    reset,
    locked,
    clk_in1);
  output clk_out1;
  output clk_out2;
  output clk_out3;
  output clk_out4;
  output clk_out5;
  output clk_out6;
  input reset;
  output locked;
  input clk_in1;

  (* IBUF_LOW_PWR *) wire clk_in1;
  wire clk_out1;
  wire clk_out2;
  wire clk_out3;
  wire clk_out4;
  wire clk_out5;
  wire clk_out6;
  wire locked;
  wire reset;

  clk_wiz_0_firesim_clk_wiz inst
       (.clk_in1(clk_in1),
        .clk_out1(clk_out1),
        .clk_out2(clk_out2),
        .clk_out3(clk_out3),
        .clk_out4(clk_out4),
        .clk_out5(clk_out5),
        .clk_out6(clk_out6),
        .locked(locked),
        .reset(reset));
endmodule

module clk_wiz_0_firesim_clk_wiz
   (clk_out1,
    clk_out2,
    clk_out3,
    clk_out4,
    clk_out5,
    clk_out6,
    reset,
    locked,
    clk_in1);
  output clk_out1;
  output clk_out2;
  output clk_out3;
  output clk_out4;
  output clk_out5;
  output clk_out6;
  input reset;
  output locked;
  input clk_in1;

  wire clk_in1;
  wire clk_in1_clk_wiz_0_firesim;
  wire clk_out1;
  wire clk_out1_clk_wiz_0_firesim;
  wire clk_out2;
  wire clk_out2_clk_wiz_0_firesim;
  wire clk_out3;
  wire clk_out3_clk_wiz_0_firesim;
  wire clk_out4;
  wire clk_out4_clk_wiz_0_firesim;
  wire clk_out5;
  wire clk_out5_clk_wiz_0_firesim;
  wire clk_out6;
  wire clk_out6_clk_wiz_0_firesim;
  wire clkfbout_buf_clk_wiz_0_firesim;
  wire clkfbout_clk_wiz_0_firesim;
  wire locked;
  wire reset;
  wire NLW_mmcme4_adv_inst_CDDCDONE_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKFBOUTB_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKFBSTOPPED_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKINSTOPPED_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKOUT0B_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKOUT1B_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKOUT2B_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKOUT3B_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_CLKOUT6_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_DRDY_UNCONNECTED;
  wire NLW_mmcme4_adv_inst_PSDONE_UNCONNECTED;
  wire [15:0]NLW_mmcme4_adv_inst_DO_UNCONNECTED;

  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkf_buf
       (.CE(1'b1),
        .I(clkfbout_clk_wiz_0_firesim),
        .O(clkfbout_buf_clk_wiz_0_firesim));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* CAPACITANCE = "DONT_CARE" *) 
  (* IBUF_DELAY_VALUE = "0" *) 
  (* IFD_DELAY_VALUE = "AUTO" *) 
  IBUF #(
    .IOSTANDARD("DEFAULT")) 
    clkin1_ibuf
       (.I(clk_in1),
        .O(clk_in1_clk_wiz_0_firesim));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout1_buf
       (.CE(1'b1),
        .I(clk_out1_clk_wiz_0_firesim),
        .O(clk_out1));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout2_buf
       (.CE(1'b1),
        .I(clk_out2_clk_wiz_0_firesim),
        .O(clk_out2));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout3_buf
       (.CE(1'b1),
        .I(clk_out3_clk_wiz_0_firesim),
        .O(clk_out3));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout4_buf
       (.CE(1'b1),
        .I(clk_out4_clk_wiz_0_firesim),
        .O(clk_out4));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout5_buf
       (.CE(1'b1),
        .I(clk_out5_clk_wiz_0_firesim),
        .O(clk_out5));
  (* BOX_TYPE = "PRIMITIVE" *) 
  (* XILINX_LEGACY_PRIM = "BUFG" *) 
  (* XILINX_TRANSFORM_PINMAP = "VCC:CE" *) 
  BUFGCE #(
    .CE_TYPE("ASYNC"),
    .SIM_DEVICE("ULTRASCALE_PLUS")) 
    clkout6_buf
       (.CE(1'b1),
        .I(clk_out6_clk_wiz_0_firesim),
        .O(clk_out6));
  (* BOX_TYPE = "PRIMITIVE" *) 
  MMCME4_ADV #(
    .BANDWIDTH("OPTIMIZED"),
    .CLKFBOUT_MULT_F(49.000000),
    .CLKFBOUT_PHASE(0.000000),
    .CLKFBOUT_USE_FINE_PS("FALSE"),
    .CLKIN1_PERIOD(8.000000),
    .CLKIN2_PERIOD(0.000000),
    .CLKOUT0_DIVIDE_F(122.500000),
    .CLKOUT0_DUTY_CYCLE(0.500000),
    .CLKOUT0_PHASE(0.000000),
    .CLKOUT0_USE_FINE_PS("FALSE"),
    .CLKOUT1_DIVIDE(7),
    .CLKOUT1_DUTY_CYCLE(0.500000),
    .CLKOUT1_PHASE(0.000000),
    .CLKOUT1_USE_FINE_PS("FALSE"),
    .CLKOUT2_DIVIDE(8),
    .CLKOUT2_DUTY_CYCLE(0.500000),
    .CLKOUT2_PHASE(0.000000),
    .CLKOUT2_USE_FINE_PS("FALSE"),
    .CLKOUT3_DIVIDE(14),
    .CLKOUT3_DUTY_CYCLE(0.500000),
    .CLKOUT3_PHASE(0.000000),
    .CLKOUT3_USE_FINE_PS("FALSE"),
    .CLKOUT4_CASCADE("FALSE"),
    .CLKOUT4_DIVIDE(14),
    .CLKOUT4_DUTY_CYCLE(0.500000),
    .CLKOUT4_PHASE(0.000000),
    .CLKOUT4_USE_FINE_PS("FALSE"),
    .CLKOUT5_DIVIDE(16),
    .CLKOUT5_DUTY_CYCLE(0.500000),
    .CLKOUT5_PHASE(0.000000),
    .CLKOUT5_USE_FINE_PS("FALSE"),
    .CLKOUT6_DIVIDE(1),
    .CLKOUT6_DUTY_CYCLE(0.500000),
    .CLKOUT6_PHASE(0.000000),
    .CLKOUT6_USE_FINE_PS("FALSE"),
    .COMPENSATION("ZHOLD"),
    .DIVCLK_DIVIDE(5),
    .IS_CLKFBIN_INVERTED(1'b0),
    .IS_CLKIN1_INVERTED(1'b0),
    .IS_CLKIN2_INVERTED(1'b0),
    .IS_CLKINSEL_INVERTED(1'b0),
    .IS_PSEN_INVERTED(1'b0),
    .IS_PSINCDEC_INVERTED(1'b0),
    .IS_PWRDWN_INVERTED(1'b0),
    .IS_RST_INVERTED(1'b0),
    .REF_JITTER1(0.010000),
    .REF_JITTER2(0.010000),
    .SS_EN("FALSE"),
    .SS_MODE("CENTER_HIGH"),
    .SS_MOD_PERIOD(10000),
    .STARTUP_WAIT("FALSE")) 
    mmcme4_adv_inst
       (.CDDCDONE(NLW_mmcme4_adv_inst_CDDCDONE_UNCONNECTED),
        .CDDCREQ(1'b0),
        .CLKFBIN(clkfbout_buf_clk_wiz_0_firesim),
        .CLKFBOUT(clkfbout_clk_wiz_0_firesim),
        .CLKFBOUTB(NLW_mmcme4_adv_inst_CLKFBOUTB_UNCONNECTED),
        .CLKFBSTOPPED(NLW_mmcme4_adv_inst_CLKFBSTOPPED_UNCONNECTED),
        .CLKIN1(clk_in1_clk_wiz_0_firesim),
        .CLKIN2(1'b0),
        .CLKINSEL(1'b1),
        .CLKINSTOPPED(NLW_mmcme4_adv_inst_CLKINSTOPPED_UNCONNECTED),
        .CLKOUT0(clk_out1_clk_wiz_0_firesim),
        .CLKOUT0B(NLW_mmcme4_adv_inst_CLKOUT0B_UNCONNECTED),
        .CLKOUT1(clk_out2_clk_wiz_0_firesim),
        .CLKOUT1B(NLW_mmcme4_adv_inst_CLKOUT1B_UNCONNECTED),
        .CLKOUT2(clk_out3_clk_wiz_0_firesim),
        .CLKOUT2B(NLW_mmcme4_adv_inst_CLKOUT2B_UNCONNECTED),
        .CLKOUT3(clk_out4_clk_wiz_0_firesim),
        .CLKOUT3B(NLW_mmcme4_adv_inst_CLKOUT3B_UNCONNECTED),
        .CLKOUT4(clk_out5_clk_wiz_0_firesim),
        .CLKOUT5(clk_out6_clk_wiz_0_firesim),
        .CLKOUT6(NLW_mmcme4_adv_inst_CLKOUT6_UNCONNECTED),
        .DADDR({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .DCLK(1'b0),
        .DEN(1'b0),
        .DI({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .DO(NLW_mmcme4_adv_inst_DO_UNCONNECTED[15:0]),
        .DRDY(NLW_mmcme4_adv_inst_DRDY_UNCONNECTED),
        .DWE(1'b0),
        .LOCKED(locked),
        .PSCLK(1'b0),
        .PSDONE(NLW_mmcme4_adv_inst_PSDONE_UNCONNECTED),
        .PSEN(1'b0),
        .PSINCDEC(1'b0),
        .PWRDWN(1'b0),
        .RST(reset));
endmodule
`ifndef GLBL
`define GLBL
`timescale  1 ps / 1 ps

module glbl ();

    parameter ROC_WIDTH = 100000;
    parameter TOC_WIDTH = 0;
    parameter GRES_WIDTH = 10000;
    parameter GRES_START = 10000;

//--------   STARTUP Globals --------------
    wire GSR;
    wire GTS;
    wire GWE;
    wire PRLD;
    wire GRESTORE;
    tri1 p_up_tmp;
    tri (weak1, strong0) PLL_LOCKG = p_up_tmp;

    wire PROGB_GLBL;
    wire CCLKO_GLBL;
    wire FCSBO_GLBL;
    wire [3:0] DO_GLBL;
    wire [3:0] DI_GLBL;
   
    reg GSR_int;
    reg GTS_int;
    reg PRLD_int;
    reg GRESTORE_int;

//--------   JTAG Globals --------------
    wire JTAG_TDO_GLBL;
    wire JTAG_TCK_GLBL;
    wire JTAG_TDI_GLBL;
    wire JTAG_TMS_GLBL;
    wire JTAG_TRST_GLBL;

    reg JTAG_CAPTURE_GLBL;
    reg JTAG_RESET_GLBL;
    reg JTAG_SHIFT_GLBL;
    reg JTAG_UPDATE_GLBL;
    reg JTAG_RUNTEST_GLBL;

    reg JTAG_SEL1_GLBL = 0;
    reg JTAG_SEL2_GLBL = 0 ;
    reg JTAG_SEL3_GLBL = 0;
    reg JTAG_SEL4_GLBL = 0;

    reg JTAG_USER_TDO1_GLBL = 1'bz;
    reg JTAG_USER_TDO2_GLBL = 1'bz;
    reg JTAG_USER_TDO3_GLBL = 1'bz;
    reg JTAG_USER_TDO4_GLBL = 1'bz;

    assign (strong1, weak0) GSR = GSR_int;
    assign (strong1, weak0) GTS = GTS_int;
    assign (weak1, weak0) PRLD = PRLD_int;
    assign (strong1, weak0) GRESTORE = GRESTORE_int;

    initial begin
	GSR_int = 1'b1;
	PRLD_int = 1'b1;
	#(ROC_WIDTH)
	GSR_int = 1'b0;
	PRLD_int = 1'b0;
    end

    initial begin
	GTS_int = 1'b1;
	#(TOC_WIDTH)
	GTS_int = 1'b0;
    end

    initial begin 
	GRESTORE_int = 1'b0;
	#(GRES_START);
	GRESTORE_int = 1'b1;
	#(GRES_WIDTH);
	GRESTORE_int = 1'b0;
    end

endmodule
`endif
