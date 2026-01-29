// Copyright 1986-2022 Xilinx, Inc. All Rights Reserved.
// Copyright 2022-2025 Advanced Micro Devices, Inc. All Rights Reserved.
// -------------------------------------------------------------------------------

`timescale 1 ps / 1 ps

(* BLOCK_STUB = "true" *)
module clk_wiz_0_firesim (
  reset,
  clk_in1,
  clk_out1,
  clk_out2,
  clk_out3,
  clk_out4,
  clk_out5,
  clk_out6,
  locked
);

  (* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 reset RST" *)
  (* X_INTERFACE_MODE = "slave reset" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME reset, POLARITY ACTIVE_HIGH, BOARD.ASSOCIATED_PARAM RESET_BOARD_INTERFACE, INSERT_VIP 0" *)
  input reset;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_IN1 CLK_IN1" *)
  (* X_INTERFACE_MODE = "slave clock_CLK_IN1" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_IN1, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0, BOARD.ASSOCIATED_PARAM CLK_IN1_BOARD_INTERFACE" *)
  input clk_in1;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT1 CLK_OUT1" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT1" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT1, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out1;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT2 CLK_OUT2" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT2" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT2, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out2;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT3 CLK_OUT3" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT3" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT3, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out3;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT4 CLK_OUT4" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT4" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT4, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out4;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT5 CLK_OUT5" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT5" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT5, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out5;
  (* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 clock_CLK_OUT6 CLK_OUT6" *)
  (* X_INTERFACE_MODE = "master clock_CLK_OUT6" *)
  (* X_INTERFACE_PARAMETER = "XIL_INTERFACENAME clock_CLK_OUT6, FREQ_HZ 100000000, FREQ_TOLERANCE_HZ 0, PHASE 0.0, CLK_DOMAIN , ASSOCIATED_BUSIF , ASSOCIATED_PORT , ASSOCIATED_RESET , INSERT_VIP 0" *)
  output clk_out6;
  (* X_INTERFACE_IGNORE = "true" *)
  output locked;

  // stub module has no contents

endmodule
