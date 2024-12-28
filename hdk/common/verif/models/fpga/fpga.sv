// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// ============================================================================


module fpga(
   //
   // Auto-generated file that defines all of the external ports of FPGA
   //
   `include "fpga_ports.vh"
);
   //
   // Auto-generated file that defines all of the internal signals that
   // connects directly between SH and CL
   //
   `include "fpga_signals.vh"
   //
   // SHELL BFM instantiation
   //
   sh_bfm sh(.*);
   //
   // Developer's CL Design instantiation
   // User shall change the CL type by using the CL_NAME define during
   // compile time
   //
`ifndef CL_NAME
   `define CL_NAME cl_dram_hbm_dma
`endif//CL_NAME
   `CL_NAME CL(.*);

`ifdef C2C_LOOPBACK

  assign PCIE_RP_REF_CLK_P = clk_hbm_ref;
  assign PCIE_RP_REF_CLK_N = ~clk_hbm_ref;
  assign PCIE_EP_REF_CLK_P = clk_hbm_ref;
  assign PCIE_EP_REF_CLK_N = ~clk_hbm_ref;

  assign PCIE_EP_PERSTN = PCIE_RP_PERSTN;

  assign CL.rp_common_commands_in = CL.ep_common_commands_out;
  assign CL.rp_pipe_rx_0_sigs     = CL.ep_pipe_tx_0_sigs;
  assign CL.rp_pipe_rx_1_sigs     = CL.ep_pipe_tx_1_sigs;
  assign CL.rp_pipe_rx_2_sigs     = CL.ep_pipe_tx_2_sigs;
  assign CL.rp_pipe_rx_3_sigs     = CL.ep_pipe_tx_3_sigs;
  assign CL.rp_pipe_rx_4_sigs     = CL.ep_pipe_tx_4_sigs;
  assign CL.rp_pipe_rx_5_sigs     = CL.ep_pipe_tx_5_sigs;
  assign CL.rp_pipe_rx_6_sigs     = CL.ep_pipe_tx_6_sigs;
  assign CL.rp_pipe_rx_7_sigs     = CL.ep_pipe_tx_7_sigs;
  assign CL.rp_pipe_rx_8_sigs     = CL.ep_pipe_tx_8_sigs;
  assign CL.rp_pipe_rx_9_sigs     = CL.ep_pipe_tx_9_sigs;
  assign CL.rp_pipe_rx_10_sigs    = CL.ep_pipe_tx_10_sigs;
  assign CL.rp_pipe_rx_11_sigs    = CL.ep_pipe_tx_11_sigs;
  assign CL.rp_pipe_rx_12_sigs    = CL.ep_pipe_tx_12_sigs;
  assign CL.rp_pipe_rx_13_sigs    = CL.ep_pipe_tx_13_sigs;
  assign CL.rp_pipe_rx_14_sigs    = CL.ep_pipe_tx_14_sigs;
  assign CL.rp_pipe_rx_15_sigs    = CL.ep_pipe_tx_15_sigs;
  assign CL.ep_common_commands_in = CL.rp_common_commands_out;
  assign CL.ep_pipe_rx_0_sigs     = CL.rp_pipe_tx_0_sigs;
  assign CL.ep_pipe_rx_1_sigs     = CL.rp_pipe_tx_1_sigs;
  assign CL.ep_pipe_rx_2_sigs     = CL.rp_pipe_tx_2_sigs;
  assign CL.ep_pipe_rx_3_sigs     = CL.rp_pipe_tx_3_sigs;
  assign CL.ep_pipe_rx_4_sigs     = CL.rp_pipe_tx_4_sigs;
  assign CL.ep_pipe_rx_5_sigs     = CL.rp_pipe_tx_5_sigs;
  assign CL.ep_pipe_rx_6_sigs     = CL.rp_pipe_tx_6_sigs;
  assign CL.ep_pipe_rx_7_sigs     = CL.rp_pipe_tx_7_sigs;
  assign CL.ep_pipe_rx_8_sigs     = CL.rp_pipe_tx_8_sigs;
  assign CL.ep_pipe_rx_9_sigs     = CL.rp_pipe_tx_9_sigs;
  assign CL.ep_pipe_rx_10_sigs    = CL.rp_pipe_tx_10_sigs;
  assign CL.ep_pipe_rx_11_sigs    = CL.rp_pipe_tx_11_sigs;
  assign CL.ep_pipe_rx_12_sigs    = CL.rp_pipe_tx_12_sigs;
  assign CL.ep_pipe_rx_13_sigs    = CL.rp_pipe_tx_13_sigs;
  assign CL.ep_pipe_rx_14_sigs    = CL.rp_pipe_tx_14_sigs;
  assign CL.ep_pipe_rx_15_sigs    = CL.rp_pipe_tx_15_sigs;

`endif // `ifdef C2C_LOOPBACK

endmodule : fpga
