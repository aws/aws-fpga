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


// Only the DDR pins are connected. The AXI and stats interfaces are tied-off.

//-------------------------------------------------
// Tie-off AXI interfaces to sh_ddr module
//-------------------------------------------------
logic         tie_zero      = '0;
logic [ 15:0] tie_zero_id   = '0;
logic [ 63:0] tie_zero_addr = '0;
logic [  7:0] tie_zero_len  = '0;
logic [511:0] tie_zero_data = '0;
logic [ 63:0] tie_zero_strb = '0;

sh_ddr
  #(
    .DDR_PRESENT (0)
    )
SH_DDR
  (
   .clk                       (clk_main_a0                  ),
   .rst_n                     (rst_main_n_sync              ),
   .stat_clk                  (clk_main_a0                  ),
   .stat_rst_n                (rst_main_n_sync              ),
   .CLK_DIMM_DP               (CLK_DIMM_DP                  ),
   .CLK_DIMM_DN               (CLK_DIMM_DN                  ),
   .M_ACT_N                   (M_ACT_N                      ),
   .M_MA                      (M_MA                         ),
   .M_BA                      (M_BA                         ),
   .M_BG                      (M_BG                         ),
   .M_CKE                     (M_CKE                        ),
   .M_ODT                     (M_ODT                        ),
   .M_CS_N                    (M_CS_N                       ),
   .M_CLK_DN                  (M_CLK_DN                     ),
   .M_CLK_DP                  (M_CLK_DP                     ),
   .M_PAR                     (M_PAR                        ),
   .M_DQ                      (M_DQ                         ),
   .M_ECC                     (M_ECC                        ),
   .M_DQS_DP                  (M_DQS_DP                     ),
   .M_DQS_DN                  (M_DQS_DN                     ),
   .cl_RST_DIMM_N             (RST_DIMM_N                   ),
   .cl_sh_ddr_axi_awid        (tie_zero_id                  ),
   .cl_sh_ddr_axi_awaddr      (tie_zero_addr                ),
   .cl_sh_ddr_axi_awlen       (tie_zero_len                 ),
   .cl_sh_ddr_axi_awsize      (3'd6                         ),
   .cl_sh_ddr_axi_awvalid     (tie_zero                     ),
   .cl_sh_ddr_axi_awburst     (2'b01                        ),
   .cl_sh_ddr_axi_awready     (                             ),
   .cl_sh_ddr_axi_wdata       (tie_zero_data                ),
   .cl_sh_ddr_axi_wstrb       (tie_zero_strb                ),
   .cl_sh_ddr_axi_wlast       (tie_zero                     ),
   .cl_sh_ddr_axi_wvalid      (tie_zero                     ),
   .cl_sh_ddr_axi_wready      (                             ),
   .cl_sh_ddr_axi_bid         (                             ),
   .cl_sh_ddr_axi_bresp       (                             ),
   .cl_sh_ddr_axi_bvalid      (                             ),
   .cl_sh_ddr_axi_bready      (tie_zero                     ),
   .cl_sh_ddr_axi_arid        (tie_zero_id                  ),
   .cl_sh_ddr_axi_araddr      (tie_zero_addr                ),
   .cl_sh_ddr_axi_arlen       (tie_zero_len                 ),
   .cl_sh_ddr_axi_arsize      (3'd6                         ),
   .cl_sh_ddr_axi_arvalid     (tie_zero                     ),
   .cl_sh_ddr_axi_arburst     (2'b01                        ),
   .cl_sh_ddr_axi_arready     (                             ),
   .cl_sh_ddr_axi_rid         (                             ),
   .cl_sh_ddr_axi_rdata       (                             ),
   .cl_sh_ddr_axi_rresp       (                             ),
   .cl_sh_ddr_axi_rlast       (                             ),
   .cl_sh_ddr_axi_rvalid      (                             ),
   .cl_sh_ddr_axi_rready      (tie_zero                     ),
   .sh_ddr_stat_bus_addr      (8'd0                         ),
   .sh_ddr_stat_bus_wdata     (32'd0                        ),
   .sh_ddr_stat_bus_wr        (1'd0                         ),
   .sh_ddr_stat_bus_rd        (1'd0                         ),
   .sh_ddr_stat_bus_ack       (                             ),
   .sh_ddr_stat_bus_rdata     (                             ),
   .ddr_sh_stat_int           (                             ),
   .sh_cl_ddr_is_ready        (                             )
   );

// sh_ddr stats bus tie off to cl_ports.vh
// Needed in order not to hang the interface
always_comb begin
   cl_sh_ddr_stat_ack   = 1'd1;
   cl_sh_ddr_stat_rdata = '0;
   cl_sh_ddr_stat_int   = '0;
end
