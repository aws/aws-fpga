//------------------------------------------------------------------------------
// Amazon FPGA Hardware Development Kit
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
//------------------------------------------------------------------------------

module sh_ddr
  #(
    parameter DDR_PRESENT = 1,

    // NOTE TO CL DEVELOPERS:
    // The below two parameters should not be changed.
    // Changing these parameters will cause place errors for DDR_A and DDR_D pins.
    // When set to 1, they will ensure that DDR_A/D IO buffers are correctly instanced
    parameter DDR_IO = 1,

    // Following paramters are specific to AXI4 interface. CL developers should NOT change these values. Please use these default values.
    parameter DATA_WIDTH   = 512,
    parameter ADDR_WIDTH   = 64,
    parameter ID_WIDTH     = 16,
    parameter LEN_WIDTH    = 8,
    parameter AXUSER_WIDTH = 1
    )
   (

    //---------------------------
    // Main clock/reset
    //---------------------------
    input                             clk,
    input                             rst_n,

    input                             stat_clk, // Stats interface clock
    input                             stat_rst_n,

    //--------------------------------------------------------
    // DDR Physical Interface- DDR4 x72 RDIMM Interface
    //--------------------------------------------------------
    input logic                       CLK_DIMM_DP,
    input logic                       CLK_DIMM_DN,
    output logic                      M_ACT_N,
    output logic [17:0]               M_MA,
    output logic [1:0]                M_BA,
    output logic [1:0]                M_BG,
    output logic [1:0]                M_CKE,
    output logic [1:0]                M_ODT,
    output logic [1:0]                M_CS_N,
    output logic [1:0]                M_CLK_DN,
    output logic [1:0]                M_CLK_DP,
    output logic                      M_PAR,
    inout        [63:0]               M_DQ,
    inout        [7:0]                M_ECC,
    inout        [17:0]               M_DQS_DP,
    inout        [17:0]               M_DQS_DN,
    output logic                      cl_RST_DIMM_N,

    //------------------------------------------------------
    // DDR-4 Interface from CL (AXI-4)
    //------------------------------------------------------
    input logic [ID_WIDTH-1:0]        cl_sh_ddr_axi_awid,
    input logic [ADDR_WIDTH-1:0]      cl_sh_ddr_axi_awaddr,
    input logic [LEN_WIDTH-1:0]       cl_sh_ddr_axi_awlen,
    input logic [2:0]                 cl_sh_ddr_axi_awsize,
    input logic                       cl_sh_ddr_axi_awvalid,
    input logic [1:0]                 cl_sh_ddr_axi_awburst,
    input logic                       cl_sh_ddr_axi_awuser,
    output logic                      cl_sh_ddr_axi_awready,

    input logic [DATA_WIDTH-1:0]      cl_sh_ddr_axi_wdata,
    input logic [(DATA_WIDTH>>3)-1:0] cl_sh_ddr_axi_wstrb,
    input logic                       cl_sh_ddr_axi_wlast,
    input logic                       cl_sh_ddr_axi_wvalid,
    output logic                      cl_sh_ddr_axi_wready,

    output logic [ID_WIDTH-1:0]       cl_sh_ddr_axi_bid,
    output logic [1:0]                cl_sh_ddr_axi_bresp,
    output logic                      cl_sh_ddr_axi_bvalid,
    input logic                       cl_sh_ddr_axi_bready,

    input logic [ID_WIDTH-1:0]        cl_sh_ddr_axi_arid,
    input logic [ADDR_WIDTH-1:0]      cl_sh_ddr_axi_araddr,
    input logic [LEN_WIDTH-1:0]       cl_sh_ddr_axi_arlen,
    input logic [2:0]                 cl_sh_ddr_axi_arsize,
    input logic                       cl_sh_ddr_axi_arvalid,
    input logic [1:0]                 cl_sh_ddr_axi_arburst,
    input logic                       cl_sh_ddr_axi_aruser,
    output logic                      cl_sh_ddr_axi_arready,

    output logic [ID_WIDTH-1:0]       cl_sh_ddr_axi_rid,
    output logic [DATA_WIDTH-1:0]     cl_sh_ddr_axi_rdata,
    output logic [1:0]                cl_sh_ddr_axi_rresp,
    output logic                      cl_sh_ddr_axi_rlast,
    output logic                      cl_sh_ddr_axi_rvalid,
    input logic                       cl_sh_ddr_axi_rready,

    //--------------------------------------------------------
    // CFG Stats interface from Shell to DDR4
    //--------------------------------------------------------
    input logic [7:0]                 sh_ddr_stat_bus_addr,
    input logic [31:0]                sh_ddr_stat_bus_wdata,
    input logic                       sh_ddr_stat_bus_wr,
    input logic                       sh_ddr_stat_bus_rd,
    output logic                      sh_ddr_stat_bus_ack,
    output logic [31:0]               sh_ddr_stat_bus_rdata,

    output logic [7:0]                ddr_sh_stat_int,
    output logic                      sh_cl_ddr_is_ready
   );

endmodule
