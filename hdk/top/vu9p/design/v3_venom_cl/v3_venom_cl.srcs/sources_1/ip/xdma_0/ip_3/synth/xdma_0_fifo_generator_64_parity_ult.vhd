-- (c) Copyright 1995-2016 Xilinx, Inc. All rights reserved.
-- 
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
-- 
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
-- 
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
-- 
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-- 
-- DO NOT MODIFY THIS FILE.

-- IP VLNV: xilinx.com:ip:fifo_generator:13.1
-- IP Revision: 2

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

LIBRARY fifo_generator_v13_1_2;
USE fifo_generator_v13_1_2.fifo_generator_v13_1_2;

ENTITY xdma_0_fifo_generator_64_parity_ult IS
  PORT (
    clk : IN STD_LOGIC;
    srst : IN STD_LOGIC;
    din : IN STD_LOGIC_VECTOR(71 DOWNTO 0);
    wr_en : IN STD_LOGIC;
    rd_en : IN STD_LOGIC;
    dout : OUT STD_LOGIC_VECTOR(71 DOWNTO 0);
    full : OUT STD_LOGIC;
    empty : OUT STD_LOGIC;
    prog_full : OUT STD_LOGIC;
    wr_rst_busy : OUT STD_LOGIC;
    rd_rst_busy : OUT STD_LOGIC
  );
END xdma_0_fifo_generator_64_parity_ult;

ARCHITECTURE xdma_0_fifo_generator_64_parity_ult_arch OF xdma_0_fifo_generator_64_parity_ult IS
  ATTRIBUTE DowngradeIPIdentifiedWarnings : STRING;
  ATTRIBUTE DowngradeIPIdentifiedWarnings OF xdma_0_fifo_generator_64_parity_ult_arch: ARCHITECTURE IS "yes";
  COMPONENT fifo_generator_v13_1_2 IS
    GENERIC (
      C_COMMON_CLOCK : INTEGER;
      C_SELECT_XPM : INTEGER;
      C_COUNT_TYPE : INTEGER;
      C_DATA_COUNT_WIDTH : INTEGER;
      C_DEFAULT_VALUE : STRING;
      C_DIN_WIDTH : INTEGER;
      C_DOUT_RST_VAL : STRING;
      C_DOUT_WIDTH : INTEGER;
      C_ENABLE_RLOCS : INTEGER;
      C_FAMILY : STRING;
      C_FULL_FLAGS_RST_VAL : INTEGER;
      C_HAS_ALMOST_EMPTY : INTEGER;
      C_HAS_ALMOST_FULL : INTEGER;
      C_HAS_BACKUP : INTEGER;
      C_HAS_DATA_COUNT : INTEGER;
      C_HAS_INT_CLK : INTEGER;
      C_HAS_MEMINIT_FILE : INTEGER;
      C_HAS_OVERFLOW : INTEGER;
      C_HAS_RD_DATA_COUNT : INTEGER;
      C_HAS_RD_RST : INTEGER;
      C_HAS_RST : INTEGER;
      C_HAS_SRST : INTEGER;
      C_HAS_UNDERFLOW : INTEGER;
      C_HAS_VALID : INTEGER;
      C_HAS_WR_ACK : INTEGER;
      C_HAS_WR_DATA_COUNT : INTEGER;
      C_HAS_WR_RST : INTEGER;
      C_IMPLEMENTATION_TYPE : INTEGER;
      C_INIT_WR_PNTR_VAL : INTEGER;
      C_MEMORY_TYPE : INTEGER;
      C_MIF_FILE_NAME : STRING;
      C_OPTIMIZATION_MODE : INTEGER;
      C_OVERFLOW_LOW : INTEGER;
      C_PRELOAD_LATENCY : INTEGER;
      C_PRELOAD_REGS : INTEGER;
      C_PRIM_FIFO_TYPE : STRING;
      C_PROG_EMPTY_THRESH_ASSERT_VAL : INTEGER;
      C_PROG_EMPTY_THRESH_NEGATE_VAL : INTEGER;
      C_PROG_EMPTY_TYPE : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL : INTEGER;
      C_PROG_FULL_THRESH_NEGATE_VAL : INTEGER;
      C_PROG_FULL_TYPE : INTEGER;
      C_RD_DATA_COUNT_WIDTH : INTEGER;
      C_RD_DEPTH : INTEGER;
      C_RD_FREQ : INTEGER;
      C_RD_PNTR_WIDTH : INTEGER;
      C_UNDERFLOW_LOW : INTEGER;
      C_USE_DOUT_RST : INTEGER;
      C_USE_ECC : INTEGER;
      C_USE_EMBEDDED_REG : INTEGER;
      C_USE_PIPELINE_REG : INTEGER;
      C_POWER_SAVING_MODE : INTEGER;
      C_USE_FIFO16_FLAGS : INTEGER;
      C_USE_FWFT_DATA_COUNT : INTEGER;
      C_VALID_LOW : INTEGER;
      C_WR_ACK_LOW : INTEGER;
      C_WR_DATA_COUNT_WIDTH : INTEGER;
      C_WR_DEPTH : INTEGER;
      C_WR_FREQ : INTEGER;
      C_WR_PNTR_WIDTH : INTEGER;
      C_WR_RESPONSE_LATENCY : INTEGER;
      C_MSGON_VAL : INTEGER;
      C_ENABLE_RST_SYNC : INTEGER;
      C_EN_SAFETY_CKT : INTEGER;
      C_ERROR_INJECTION_TYPE : INTEGER;
      C_SYNCHRONIZER_STAGE : INTEGER;
      C_INTERFACE_TYPE : INTEGER;
      C_AXI_TYPE : INTEGER;
      C_HAS_AXI_WR_CHANNEL : INTEGER;
      C_HAS_AXI_RD_CHANNEL : INTEGER;
      C_HAS_SLAVE_CE : INTEGER;
      C_HAS_MASTER_CE : INTEGER;
      C_ADD_NGC_CONSTRAINT : INTEGER;
      C_USE_COMMON_OVERFLOW : INTEGER;
      C_USE_COMMON_UNDERFLOW : INTEGER;
      C_USE_DEFAULT_SETTINGS : INTEGER;
      C_AXI_ID_WIDTH : INTEGER;
      C_AXI_ADDR_WIDTH : INTEGER;
      C_AXI_DATA_WIDTH : INTEGER;
      C_AXI_LEN_WIDTH : INTEGER;
      C_AXI_LOCK_WIDTH : INTEGER;
      C_HAS_AXI_ID : INTEGER;
      C_HAS_AXI_AWUSER : INTEGER;
      C_HAS_AXI_WUSER : INTEGER;
      C_HAS_AXI_BUSER : INTEGER;
      C_HAS_AXI_ARUSER : INTEGER;
      C_HAS_AXI_RUSER : INTEGER;
      C_AXI_ARUSER_WIDTH : INTEGER;
      C_AXI_AWUSER_WIDTH : INTEGER;
      C_AXI_WUSER_WIDTH : INTEGER;
      C_AXI_BUSER_WIDTH : INTEGER;
      C_AXI_RUSER_WIDTH : INTEGER;
      C_HAS_AXIS_TDATA : INTEGER;
      C_HAS_AXIS_TID : INTEGER;
      C_HAS_AXIS_TDEST : INTEGER;
      C_HAS_AXIS_TUSER : INTEGER;
      C_HAS_AXIS_TREADY : INTEGER;
      C_HAS_AXIS_TLAST : INTEGER;
      C_HAS_AXIS_TSTRB : INTEGER;
      C_HAS_AXIS_TKEEP : INTEGER;
      C_AXIS_TDATA_WIDTH : INTEGER;
      C_AXIS_TID_WIDTH : INTEGER;
      C_AXIS_TDEST_WIDTH : INTEGER;
      C_AXIS_TUSER_WIDTH : INTEGER;
      C_AXIS_TSTRB_WIDTH : INTEGER;
      C_AXIS_TKEEP_WIDTH : INTEGER;
      C_WACH_TYPE : INTEGER;
      C_WDCH_TYPE : INTEGER;
      C_WRCH_TYPE : INTEGER;
      C_RACH_TYPE : INTEGER;
      C_RDCH_TYPE : INTEGER;
      C_AXIS_TYPE : INTEGER;
      C_IMPLEMENTATION_TYPE_WACH : INTEGER;
      C_IMPLEMENTATION_TYPE_WDCH : INTEGER;
      C_IMPLEMENTATION_TYPE_WRCH : INTEGER;
      C_IMPLEMENTATION_TYPE_RACH : INTEGER;
      C_IMPLEMENTATION_TYPE_RDCH : INTEGER;
      C_IMPLEMENTATION_TYPE_AXIS : INTEGER;
      C_APPLICATION_TYPE_WACH : INTEGER;
      C_APPLICATION_TYPE_WDCH : INTEGER;
      C_APPLICATION_TYPE_WRCH : INTEGER;
      C_APPLICATION_TYPE_RACH : INTEGER;
      C_APPLICATION_TYPE_RDCH : INTEGER;
      C_APPLICATION_TYPE_AXIS : INTEGER;
      C_PRIM_FIFO_TYPE_WACH : STRING;
      C_PRIM_FIFO_TYPE_WDCH : STRING;
      C_PRIM_FIFO_TYPE_WRCH : STRING;
      C_PRIM_FIFO_TYPE_RACH : STRING;
      C_PRIM_FIFO_TYPE_RDCH : STRING;
      C_PRIM_FIFO_TYPE_AXIS : STRING;
      C_USE_ECC_WACH : INTEGER;
      C_USE_ECC_WDCH : INTEGER;
      C_USE_ECC_WRCH : INTEGER;
      C_USE_ECC_RACH : INTEGER;
      C_USE_ECC_RDCH : INTEGER;
      C_USE_ECC_AXIS : INTEGER;
      C_ERROR_INJECTION_TYPE_WACH : INTEGER;
      C_ERROR_INJECTION_TYPE_WDCH : INTEGER;
      C_ERROR_INJECTION_TYPE_WRCH : INTEGER;
      C_ERROR_INJECTION_TYPE_RACH : INTEGER;
      C_ERROR_INJECTION_TYPE_RDCH : INTEGER;
      C_ERROR_INJECTION_TYPE_AXIS : INTEGER;
      C_DIN_WIDTH_WACH : INTEGER;
      C_DIN_WIDTH_WDCH : INTEGER;
      C_DIN_WIDTH_WRCH : INTEGER;
      C_DIN_WIDTH_RACH : INTEGER;
      C_DIN_WIDTH_RDCH : INTEGER;
      C_DIN_WIDTH_AXIS : INTEGER;
      C_WR_DEPTH_WACH : INTEGER;
      C_WR_DEPTH_WDCH : INTEGER;
      C_WR_DEPTH_WRCH : INTEGER;
      C_WR_DEPTH_RACH : INTEGER;
      C_WR_DEPTH_RDCH : INTEGER;
      C_WR_DEPTH_AXIS : INTEGER;
      C_WR_PNTR_WIDTH_WACH : INTEGER;
      C_WR_PNTR_WIDTH_WDCH : INTEGER;
      C_WR_PNTR_WIDTH_WRCH : INTEGER;
      C_WR_PNTR_WIDTH_RACH : INTEGER;
      C_WR_PNTR_WIDTH_RDCH : INTEGER;
      C_WR_PNTR_WIDTH_AXIS : INTEGER;
      C_HAS_DATA_COUNTS_WACH : INTEGER;
      C_HAS_DATA_COUNTS_WDCH : INTEGER;
      C_HAS_DATA_COUNTS_WRCH : INTEGER;
      C_HAS_DATA_COUNTS_RACH : INTEGER;
      C_HAS_DATA_COUNTS_RDCH : INTEGER;
      C_HAS_DATA_COUNTS_AXIS : INTEGER;
      C_HAS_PROG_FLAGS_WACH : INTEGER;
      C_HAS_PROG_FLAGS_WDCH : INTEGER;
      C_HAS_PROG_FLAGS_WRCH : INTEGER;
      C_HAS_PROG_FLAGS_RACH : INTEGER;
      C_HAS_PROG_FLAGS_RDCH : INTEGER;
      C_HAS_PROG_FLAGS_AXIS : INTEGER;
      C_PROG_FULL_TYPE_WACH : INTEGER;
      C_PROG_FULL_TYPE_WDCH : INTEGER;
      C_PROG_FULL_TYPE_WRCH : INTEGER;
      C_PROG_FULL_TYPE_RACH : INTEGER;
      C_PROG_FULL_TYPE_RDCH : INTEGER;
      C_PROG_FULL_TYPE_AXIS : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_WACH : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_WDCH : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_WRCH : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_RACH : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_RDCH : INTEGER;
      C_PROG_FULL_THRESH_ASSERT_VAL_AXIS : INTEGER;
      C_PROG_EMPTY_TYPE_WACH : INTEGER;
      C_PROG_EMPTY_TYPE_WDCH : INTEGER;
      C_PROG_EMPTY_TYPE_WRCH : INTEGER;
      C_PROG_EMPTY_TYPE_RACH : INTEGER;
      C_PROG_EMPTY_TYPE_RDCH : INTEGER;
      C_PROG_EMPTY_TYPE_AXIS : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH : INTEGER;
      C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS : INTEGER;
      C_REG_SLICE_MODE_WACH : INTEGER;
      C_REG_SLICE_MODE_WDCH : INTEGER;
      C_REG_SLICE_MODE_WRCH : INTEGER;
      C_REG_SLICE_MODE_RACH : INTEGER;
      C_REG_SLICE_MODE_RDCH : INTEGER;
      C_REG_SLICE_MODE_AXIS : INTEGER
    );
    PORT (
      backup : IN STD_LOGIC;
      backup_marker : IN STD_LOGIC;
      clk : IN STD_LOGIC;
      rst : IN STD_LOGIC;
      srst : IN STD_LOGIC;
      wr_clk : IN STD_LOGIC;
      wr_rst : IN STD_LOGIC;
      rd_clk : IN STD_LOGIC;
      rd_rst : IN STD_LOGIC;
      din : IN STD_LOGIC_VECTOR(71 DOWNTO 0);
      wr_en : IN STD_LOGIC;
      rd_en : IN STD_LOGIC;
      prog_empty_thresh : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_empty_thresh_assert : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_empty_thresh_negate : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_full_thresh : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_full_thresh_assert : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_full_thresh_negate : IN STD_LOGIC_VECTOR(8 DOWNTO 0);
      int_clk : IN STD_LOGIC;
      injectdbiterr : IN STD_LOGIC;
      injectsbiterr : IN STD_LOGIC;
      sleep : IN STD_LOGIC;
      dout : OUT STD_LOGIC_VECTOR(71 DOWNTO 0);
      full : OUT STD_LOGIC;
      almost_full : OUT STD_LOGIC;
      wr_ack : OUT STD_LOGIC;
      overflow : OUT STD_LOGIC;
      empty : OUT STD_LOGIC;
      almost_empty : OUT STD_LOGIC;
      valid : OUT STD_LOGIC;
      underflow : OUT STD_LOGIC;
      data_count : OUT STD_LOGIC_VECTOR(8 DOWNTO 0);
      rd_data_count : OUT STD_LOGIC_VECTOR(8 DOWNTO 0);
      wr_data_count : OUT STD_LOGIC_VECTOR(8 DOWNTO 0);
      prog_full : OUT STD_LOGIC;
      prog_empty : OUT STD_LOGIC;
      sbiterr : OUT STD_LOGIC;
      dbiterr : OUT STD_LOGIC;
      wr_rst_busy : OUT STD_LOGIC;
      rd_rst_busy : OUT STD_LOGIC;
      m_aclk : IN STD_LOGIC;
      s_aclk : IN STD_LOGIC;
      s_aresetn : IN STD_LOGIC;
      m_aclk_en : IN STD_LOGIC;
      s_aclk_en : IN STD_LOGIC;
      s_axi_awid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_awaddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      s_axi_awlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
      s_axi_awsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
      s_axi_awburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_awlock : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_awcache : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_awprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
      s_axi_awqos : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_awregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_awuser : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_awvalid : IN STD_LOGIC;
      s_axi_awready : OUT STD_LOGIC;
      s_axi_wid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_wdata : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
      s_axi_wstrb : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
      s_axi_wlast : IN STD_LOGIC;
      s_axi_wuser : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_wvalid : IN STD_LOGIC;
      s_axi_wready : OUT STD_LOGIC;
      s_axi_bid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_bresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_buser : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_bvalid : OUT STD_LOGIC;
      s_axi_bready : IN STD_LOGIC;
      m_axi_awid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_awaddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      m_axi_awlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
      m_axi_awsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
      m_axi_awburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      m_axi_awlock : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_awcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_awprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
      m_axi_awqos : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_awregion : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_awuser : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_awvalid : OUT STD_LOGIC;
      m_axi_awready : IN STD_LOGIC;
      m_axi_wid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_wdata : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
      m_axi_wstrb : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
      m_axi_wlast : OUT STD_LOGIC;
      m_axi_wuser : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_wvalid : OUT STD_LOGIC;
      m_axi_wready : IN STD_LOGIC;
      m_axi_bid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_bresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
      m_axi_buser : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_bvalid : IN STD_LOGIC;
      m_axi_bready : OUT STD_LOGIC;
      s_axi_arid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_araddr : IN STD_LOGIC_VECTOR(31 DOWNTO 0);
      s_axi_arlen : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
      s_axi_arsize : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
      s_axi_arburst : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_arlock : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_arcache : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_arprot : IN STD_LOGIC_VECTOR(2 DOWNTO 0);
      s_axi_arqos : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_arregion : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      s_axi_aruser : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_arvalid : IN STD_LOGIC;
      s_axi_arready : OUT STD_LOGIC;
      s_axi_rid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_rdata : OUT STD_LOGIC_VECTOR(63 DOWNTO 0);
      s_axi_rresp : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      s_axi_rlast : OUT STD_LOGIC;
      s_axi_ruser : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axi_rvalid : OUT STD_LOGIC;
      s_axi_rready : IN STD_LOGIC;
      m_axi_arid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_araddr : OUT STD_LOGIC_VECTOR(31 DOWNTO 0);
      m_axi_arlen : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
      m_axi_arsize : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
      m_axi_arburst : OUT STD_LOGIC_VECTOR(1 DOWNTO 0);
      m_axi_arlock : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_arcache : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_arprot : OUT STD_LOGIC_VECTOR(2 DOWNTO 0);
      m_axi_arqos : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_arregion : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axi_aruser : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_arvalid : OUT STD_LOGIC;
      m_axi_arready : IN STD_LOGIC;
      m_axi_rid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_rdata : IN STD_LOGIC_VECTOR(63 DOWNTO 0);
      m_axi_rresp : IN STD_LOGIC_VECTOR(1 DOWNTO 0);
      m_axi_rlast : IN STD_LOGIC;
      m_axi_ruser : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axi_rvalid : IN STD_LOGIC;
      m_axi_rready : OUT STD_LOGIC;
      s_axis_tvalid : IN STD_LOGIC;
      s_axis_tready : OUT STD_LOGIC;
      s_axis_tdata : IN STD_LOGIC_VECTOR(7 DOWNTO 0);
      s_axis_tstrb : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axis_tkeep : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axis_tlast : IN STD_LOGIC;
      s_axis_tid : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axis_tdest : IN STD_LOGIC_VECTOR(0 DOWNTO 0);
      s_axis_tuser : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      m_axis_tvalid : OUT STD_LOGIC;
      m_axis_tready : IN STD_LOGIC;
      m_axis_tdata : OUT STD_LOGIC_VECTOR(7 DOWNTO 0);
      m_axis_tstrb : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axis_tkeep : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axis_tlast : OUT STD_LOGIC;
      m_axis_tid : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axis_tdest : OUT STD_LOGIC_VECTOR(0 DOWNTO 0);
      m_axis_tuser : OUT STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_aw_injectsbiterr : IN STD_LOGIC;
      axi_aw_injectdbiterr : IN STD_LOGIC;
      axi_aw_prog_full_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_aw_prog_empty_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_aw_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_aw_wr_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_aw_rd_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_aw_sbiterr : OUT STD_LOGIC;
      axi_aw_dbiterr : OUT STD_LOGIC;
      axi_aw_overflow : OUT STD_LOGIC;
      axi_aw_underflow : OUT STD_LOGIC;
      axi_aw_prog_full : OUT STD_LOGIC;
      axi_aw_prog_empty : OUT STD_LOGIC;
      axi_w_injectsbiterr : IN STD_LOGIC;
      axi_w_injectdbiterr : IN STD_LOGIC;
      axi_w_prog_full_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axi_w_prog_empty_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axi_w_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_w_wr_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_w_rd_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_w_sbiterr : OUT STD_LOGIC;
      axi_w_dbiterr : OUT STD_LOGIC;
      axi_w_overflow : OUT STD_LOGIC;
      axi_w_underflow : OUT STD_LOGIC;
      axi_w_prog_full : OUT STD_LOGIC;
      axi_w_prog_empty : OUT STD_LOGIC;
      axi_b_injectsbiterr : IN STD_LOGIC;
      axi_b_injectdbiterr : IN STD_LOGIC;
      axi_b_prog_full_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_b_prog_empty_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_b_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_b_wr_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_b_rd_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_b_sbiterr : OUT STD_LOGIC;
      axi_b_dbiterr : OUT STD_LOGIC;
      axi_b_overflow : OUT STD_LOGIC;
      axi_b_underflow : OUT STD_LOGIC;
      axi_b_prog_full : OUT STD_LOGIC;
      axi_b_prog_empty : OUT STD_LOGIC;
      axi_ar_injectsbiterr : IN STD_LOGIC;
      axi_ar_injectdbiterr : IN STD_LOGIC;
      axi_ar_prog_full_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_ar_prog_empty_thresh : IN STD_LOGIC_VECTOR(3 DOWNTO 0);
      axi_ar_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_ar_wr_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_ar_rd_data_count : OUT STD_LOGIC_VECTOR(4 DOWNTO 0);
      axi_ar_sbiterr : OUT STD_LOGIC;
      axi_ar_dbiterr : OUT STD_LOGIC;
      axi_ar_overflow : OUT STD_LOGIC;
      axi_ar_underflow : OUT STD_LOGIC;
      axi_ar_prog_full : OUT STD_LOGIC;
      axi_ar_prog_empty : OUT STD_LOGIC;
      axi_r_injectsbiterr : IN STD_LOGIC;
      axi_r_injectdbiterr : IN STD_LOGIC;
      axi_r_prog_full_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axi_r_prog_empty_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axi_r_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_r_wr_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_r_rd_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axi_r_sbiterr : OUT STD_LOGIC;
      axi_r_dbiterr : OUT STD_LOGIC;
      axi_r_overflow : OUT STD_LOGIC;
      axi_r_underflow : OUT STD_LOGIC;
      axi_r_prog_full : OUT STD_LOGIC;
      axi_r_prog_empty : OUT STD_LOGIC;
      axis_injectsbiterr : IN STD_LOGIC;
      axis_injectdbiterr : IN STD_LOGIC;
      axis_prog_full_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axis_prog_empty_thresh : IN STD_LOGIC_VECTOR(9 DOWNTO 0);
      axis_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axis_wr_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axis_rd_data_count : OUT STD_LOGIC_VECTOR(10 DOWNTO 0);
      axis_sbiterr : OUT STD_LOGIC;
      axis_dbiterr : OUT STD_LOGIC;
      axis_overflow : OUT STD_LOGIC;
      axis_underflow : OUT STD_LOGIC;
      axis_prog_full : OUT STD_LOGIC;
      axis_prog_empty : OUT STD_LOGIC
    );
  END COMPONENT fifo_generator_v13_1_2;
  ATTRIBUTE X_CORE_INFO : STRING;
  ATTRIBUTE X_CORE_INFO OF xdma_0_fifo_generator_64_parity_ult_arch: ARCHITECTURE IS "fifo_generator_v13_1_2,Vivado 2016.3_AR68069";
  ATTRIBUTE CHECK_LICENSE_TYPE : STRING;
  ATTRIBUTE CHECK_LICENSE_TYPE OF xdma_0_fifo_generator_64_parity_ult_arch : ARCHITECTURE IS "xdma_0_fifo_generator_64_parity_ult,fifo_generator_v13_1_2,{}";
  ATTRIBUTE CORE_GENERATION_INFO : STRING;
  ATTRIBUTE CORE_GENERATION_INFO OF xdma_0_fifo_generator_64_parity_ult_arch: ARCHITECTURE IS "xdma_0_fifo_generator_64_parity_ult,fifo_generator_v13_1_2,{x_ipProduct=Vivado 2016.3_AR68069,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=fifo_generator,x_ipVersion=13.1,x_ipCoreRevision=2,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,C_COMMON_CLOCK=1,C_SELECT_XPM=0,C_COUNT_TYPE=0,C_DATA_COUNT_WIDTH=9,C_DEFAULT_VALUE=BlankString,C_DIN_WIDTH=72,C_DOUT_RST_VAL=0,C_DOUT_WIDTH=72,C_ENABLE_RLOCS=0,C_FAMILY=virtexuplus,C_FULL_FLAGS_RST_VAL=0,C_HAS_ALMOST_EMPTY=0,C_HAS_ALMOST_FULL=0,C_HAS_BACKUP=0,C_HAS" & 
"_DATA_COUNT=0,C_HAS_INT_CLK=0,C_HAS_MEMINIT_FILE=0,C_HAS_OVERFLOW=0,C_HAS_RD_DATA_COUNT=0,C_HAS_RD_RST=0,C_HAS_RST=0,C_HAS_SRST=1,C_HAS_UNDERFLOW=0,C_HAS_VALID=0,C_HAS_WR_ACK=0,C_HAS_WR_DATA_COUNT=0,C_HAS_WR_RST=0,C_IMPLEMENTATION_TYPE=6,C_INIT_WR_PNTR_VAL=0,C_MEMORY_TYPE=4,C_MIF_FILE_NAME=BlankString,C_OPTIMIZATION_MODE=0,C_OVERFLOW_LOW=0,C_PRELOAD_LATENCY=0,C_PRELOAD_REGS=1,C_PRIM_FIFO_TYPE=512x72,C_PROG_EMPTY_THRESH_ASSERT_VAL=4,C_PROG_EMPTY_THRESH_NEGATE_VAL=5,C_PROG_EMPTY_TYPE=0,C_PROG_FULL" & 
"_THRESH_ASSERT_VAL=511,C_PROG_FULL_THRESH_NEGATE_VAL=510,C_PROG_FULL_TYPE=1,C_RD_DATA_COUNT_WIDTH=9,C_RD_DEPTH=512,C_RD_FREQ=1,C_RD_PNTR_WIDTH=9,C_UNDERFLOW_LOW=0,C_USE_DOUT_RST=1,C_USE_ECC=0,C_USE_EMBEDDED_REG=1,C_USE_PIPELINE_REG=0,C_POWER_SAVING_MODE=0,C_USE_FIFO16_FLAGS=0,C_USE_FWFT_DATA_COUNT=0,C_VALID_LOW=0,C_WR_ACK_LOW=0,C_WR_DATA_COUNT_WIDTH=9,C_WR_DEPTH=512,C_WR_FREQ=1,C_WR_PNTR_WIDTH=9,C_WR_RESPONSE_LATENCY=1,C_MSGON_VAL=1,C_ENABLE_RST_SYNC=1,C_EN_SAFETY_CKT=0,C_ERROR_INJECTION_TYPE=0," & 
"C_SYNCHRONIZER_STAGE=2,C_INTERFACE_TYPE=0,C_AXI_TYPE=1,C_HAS_AXI_WR_CHANNEL=1,C_HAS_AXI_RD_CHANNEL=1,C_HAS_SLAVE_CE=0,C_HAS_MASTER_CE=0,C_ADD_NGC_CONSTRAINT=0,C_USE_COMMON_OVERFLOW=0,C_USE_COMMON_UNDERFLOW=0,C_USE_DEFAULT_SETTINGS=0,C_AXI_ID_WIDTH=1,C_AXI_ADDR_WIDTH=32,C_AXI_DATA_WIDTH=64,C_AXI_LEN_WIDTH=8,C_AXI_LOCK_WIDTH=1,C_HAS_AXI_ID=0,C_HAS_AXI_AWUSER=0,C_HAS_AXI_WUSER=0,C_HAS_AXI_BUSER=0,C_HAS_AXI_ARUSER=0,C_HAS_AXI_RUSER=0,C_AXI_ARUSER_WIDTH=1,C_AXI_AWUSER_WIDTH=1,C_AXI_WUSER_WIDTH=1,C_AX" & 
"I_BUSER_WIDTH=1,C_AXI_RUSER_WIDTH=1,C_HAS_AXIS_TDATA=1,C_HAS_AXIS_TID=0,C_HAS_AXIS_TDEST=0,C_HAS_AXIS_TUSER=1,C_HAS_AXIS_TREADY=1,C_HAS_AXIS_TLAST=0,C_HAS_AXIS_TSTRB=0,C_HAS_AXIS_TKEEP=0,C_AXIS_TDATA_WIDTH=8,C_AXIS_TID_WIDTH=1,C_AXIS_TDEST_WIDTH=1,C_AXIS_TUSER_WIDTH=4,C_AXIS_TSTRB_WIDTH=1,C_AXIS_TKEEP_WIDTH=1,C_WACH_TYPE=0,C_WDCH_TYPE=0,C_WRCH_TYPE=0,C_RACH_TYPE=0,C_RDCH_TYPE=0,C_AXIS_TYPE=0,C_IMPLEMENTATION_TYPE_WACH=1,C_IMPLEMENTATION_TYPE_WDCH=1,C_IMPLEMENTATION_TYPE_WRCH=1,C_IMPLEMENTATION_T" & 
"YPE_RACH=1,C_IMPLEMENTATION_TYPE_RDCH=1,C_IMPLEMENTATION_TYPE_AXIS=1,C_APPLICATION_TYPE_WACH=0,C_APPLICATION_TYPE_WDCH=0,C_APPLICATION_TYPE_WRCH=0,C_APPLICATION_TYPE_RACH=0,C_APPLICATION_TYPE_RDCH=0,C_APPLICATION_TYPE_AXIS=0,C_PRIM_FIFO_TYPE_WACH=512x36,C_PRIM_FIFO_TYPE_WDCH=512x72,C_PRIM_FIFO_TYPE_WRCH=512x36,C_PRIM_FIFO_TYPE_RACH=512x36,C_PRIM_FIFO_TYPE_RDCH=512x72,C_PRIM_FIFO_TYPE_AXIS=1kx18,C_USE_ECC_WACH=0,C_USE_ECC_WDCH=0,C_USE_ECC_WRCH=0,C_USE_ECC_RACH=0,C_USE_ECC_RDCH=0,C_USE_ECC_AXIS=0," & 
"C_ERROR_INJECTION_TYPE_WACH=0,C_ERROR_INJECTION_TYPE_WDCH=0,C_ERROR_INJECTION_TYPE_WRCH=0,C_ERROR_INJECTION_TYPE_RACH=0,C_ERROR_INJECTION_TYPE_RDCH=0,C_ERROR_INJECTION_TYPE_AXIS=0,C_DIN_WIDTH_WACH=1,C_DIN_WIDTH_WDCH=64,C_DIN_WIDTH_WRCH=2,C_DIN_WIDTH_RACH=32,C_DIN_WIDTH_RDCH=64,C_DIN_WIDTH_AXIS=1,C_WR_DEPTH_WACH=16,C_WR_DEPTH_WDCH=1024,C_WR_DEPTH_WRCH=16,C_WR_DEPTH_RACH=16,C_WR_DEPTH_RDCH=1024,C_WR_DEPTH_AXIS=1024,C_WR_PNTR_WIDTH_WACH=4,C_WR_PNTR_WIDTH_WDCH=10,C_WR_PNTR_WIDTH_WRCH=4,C_WR_PNTR_WID" & 
"TH_RACH=4,C_WR_PNTR_WIDTH_RDCH=10,C_WR_PNTR_WIDTH_AXIS=10,C_HAS_DATA_COUNTS_WACH=0,C_HAS_DATA_COUNTS_WDCH=0,C_HAS_DATA_COUNTS_WRCH=0,C_HAS_DATA_COUNTS_RACH=0,C_HAS_DATA_COUNTS_RDCH=0,C_HAS_DATA_COUNTS_AXIS=0,C_HAS_PROG_FLAGS_WACH=0,C_HAS_PROG_FLAGS_WDCH=0,C_HAS_PROG_FLAGS_WRCH=0,C_HAS_PROG_FLAGS_RACH=0,C_HAS_PROG_FLAGS_RDCH=0,C_HAS_PROG_FLAGS_AXIS=0,C_PROG_FULL_TYPE_WACH=0,C_PROG_FULL_TYPE_WDCH=0,C_PROG_FULL_TYPE_WRCH=0,C_PROG_FULL_TYPE_RACH=0,C_PROG_FULL_TYPE_RDCH=0,C_PROG_FULL_TYPE_AXIS=0,C_PR" & 
"OG_FULL_THRESH_ASSERT_VAL_WACH=1023,C_PROG_FULL_THRESH_ASSERT_VAL_WDCH=1023,C_PROG_FULL_THRESH_ASSERT_VAL_WRCH=1023,C_PROG_FULL_THRESH_ASSERT_VAL_RACH=1023,C_PROG_FULL_THRESH_ASSERT_VAL_RDCH=1023,C_PROG_FULL_THRESH_ASSERT_VAL_AXIS=1023,C_PROG_EMPTY_TYPE_WACH=0,C_PROG_EMPTY_TYPE_WDCH=0,C_PROG_EMPTY_TYPE_WRCH=0,C_PROG_EMPTY_TYPE_RACH=0,C_PROG_EMPTY_TYPE_RDCH=0,C_PROG_EMPTY_TYPE_AXIS=0,C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH=1022,C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH=1022,C_PROG_EMPTY_THRESH_ASSERT_VAL_W" & 
"RCH=1022,C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH=1022,C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH=1022,C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS=1022,C_REG_SLICE_MODE_WACH=0,C_REG_SLICE_MODE_WDCH=0,C_REG_SLICE_MODE_WRCH=0,C_REG_SLICE_MODE_RACH=0,C_REG_SLICE_MODE_RDCH=0,C_REG_SLICE_MODE_AXIS=0}";
  ATTRIBUTE X_INTERFACE_INFO : STRING;
  ATTRIBUTE X_INTERFACE_INFO OF clk: SIGNAL IS "xilinx.com:signal:clock:1.0 core_clk CLK";
  ATTRIBUTE X_INTERFACE_INFO OF din: SIGNAL IS "xilinx.com:interface:fifo_write:1.0 FIFO_WRITE WR_DATA";
  ATTRIBUTE X_INTERFACE_INFO OF wr_en: SIGNAL IS "xilinx.com:interface:fifo_write:1.0 FIFO_WRITE WR_EN";
  ATTRIBUTE X_INTERFACE_INFO OF rd_en: SIGNAL IS "xilinx.com:interface:fifo_read:1.0 FIFO_READ RD_EN";
  ATTRIBUTE X_INTERFACE_INFO OF dout: SIGNAL IS "xilinx.com:interface:fifo_read:1.0 FIFO_READ RD_DATA";
  ATTRIBUTE X_INTERFACE_INFO OF full: SIGNAL IS "xilinx.com:interface:fifo_write:1.0 FIFO_WRITE FULL";
  ATTRIBUTE X_INTERFACE_INFO OF empty: SIGNAL IS "xilinx.com:interface:fifo_read:1.0 FIFO_READ EMPTY";
BEGIN
  U0 : fifo_generator_v13_1_2
    GENERIC MAP (
      C_COMMON_CLOCK => 1,
      C_SELECT_XPM => 0,
      C_COUNT_TYPE => 0,
      C_DATA_COUNT_WIDTH => 9,
      C_DEFAULT_VALUE => "BlankString",
      C_DIN_WIDTH => 72,
      C_DOUT_RST_VAL => "0",
      C_DOUT_WIDTH => 72,
      C_ENABLE_RLOCS => 0,
      C_FAMILY => "virtexuplus",
      C_FULL_FLAGS_RST_VAL => 0,
      C_HAS_ALMOST_EMPTY => 0,
      C_HAS_ALMOST_FULL => 0,
      C_HAS_BACKUP => 0,
      C_HAS_DATA_COUNT => 0,
      C_HAS_INT_CLK => 0,
      C_HAS_MEMINIT_FILE => 0,
      C_HAS_OVERFLOW => 0,
      C_HAS_RD_DATA_COUNT => 0,
      C_HAS_RD_RST => 0,
      C_HAS_RST => 0,
      C_HAS_SRST => 1,
      C_HAS_UNDERFLOW => 0,
      C_HAS_VALID => 0,
      C_HAS_WR_ACK => 0,
      C_HAS_WR_DATA_COUNT => 0,
      C_HAS_WR_RST => 0,
      C_IMPLEMENTATION_TYPE => 6,
      C_INIT_WR_PNTR_VAL => 0,
      C_MEMORY_TYPE => 4,
      C_MIF_FILE_NAME => "BlankString",
      C_OPTIMIZATION_MODE => 0,
      C_OVERFLOW_LOW => 0,
      C_PRELOAD_LATENCY => 0,
      C_PRELOAD_REGS => 1,
      C_PRIM_FIFO_TYPE => "512x72",
      C_PROG_EMPTY_THRESH_ASSERT_VAL => 4,
      C_PROG_EMPTY_THRESH_NEGATE_VAL => 5,
      C_PROG_EMPTY_TYPE => 0,
      C_PROG_FULL_THRESH_ASSERT_VAL => 511,
      C_PROG_FULL_THRESH_NEGATE_VAL => 510,
      C_PROG_FULL_TYPE => 1,
      C_RD_DATA_COUNT_WIDTH => 9,
      C_RD_DEPTH => 512,
      C_RD_FREQ => 1,
      C_RD_PNTR_WIDTH => 9,
      C_UNDERFLOW_LOW => 0,
      C_USE_DOUT_RST => 1,
      C_USE_ECC => 0,
      C_USE_EMBEDDED_REG => 1,
      C_USE_PIPELINE_REG => 0,
      C_POWER_SAVING_MODE => 0,
      C_USE_FIFO16_FLAGS => 0,
      C_USE_FWFT_DATA_COUNT => 0,
      C_VALID_LOW => 0,
      C_WR_ACK_LOW => 0,
      C_WR_DATA_COUNT_WIDTH => 9,
      C_WR_DEPTH => 512,
      C_WR_FREQ => 1,
      C_WR_PNTR_WIDTH => 9,
      C_WR_RESPONSE_LATENCY => 1,
      C_MSGON_VAL => 1,
      C_ENABLE_RST_SYNC => 1,
      C_EN_SAFETY_CKT => 0,
      C_ERROR_INJECTION_TYPE => 0,
      C_SYNCHRONIZER_STAGE => 2,
      C_INTERFACE_TYPE => 0,
      C_AXI_TYPE => 1,
      C_HAS_AXI_WR_CHANNEL => 1,
      C_HAS_AXI_RD_CHANNEL => 1,
      C_HAS_SLAVE_CE => 0,
      C_HAS_MASTER_CE => 0,
      C_ADD_NGC_CONSTRAINT => 0,
      C_USE_COMMON_OVERFLOW => 0,
      C_USE_COMMON_UNDERFLOW => 0,
      C_USE_DEFAULT_SETTINGS => 0,
      C_AXI_ID_WIDTH => 1,
      C_AXI_ADDR_WIDTH => 32,
      C_AXI_DATA_WIDTH => 64,
      C_AXI_LEN_WIDTH => 8,
      C_AXI_LOCK_WIDTH => 1,
      C_HAS_AXI_ID => 0,
      C_HAS_AXI_AWUSER => 0,
      C_HAS_AXI_WUSER => 0,
      C_HAS_AXI_BUSER => 0,
      C_HAS_AXI_ARUSER => 0,
      C_HAS_AXI_RUSER => 0,
      C_AXI_ARUSER_WIDTH => 1,
      C_AXI_AWUSER_WIDTH => 1,
      C_AXI_WUSER_WIDTH => 1,
      C_AXI_BUSER_WIDTH => 1,
      C_AXI_RUSER_WIDTH => 1,
      C_HAS_AXIS_TDATA => 1,
      C_HAS_AXIS_TID => 0,
      C_HAS_AXIS_TDEST => 0,
      C_HAS_AXIS_TUSER => 1,
      C_HAS_AXIS_TREADY => 1,
      C_HAS_AXIS_TLAST => 0,
      C_HAS_AXIS_TSTRB => 0,
      C_HAS_AXIS_TKEEP => 0,
      C_AXIS_TDATA_WIDTH => 8,
      C_AXIS_TID_WIDTH => 1,
      C_AXIS_TDEST_WIDTH => 1,
      C_AXIS_TUSER_WIDTH => 4,
      C_AXIS_TSTRB_WIDTH => 1,
      C_AXIS_TKEEP_WIDTH => 1,
      C_WACH_TYPE => 0,
      C_WDCH_TYPE => 0,
      C_WRCH_TYPE => 0,
      C_RACH_TYPE => 0,
      C_RDCH_TYPE => 0,
      C_AXIS_TYPE => 0,
      C_IMPLEMENTATION_TYPE_WACH => 1,
      C_IMPLEMENTATION_TYPE_WDCH => 1,
      C_IMPLEMENTATION_TYPE_WRCH => 1,
      C_IMPLEMENTATION_TYPE_RACH => 1,
      C_IMPLEMENTATION_TYPE_RDCH => 1,
      C_IMPLEMENTATION_TYPE_AXIS => 1,
      C_APPLICATION_TYPE_WACH => 0,
      C_APPLICATION_TYPE_WDCH => 0,
      C_APPLICATION_TYPE_WRCH => 0,
      C_APPLICATION_TYPE_RACH => 0,
      C_APPLICATION_TYPE_RDCH => 0,
      C_APPLICATION_TYPE_AXIS => 0,
      C_PRIM_FIFO_TYPE_WACH => "512x36",
      C_PRIM_FIFO_TYPE_WDCH => "512x72",
      C_PRIM_FIFO_TYPE_WRCH => "512x36",
      C_PRIM_FIFO_TYPE_RACH => "512x36",
      C_PRIM_FIFO_TYPE_RDCH => "512x72",
      C_PRIM_FIFO_TYPE_AXIS => "1kx18",
      C_USE_ECC_WACH => 0,
      C_USE_ECC_WDCH => 0,
      C_USE_ECC_WRCH => 0,
      C_USE_ECC_RACH => 0,
      C_USE_ECC_RDCH => 0,
      C_USE_ECC_AXIS => 0,
      C_ERROR_INJECTION_TYPE_WACH => 0,
      C_ERROR_INJECTION_TYPE_WDCH => 0,
      C_ERROR_INJECTION_TYPE_WRCH => 0,
      C_ERROR_INJECTION_TYPE_RACH => 0,
      C_ERROR_INJECTION_TYPE_RDCH => 0,
      C_ERROR_INJECTION_TYPE_AXIS => 0,
      C_DIN_WIDTH_WACH => 1,
      C_DIN_WIDTH_WDCH => 64,
      C_DIN_WIDTH_WRCH => 2,
      C_DIN_WIDTH_RACH => 32,
      C_DIN_WIDTH_RDCH => 64,
      C_DIN_WIDTH_AXIS => 1,
      C_WR_DEPTH_WACH => 16,
      C_WR_DEPTH_WDCH => 1024,
      C_WR_DEPTH_WRCH => 16,
      C_WR_DEPTH_RACH => 16,
      C_WR_DEPTH_RDCH => 1024,
      C_WR_DEPTH_AXIS => 1024,
      C_WR_PNTR_WIDTH_WACH => 4,
      C_WR_PNTR_WIDTH_WDCH => 10,
      C_WR_PNTR_WIDTH_WRCH => 4,
      C_WR_PNTR_WIDTH_RACH => 4,
      C_WR_PNTR_WIDTH_RDCH => 10,
      C_WR_PNTR_WIDTH_AXIS => 10,
      C_HAS_DATA_COUNTS_WACH => 0,
      C_HAS_DATA_COUNTS_WDCH => 0,
      C_HAS_DATA_COUNTS_WRCH => 0,
      C_HAS_DATA_COUNTS_RACH => 0,
      C_HAS_DATA_COUNTS_RDCH => 0,
      C_HAS_DATA_COUNTS_AXIS => 0,
      C_HAS_PROG_FLAGS_WACH => 0,
      C_HAS_PROG_FLAGS_WDCH => 0,
      C_HAS_PROG_FLAGS_WRCH => 0,
      C_HAS_PROG_FLAGS_RACH => 0,
      C_HAS_PROG_FLAGS_RDCH => 0,
      C_HAS_PROG_FLAGS_AXIS => 0,
      C_PROG_FULL_TYPE_WACH => 0,
      C_PROG_FULL_TYPE_WDCH => 0,
      C_PROG_FULL_TYPE_WRCH => 0,
      C_PROG_FULL_TYPE_RACH => 0,
      C_PROG_FULL_TYPE_RDCH => 0,
      C_PROG_FULL_TYPE_AXIS => 0,
      C_PROG_FULL_THRESH_ASSERT_VAL_WACH => 1023,
      C_PROG_FULL_THRESH_ASSERT_VAL_WDCH => 1023,
      C_PROG_FULL_THRESH_ASSERT_VAL_WRCH => 1023,
      C_PROG_FULL_THRESH_ASSERT_VAL_RACH => 1023,
      C_PROG_FULL_THRESH_ASSERT_VAL_RDCH => 1023,
      C_PROG_FULL_THRESH_ASSERT_VAL_AXIS => 1023,
      C_PROG_EMPTY_TYPE_WACH => 0,
      C_PROG_EMPTY_TYPE_WDCH => 0,
      C_PROG_EMPTY_TYPE_WRCH => 0,
      C_PROG_EMPTY_TYPE_RACH => 0,
      C_PROG_EMPTY_TYPE_RDCH => 0,
      C_PROG_EMPTY_TYPE_AXIS => 0,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WACH => 1022,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WDCH => 1022,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_WRCH => 1022,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_RACH => 1022,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_RDCH => 1022,
      C_PROG_EMPTY_THRESH_ASSERT_VAL_AXIS => 1022,
      C_REG_SLICE_MODE_WACH => 0,
      C_REG_SLICE_MODE_WDCH => 0,
      C_REG_SLICE_MODE_WRCH => 0,
      C_REG_SLICE_MODE_RACH => 0,
      C_REG_SLICE_MODE_RDCH => 0,
      C_REG_SLICE_MODE_AXIS => 0
    )
    PORT MAP (
      backup => '0',
      backup_marker => '0',
      clk => clk,
      rst => '0',
      srst => srst,
      wr_clk => '0',
      wr_rst => '0',
      rd_clk => '0',
      rd_rst => '0',
      din => din,
      wr_en => wr_en,
      rd_en => rd_en,
      prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      prog_empty_thresh_assert => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      prog_empty_thresh_negate => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      prog_full_thresh_assert => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      prog_full_thresh_negate => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 9)),
      int_clk => '0',
      injectdbiterr => '0',
      injectsbiterr => '0',
      sleep => '0',
      dout => dout,
      full => full,
      empty => empty,
      prog_full => prog_full,
      wr_rst_busy => wr_rst_busy,
      rd_rst_busy => rd_rst_busy,
      m_aclk => '0',
      s_aclk => '0',
      s_aresetn => '0',
      m_aclk_en => '0',
      s_aclk_en => '0',
      s_axi_awid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_awaddr => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      s_axi_awlen => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 8)),
      s_axi_awsize => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 3)),
      s_axi_awburst => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 2)),
      s_axi_awlock => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_awcache => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_awprot => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 3)),
      s_axi_awqos => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_awregion => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_awuser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_awvalid => '0',
      s_axi_wid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_wdata => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 64)),
      s_axi_wstrb => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 8)),
      s_axi_wlast => '0',
      s_axi_wuser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_wvalid => '0',
      s_axi_bready => '0',
      m_axi_awready => '0',
      m_axi_wready => '0',
      m_axi_bid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      m_axi_bresp => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 2)),
      m_axi_buser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      m_axi_bvalid => '0',
      s_axi_arid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_araddr => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 32)),
      s_axi_arlen => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 8)),
      s_axi_arsize => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 3)),
      s_axi_arburst => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 2)),
      s_axi_arlock => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_arcache => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_arprot => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 3)),
      s_axi_arqos => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_arregion => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      s_axi_aruser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axi_arvalid => '0',
      s_axi_rready => '0',
      m_axi_arready => '0',
      m_axi_rid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      m_axi_rdata => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 64)),
      m_axi_rresp => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 2)),
      m_axi_rlast => '0',
      m_axi_ruser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      m_axi_rvalid => '0',
      s_axis_tvalid => '0',
      s_axis_tdata => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 8)),
      s_axis_tstrb => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axis_tkeep => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axis_tlast => '0',
      s_axis_tid => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axis_tdest => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 1)),
      s_axis_tuser => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      m_axis_tready => '0',
      axi_aw_injectsbiterr => '0',
      axi_aw_injectdbiterr => '0',
      axi_aw_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_aw_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_w_injectsbiterr => '0',
      axi_w_injectdbiterr => '0',
      axi_w_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10)),
      axi_w_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10)),
      axi_b_injectsbiterr => '0',
      axi_b_injectdbiterr => '0',
      axi_b_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_b_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_ar_injectsbiterr => '0',
      axi_ar_injectdbiterr => '0',
      axi_ar_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_ar_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 4)),
      axi_r_injectsbiterr => '0',
      axi_r_injectdbiterr => '0',
      axi_r_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10)),
      axi_r_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10)),
      axis_injectsbiterr => '0',
      axis_injectdbiterr => '0',
      axis_prog_full_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10)),
      axis_prog_empty_thresh => STD_LOGIC_VECTOR(TO_UNSIGNED(0, 10))
    );
END xdma_0_fifo_generator_64_parity_ult_arch;
