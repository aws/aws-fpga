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


///////////////////////////////////////////////////////////////////////////////////////
// CL_KERNEL_CTL
// --------------
// - Kernel Controller
// - Provide CFG interface to Kernel registers
// - Issue Write/Read Requests to the target memory channels.
// - Supports multiple outstanding transcations on multiple channels.
// - Implement Aggregate Performance Counters
//
///////////////////////////////////////////////////////////////////////////////////////

module cl_kernel_ctl
  #(
    parameter NUM_OT            = 64, // Number of Outstanding Transaactions
    parameter NUM_CHANNELS      = 32
    )
   (
    input  logic                      clk_main_a0,
    input  logic                      rst_main_a0,
    input  logic                      clk_hbm,
    input  logic                      rst_hbm_n,
    output logic [NUM_CHANNELS-1:0]   o_wr_pulse,                       // clk_hbm domain
    output logic [NUM_CHANNELS-1:0]   o_rd_pulse,                       // clk_hbm domain
    output logic [7:0]                o_cfg_axlen,                      // clk_hbm domain
    output logic [31:0]               o_cfg_wdata_pattern,              // clk_hbm domian
    //
    // input done pulse from clk_hbm domain
    //
    input  logic [NUM_CHANNELS-1:0]   i_wr_done_pulse,                  // in clk_hbm domain
    input  logic [NUM_CHANNELS-1:0]   i_rd_done_pulse,                  // in clk_hbm domain
    input  logic [NUM_CHANNELS-1:0]   i_bresp_err_pulse,                // in clk_hbm domain
    input  logic [NUM_CHANNELS-1:0]   i_rresp_err_pulse,                // in clk_hbm domain
    //
    // CFG Interface
    //
    input  logic [31:0]               i_cfg_addr,
    input  logic [31:0]               i_cfg_wdata,
    input  logic                      i_cfg_wr,
    input  logic                      i_cfg_rd,
    output logic [31:0]               o_cfg_rdata,
    output logic                      o_cfg_ack,
    output logic                      o_kernel_enable
    );

   //===================================================================
   // local signals
   //===================================================================
   logic [31:0]                       wr_start_req;
   logic [31:0]                       main_bresp_err;
   logic [31:0]                       wr_pend_txns [0:NUM_CHANNELS-1];
   logic [31:0]                       wr_req_done;
   logic [31:0]                       rd_start_req;
   logic [31:0]                       main_rresp_err;
   logic [31:0]                       rd_pend_txns [0:NUM_CHANNELS-1];
   logic [31:0]                       rd_req_done;
   logic [31:0]                       cfg_axlen;
   logic [31:0]                       cfg_wdata_pattern;
   logic                              cfg_kernel_enable;

   //=====================================================================
   // Instantiate WR/RD Request Queues per channel
   //=====================================================================
   generate //{
      for (genvar jj = 0; jj < NUM_CHANNELS; jj++) begin : WR_RD_QUEUE_I //{
         //
         // WR Requests to HBM
         //
         cl_kernel_req #(.NUM_OT(NUM_OT)) CL_WR_REQ_Q_I
                       (
                        .clk_main_a0       (clk_main_a0            ),
                        .rst_main_a0       (rst_main_a0            ),
                        .clk_hbm           (clk_hbm                ),
                        .rst_hbm_n         (rst_hbm_n              ),
                        .i_main_start_req  (wr_start_req[jj]       ),
                        .o_main_pend_txns  (wr_pend_txns[jj][31:0] ),
                        .o_main_req_done   (wr_req_done[jj]        ),
                        .o_main_resp_err   (main_bresp_err[jj]     ),
                        .o_hbm_req_pulse   (o_wr_pulse[jj]         ),
                        .i_hbm_done_pulse  (i_wr_done_pulse[jj]    ),
                        .i_hbm_resp_err    (i_bresp_err_pulse[jj]  )
                        );

         //
         // RD Requests to HBM
         //
         cl_kernel_req #(.NUM_OT(NUM_OT)) CL_RD_REQ_Q_I
                       (
                        .clk_main_a0       (clk_main_a0            ),
                        .rst_main_a0       (rst_main_a0            ),
                        .clk_hbm           (clk_hbm                ),
                        .rst_hbm_n         (rst_hbm_n              ),
                        .i_main_start_req  (rd_start_req[jj]       ),
                        .o_main_pend_txns  (rd_pend_txns[jj][31:0] ),
                        .o_main_req_done   (rd_req_done[jj]        ),
                        .o_main_resp_err   (main_rresp_err[jj]     ),
                        .o_hbm_req_pulse   (o_rd_pulse[jj]         ),
                        .i_hbm_done_pulse  (i_rd_done_pulse[jj]    ),
                        .i_hbm_resp_err    (i_rresp_err_pulse[jj]  )
                        );
      end : WR_RD_QUEUE_I//}
   endgenerate //}

   //=====================================================================
   // Instantiate Registers
   //=====================================================================
   cl_kernel_regs
     #(
       .NUM_CHANNELS  (NUM_CHANNELS  )
       )
   CL_KERNEL_REGS_I
     (
      .clk_main_a0         (clk_main_a0       ),
      .rst_main_a0         (rst_main_a0       ),
      .i_num_ot            (NUM_OT            ),
      .i_cfg_addr          (i_cfg_addr        ),
      .i_cfg_wdata         (i_cfg_wdata       ),
      .i_cfg_wr            (i_cfg_wr          ),
      .i_cfg_rd            (i_cfg_rd          ),
      .o_cfg_rdata         (o_cfg_rdata       ),
      .o_cfg_ack           (o_cfg_ack         ),
      .o_wr_start          (wr_start_req      ),
      .o_rd_start          (rd_start_req      ),
      .o_cfg_axlen         (cfg_axlen         ),
      .o_cfg_wdata_pattern (cfg_wdata_pattern ),
      .i_wr_done           (wr_req_done       ),
      .i_rd_done           (rd_req_done       ),
      .i_bresp_err         (main_bresp_err    ),
      .i_rresp_err         (main_rresp_err    ),
      .i_wr_pend_txns      (wr_pend_txns      ),
      .i_rd_pend_txns      (rd_pend_txns      ),
      .o_kernel_enable     (cfg_kernel_enable )
      );

   //
   // CDC for axi length
   // (OK to have CDC without handshake since these bits are configured well before data transfers)
   //
   // **NOTE**: Please update hpr/constraints/timing/cl_dram_hbm_dma_timing.xdc also if changing PIPE_STAGES to a different value.
   localparam                             PIPE_STAGES = 4;
   logic [$bits(o_cfg_axlen)-1:0]         sync_cfg_axlen;
   logic [$bits(o_cfg_wdata_pattern)-1:0] sync_wdata_pattern;
   logic                                  sync_kernel_enable;

   xpm_cdc_array_single
     #(
       .DEST_SYNC_FF      (2                 ),
       .INIT_SYNC_FF      (0                 ),
       .SIM_ASSERT_CHK    (0                 ),
       .SRC_INPUT_REG     (0                 ),
       .WIDTH             ($bits(o_cfg_axlen))
       )
   CDC_XPM_AXLEN
     (
      .src_clk            (clk_main_a0    ),
      .src_in             (cfg_axlen      ),
      .dest_clk           (clk_hbm        ),
      .dest_out           (sync_cfg_axlen )
      );

   lib_pipe #(.WIDTH($bits(o_cfg_axlen)), .STAGES(PIPE_STAGES)) PIPE_AXLEN_HBM (.clk(clk_hbm), .rst_n(1'b1), .in_bus(sync_cfg_axlen), .out_bus(o_cfg_axlen));

   //
   // CDC for wdata pattern
   // (OK to have CDC without handshake since these bits are configured well before data transfers)
   //
   xpm_cdc_array_single
     #(
       .DEST_SYNC_FF      (2                 ),
       .INIT_SYNC_FF      (0                 ),
       .SIM_ASSERT_CHK    (0                 ),
       .SRC_INPUT_REG     (0                 ),
       .WIDTH             ($bits(o_cfg_wdata_pattern))
       )
   CDC_XPM_WDATA
     (
      .src_clk            (clk_main_a0         ),
      .src_in             (cfg_wdata_pattern   ),
      .dest_clk           (clk_hbm             ),
      .dest_out           (sync_wdata_pattern  )
      );

   lib_pipe #(.WIDTH($bits(o_cfg_wdata_pattern)), .STAGES(PIPE_STAGES)) PIPE_WDATA_PAT_HBM (.clk(clk_hbm), .rst_n(1'b1), .in_bus(sync_wdata_pattern), .out_bus(o_cfg_wdata_pattern));

   //
   // CDC for o_kernel_enable
   // (OK to have CDC without handshake since these bits are configured well before data transfers)
   //
   xpm_cdc_single
      #(
        .DEST_SYNC_FF      (2                 ),
        .INIT_SYNC_FF      (0                 ),
        .SIM_ASSERT_CHK    (0                 ),
        .SRC_INPUT_REG     (0                 )
        )
   CDC_XPM_KERNL_EN
      (
       .src_clk            (clk_main_a0        ),
       .src_in             (cfg_kernel_enable  ),
       .dest_clk           (clk_hbm            ),
       .dest_out           (sync_kernel_enable )
       );

   lib_pipe #(.WIDTH($bits(o_kernel_enable)), .STAGES(PIPE_STAGES)) PIPE_KERN_EN_HBM (.clk(clk_hbm), .rst_n(1'b1), .in_bus(sync_kernel_enable), .out_bus(o_kernel_enable));

endmodule // cl_kernel_ctl
