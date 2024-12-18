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



task program_cl_hbm_perf_kernel(logic [31:0] selected_channel_for_latency_measurement = 32'd0, logic [3:0] axlen = 4'hf, logic [31:0] data_pattern = 32'hCAFE_FA15);
   `define KERN_CFG_REG 12'h400
   `define CHANNEL_AVAIL_REG 12'h404
   `define NUM_OT_REG 12'h408
   `define CHNL_SEL_REG 12'h40C
   `define AXLEN_REG 12'h410
   `define WDATA_PATTERN_REG 12'h414

   $display("Programming KERN_CFG_REG to enable MUX");
   tb.poke_ocl(.addr(`KERN_CFG_REG), .data(32'd1));

   $display("Read CHANNEL_AVAIL_REG");
   check_peek_ocl(.addr(`CHANNEL_AVAIL_REG), .data(32'd32));

   $display("Programming CHNL_SEL_REG");
   tb.poke_ocl(.addr(`CHNL_SEL_REG), .data(selected_channel_for_latency_measurement));

   $display("Programming AXLEN_REG");
   tb.poke_ocl(.addr(`AXLEN_REG), .data(32'(axlen)));

   $display("Programming WDATA_PATTERN_REG");
   tb.poke_ocl(.addr(`WDATA_PATTERN_REG), .data(data_pattern));
endtask

task run_cl_hbm_perf_kernel_writes(logic [31:0] selected_channels = 32'hFFFF_FFFF);
   `define WR_CTL_REG 12'h418
   `define WR_OT_REG 12'h444
   logic [31:0]  read_data;
   automatic int count = 0;

   $display("Start Write Transfers in WR_CTL_REG");
   tb.poke_ocl(.addr(`WR_CTL_REG), .data(selected_channels));

   #2000ns;

   $display("Reading WR_OT_REG");
   tb.peek_ocl(.addr(`WR_OT_REG), .data(read_data));
   $display("Reading WR_OT_REG value = 0x%08x", read_data);

   #100ns;

   $display("Stop Write Transfers in WR_CTL_REG");
   tb.poke_ocl(.addr(`WR_CTL_REG), .data(32'd0));

   $display("Waiting for all pending txns to complete. WR_OT_REG to be empty");
   do begin
      count++;
      #100ns;
      tb.peek_ocl(.addr(`WR_OT_REG), .data(read_data));
   end while ((read_data != '0) && (count < 5000));
   if (count >= 5000) begin
     error_count++;
     $error("__ERROR__: timeout waiting for writes to complete. WR_OT_REG != 0.");
   end
endtask

task run_cl_hbm_perf_kernel_reads(logic [31:0] selected_channels = 32'hFFFF_FFFF);
   `define RD_CTL_REG 12'h41C
   `define RD_OT_REG 12'h464
   logic [31:0]  read_data;
   automatic int count = 0;

   $display("Start Read Transfers in RD_CTL_REG");
   tb.poke_ocl(.addr(`RD_CTL_REG), .data(selected_channels));

   #2000ns;

   $display("Reading RD_OT_REG");
   tb.peek_ocl(.addr(`RD_OT_REG), .data(read_data));
   $display("Reading RD_OT_REG value = 0x%08x", read_data);

   #2000ns; // Longer than run_cl_hbm_perf_kernel_writes() since reads take longer (write count will equal read count by design)

   $display("Stop Read Transfers in RD_CTL_REG");
   tb.poke_ocl(.addr(`RD_CTL_REG), .data(32'd0));

   $display("Waiting for all pending txns to complete. RD_OT_REG to be empty");
   do begin
      count++;
      #100ns;
      tb.peek_ocl(.addr(`RD_OT_REG), .data(read_data));
   end while ((read_data != '0) && (count < 5000));
   if (count >= 5000) begin
     error_count++;
     $error("__ERROR__: timeout waiting for reads to complete. RD_OT_REG != 0.");
   end
endtask

task check_for_cl_hbm_perf_kernel_response_errors();
   `define BRESP_ERR_REG 12'h448
   `define RRESP_ERR_REG 12'h468
   logic [31:0] read_data;

   $display("Reading BRESP_ERR_REG");
   tb.peek_ocl(.addr(`BRESP_ERR_REG), .data(read_data));
   $display("BRESP_ERR_REG value = %016d", read_data);
   if (read_data != 32'h0) begin
     error_count++;
     $error("BRESP_ERR_REG is non-zero!");
   end

   $display("Reading RRESP_ERR_REG");
   tb.peek_ocl(.addr(`RRESP_ERR_REG), .data(read_data));
   $display("RRESP_ERR_REG value = %016d", read_data);
   if (read_data != 32'h0) begin
      error_count++;
      $error("RRESP_ERR_REG is non-zero!");
   end
endtask

task print_cl_hbm_perf_kernel_latencies();
   `define WR_LATENCY_REG 12'h440
   `define RD_LATENCY_REG 12'h460
   logic [31:0] read_data;

   $display("Reading WR_LATENCY_REG");
   tb.peek_ocl(.addr(`WR_LATENCY_REG), .data(read_data));
   $display("WR_LATENCY_REG value = 0x%x", read_data);
   if (read_data < 'h10 || read_data > 'h40) begin
      error_count++;
      $error("Write latency of 0x%x is out of 0x10-0x40 range!", read_data);
   end

   $display("Reading RD_LATENCY_REG");
   tb.peek_ocl(.addr(`RD_LATENCY_REG), .data(read_data));
   $display("RD_LATENCY_REG value = 0x%x", read_data);
   if (read_data < 'h10 || read_data > 'h80) begin
      error_count++;
      $error("Read latency of 0x%x is out of 0x10-0x80 range!", read_data);
   end
endtask

task print_cl_hbm_perf_kernel_bandwidth_performance(logic [31:0] selected_channels,logic [3:0] axlen);
   `define WR_CYC_CNT_LO_REG 12'h430
   `define WR_CYC_CNT_HI_REG 12'h434
   `define WR_TIMER_LO_REG 12'h438
   `define WR_TIMER_HI_REG 12'h43C

   `define RD_CYC_CNT_LO_REG 12'h450
   `define RD_CYC_CNT_HI_REG 12'h454
   `define RD_TIMER_LO_REG 12'h458
   `define RD_TIMER_HI_REG 12'h45C

   real wr_bw, expected_wr_bandwidth;
   real rd_bw, expected_rd_bandwidth;
   logic [63:0] wr_cyc_count, wr_timer;
   logic [63:0] rd_cyc_count, rd_timer;

   $display("Reading WR_CYC_CNT");
   tb.peek_ocl(.addr(`WR_CYC_CNT_LO_REG), .data(wr_cyc_count[31:0]));
   tb.peek_ocl(.addr(`WR_CYC_CNT_HI_REG), .data(wr_cyc_count[63:32]));
   $display("WR_CYC_CNT value = 0x%x", wr_cyc_count);

   $display("Reading WR_TIMER");
   tb.peek_ocl(.addr(`WR_TIMER_LO_REG), .data(wr_timer[31:0]));
   tb.peek_ocl(.addr(`WR_TIMER_HI_REG), .data(wr_timer[63:32]));
   $display("WR_TIMER value = %016d", wr_timer);

   $display("Reading RD_CYC_CNT");
   tb.peek_ocl(.addr(`RD_CYC_CNT_LO_REG), .data(rd_cyc_count[31:0]));
   tb.peek_ocl(.addr(`RD_CYC_CNT_HI_REG), .data(rd_cyc_count[63:32]));
   $display("RD_CYC_CNT value = 0x%x", rd_cyc_count);

   $display("Reading RD_TIMER");
   tb.peek_ocl(.addr(`RD_TIMER_LO_REG), .data(rd_timer[31:0]));
   tb.peek_ocl(.addr(`RD_TIMER_HI_REG), .data(rd_timer[63:32]));
   $display("RD_TIMER value = %016d", rd_timer);

   wr_bw = (wr_timer == 0) ? 0 : ((wr_cyc_count * (axlen + 1) * $countones(selected_channels))/(wr_timer * 4.0));
   rd_bw = (rd_timer == 0) ? 0 : ((rd_cyc_count * (axlen + 1) * $countones(selected_channels))/(rd_timer * 4.0));
   $display("=======PERFORMANCE INFO=============");
   $display("Write BW = %-0.2f GB/s", wr_bw);
   $display("Read BW  = %-0.2f GB/s", rd_bw);

   expected_wr_bandwidth = (400.0 * $pow( $countones(selected_channels), 3 ) / $pow( 32.0, 3 ));
   expected_rd_bandwidth = (340.0 * $pow( $countones(selected_channels), 3 ) / $pow( 32.0, 3 ));

   if (wr_bw < expected_wr_bandwidth) begin
      $error("Write Bandwidth of %3.1f is below %3.1f GB/s", wr_bw, expected_wr_bandwidth);
      error_count++;
   end
   if (rd_bw < expected_rd_bandwidth) begin
      $error("Read Bandwidth of %3.1f is below %3.1f GB/s", rd_bw, expected_rd_bandwidth);
      error_count++;
   end
endtask
