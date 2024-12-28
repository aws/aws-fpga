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


module test_dram_dma_axi_mstr();

   import tb_type_defines_pkg::*;

   `include "base_test_utils.svh";

    // AXI Master Command Register Addresses
    localparam AXI_MSTR_CCR_ADDR   = 32'h0000_0500;
    localparam AXI_MSTR_CAHR_ADDR  = 32'h0000_0504;
    localparam AXI_MSTR_CALR_ADDR  = 32'h0000_0508;
    localparam AXI_MSTR_CWDR_ADDR  = 32'h0000_050C;

    localparam DDR_BASE_HI_ADDR = 32'h0000_0001;
    localparam DDR_BASE_LO_ADDR = 32'hA021_F700;
    localparam DDR_BASE_DATA    = 32'hA5A6_0000;

    localparam DDR_OFFSET_8_GB_HI_ADDR = 32'h0000_0002;
    localparam DDR_OFFSET_8_GB_LO_ADDR = 32'h529C_8400;
    localparam DDR_OFFSET_8_GB_DATA    = 32'h1B80_C948;

    localparam DDR_OFFSET_16_GB_HI_ADDR = 32'h0000_0004;
    localparam DDR_OFFSET_16_GB_LO_ADDR = 32'h2078_BC00;
    localparam DDR_OFFSET_16_GB_DATA    = 32'h8BD1_8801;

    localparam DDR_OFFSET_24_GB_HI_ADDR = 32'h0000_0006;
    localparam DDR_OFFSET_24_GB_LO_ADDR = 32'hD016_7700;
    localparam DDR_OFFSET_24_GB_DATA    = 32'hCA02_183D;


    initial begin

       logic [63:0] host_memory_buffer_address;


       tb.power_up(.clk_recipe_a(ClockRecipe::A1),
                  .clk_recipe_b(ClockRecipe::B0),
                  .clk_recipe_c(ClockRecipe::C0));
       initialize_ddr();
       deselect_cl_tst_hw();

       tb.issue_flr();

       $display("[%t] : starting H2C DMA channels ", $realtime);

       $display("[%t] : ******* DDR Base Address *******", $realtime);
       for (int i = 0; i <= 12; i=i+4) begin //{
         // Set AXI Master Command Registers
         // addr = 0x1_a021f700, Write
         $display("[%t] : Setting DDR Base Address Command Registers ", $realtime);// addr = 0x1_a021f700
         tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_BASE_HI_ADDR));  // Set High Address --
         tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_BASE_LO_ADDR + i));  // Set Low  Address
         tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_BASE_DATA | i));     // Set Write Data
         tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR),  .data(32'h0000_0001)); // Issue Write Command

         // Wait for write command to complete
         $display("[%t] : Waiting for DDR Base Address write command to complete.  ", $realtime);
         do begin
            #10ns;
         end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
         $display("[%t] : DDR Base Address write command completed.  ", $realtime);
           $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                          $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                     (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                     (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                     (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
         #40ns;
	end // for (int i = 0; i <= 12; i=i+4) //}

for (int i = 0; i <= 12; i=i+4) begin //{
        tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_BASE_HI_ADDR));  // Set High Address --
        tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_BASE_LO_ADDR + i));  // Set Low  Address
        tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_BASE_DATA | i));     // Set Write Data

       // Issue read transaction
       $display("[%t] : Issuing DDR Base Address read command.  ", $realtime);
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR), .data(32'h0000_0005)); // Issue Read Command

       // Wait for read command to complete
       $display("[%t] : Waiting for DDR Base Address read command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Base Address read command completed.  ", $realtime);

	 #40ns;
        $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );

       $display("[%t] : Comparing DDR Base Address write and read data.  ", $realtime);
       $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
       if (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0] !== tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0]) begin
         $error("[%t] : *** ERROR *** Data mismatch, addr:0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0] );
         error_count++;
       end
end //}


       $display("[%t] : ******* DDR Offset 8 GB *******", $realtime);
for (int i = 0; i <= 12; i=i+4) begin //{
       // Set AXI Master Command Registers
       // addr = 0x1_a021f700, Write
       $display("[%t] : Setting DDR Offset 8 GB Command Registers ", $realtime);// addr = 0x1_a021f700
       tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_8_GB_HI_ADDR));  // Set High Address
       tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_8_GB_LO_ADDR + i));  // Set Low  Address
       tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_8_GB_DATA | i));     // Set Write Data
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR),  .data(32'h0000_0001)); // Issue Write Command

       // Wait for write command to complete
       $display("[%t] : Waiting for DDR Offset 8 GB write command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 8 GB write command completed.  ", $realtime);
	 $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
   #40ns;
end // for (int i = 0; i <= 12; i=i+4) //}

for (int i = 0; i <= 12; i=i+4) begin //{
        tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_8_GB_HI_ADDR));  // Set High Address
        tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_8_GB_LO_ADDR + i));  // Set Low  Address
        tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_8_GB_DATA | i));     // Set Write Data

       // Issue read transaction
       $display("[%t] : Issuing DDR Offset 8 GB read command.  ", $realtime);
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR), .data(32'h0000_0005)); // Issue Read Command

       // Wait for read command to complete
       $display("[%t] : Waiting for DDR Offset 8 GB read command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 8 GB read command completed.  ", $realtime);

	 #40ns;
        $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );

       $display("[%t] : Comparing DDR Offset 8 GB write and read data.  ", $realtime);
       $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
       if (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0] !== tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0]) begin
         $error("[%t] : *** ERROR *** Data mismatch, addr:0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0] );
         error_count++;
       end
end //}


       $display("[%t] : ******* DDR Offset 16 GB *******", $realtime);
for (int i = 0; i <= 12; i=i+4) begin //{
       // Set AXI Master Command Registers
       // addr = 0x1_a021f700, Write
       $display("[%t] : Setting DDR Base Address Command Registers ", $realtime);// addr = 0x1_a021f700
       tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_16_GB_HI_ADDR));  // Set High Address --
       tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_16_GB_LO_ADDR + i));  // Set Low  Address
       tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_16_GB_DATA | i));     // Set Write Data
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR),  .data(32'h0000_0001)); // Issue Write Command

       // Wait for write command to complete
       $display("[%t] : Waiting for DDR Offset 16 GB write command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 16 GB write command completed.  ", $realtime);
	 $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
   #40ns;
end // for (int i = 0; i <= 12; i=i+4) //}

for (int i = 0; i <= 12; i=i+4) begin //{
        tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_16_GB_HI_ADDR));  // Set High Address --
        tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_16_GB_LO_ADDR + i));  // Set Low  Address
        tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_16_GB_DATA | i));     // Set Write Data

       // Issue read transaction
       $display("[%t] : Issuing DDR Offset 16 GB read command.  ", $realtime);
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR), .data(32'h0000_0005)); // Issue Read Command

       // Wait for read command to complete
       $display("[%t] : Waiting for DDR Offset 16 GB read command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 16 GB read command completed.  ", $realtime);

	 #40ns;
        $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );

       $display("[%t] : Comparing DDR Offset 16 GB write and read data.  ", $realtime);
       $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
       if (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0] !== tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0]) begin
         $error("[%t] : *** ERROR *** Data mismatch, addr:0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0] );
         error_count++;
       end
end //}



       $display("[%t] : ******* DDR Offset 24 GB *******", $realtime);
for (int i = 0; i <= 12; i=i+4) begin //{
       // Set AXI Master Command Registers
       // addr = 0x1_a021f700, Write
       $display("[%t] : Setting DDR Base Address Command Registers ", $realtime);// addr = 0x1_a021f700
       tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_24_GB_HI_ADDR));  // Set High Address --
       tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_24_GB_LO_ADDR + i));  // Set Low  Address
       tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_24_GB_DATA | i));     // Set Write Data
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR),  .data(32'h0000_0001)); // Issue Write Command

       // Wait for write command to complete
       $display("[%t] : Waiting for DDR Offset 24 GB write command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 24 GB write command completed.  ", $realtime);
	 $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
   #40ns;
end // for (int i = 0; i <= 12; i=i+4) //}

for (int i = 0; i <= 12; i=i+4) begin //{
        tb.poke_ocl(.addr(AXI_MSTR_CAHR_ADDR), .data(DDR_OFFSET_24_GB_HI_ADDR));  // Set High Address --
        tb.poke_ocl(.addr(AXI_MSTR_CALR_ADDR), .data(DDR_OFFSET_24_GB_LO_ADDR + i));  // Set Low  Address
        tb.poke_ocl(.addr(AXI_MSTR_CWDR_ADDR), .data(DDR_OFFSET_24_GB_DATA | i));     // Set Write Data

       // Issue read transaction
       $display("[%t] : Issuing DDR Offset 24 GB read command.  ", $realtime);
       tb.poke_ocl(.addr(AXI_MSTR_CCR_ADDR), .data(32'h0000_0005)); // Issue Read Command

       // Wait for read command to complete
       $display("[%t] : Waiting for DDR Offset 24 GB read command to complete.  ", $realtime);
       do begin
          #10ns;
       end while (!tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_done_q);
       $display("[%t] : DDR Offset 24 GB read command completed.  ", $realtime);

	 #40ns;
        $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );

       $display("[%t] : Comparing DDR Offset 24 GB write and read data.  ", $realtime);
       $display("[%t] : addr: 0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q),
                                   (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q) );
       if (tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0] !== tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0]) begin
         $error("[%t] : *** ERROR *** Data mismatch, addr:0x%0h_%0h write data is: 0x%h read data is: 0x%h",
                        $realtime, tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_hi_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_addr_lo_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_wr_data_q[31:0],
                                   tb.card.fpga.CL.CL_DRAM_HBM_DMA_AXI_MSTR.cmd_rd_data_q[31:0] );
         error_count++;
       end
end //}

       #500ns;
       tb.power_down();

       report_pass_fail_status();

       $finish;
    end // initial begin
endmodule // test_dram_dma_axi_mstr
