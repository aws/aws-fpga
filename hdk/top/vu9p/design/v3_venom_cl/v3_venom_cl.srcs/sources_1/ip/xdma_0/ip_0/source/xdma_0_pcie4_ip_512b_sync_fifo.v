//-----------------------------------------------------------------------------
//
// (c) Copyright 2012-2012 Xilinx, Inc. All rights reserved.
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
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express v4.0 Integrated Block
// File       : xdma_0_pcie4_ip_512b_sync_fifo.v
// Version    : 1.1 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module xdma_0_pcie4_ip_512b_sync_fifo #
  (
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter AXISTEN_IF_EXT_512_INTFC_RAM_STYLE = "SRL",
   parameter FIFO_WIDTH = 512,
   parameter FIFO_DEPTH = 8,
   parameter FIFO_ALMOST_FULL_THRESHOLD = 5
   ) 
  (
    input  wire           clk_i // clock
   ,input  wire           reset_n_i // Reset
   ,input  wire           link_down_reset_i // Reset FIFO on link down

   ,input wire [FIFO_WIDTH-1:0] write_data_i
   ,input wire write_en_i
   ,input wire read_en_i
   ,output wire [FIFO_WIDTH-1:0] read_data_o
   ,output wire read_data_valid_o
   ,output reg fifo_almost_full
   );
   
   reg [2:0] write_ptr;
   reg [2:0] read_ptr;
   reg [3:0] fifo_occupancy;
   wire      fifo_empty;
   wire      fifo_full;

  integer    i;

   reg [FIFO_WIDTH-1:0] ram_array[FIFO_DEPTH-1:0];
   
  // SRL 16 should be inferred when RAM_STYLE = "SRL"
  generate 
    if (AXISTEN_IF_EXT_512_INTFC_RAM_STYLE =="SRL") 
      begin: srl_style_fifo

    // synthesis translate_off
    initial
          begin
        for (i=0; i < FIFO_DEPTH; i=i+1)
          ram_array[i] = 0;
      end
        // synthesis translate_on

  //Write to SRL inputs, and shift SRL
  always @(posedge clk_i)
      if (write_en_i & ~fifo_full)
        begin
      for (i= (FIFO_DEPTH-1); i>0; i=i-1)
        ram_array[i] <= #TCQ ram_array[i-1];
      ram_array[0]    <= #TCQ write_data_i;
        end

  //Maintain read pointer based on occupancy of the FIFO.
  // Read pointer points to the highest index of full locations.
   always @(posedge clk_i)
     if (~reset_n_i)
       read_ptr <= #TCQ 3'd0;
     else if (link_down_reset_i)
       read_ptr <= #TCQ 3'd0;
     else if (write_en_i && ~fifo_full &&
          (~(read_en_i & ~fifo_empty)))
       // Write but no read
       begin
     if (~fifo_empty)
       read_ptr <= #TCQ read_ptr + 3'd1;
       end
     else if ((~(write_en_i & ~fifo_full)) &&
          read_en_i && ~fifo_empty &&
          (read_ptr != 3'd0))
       // Read but no write
       read_ptr <= #TCQ read_ptr - 3'd1;

     assign    read_data_o = ram_array[read_ptr];
   end // block: srl_style_fifo
    else
      begin
   // Write pointer
   always @(posedge clk_i)
     if (~reset_n_i)
       write_ptr <= #TCQ 3'd0;
     else if (link_down_reset_i)
       write_ptr <= #TCQ 3'd0;
     else if (write_en_i & ~fifo_full)
       begin
      if (write_ptr == FIFO_DEPTH-1)
        write_ptr <= #TCQ 3'd0;
      else
        write_ptr <= #TCQ write_ptr + 3'd1;
       end
   always @(posedge clk_i)
     if (write_en_i & ~fifo_full)
       ram_array[write_ptr] <= #TCQ write_data_i;

   // Read pointer
   always @(posedge clk_i)
     if (~reset_n_i)
       read_ptr <= #TCQ 3'd0;
     else if (link_down_reset_i)
       read_ptr <= #TCQ 3'd0;
     else if (read_en_i & ~fifo_empty)
       begin
      if (read_ptr == FIFO_DEPTH-1)
        read_ptr <= #TCQ 3'd0;
      else
        read_ptr <= #TCQ read_ptr + 3'd1;
       end
    assign    read_data_o = ram_array[read_ptr];

    end // else: !if(AXISTEN_IF_EXT_512_INTFC_RAM_STYLE =="SRL")
  endgenerate

   // Maintain FIFO occupancy
   always @(posedge clk_i)
     if (~reset_n_i)
       fifo_occupancy <= #TCQ 4'd0;
     else if (link_down_reset_i)
       fifo_occupancy <= #TCQ 4'd0;
     else if (write_en_i & ~fifo_full &
          ~(read_en_i & ~fifo_empty))
       fifo_occupancy <= #TCQ fifo_occupancy + 4'd1;
     else if (~(write_en_i & ~fifo_full) &
          read_en_i & ~fifo_empty)
       fifo_occupancy <= #TCQ fifo_occupancy - 4'd1;

   always @(posedge clk_i)
     if (~reset_n_i)
       fifo_almost_full <= #TCQ 1'b0;
     else
       fifo_almost_full <= #TCQ (fifo_occupancy >= FIFO_ALMOST_FULL_THRESHOLD);

   assign    fifo_empty = (fifo_occupancy == 4'd0);
   assign    fifo_full = (fifo_occupancy == FIFO_DEPTH);
   assign    read_data_valid_o = ~fifo_empty;

endmodule // pcie_4_0_512b_sync_fifo


