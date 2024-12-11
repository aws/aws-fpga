//-----------------------------------------------------------------------------
//
// (c) Copyright 1995, 2007, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
//
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// AMD, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND AMD HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) AMD shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or AMD had been advised of the
// possibility of the same.
//
// CRITICAL APPLICATIONS
// AMD products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of AMD products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
//
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
//
//-----------------------------------------------------------------------------
//
// Project    : UltraScale+ FPGA PCI Express CCIX v4.0 Integrated Block
// File       : pcie_bridge_ep_pcie4c_ip_512b_async_fifo.v
// Version    : 1.0 
//-----------------------------------------------------------------------------
//--------------------------------------------------------------------------------------------------
`timescale 1ps/1ps
(* DowngradeIPIdentifiedWarnings = "yes" *)
module pcie_bridge_ep_pcie4c_ip_512b_async_fifo #(
   parameter TCQ = 100,
   parameter IMPL_TARGET = "SOFT",
   parameter IN_DATA_WIDTH = 512,
   parameter FIFO_WIDTH = 256,
   parameter FIFO_DEPTH = 16,
   parameter FIFO_ALMOST_FULL_THRESHOLD = 7
   ) 
  (
   // Write side
    input  wire           clk_i // clock
   ,input  wire           clk_en_i // clock enable, valid in alternate cycles
   ,input  wire           reset_n_i // Reset 
   ,input  wire           link_down_reset_i // Reset FIFO on link down
   ,input wire [IN_DATA_WIDTH-1:0] write_data_i
   ,input wire [1:0]       write_en_i
   ,output wire            fifo_almost_full_o
   // Read side
   ,input                 read_en_i
   ,output wire [FIFO_WIDTH-1:0] read_data_o
   ,output wire           read_data_valid_o
   );
   
  reg [3:0]    read_ptr;
  reg [3:0]    fifo_occupancy;
  reg            fifo_empty;

  integer    i;

  reg [FIFO_WIDTH-1:0]  ram_array[FIFO_DEPTH-1:0];
  reg [FIFO_WIDTH-1:0]     write_data_reg;
  reg             write_data_valid_reg;

  // Convert input data to core clock domain by registering it.
  // Serialize writes of lower and upper halves.
  
  always @(posedge clk_i)
    if (~reset_n_i)
      write_data_reg <= #TCQ {FIFO_WIDTH{1'b0}};
    else
      begin
    if (~clk_en_i & write_en_i[0])
      write_data_reg[FIFO_WIDTH-1:0] <= #TCQ write_data_i[IN_DATA_WIDTH/2-1:0];
    else if (clk_en_i & write_en_i[1])
      write_data_reg[FIFO_WIDTH-1:0] <= #TCQ write_data_i[IN_DATA_WIDTH-1:IN_DATA_WIDTH/2];
      end

  always @(posedge clk_i)
    if (~reset_n_i)
      write_data_valid_reg <= #TCQ 1'b0;
    else
      begin
    if (~clk_en_i)
      write_data_valid_reg <= #TCQ  write_en_i[0];
    else
      write_data_valid_reg <= #TCQ  write_en_i[1];
      end

  // synthesis translate_off
  initial
  begin
    for (i=0; i < FIFO_WIDTH; i=i+1)
      begin
    ram_array[i] = 0;
      end
  end
  // synthesis translate_on

  //Write to SRL inputs, and shift SRL
  always @(posedge clk_i)
    if (write_data_valid_reg)
      begin
    for (i= (FIFO_DEPTH-1); i>0; i=i-1)
      ram_array[i] <= #TCQ ram_array[i-1];
     ram_array[0]   <= #TCQ write_data_reg[FIFO_WIDTH-1:0];
      end
    
   // Read pointer
   always @(posedge clk_i)
     if (~reset_n_i)
       read_ptr <= #(TCQ) 4'd0;
     else if (link_down_reset_i)
       read_ptr <= #(TCQ) 4'd0;
     else if ((read_en_i & ~fifo_empty) &
          (~write_data_valid_reg))
       // Read but no write in this cycle
       begin
     if (read_ptr != 4'd0)
       read_ptr <= #TCQ read_ptr - 4'd1;
       end
       else if (~(read_en_i & ~fifo_empty) &
          write_data_valid_reg)
     // Write but no read in this cycle
     begin
       if (~fifo_empty)
         read_ptr <= #TCQ read_ptr + 4'd1;
     end
  
   // Maintain FIFO occupancy
   always @(posedge clk_i)
     if (~reset_n_i)
       begin
     fifo_occupancy <= #TCQ 4'd0;
     fifo_empty <= #TCQ 1'b1;
       end
     else if (link_down_reset_i)
       begin
     fifo_occupancy <= #TCQ 4'd0;
     fifo_empty <= #TCQ 1'b1;
       end
     else if ((read_en_i & ~fifo_empty) &
          (~write_data_valid_reg))
       // Read but no write in this cycle
       begin
     fifo_occupancy <= #TCQ fifo_occupancy - 4'd1;
     fifo_empty <= #TCQ (fifo_occupancy == 4'd1);
       end
     else if (~(read_en_i & ~fifo_empty) &
          write_data_valid_reg)
       // Write but no read in this cycle
       begin
     fifo_occupancy <= #TCQ fifo_occupancy + 4'd1;
     fifo_empty <= #TCQ 1'b0;
       end
  
  assign fifo_almost_full_o = (fifo_occupancy >= FIFO_ALMOST_FULL_THRESHOLD);

   assign    read_data_o = ram_array[read_ptr[3:0]];
   assign    read_data_valid_o = ~fifo_empty;

endmodule // pcie_4_0_512b_async_fifo




