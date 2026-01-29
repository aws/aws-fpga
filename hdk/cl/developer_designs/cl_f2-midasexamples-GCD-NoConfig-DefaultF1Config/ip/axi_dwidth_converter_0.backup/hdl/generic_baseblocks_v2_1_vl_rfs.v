// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized AND with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_carry_and #
  (
   parameter         C_FAMILY                         = "virtex6"
                       // FPGA Family. Current version: virtex6 or spartan6.
   )
  (
   input  wire        CIN,
   input  wire        S,
   output wire        COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////

  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL
      assign COUT = CIN & S;
      
    end else begin : USE_FPGA
      MUXCY and_inst 
      (
       .O (COUT), 
       .CI (CIN), 
       .DI (1'b0), 
       .S (S)
      ); 
      
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized AND with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_carry_latch_and #
  (
   parameter          C_FAMILY                         = "virtex6"
                       // FPGA Family. Current version: virtex6 or spartan6.
   )
  (
   input  wire        CIN,
   input  wire        I,
   output wire        O
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////

  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL
      assign O = CIN & ~I;
      
    end else begin : USE_FPGA
      wire I_n;
      
      assign I_n = ~I;
    
      AND2B1L and2b1l_inst 
        (
         .O(O),
         .DI(CIN),
         .SRI(I_n)
        );
      
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized OR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_carry_latch_or #
  (
   parameter          C_FAMILY                         = "virtex6"
                       // FPGA Family. Current version: virtex6 or spartan6.
   )
  (
   input  wire        CIN,
   input  wire        I,
   output wire        O
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL
      assign O = CIN | I;
      
    end else begin : USE_FPGA
      OR2L or2l_inst1
        (
         .O(O),
         .DI(CIN),
         .SRI(I)
        );
      
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized OR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_carry_or #
  (
   parameter         C_FAMILY                         = "virtex6"
                       // FPGA Family. Current version: virtex6 or spartan6.
   )
  (
   input  wire        CIN,
   input  wire        S,
   output wire        COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL
      assign COUT = CIN | S;
      
    end else begin : USE_FPGA
      wire S_n;
      
      assign S_n = ~S;
    
      MUXCY and_inst 
      (
       .O (COUT), 
       .CI (CIN), 
       .DI (1'b1), 
       .S (S_n)
      ); 
      
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_carry #
  (
   parameter         C_FAMILY                         = "virtex6"
                       // FPGA Family. Current version: virtex6 or spartan6.
   )
  (
   input  wire        CIN,
   input  wire        S,
   input  wire        DI,
   output wire        COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL
      assign COUT = (CIN & S) | (DI & ~S);
      
    end else begin : USE_FPGA
    
      MUXCY and_inst 
      (
       .O (COUT), 
       .CI (CIN), 
       .DI (DI), 
       .S (S)
      ); 
      
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized 16/32 word deep FIFO.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_command_fifo #
  (
   parameter         C_FAMILY                        = "virtex6",
   parameter integer C_ENABLE_S_VALID_CARRY          = 0,
   parameter integer C_ENABLE_REGISTERED_OUTPUT      = 0,
   parameter integer C_FIFO_DEPTH_LOG                = 5,      // FIFO depth = 2**C_FIFO_DEPTH_LOG
                                                               // Range = [4:5].
   parameter integer C_FIFO_WIDTH                    = 64      // Width of payload [1:512]
   )
  (
   // Global inputs
   input  wire                        ACLK,    // Clock
   input  wire                        ARESET,  // Reset
   // Information
   output wire                        EMPTY,   // FIFO empty (all stages)
   // Slave  Port
   input  wire [C_FIFO_WIDTH-1:0]     S_MESG,  // Payload (may be any set of channel signals)
   input  wire                        S_VALID, // FIFO push
   output wire                        S_READY, // FIFO not full
   // Master  Port
   output wire [C_FIFO_WIDTH-1:0]     M_MESG,  // Payload
   output wire                        M_VALID, // FIFO not empty
   input  wire                        M_READY  // FIFO pop
   );

  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for data vector.
  genvar addr_cnt;
  genvar bit_cnt;
  integer index;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIFO_DEPTH_LOG-1:0] addr;
  wire                        buffer_Full;
  wire                        buffer_Empty;
  
  wire                        next_Data_Exists;
  reg                         data_Exists_I = 1'b0;
  
  wire                        valid_Write;
  wire                        new_write;
  
  wire [C_FIFO_DEPTH_LOG-1:0] hsum_A;
  wire [C_FIFO_DEPTH_LOG-1:0] sum_A;
  wire [C_FIFO_DEPTH_LOG-1:0] addr_cy;

  wire                        buffer_full_early;
  
  wire [C_FIFO_WIDTH-1:0]     M_MESG_I;   // Payload
  wire                        M_VALID_I;  // FIFO not empty
  wire                        M_READY_I;  // FIFO pop
  
  /////////////////////////////////////////////////////////////////////////////
  // Create Flags 
  /////////////////////////////////////////////////////////////////////////////
  
  assign buffer_full_early  = ( (addr == {{C_FIFO_DEPTH_LOG-1{1'b1}}, 1'b0}) & valid_Write & ~M_READY_I ) |
                              ( buffer_Full & ~M_READY_I );

  assign S_READY            = ~buffer_Full;

  assign buffer_Empty       = (addr == {C_FIFO_DEPTH_LOG{1'b0}});

  assign next_Data_Exists   = (data_Exists_I & ~buffer_Empty) |
                              (buffer_Empty & S_VALID) |
                              (data_Exists_I & ~(M_READY_I & data_Exists_I));

  always @ (posedge ACLK) begin
    if (ARESET) begin
      data_Exists_I <= 1'b0;
    end else begin
      data_Exists_I <= next_Data_Exists;
    end
  end

  assign M_VALID_I = data_Exists_I;
  
  // Select RTL or FPGA optimized instatiations for critical parts.
  generate
    if ( C_FAMILY == "rtl" || C_ENABLE_S_VALID_CARRY == 0 ) begin : USE_RTL_VALID_WRITE
      reg                         buffer_Full_q = 1'b0;
      
      assign valid_Write = S_VALID & ~buffer_Full;
      
      assign new_write = (S_VALID | ~buffer_Empty);
     
      assign addr_cy[0] = valid_Write;
      
      always @ (posedge ACLK) begin
        if (ARESET) begin
          buffer_Full_q <= 1'b0;
        end else if ( data_Exists_I ) begin
          buffer_Full_q <= buffer_full_early;
        end
      end
      assign buffer_Full = buffer_Full_q;
      
    end else begin : USE_FPGA_VALID_WRITE
      wire s_valid_dummy1;
      wire s_valid_dummy2;
      wire sel_s_valid;
      wire sel_new_write;
      wire valid_Write_dummy1;
      wire valid_Write_dummy2;
      
      assign sel_s_valid = ~buffer_Full;
      
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) s_valid_dummy_inst1
        (
         .CIN(S_VALID),
         .S(1'b1),
         .COUT(s_valid_dummy1)
         );
      
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) s_valid_dummy_inst2
        (
         .CIN(s_valid_dummy1),
         .S(1'b1),
         .COUT(s_valid_dummy2)
         );
      
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) valid_write_inst
        (
         .CIN(s_valid_dummy2),
         .S(sel_s_valid),
         .COUT(valid_Write)
         );
      
      assign sel_new_write = ~buffer_Empty;
       
      generic_baseblocks_v2_1_2_carry_latch_or #
        (
         .C_FAMILY(C_FAMILY)
         ) new_write_inst
        (
         .CIN(valid_Write),
         .I(sel_new_write),
         .O(new_write)
         );
         
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) valid_write_dummy_inst1
        (
         .CIN(valid_Write),
         .S(1'b1),
         .COUT(valid_Write_dummy1)
         );
      
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) valid_write_dummy_inst2
        (
         .CIN(valid_Write_dummy1),
         .S(1'b1),
         .COUT(valid_Write_dummy2)
         );
      
      generic_baseblocks_v2_1_2_carry_and #
        (
         .C_FAMILY(C_FAMILY)
         ) valid_write_dummy_inst3
        (
         .CIN(valid_Write_dummy2),
         .S(1'b1),
         .COUT(addr_cy[0])
         );
      
      FDRE #(
       .INIT(1'b0)              // Initial value of register (1'b0 or 1'b1)
       ) FDRE_I1 (
       .Q(buffer_Full),         // Data output
       .C(ACLK),                // Clock input
       .CE(data_Exists_I),      // Clock enable input
       .R(ARESET),              // Synchronous reset input
       .D(buffer_full_early)    // Data input
       );
       
    end
  endgenerate
      
    
  /////////////////////////////////////////////////////////////////////////////
  // Create address pointer
  /////////////////////////////////////////////////////////////////////////////

  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_ADDR
    
      reg  [C_FIFO_DEPTH_LOG-1:0] addr_q = {C_FIFO_DEPTH_LOG{1'b0}};
      
      always @ (posedge ACLK) begin
        if (ARESET) begin
          addr_q <= {C_FIFO_DEPTH_LOG{1'b0}};
        end else if ( data_Exists_I ) begin
          if ( valid_Write & ~(M_READY_I & data_Exists_I) ) begin
            addr_q <= addr_q + 1'b1;
          end else if ( ~valid_Write & (M_READY_I & data_Exists_I) & ~buffer_Empty ) begin
            addr_q <= addr_q - 1'b1;
          end
          else begin
            addr_q <= addr_q;
          end
        end
        else begin
          addr_q <= addr_q;
        end
      end
      
      assign addr = addr_q;
      
    end else begin : USE_FPGA_ADDR
      for (addr_cnt = 0; addr_cnt < C_FIFO_DEPTH_LOG ; addr_cnt = addr_cnt + 1) begin : ADDR_GEN
        assign hsum_A[addr_cnt] = ((M_READY_I & data_Exists_I) ^ addr[addr_cnt]) & new_write;
        
        // Don't need the last muxcy, addr_cy(last) is not used anywhere
        if ( addr_cnt < C_FIFO_DEPTH_LOG - 1 ) begin : USE_MUXCY
          MUXCY MUXCY_inst (
           .DI(addr[addr_cnt]),
           .CI(addr_cy[addr_cnt]),
           .S(hsum_A[addr_cnt]),
           .O(addr_cy[addr_cnt+1])
           );
           
        end
        else begin : NO_MUXCY
        end
        
        XORCY XORCY_inst (
         .LI(hsum_A[addr_cnt]),
         .CI(addr_cy[addr_cnt]),
         .O(sum_A[addr_cnt])
         );
        
        FDRE #(
         .INIT(1'b0)             // Initial value of register (1'b0 or 1'b1)
         ) FDRE_inst (
         .Q(addr[addr_cnt]),     // Data output
         .C(ACLK),               // Clock input
         .CE(data_Exists_I),     // Clock enable input
         .R(ARESET),             // Synchronous reset input
         .D(sum_A[addr_cnt])     // Data input
         );
        
      end // end for bit_cnt
    end // C_FAMILY
  endgenerate
      
      
  /////////////////////////////////////////////////////////////////////////////
  // Data storage
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" ) begin : USE_RTL_FIFO
      reg  [C_FIFO_WIDTH-1:0] data_srl[2 ** C_FIFO_DEPTH_LOG-1:0];
      
      always @ (posedge ACLK) begin
        if ( valid_Write ) begin
          for (index = 0; index < 2 ** C_FIFO_DEPTH_LOG-1 ; index = index + 1) begin
            data_srl[index+1] <= data_srl[index];
          end
          data_srl[0]   <= S_MESG;
        end
      end
      
      assign M_MESG_I = data_srl[addr];
      
    end else begin : USE_FPGA_FIFO
      for (bit_cnt = 0; bit_cnt < C_FIFO_WIDTH ; bit_cnt = bit_cnt + 1) begin : DATA_GEN
        
        if ( C_FIFO_DEPTH_LOG == 5 ) begin : USE_32
            SRLC32E # (
             .INIT(32'h00000000)    // Initial Value of Shift Register
            ) SRLC32E_inst (
             .Q(M_MESG_I[bit_cnt]), // SRL data output
             .Q31(),                // SRL cascade output pin
             .A(addr),              // 5-bit shift depth select input
             .CE(valid_Write),      // Clock enable input
             .CLK(ACLK),            // Clock input
             .D(S_MESG[bit_cnt])    // SRL data input
            );
        end else begin : USE_16
            SRLC16E # (
             .INIT(32'h00000000)    // Initial Value of Shift Register
            ) SRLC16E_inst (
             .Q(M_MESG_I[bit_cnt]), // SRL data output
             .Q15(),                // SRL cascade output pin
             .A0(addr[0]),          // 4-bit shift depth select input 0
             .A1(addr[1]),          // 4-bit shift depth select input 1
             .A2(addr[2]),          // 4-bit shift depth select input 2
             .A3(addr[3]),          // 4-bit shift depth select input 3
             .CE(valid_Write),      // Clock enable input
             .CLK(ACLK),            // Clock input
             .D(S_MESG[bit_cnt])    // SRL data input
            );
        end // C_FIFO_DEPTH_LOG
      
      end // end for bit_cnt
    end // C_FAMILY
  endgenerate
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Pipeline stage
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_ENABLE_REGISTERED_OUTPUT != 0 ) begin : USE_FF_OUT
      
      wire [C_FIFO_WIDTH-1:0]     M_MESG_FF;    // Payload
      wire                        M_VALID_FF;   // FIFO not empty
      
      // Select RTL or FPGA optimized instatiations for critical parts.
      if ( C_FAMILY == "rtl" ) begin : USE_RTL_OUTPUT_PIPELINE
      
        reg  [C_FIFO_WIDTH-1:0]     M_MESG_Q;   // Payload
        reg                         M_VALID_Q = 1'b0;  // FIFO not empty
        
        always @ (posedge ACLK) begin
          if (ARESET) begin
            M_MESG_Q    <= {C_FIFO_WIDTH{1'b0}};
            M_VALID_Q   <= 1'b0;
          end else begin
            if ( M_READY_I ) begin
              M_MESG_Q    <= M_MESG_I;
              M_VALID_Q   <= M_VALID_I;
            end
          end
        end
      
        assign M_MESG_FF     = M_MESG_Q;
        assign M_VALID_FF    = M_VALID_Q;
        
      end else begin : USE_FPGA_OUTPUT_PIPELINE
      
        reg  [C_FIFO_WIDTH-1:0]     M_MESG_CMB;   // Payload
        reg                         M_VALID_CMB;  // FIFO not empty
        
        always @ *
        begin
          if ( M_READY_I ) begin
            M_MESG_CMB  <= M_MESG_I;
            M_VALID_CMB <= M_VALID_I;
          end else begin
            M_MESG_CMB  <= M_MESG_FF;
            M_VALID_CMB <= M_VALID_FF;
          end
        end
        
        for (bit_cnt = 0; bit_cnt < C_FIFO_WIDTH ; bit_cnt = bit_cnt + 1) begin : DATA_GEN
              
          FDRE #(
           .INIT(1'b0)                    // Initial value of register (1'b0 or 1'b1)
           ) FDRE_inst (
           .Q(M_MESG_FF[bit_cnt]),        // Data output
           .C(ACLK),                      // Clock input
           .CE(1'b1),                     // Clock enable input
           .R(ARESET),                    // Synchronous reset input
           .D(M_MESG_CMB[bit_cnt])        // Data input
           );
        end // end for bit_cnt
            
        FDRE #(
         .INIT(1'b0)                    // Initial value of register (1'b0 or 1'b1)
         ) FDRE_inst (
         .Q(M_VALID_FF),                // Data output
         .C(ACLK),                      // Clock input
         .CE(1'b1),                     // Clock enable input
         .R(ARESET),                    // Synchronous reset input
         .D(M_VALID_CMB)                // Data input
         );
      
      end
      
      assign EMPTY      = ~M_VALID_I & ~M_VALID_FF;
      assign M_MESG     = M_MESG_FF;
      assign M_VALID    = M_VALID_FF;
      assign M_READY_I  = ( M_READY & M_VALID_FF ) | ~M_VALID_FF;
      
    end else begin : NO_FF_OUT
      
      assign EMPTY      = ~M_VALID_I;
      assign M_MESG     = M_MESG_I;
      assign M_VALID    = M_VALID_I;
      assign M_READY_I  = M_READY;
      
    end
  endgenerate

endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR (against constant) with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_mask_static #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter         C_VALUE                          = 4'b0,
                       // Static value to compare against.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] M,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar lut_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 3;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] m_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {C_VALUE, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign m_local        = {M, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = C_VALUE;
      assign m_local        = M;
    end
    
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (lut_cnt = 0; lut_cnt < C_NUM_LUT ; lut_cnt = lut_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[lut_cnt] = ( ( a_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) == 
                              ( b_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[lut_cnt+1]),
       .CIN   (carry_local[lut_cnt]),
       .S     (sel[lut_cnt])
      ); 
      
    end // end for lut_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_mask #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   input  wire [C_DATA_WIDTH-1:0] M,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar lut_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 2;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] m_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign m_local        = {M, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
      assign m_local        = M;
    end
  
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (lut_cnt = 0; lut_cnt < C_NUM_LUT ; lut_cnt = lut_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[lut_cnt] = ( ( a_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) == 
                              ( b_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[lut_cnt+1]),
       .CIN   (carry_local[lut_cnt]),
       .S     (sel[lut_cnt])
      ); 
      
    end // end for lut_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR (against constant) with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_sel_mask_static #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter         C_VALUE                          = 4'b0,
                       // Static value to compare against.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire                    S,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   input  wire [C_DATA_WIDTH-1:0] M,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar lut_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 1;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] m_local;
  wire [C_FIX_DATA_WIDTH-1:0] v_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign m_local        = {M,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign v_local        = {C_VALUE, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
      assign m_local        = M;
      assign v_local        = C_VALUE;
    end
    
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (lut_cnt = 0; lut_cnt < C_NUM_LUT ; lut_cnt = lut_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[lut_cnt] = ( ( ( a_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ==
                                ( v_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ) & ( S == 1'b0 ) ) |
                            ( ( ( b_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ==
                                ( v_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ) & ( S == 1'b1 ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[lut_cnt+1]),
       .CIN   (carry_local[lut_cnt]),
       .S     (sel[lut_cnt])
      ); 
      
    end // end for lut_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_sel_mask #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire                    S,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   input  wire [C_DATA_WIDTH-1:0] M,
   input  wire [C_DATA_WIDTH-1:0] V,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar lut_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 1;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] m_local;
  wire [C_FIX_DATA_WIDTH-1:0] v_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign m_local        = {M, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign v_local        = {V, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
      assign m_local        = M;
      assign v_local        = V;
    end
    
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (lut_cnt = 0; lut_cnt < C_NUM_LUT ; lut_cnt = lut_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[lut_cnt] = ( ( ( a_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ==
                                ( v_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ) & ( S == 1'b0 ) ) |
                            ( ( ( b_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ==
                                ( v_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] &
                                  m_local[lut_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) ) & ( S == 1'b1 ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[lut_cnt+1]),
       .CIN   (carry_local[lut_cnt]),
       .S     (sel[lut_cnt])
      ); 
      
    end // end for lut_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR (against constant) with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_sel_static #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter         C_VALUE                          = 4'b0,
                       // Static value to compare against.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire                    S,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 2;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] v_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign v_local        = {C_VALUE, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
      assign v_local        = C_VALUE;
    end
    
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (bit_cnt = 0; bit_cnt < C_NUM_LUT ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[bit_cnt] = ( ( a_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                                v_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) & ( S == 1'b0 ) ) |
                            ( ( b_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                                v_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) & ( S == 1'b1 ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[bit_cnt+1]),
       .CIN   (carry_local[bit_cnt]),
       .S     (sel[bit_cnt])
      ); 
      
    end // end for bit_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_sel #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire                    S,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   input  wire [C_DATA_WIDTH-1:0] V,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 1;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_FIX_DATA_WIDTH-1:0] v_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign v_local        = {V, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
      assign v_local        = V;
    end
  
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (bit_cnt = 0; bit_cnt < C_NUM_LUT ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[bit_cnt] = ( ( a_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                                v_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) & ( S == 1'b0 ) ) |
                            ( ( b_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                                v_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] ) & ( S == 1'b1 ) );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[bit_cnt+1]),
       .CIN   (carry_local[bit_cnt]),
       .S     (sel[bit_cnt])
      ); 
      
    end // end for bit_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR (against constant) with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator_static #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter         C_VALUE                          = 4'b0,
                       // Static value to compare against.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire [C_DATA_WIDTH-1:0] A,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 6;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A,       {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {C_VALUE, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = C_VALUE;
    end
    
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (bit_cnt = 0; bit_cnt < C_NUM_LUT ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[bit_cnt] = ( a_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                              b_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[bit_cnt+1]),
       .CIN   (carry_local[bit_cnt]),
       .S     (sel[bit_cnt])
      ); 
      
    end // end for bit_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized COMPARATOR with generic_baseblocks_v2_1_2_carry logic.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_comparator #
  (
   parameter         C_FAMILY                         = "virtex6", 
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_DATA_WIDTH                     = 4
                       // Data width for comparator.
   )
  (
   input  wire                    CIN,
   input  wire [C_DATA_WIDTH-1:0] A,
   input  wire [C_DATA_WIDTH-1:0] B,
   output wire                    COUT
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  // Bits per LUT for this architecture.
  localparam integer C_BITS_PER_LUT   = 3;
  
  // Constants for packing levels.
  localparam integer C_NUM_LUT        = ( C_DATA_WIDTH + C_BITS_PER_LUT - 1 ) / C_BITS_PER_LUT;
  
  // 
  localparam integer C_FIX_DATA_WIDTH = ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) ? C_NUM_LUT * C_BITS_PER_LUT :
                                        C_DATA_WIDTH;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  wire [C_FIX_DATA_WIDTH-1:0] a_local;
  wire [C_FIX_DATA_WIDTH-1:0] b_local;
  wire [C_NUM_LUT-1:0]        sel;
  wire [C_NUM_LUT:0]          carry_local;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // 
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    // Assign input to local vectors.
    assign carry_local[0] = CIN;
    
    // Extend input data to fit.
    if ( C_NUM_LUT * C_BITS_PER_LUT > C_DATA_WIDTH ) begin : USE_EXTENDED_DATA
      assign a_local        = {A, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
      assign b_local        = {B, {C_NUM_LUT * C_BITS_PER_LUT - C_DATA_WIDTH{1'b0}}};
    end else begin : NO_EXTENDED_DATA
      assign a_local        = A;
      assign b_local        = B;
    end
  
    // Instantiate one generic_baseblocks_v2_1_2_carry and per level.
    for (bit_cnt = 0; bit_cnt < C_NUM_LUT ; bit_cnt = bit_cnt + 1) begin : LUT_LEVEL
      // Create the local select signal
      assign sel[bit_cnt] = ( a_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] == 
                              b_local[bit_cnt*C_BITS_PER_LUT +: C_BITS_PER_LUT] );
    
      // Instantiate each LUT level.
      generic_baseblocks_v2_1_2_carry_and # 
      (
       .C_FAMILY(C_FAMILY)
      ) compare_inst 
      (
       .COUT  (carry_local[bit_cnt+1]),
       .CIN   (carry_local[bit_cnt]),
       .S     (sel[bit_cnt])
      ); 
      
    end // end for bit_cnt
    
    // Assign output from local vector.
    assign COUT = carry_local[C_NUM_LUT];
    
  endgenerate
  
  
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized Mux using MUXF7/8.
//  Any generic_baseblocks_v2_1_2_mux ratio.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   mux_enc
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_mux_enc #
  (
   parameter         C_FAMILY                       = "rtl",
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_RATIO                        = 4,
                       // Mux select ratio. Can be any binary value (>= 1)
   parameter integer C_SEL_WIDTH                    = 2,
                       // Log2-ceiling of C_RATIO (>= 1)
   parameter integer C_DATA_WIDTH                   = 1
                       // Data width for generic_baseblocks_v2_1_2_comparator (>= 1)
   )
  (
   input  wire [C_SEL_WIDTH-1:0]                    S,
   input  wire [C_RATIO*C_DATA_WIDTH-1:0]           A,
   output wire [C_DATA_WIDTH-1:0]                   O,
   input  wire                                      OE
   );
  
  wire [C_DATA_WIDTH-1:0] o_i;
  genvar bit_cnt;
  
  function [C_DATA_WIDTH-1:0] f_mux
    (
     input [C_SEL_WIDTH-1:0] s,
     input [C_RATIO*C_DATA_WIDTH-1:0] a
     );
    integer i;
    reg [C_RATIO*C_DATA_WIDTH-1:0] carry;
    begin
      carry[C_DATA_WIDTH-1:0] = {C_DATA_WIDTH{(s==0)?1'b1:1'b0}} & a[C_DATA_WIDTH-1:0];
      for (i=1;i<C_RATIO;i=i+1) begin : gen_carrychain_enc
        carry[i*C_DATA_WIDTH +: C_DATA_WIDTH] = 
          carry[(i-1)*C_DATA_WIDTH +: C_DATA_WIDTH] |
          ({C_DATA_WIDTH{(s==i)?1'b1:1'b0}} & a[i*C_DATA_WIDTH +: C_DATA_WIDTH]);
      end
      f_mux = carry[C_DATA_WIDTH*C_RATIO-1:C_DATA_WIDTH*(C_RATIO-1)];
    end
  endfunction
  
  function [C_DATA_WIDTH-1:0] f_mux4
    (
     input [1:0] s,
     input [4*C_DATA_WIDTH-1:0] a
     );
    integer i;
    reg [4*C_DATA_WIDTH-1:0] carry;
    begin
      carry[C_DATA_WIDTH-1:0] = {C_DATA_WIDTH{(s==0)?1'b1:1'b0}} & a[C_DATA_WIDTH-1:0];
      for (i=1;i<4;i=i+1) begin : gen_carrychain_enc
        carry[i*C_DATA_WIDTH +: C_DATA_WIDTH] = 
          carry[(i-1)*C_DATA_WIDTH +: C_DATA_WIDTH] |
          ({C_DATA_WIDTH{(s==i)?1'b1:1'b0}} & a[i*C_DATA_WIDTH +: C_DATA_WIDTH]);
      end
      f_mux4 = carry[C_DATA_WIDTH*4-1:C_DATA_WIDTH*3];
    end
  endfunction
  
  assign O = o_i & {C_DATA_WIDTH{OE}};  // OE is gated AFTER any MUXF7/8 (can only optimize forward into downstream logic)
  
  generate
    if ( C_RATIO < 2 ) begin : gen_bypass
      assign o_i = A;
    end else if ( C_FAMILY == "rtl" || C_RATIO < 5 ) begin : gen_rtl
      assign o_i = f_mux(S, A);
      
    end else begin : gen_fpga
      wire [C_DATA_WIDTH-1:0] l;
      wire [C_DATA_WIDTH-1:0] h;
      wire [C_DATA_WIDTH-1:0] ll;
      wire [C_DATA_WIDTH-1:0] lh;
      wire [C_DATA_WIDTH-1:0] hl;
      wire [C_DATA_WIDTH-1:0] hh;
      
      case (C_RATIO)
        1, 5, 9, 13: 
          assign hh = A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH];
        2, 6, 10, 14:
          assign hh = S[0] ? 
            A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
            A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] ;
        3, 7, 11, 15:
          assign hh = S[1] ? 
            A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
            (S[0] ? 
              A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-3)*C_DATA_WIDTH +: C_DATA_WIDTH] );
        4, 8, 12, 16:
          assign hh = S[1] ? 
            (S[0] ? 
              A[(C_RATIO-1)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-2)*C_DATA_WIDTH +: C_DATA_WIDTH] ) :
            (S[0] ? 
              A[(C_RATIO-3)*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[(C_RATIO-4)*C_DATA_WIDTH +: C_DATA_WIDTH] );
        17:
          assign hh = S[1] ? 
            (S[0] ? 
              A[15*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[14*C_DATA_WIDTH +: C_DATA_WIDTH] ) :
            (S[0] ? 
              A[13*C_DATA_WIDTH +: C_DATA_WIDTH] :
              A[12*C_DATA_WIDTH +: C_DATA_WIDTH] );
        default:
          assign hh = 0; 
      endcase

      case (C_RATIO)
        5, 6, 7, 8: begin
          assign l = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_5_8
            MUXF7 mux_s2_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        9, 10, 11, 12: begin
          assign ll = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_9_12
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        13,14,15,16: begin
          assign ll = f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);
          assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          assign hl = f_mux4(S[1:0], A[8*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_13_16
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF7 muxf_s2_hi_inst 
            (
             .I0  (hl[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (h[bit_cnt])
            );
          
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (h[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        17: begin
          assign ll = S[4] ? A[16*C_DATA_WIDTH +: C_DATA_WIDTH] : f_mux4(S[1:0], A[0 +: 4*C_DATA_WIDTH]);  // 5-input mux
          assign lh = f_mux4(S[1:0], A[4*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          assign hl = f_mux4(S[1:0], A[8*C_DATA_WIDTH +: 4*C_DATA_WIDTH]);
          for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : gen_mux_17
            MUXF7 muxf_s2_low_inst 
            (
             .I0  (ll[bit_cnt]),
             .I1  (lh[bit_cnt]),
             .S   (S[2]),
             .O   (l[bit_cnt])
            ); 
            MUXF7 muxf_s2_hi_inst 
            (
             .I0  (hl[bit_cnt]),
             .I1  (hh[bit_cnt]),
             .S   (S[2]),
             .O   (h[bit_cnt])
            ); 
            MUXF8 muxf_s3_inst 
            (
             .I0  (l[bit_cnt]),
             .I1  (h[bit_cnt]),
             .S   (S[3]),
             .O   (o_i[bit_cnt])
            ); 
          end
        end
          
        default:  // If RATIO > 17, use RTL
          assign o_i = f_mux(S, A);
      endcase
    end  // gen_fpga
  endgenerate
endmodule


// (c) Copyright 2010-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// Description: 
//  Optimized Mux from 2:1 upto 16:1.
//
// Verilog-standard:  Verilog 2001
//--------------------------------------------------------------------------
//
// Structure:
//   
//
//--------------------------------------------------------------------------
`timescale 1ps/1ps


(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_mux #
  (
   parameter         C_FAMILY                         = "rtl",
                       // FPGA Family. Current version: virtex6 or spartan6.
   parameter integer C_SEL_WIDTH                      = 4,
                       // Data width for comparator.
   parameter integer C_DATA_WIDTH                     = 2
                       // Data width for comparator.
   )
  (
   input  wire [C_SEL_WIDTH-1:0]                    S,
   input  wire [(2**C_SEL_WIDTH)*C_DATA_WIDTH-1:0]  A,
   output wire [C_DATA_WIDTH-1:0]                   O
   );
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Variables for generating parameter controlled instances.
  /////////////////////////////////////////////////////////////////////////////
  
  // Generate variable for bit vector.
  genvar bit_cnt;
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Local params
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Functions
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Internal signals
  /////////////////////////////////////////////////////////////////////////////
  
  
  /////////////////////////////////////////////////////////////////////////////
  // Instantiate or use RTL code
  /////////////////////////////////////////////////////////////////////////////
  
  generate
    if ( C_FAMILY == "rtl" || C_SEL_WIDTH < 3 ) begin : USE_RTL
      assign O = A[(S)*C_DATA_WIDTH +: C_DATA_WIDTH];
      
    end else begin : USE_FPGA
      
      wire [C_DATA_WIDTH-1:0] C;
      wire [C_DATA_WIDTH-1:0] D;
      
      // Lower half recursively.
      generic_baseblocks_v2_1_2_mux # 
      (
       .C_FAMILY      (C_FAMILY),
       .C_SEL_WIDTH   (C_SEL_WIDTH-1),
       .C_DATA_WIDTH  (C_DATA_WIDTH)
      ) mux_c_inst 
      (
       .S   (S[C_SEL_WIDTH-2:0]),
       .A   (A[(2**(C_SEL_WIDTH-1))*C_DATA_WIDTH-1 : 0]),
       .O   (C)
      ); 
      
      // Upper half recursively.
      generic_baseblocks_v2_1_2_mux # 
      (
       .C_FAMILY      (C_FAMILY),
       .C_SEL_WIDTH   (C_SEL_WIDTH-1),
       .C_DATA_WIDTH  (C_DATA_WIDTH)
      ) mux_d_inst 
      (
       .S   (S[C_SEL_WIDTH-2:0]),
       .A   (A[(2**C_SEL_WIDTH)*C_DATA_WIDTH-1 : (2**(C_SEL_WIDTH-1))*C_DATA_WIDTH]),
       .O   (D)
      ); 
      
      // Generate instantiated generic_baseblocks_v2_1_2_mux components as required.
      for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : NUM
        if ( C_SEL_WIDTH == 4 ) begin : USE_F8
        
          MUXF8 muxf8_inst 
          (
           .I0  (C[bit_cnt]),
           .I1  (D[bit_cnt]),
           .S   (S[C_SEL_WIDTH-1]),
           .O   (O[bit_cnt])
          ); 
          
        end else if ( C_SEL_WIDTH == 3 ) begin : USE_F7
      
          MUXF7 muxf7_inst 
          (
           .I0  (C[bit_cnt]),
           .I1  (D[bit_cnt]),
           .S   (S[C_SEL_WIDTH-1]),
           .O   (O[bit_cnt])
          ); 
          
        end // C_SEL_WIDTH
      end // end for bit_cnt
    
    end
  endgenerate
  
  
endmodule


// (c) Copyright 2009-2011, 2023 Advanced Micro Devices, Inc. All rights reserved.
//
// This file contains confidential and proprietary information
// of AMD and is protected under U.S. and international copyright
// and other intellectual property laws.
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
////////////////////////////////////////////////////////////
//
// File name: nto1_mux.v
//
// Description: N:1 MUX based on either binary-encoded or one-hot select input
//   One-hot mode does not protect against multiple active SEL_ONEHOT inputs.
//   Note: All port signals changed to all-upper-case (w.r.t. prior version).
//
//-----------------------------------------------------------------------------

`timescale 1ps/1ps
`default_nettype none

(* DowngradeIPIdentifiedWarnings="yes" *) 
module generic_baseblocks_v2_1_2_nto1_mux #
  (
   parameter integer C_RATIO         =  1,  // Range: >=1
   parameter integer C_SEL_WIDTH     =  1,  // Range: >=1; recommended: ceil_log2(C_RATIO)
   parameter integer C_DATAOUT_WIDTH =  1,  // Range: >=1
   parameter integer C_ONEHOT        =  0   // Values: 0 = binary-encoded (use SEL); 1 = one-hot (use SEL_ONEHOT)
   )
  (
   input  wire [C_RATIO-1:0]                 SEL_ONEHOT,  // One-hot generic_baseblocks_v2_1_2_mux select (only used if C_ONEHOT=1)
   input  wire [C_SEL_WIDTH-1:0]             SEL,         // Binary-encoded generic_baseblocks_v2_1_2_mux select (only used if C_ONEHOT=0)
   input  wire [C_RATIO*C_DATAOUT_WIDTH-1:0] IN,          // Data input array (num_selections x data_width)
   output wire [C_DATAOUT_WIDTH-1:0]         OUT          // Data output vector
   );

  wire [C_DATAOUT_WIDTH*C_RATIO-1:0] carry;
  genvar i;
  
  generate
    if (C_ONEHOT == 0) begin : gen_encoded
      assign carry[C_DATAOUT_WIDTH-1:0] = {C_DATAOUT_WIDTH{(SEL==0)?1'b1:1'b0}} & IN[C_DATAOUT_WIDTH-1:0];
      for (i=1;i<C_RATIO;i=i+1) begin : gen_carrychain_enc
        assign carry[(i+1)*C_DATAOUT_WIDTH-1:i*C_DATAOUT_WIDTH] = 
               carry[i*C_DATAOUT_WIDTH-1:(i-1)*C_DATAOUT_WIDTH] |
               {C_DATAOUT_WIDTH{(SEL==i)?1'b1:1'b0}} & IN[(i+1)*C_DATAOUT_WIDTH-1:i*C_DATAOUT_WIDTH];
      end
    end else begin : gen_onehot
      assign carry[C_DATAOUT_WIDTH-1:0] = {C_DATAOUT_WIDTH{SEL_ONEHOT[0]}} & IN[C_DATAOUT_WIDTH-1:0];
      for (i=1;i<C_RATIO;i=i+1) begin : gen_carrychain_hot
        assign carry[(i+1)*C_DATAOUT_WIDTH-1:i*C_DATAOUT_WIDTH] = 
               carry[i*C_DATAOUT_WIDTH-1:(i-1)*C_DATAOUT_WIDTH] |
               {C_DATAOUT_WIDTH{SEL_ONEHOT[i]}} & IN[(i+1)*C_DATAOUT_WIDTH-1:i*C_DATAOUT_WIDTH];
      end
    end
  endgenerate
  assign OUT = carry[C_DATAOUT_WIDTH*C_RATIO-1:
                     C_DATAOUT_WIDTH*(C_RATIO-1)];
endmodule

`default_nettype wire


