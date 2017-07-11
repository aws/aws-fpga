// -- (c) Copyright 2013 Xilinx, Inc. All rights reserved. 
// --                                                             
// -- This file contains confidential and proprietary information 
// -- of Xilinx, Inc. and is protected under U.S. and             
// -- international copyright and other intellectual property     
// -- laws.                                                       
// --                                                             
// -- DISCLAIMER                                                  
// -- This disclaimer is not a license and does not grant any     
// -- rights to the materials distributed herewith. Except as     
// -- otherwise provided in a valid license issued to you by      
// -- Xilinx, and to the maximum extent permitted by applicable   
// -- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND     
// -- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES 
// -- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING   
// -- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-      
// -- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and    
// -- (2) Xilinx shall not be liable (whether in contract or tort,
// -- including negligence, or under any other theory of          
// -- liability) for any loss or damage of any kind or nature     
// -- related to, arising under or in connection with these       
// -- materials, including for any direct, or any indirect,       
// -- special, incidental, or consequential loss or damage        
// -- (including loss of data, profits, goodwill, or any type of  
// -- loss or damage suffered as a result of any action brought   
// -- by a third party) even if such damage or loss was           
// -- reasonably foreseeable or Xilinx had been advised of the    
// -- possibility of the same.                                    
// --                                                             
// -- CRITICAL APPLICATIONS                                       
// -- Xilinx products are not designed or intended to be fail-    
// -- safe, or for use in any application requiring fail-safe     
// -- performance, such as life-support or safety devices or      
// -- systems, Class III medical devices, nuclear facilities,     
// -- applications related to the deployment of airbags, or any   
// -- other applications that could lead to death, personal       
// -- injury, or severe property or environmental damage          
// -- (individually and collectively, "Critical                   
// -- Applications"). Customer assumes the sole risk and          
// -- liability of any use of Xilinx products in Critical         
// -- Applications, subject only to applicable laws and           
// -- regulations governing limitations on product liability.     
// --                                                             
// -- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS    
// -- PART OF THIS FILE AT ALL TIMES.                             
// --  
///////////////////////////////////////////////////////////////////////////////
//
// File name: ddr4_v2_2_0_axi_ctrl_reg_bank.v
//
// Description: AXI Lite Controller
//
// Specifications:
//
// Structure:
//
///////////////////////////////////////////////////////////////////////////////
`timescale 1ps/1ps
`default_nettype none

module ddr4_v2_2_0_axi_ctrl_reg_bank #
(
///////////////////////////////////////////////////////////////////////////////
// Parameter Definitions
///////////////////////////////////////////////////////////////////////////////
  // Width of AXI-4-Lite address bus
  parameter         C_ADDR_WIDTH            = 32,
  parameter         C_DATA_WIDTH            = 32,
  parameter         C_DQ_WIDTH              = 72,
  parameter         C_ECC_CE_COUNTER_WIDTH  = 8,
  parameter         C_ECC_ONOFF_RESET_VALUE = 1,
  parameter         C_ECC_TEST              = "ON",
  parameter         C_ECC_WIDTH             = 8,
  parameter         C_MC_ERR_ADDR_WIDTH     = 28,
  parameter         C_MEM_ADDR_ORDER        = "BANK_ROW_COLUMN",
  // # of memory Bank Address bits.
  parameter         C_BANK_WIDTH                         = 3,
  // # of memory Row Address bits.           
  parameter         C_ROW_WIDTH                          = 14,
  // # of memory Column Address bits.        
  parameter         C_COL_WIDTH                          = 10,
  parameter         C_NCK_PER_CLK           = 2,
  parameter         C_NUM_REG               = 24,
  parameter         C_NUM_REG_WIDTH         = 5,
  parameter         C_S_AXI_ADDR_WIDTH      = 32,
  parameter         C_S_AXI_BASEADDR        = 32'h0000_0000,
  // Register arrays
  parameter         C_REG_WIDTH_ARRAY       = 160'h0,
  parameter         C_REG_RDAC_ARRAY        = 5'b0,
  parameter         C_REG_WRAC_ARRAY        = 5'b0,
  parameter         C_REG_INIT_ARRAY        = 160'h0,
  parameter         C_REG_MASK_ARRAY        = 160'h0,
  parameter         C_REG_ADDR_ARRAY        = 160'h0000_f00C_0000_f008_0000_f004_0000_f000_FFFF_FFFF,
  // Register Indices
  parameter integer C_REG_FI_ECC_INDX        = 23,
  parameter integer C_REG_FI_D_127_96_INDX   = 22,
  parameter integer C_REG_FI_D_95_64_INDX    = 21,
  parameter integer C_REG_FI_D_63_32_INDX    = 20,
  parameter integer C_REG_FI_D_31_00_INDX    = 19,
  parameter integer C_REG_UE_FFA_63_32_INDX  = 18,
  parameter integer C_REG_UE_FFA_31_00_INDX  = 17,
  parameter integer C_REG_UE_FFE_INDX        = 16,
  parameter integer C_REG_UE_FFD_127_96_INDX = 15,
  parameter integer C_REG_UE_FFD_95_64_INDX  = 14,
  parameter integer C_REG_UE_FFD_63_32_INDX  = 13,
  parameter integer C_REG_UE_FFD_31_00_INDX  = 12,
  parameter integer C_REG_CE_FFA_63_32_INDX  = 11,
  parameter integer C_REG_CE_FFA_31_00_INDX  = 10,
  parameter integer C_REG_CE_FFE_INDX        = 9 ,
  parameter integer C_REG_CE_FFD_127_96_INDX = 8 ,
  parameter integer C_REG_CE_FFD_95_64_INDX  = 7 ,
  parameter integer C_REG_CE_FFD_63_32_INDX  = 6 ,
  parameter integer C_REG_CE_FFD_31_00_INDX  = 5 ,
  parameter integer C_REG_CE_CNT_INDX        = 4 ,
  parameter integer C_REG_ECC_ON_OFF_INDX    = 3 ,
  parameter integer C_REG_ECC_EN_IRQ_INDX    = 2 ,
  parameter integer C_REG_ECC_STATUS_INDX    = 1 ,
  parameter integer C_REG_DUMMY_INDX         = 0 

)
(
///////////////////////////////////////////////////////////////////////////////
// Port Declarations     
///////////////////////////////////////////////////////////////////////////////
  // AXI4-Lite Slave Interface
  // Slave Interface System Signals           
  input  wire                                  clk            , 
  input  wire                                  reset         ,
  input  wire [C_NUM_REG_WIDTH-1:0]            reg_data_sel    , 
  input  wire                                  reg_data_write  , 
  input  wire [C_DATA_WIDTH-1:0]               reg_data_in     , 
  output wire [C_DATA_WIDTH*C_NUM_REG-1:0]     reg_data_out    ,

  output wire                                  interrupt         ,
  input  wire [2*C_NCK_PER_CLK-1:0]            ecc_single      ,
  input  wire [2*C_NCK_PER_CLK-1:0]            ecc_multiple    ,
  input  wire [C_MC_ERR_ADDR_WIDTH-1:0]        ecc_err_addr    ,
  output wire                                  app_correct_en  , 
  input  wire [2*C_NCK_PER_CLK*C_DQ_WIDTH-1:0] dfi_rddata      , 
  output wire [C_DQ_WIDTH/8-1:0]               fi_xor_we       ,
  output wire [C_DQ_WIDTH-1:0]                 fi_xor_wrdata    
);

////////////////////////////////////////////////////////////////////////////////
// Functions
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Local parameters
////////////////////////////////////////////////////////////////////////////////
localparam P_FI_XOR_WE_WIDTH = (C_DQ_WIDTH%C_DATA_WIDTH)/8; 
localparam P_SHIFT_BY = C_DQ_WIDTH == 72 ? 3 : 4;
localparam P_CS_WIDTH = C_MC_ERR_ADDR_WIDTH - C_COL_WIDTH - C_ROW_WIDTH - C_BANK_WIDTH - 1;
////////////////////////////////////////////////////////////////////////////////
// Wires/Reg declarations
////////////////////////////////////////////////////////////////////////////////
integer beat;
reg  [C_DQ_WIDTH-1:0] ffs;
reg  [C_DQ_WIDTH-1:0] ffm;
wire [7:0] ecc_single_expanded;
wire [7:0] ecc_multiple_expanded;
reg  [63:0] ffas;
reg  [63:0] ffam;
reg  [2:0] ffas_lsb;
reg  [2:0] ffam_lsb;
wire [C_NUM_REG-1:0] we;
wire [C_DATA_WIDTH*C_NUM_REG-1:0] data_in;
wire [C_NUM_REG-1:0] we_int;
wire [C_DATA_WIDTH*C_NUM_REG-1:0] data_in_int;
wire [C_DATA_WIDTH*C_NUM_REG-1:0] data_out;
reg  interrupt_r;
reg  ecc_on_off_r;
reg  ce_clr_r;
reg  ue_clr_r;
wire ce_set_i;
wire ue_set_i;
reg [C_DQ_WIDTH/8-1:0]               fi_xor_we_r;
reg [C_DQ_WIDTH-1:0]                 fi_xor_wrdata_r;

////////////////////////////////////////////////////////////////////////////////
// BEGIN RTL
///////////////////////////////////////////////////////////////////////////////

// Assign outputs
assign reg_data_out = data_out;
assign interrupt = interrupt_r & ecc_on_off_r;
assign app_correct_en = ecc_on_off_r;
assign fi_xor_wrdata = fi_xor_wrdata_r;
assign fi_xor_we     = fi_xor_we_r & {C_DQ_WIDTH/8{ecc_on_off_r}};

// Calculate inputs
// Always block selects the first failing beat out C_NCK_PER_CLK*2 beats.  If
// no failing beats, default to last beat.
always @(*) begin
  ffs = dfi_rddata[(C_NCK_PER_CLK*2-1)*C_DQ_WIDTH+:C_DQ_WIDTH];
  ffm = dfi_rddata[(C_NCK_PER_CLK*2-1)*C_DQ_WIDTH+:C_DQ_WIDTH];

  for( beat = C_NCK_PER_CLK*2-2; beat >= 0 ; beat = beat - 1) begin : find_first_failing_beat
    if (ecc_single[beat]) begin
      ffs = dfi_rddata[beat*C_DQ_WIDTH+:C_DQ_WIDTH];
    end
    if (ecc_multiple[beat]) begin
      ffm = dfi_rddata[beat*C_DQ_WIDTH+:C_DQ_WIDTH];
    end
  end
end

generate
  if (C_NCK_PER_CLK == 2) begin : ecc_zero_extened
    assign ecc_single_expanded   = {4'b0, ecc_single[3:0]};
    assign ecc_multiple_expanded = {4'b0, ecc_multiple[3:0]};
  end
  else begin : no_ecc_zero_extend
    assign ecc_single_expanded   = ecc_single[7:0];
    assign ecc_multiple_expanded = ecc_multiple[7:0];
  end
endgenerate

always @(*) begin 
  (* full_case *) (* parallel_case *)
  casex (ecc_single_expanded) 
    8'bxxxx_xxx1: 
      ffas_lsb = 3'o0;
    8'bxxxx_xx10: 
      ffas_lsb = 3'o1;
    8'bxxxx_x100: 
      ffas_lsb = 3'o2;
    8'bxxxx_1000: 
      ffas_lsb = 3'o3;
    8'bxxx1_0000: 
      ffas_lsb = 3'o4;
    8'bxx10_0000: 
      ffas_lsb = 3'o5;
    8'bx100_0000: 
      ffas_lsb = 3'o6;
    8'b1000_0000: 
      ffas_lsb = 3'o7;
    default:
      ffas_lsb = 3'o0;
  endcase
end

always @(*) begin 
  (* full_case *) (* parallel_case *)
  casex (ecc_multiple_expanded)
    8'bxxxx_xxx1: 
      ffam_lsb = 3'o0;
    8'bxxxx_xx10: 
      ffam_lsb = 3'o1;
    8'bxxxx_x100: 
      ffam_lsb = 3'o2;
    8'bxxxx_1000: 
      ffam_lsb = 3'o3;
    8'bxxx1_0000: 
      ffam_lsb = 3'o4;
    8'bxx10_0000: 
      ffam_lsb = 3'o5;
    8'bx100_0000: 
      ffam_lsb = 3'o6;
    8'b1000_0000: 
      ffam_lsb = 3'o7;
    default:
      ffam_lsb = 3'o0;
  endcase
end

// Calculate first failing address
always @(*) begin
  ffas = {   ecc_single_expanded[7:0], { ( 64 - C_MC_ERR_ADDR_WIDTH - 8 ) { 1'b0 } }, ecc_err_addr[C_MC_ERR_ADDR_WIDTH-1:0] }; 
  ffam = { ecc_multiple_expanded[7:0], { ( 64 - C_MC_ERR_ADDR_WIDTH - 8 ) { 1'b0 } }, ecc_err_addr[C_MC_ERR_ADDR_WIDTH-1:0] }; 
end
   


generate
  genvar i;
  genvar j;

  for (i = 0; i < C_NUM_REG; i = i + 1) begin : inst_reg
    if (C_REG_MASK_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH] > 0) begin 
      ddr4_v2_2_0_axi_ctrl_reg #
      (
        .C_DATA_WIDTH ( C_DATA_WIDTH                                   ) ,
        .C_REG_WIDTH  ( C_REG_WIDTH_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH]) ,
        .C_INIT       ( C_REG_INIT_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH] ) ,
        .C_MASK       ( C_REG_MASK_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH] ) 
      ) 
      axi_ctrl_reg
      (
        .clk         ( clk                                       ) ,
        .reset       ( reset                                     ) ,
        .data_in     ( data_in[i*C_DATA_WIDTH+:C_REG_WIDTH_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH]]     ) ,
        .we          ( we[i]                                     ) ,
        .data_in_int ( data_in_int[i*C_DATA_WIDTH+:C_REG_WIDTH_ARRAY[i*C_DATA_WIDTH+:C_DATA_WIDTH]] ) ,
        .we_int      ( we_int[i]                                 ) ,
        .data_out    ( data_out[i*C_DATA_WIDTH+:C_DATA_WIDTH]    ) 
      );
    end
    else begin : no_reg
      assign data_out[i*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
    end
  end

  // Determine write logic for each register
  for (j = 0; j < C_NUM_REG; j = j + 1) begin : inst_reg_logic_
    case (j)
      C_REG_ECC_STATUS_INDX: 
      begin
        // Bit  Name            Desc
        //   1  CE_STATUS       If '1' a correctable error has occurred.  Cleared when '1' is written to this bit 
        //                      position.
        //   0  UE_STATUS       If '1' a uncorrectable error has occurred.  Cleared when '1' is written to this bit 
        //                      position.
        assign  we[j] = (reg_data_sel == j) && reg_data_write;
        assign  data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ~reg_data_in & data_out[j*C_DATA_WIDTH+:C_DATA_WIDTH];
        assign  we_int[j] = ecc_on_off_r;
        assign  data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {30'b0, (|ecc_single   | data_out[j*C_DATA_WIDTH + 1]), 
                                                                    (|ecc_multiple | data_out[j*C_DATA_WIDTH + 0])};

        // Drive internal signals to write to other registers
        always @(posedge clk) begin 
          ce_clr_r <= ~data_in[j*C_DATA_WIDTH + 1] & we[j];
          ue_clr_r <= ~data_in[j*C_DATA_WIDTH + 0] & we[j];
        end

        assign  ce_set_i = data_in_int[j*C_DATA_WIDTH + 1] & we_int[j] & ~data_out[j*C_DATA_WIDTH + 1];
        assign  ue_set_i = data_in_int[j*C_DATA_WIDTH + 0] & we_int[j] & ~data_out[j*C_DATA_WIDTH + 0];
      end
      C_REG_ECC_EN_IRQ_INDX: 
      begin
        // Bit  Name            Desc
        //   1  CE_EN_IRQ       If '1' the value of the CE_STATUS bit of ECC Status Register will be propagated to the
        //                      Interrupt signal.  If '0' the value of the CE_STATUS bit of ECC Status Register will not
        //                      be propagated to the Interrupt signal.
        //                      position.
        //   0  UE_EN_IRQ       See above
        //                      
        assign  we[j] = (reg_data_sel == j) ? reg_data_write : 1'b0;
        assign  data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = reg_data_in;
        assign  we_int[j] = 1'b0;
        assign  data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        always @(posedge clk) begin
          interrupt_r <= |(data_out[j*C_DATA_WIDTH+:C_DATA_WIDTH] 
                            & data_out[C_REG_ECC_STATUS_INDX*C_DATA_WIDTH+:C_DATA_WIDTH]);
        end
      end
      C_REG_ECC_ON_OFF_INDX: 
      begin
        // Bit  Name            Desc
        //   0  ECC_ON_OFF      If '0', ECC checking is disable on read operations. If '1', ECC checking is enabled on 
        //                      read operations. All correctable and uncorrectable error condtions will be captured
        //                      and status updated.
        assign we[j] = (reg_data_sel == j) ? reg_data_write : 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = reg_data_in;
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        always @(posedge clk) begin
          ecc_on_off_r <= data_out[j*C_DATA_WIDTH+0];
        end
      end
      C_REG_CE_CNT_INDX: 
      begin
        // Bit  Name            Desc
        // 7:0  CE_CNT          Register holds number of correctable errors encountered.
        assign we[j] = (reg_data_sel == j) ? reg_data_write : 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = reg_data_in;
        assign data_in_int[j*C_DATA_WIDTH+:C_ECC_CE_COUNTER_WIDTH+1] 
                = data_out[j*C_DATA_WIDTH+:C_ECC_CE_COUNTER_WIDTH+1] + 1'b1;
        assign data_in_int[j*C_DATA_WIDTH+C_ECC_CE_COUNTER_WIDTH+1+:C_DATA_WIDTH-(C_ECC_CE_COUNTER_WIDTH+1)] 
                = {C_DATA_WIDTH-(C_ECC_CE_COUNTER_WIDTH+1){1'b0}};
        // Only write if there is an error and it will not cause an overflow
        assign we_int[j] = ecc_on_off_r & (|ecc_single) & ~data_in_int[j*C_DATA_WIDTH + C_ECC_CE_COUNTER_WIDTH];

      end
      C_REG_CE_FFD_31_00_INDX: 
      begin
        assign we[j] = ce_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ce_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffs[0*C_DATA_WIDTH+:C_DATA_WIDTH];
      end
      C_REG_CE_FFD_63_32_INDX: 
      begin
        assign we[j] = ce_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ce_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffs[1*C_DATA_WIDTH+:C_DATA_WIDTH];
      end
      C_REG_CE_FFD_95_64_INDX: 
      begin
        if (C_DQ_WIDTH == 144) begin
          assign we[j] = ce_clr_r;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = ce_set_i;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffs[2*C_DATA_WIDTH+:C_DATA_WIDTH];
        end
        else begin
          assign we[j] = 1'b0;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = 1'b0;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        end
      end
      C_REG_CE_FFD_127_96_INDX: 
      begin
        if (C_DQ_WIDTH == 144) begin
          assign we[j] = ce_clr_r;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = ce_set_i;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffs[3*C_DATA_WIDTH+:C_DATA_WIDTH];
        end
        else begin
          assign we[j] = 1'b0;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = 1'b0;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        end
      end

      C_REG_CE_FFE_INDX: 
      begin
        assign we[j] = ce_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ce_set_i;
        if (C_DQ_WIDTH == 144) begin
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {{C_DATA_WIDTH-C_ECC_WIDTH{1'b0}}, ffs[128+:C_ECC_WIDTH] };
        end
        else begin
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {{C_DATA_WIDTH-C_ECC_WIDTH{1'b0}}, ffs[ 64+:C_ECC_WIDTH] };
        end
      end
      C_REG_CE_FFA_31_00_INDX: 
      begin
        assign we[j] = ce_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ce_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffas[31:0];
      end

      C_REG_CE_FFA_63_32_INDX: 
      begin
        assign we[j] = ce_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ce_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffas[63:32];
      end

      C_REG_UE_FFD_31_00_INDX: 
      begin
        assign we[j] = ue_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ue_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffm[0*C_DATA_WIDTH+:C_DATA_WIDTH];
      end
      C_REG_UE_FFD_63_32_INDX: 
      begin
        assign we[j] = ue_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ue_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffm[1*C_DATA_WIDTH+:C_DATA_WIDTH];
      end
      C_REG_UE_FFD_95_64_INDX: 
      begin
        if (C_DQ_WIDTH == 144) begin
          assign we[j] = ue_clr_r;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = ue_set_i;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffm[2*C_DATA_WIDTH+:C_DATA_WIDTH];
        end
        else begin
          assign we[j] = 1'b0;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = 1'b0;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        end
      end
      C_REG_UE_FFD_127_96_INDX: 
      begin
        if (C_DQ_WIDTH == 144) begin
          assign we[j] = ue_clr_r;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = ue_set_i;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffm[3*C_DATA_WIDTH+:C_DATA_WIDTH];
        end
        else begin
          assign we[j] = 1'b0;
          assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
          assign we_int[j] = 1'b0;
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        end
      end
      C_REG_UE_FFE_INDX: 
      begin
        assign we[j] = ue_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ue_set_i;
        if (C_DQ_WIDTH == 144) begin
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {{C_DATA_WIDTH-C_ECC_WIDTH{1'b0}}, ffm[128+:C_ECC_WIDTH] };
        end
        else begin
          assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {{C_DATA_WIDTH-C_ECC_WIDTH{1'b0}}, ffm[ 64+:C_ECC_WIDTH] };
        end
      end
      C_REG_UE_FFA_31_00_INDX: 
      begin
        assign we[j] = ue_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ue_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffam[31:0];
      end

      C_REG_UE_FFA_63_32_INDX: 
      begin
        assign we[j] = ue_clr_r;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = ue_set_i;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = ffam[63:32];
      end

      C_REG_FI_D_31_00_INDX: 
      begin
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        //if (C_ECC_TEST == "ON") begin
          always @(posedge clk) begin
            fi_xor_we_r[0*C_DATA_WIDTH/8+:C_DATA_WIDTH/8] <= (reg_data_sel == j) ? {C_DATA_WIDTH/8{reg_data_write}} 
                                                                                      : {C_DATA_WIDTH/8{1'b0}};
            fi_xor_wrdata_r[0*C_DATA_WIDTH+:C_DATA_WIDTH] <= reg_data_in[C_DATA_WIDTH-1:0];
          end
        //end
      end
      C_REG_FI_D_63_32_INDX: 
      begin
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        //if (C_ECC_TEST == "ON") begin
          always @(posedge clk) begin
            fi_xor_we_r[1*C_DATA_WIDTH/8+:C_DATA_WIDTH/8] <= (reg_data_sel == j) ? {C_DATA_WIDTH/8{reg_data_write}} 
                                                                                      : {C_DATA_WIDTH/8{1'b0}};
            fi_xor_wrdata_r[1*C_DATA_WIDTH+:C_DATA_WIDTH] <= reg_data_in[C_DATA_WIDTH-1:0];
          end
        //end
      end
      C_REG_FI_D_95_64_INDX: 
      begin
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        if (C_DQ_WIDTH == 144 /*&& C_ECC_TEST == "ON"*/) begin
          always @(posedge clk) begin
            fi_xor_we_r[2*C_DATA_WIDTH/8+:C_DATA_WIDTH/8] <= (reg_data_sel == j) ? {C_DATA_WIDTH/8{reg_data_write}} 
                                                                                    : {C_DATA_WIDTH/8{1'b0}};
            fi_xor_wrdata_r[2*C_DATA_WIDTH+:C_DATA_WIDTH] <= reg_data_in[C_DATA_WIDTH-1:0];
          end
        end
      end
      C_REG_FI_D_127_96_INDX: 
      begin
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        if (C_DQ_WIDTH == 144 /*&& C_ECC_TEST == "ON"*/) begin
          always @(posedge clk) begin
            fi_xor_we_r[3*C_DATA_WIDTH/8+:C_DATA_WIDTH/8] <= (reg_data_sel == j) ? {C_DATA_WIDTH/8{reg_data_write}} 
                                                                                    : {C_DATA_WIDTH/8{1'b0}};
            fi_xor_wrdata_r[3*C_DATA_WIDTH+:C_DATA_WIDTH] <= reg_data_in[C_DATA_WIDTH-1:0];
          end
        end
      end
      C_REG_FI_ECC_INDX: 
      begin
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};

        if (C_DQ_WIDTH == 72 /*&& C_ECC_TEST == "ON"*/) begin
          always @(posedge clk) begin
            fi_xor_we_r[2*C_DATA_WIDTH/8+:P_FI_XOR_WE_WIDTH] <= (reg_data_sel == j) ? {P_FI_XOR_WE_WIDTH{reg_data_write}}
                                                                                    : {P_FI_XOR_WE_WIDTH{1'b0}};
            fi_xor_wrdata_r[2*C_DATA_WIDTH+:C_DQ_WIDTH%C_DATA_WIDTH] <= reg_data_in[C_DQ_WIDTH%C_DATA_WIDTH-1:0];
          end
        end
        if (C_DQ_WIDTH == 144 /*&& C_ECC_TEST == "ON"*/) begin
          always @(posedge clk) begin
            fi_xor_we_r[4*C_DATA_WIDTH/8+:P_FI_XOR_WE_WIDTH] <= (reg_data_sel == j) ? {P_FI_XOR_WE_WIDTH{reg_data_write}}
                                                                                    : {P_FI_XOR_WE_WIDTH{1'b0}};
            fi_xor_wrdata_r[4*C_DATA_WIDTH+:C_DQ_WIDTH%C_DATA_WIDTH] <= reg_data_in[C_DQ_WIDTH%C_DATA_WIDTH-1:0];
          end
        end
      end
      default: 
      begin
        // Tie off reg inputs 
        assign we[j] = 1'b0;
        assign data_in[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
        assign we_int[j] = 1'b0;
        assign data_in_int[j*C_DATA_WIDTH+:C_DATA_WIDTH] = {C_DATA_WIDTH{1'b0}};
      end
      endcase
    end


endgenerate 



    
   

endmodule

`default_nettype wire

