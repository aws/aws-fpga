/*----------------------------------------------------------------------------
 * Copyright (c) 2008 Xilinx, Inc.
 * This design is confidential and proprietary of Xilinx, All Rights Reserved.
 *-----------------------------------------------------------------------------
 *   ____  ____
 *  /   /\/   /
 * /___/  \  /   Vendor: Xilinx
 * \   \   \/    Date Created: 2008/08/18
 *  \   \        
 *  /   /        
 * /___/   /\    
 * \   \  /  \ 
 *  \___\/\___\
 * 
 *Device: All
 *Purpose:
 *  XSDB Slave Interface
 *Reference:
 *  XSDB v1.00a Specification.
 *    http://teamx/apd/seg/chipscope/dev/core_dev/spec/xsdb_spec/xsdb_v1.00a.doc
 *
 *----------------------------------------------------------------------------*/
`timescale 1ps / 1ps

`include "ddr4_v2_2_10_cs_ver_inc.vh"
`include "ddr4_v2_2_10_chipscope_icon2xsdb_mstrbr_ver_inc.vh"

(* dont_touch = "true" *)
module ddr4_v2_2_10_chipscope_xsdb_slave
  #(
    parameter C_XDEVICEFAMILY        = `FAMILY_KINTEXU,
    parameter [15:0]                        C_MAJOR_VERSION        = 11,  // ise major version
    parameter [7:0]                         C_MINOR_VERSION        = 1,   // ise minor version
    parameter C_BUILD_REVISION       = 0,   // ise service pack
    parameter [`GC_XSDB_S_DATA_WIDTH-1:0]   C_CORE_TYPE            = 1,   // root coregen type 
    parameter [7:0]                         C_CORE_MAJOR_VER       = 1,   // root coregen core major version
    parameter [7:0]                         C_CORE_MINOR_VER       = 0,   // root corgen core minor version
    parameter [`GC_XSDB_S_DATA_WIDTH-1:0]   C_XSDB_SLAVE_TYPE      = 1,   // XSDB Slave Type
    parameter [`GC_XSDB_S_DATA_WIDTH-1:0]   C_NEXT_SLAVE           = 0,   // Next slave Relative reference neighbor which is part of the core.
    parameter [`GC_XSDB_S_DATA_WIDTH-1:0]   C_CSE_DRV_VER          = 1,   // CSE Slave driver version
    parameter [0:0]                         C_USE_TEST_REG         = 1,   // Set to 1 to use test reg
    parameter C_PIPE_IFACE           = 1,   // Set to 1 to add pipe delay to XSDB interface signals
    parameter [8*`GC_XSDB_S_DATA_WIDTH-1:0] C_CORE_INFO1        = 0,
    parameter [8*`GC_XSDB_S_DATA_WIDTH-1:0] C_CORE_INFO2        = 0)
  (/* outputs */
   output wire s_rst_o,
   output wire s_dclk_o,
   output wire s_den_o,
   output wire s_dwe_o,
   output wire [`GC_XSDB_S_ADDR_WIDTH-1:0] s_daddr_o,
   output wire [`GC_XSDB_S_DATA_WIDTH-1:0] s_di_o,
   output wire [`GC_XSDB_S_OPORT_WIDTH-1:0] sl_oport_o,
   /* inputs */
   input [`GC_XSDB_S_DATA_WIDTH-1:0] s_do_i,
   input [`GC_XSDB_S_IPORT_WIDTH-1:0] sl_iport_i,
   input s_drdy_i
   );
  
  
  //
  // Removing xsdb_interface_buffers in order to support new stitcher
  //
  //wire [`GC_XSDB_S_IPORT_WIDTH-1:0] sl_iport;
  //wire [`GC_XSDB_S_OPORT_WIDTH-1:0] sl_oport;
  //xsdb_interface_buffers xsdb_interface_buffers_inst (
  //  .SL_OPORT_I(sl_oport),
  //  .SL_IPORT_O(sl_iport)
  //);
  
  /* Signals */
   wire s_rst;
   wire s_dclk;
   wire s_den;
   wire s_dwe;
   wire [`GC_XSDB_S_ADDR_WIDTH-1:0] s_daddr;
   wire [`GC_XSDB_S_DATA_WIDTH-1:0] s_di;
   wire [`GC_XSDB_S_DATA_WIDTH-1:0] s_do;
   wire s_drdy; 
  
  
    
  // Internal Signals
  reg [`GC_XSDB_S_DATA_WIDTH-1:0] reg_test = 'h0;
  reg [`GC_XSDB_S_DATA_WIDTH-1:0] reg_do   = 'h0;
  reg reg_drdy  = 1'b0;
  (* UUID *)(* DONT_TOUCH = "TRUE" *)reg [(8*`GC_XSDB_S_DATA_WIDTH)-1:0]uuid_stamp;
  wire status_addr_range;

  wire rst   ;
  wire dclk  ;
  wire den   ;
  wire dwe   ;
  wire [`GC_XSDB_S_ADDR_WIDTH-1:0] daddr;
  wire [`GC_XSDB_S_DATA_WIDTH-1:0] di;   
  wire [`GC_XSDB_S_DATA_WIDTH-1:0] do_i;   
  wire drdy;
  
  // Expand from IPORT to internal signals
  assign rst    = sl_iport_i[`GC_IPORT_RST_IDX];
  assign dclk   = sl_iport_i[`GC_IPORT_DCLK_IDX];
  assign den    = sl_iport_i[`GC_IPORT_DEN_IDX];
  assign dwe    = sl_iport_i[`GC_IPORT_DWE_IDX];
  assign daddr  = sl_iport_i[`GC_IPORT_DADDR_IDX+`GC_XSDB_S_ADDR_WIDTH-1:`GC_IPORT_DADDR_IDX];
  assign di     = sl_iport_i[`GC_IPORT_DI_IDX+`GC_XSDB_S_DATA_WIDTH-1:`GC_IPORT_DI_IDX];

  always @ (posedge dclk)
  begin
    uuid_stamp <= uuid_stamp;
  end
  
  // Compress internal signals to OPORT
  assign sl_oport_o = {do_i, drdy};
  
  //////////////////////////////////////////////////////////////////////////////
  // Internal DRDY signal- reduction AND of several bits
  assign status_addr_range = & daddr[`GC_XSDB_S_ADDR_WIDTH-1:8];

  // reg_drdy asserted when daddr is in the status address range and
  // den is asserted
  always @(posedge dclk)
  begin : P_REG_DRDY
    if (rst == 1'b1)
      reg_drdy <= 1'b0;
    else
      reg_drdy <= status_addr_range && den;
  end
  
  //////////////////////////////////////////////////////////////////////////////
  // Test Register
  always @(posedge dclk)
  begin : P_TEST_REG
    if (status_addr_range == 1'b1 && den == 1'b1 && dwe == 1'b1)
      reg_test <= di;
  end
  
  always @(posedge dclk)
  begin
    case (daddr[7:0])
      8'h00 : reg_do <= uuid_stamp[0*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h01 : reg_do <= uuid_stamp[1*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h02 : reg_do <= uuid_stamp[2*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h03 : reg_do <= uuid_stamp[3*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h04 : reg_do <= uuid_stamp[4*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h05 : reg_do <= uuid_stamp[5*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h06 : reg_do <= uuid_stamp[6*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h07 : reg_do <= uuid_stamp[7*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h08 : reg_do <= C_CORE_INFO2[0*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h09 : reg_do <= C_CORE_INFO2[1*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0A : reg_do <= C_CORE_INFO2[2*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0B : reg_do <= C_CORE_INFO2[3*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0C : reg_do <= C_CORE_INFO2[4*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0D : reg_do <= C_CORE_INFO2[5*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0E : reg_do <= C_CORE_INFO2[6*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];
      8'h0F : reg_do <= C_CORE_INFO2[7*`GC_XSDB_S_DATA_WIDTH+:`GC_XSDB_S_DATA_WIDTH];      
      8'hF0 : reg_do <= C_XSDB_SLAVE_TYPE;
      8'hF1 : reg_do <= C_CSE_DRV_VER;
      8'hF2 : reg_do <= C_CORE_TYPE;
      8'hF3 : reg_do <= {C_CORE_MAJOR_VER, C_CORE_MINOR_VER};
      8'hF4 : reg_do <= {7'h0, C_USE_TEST_REG, C_MINOR_VERSION};
      8'hF5 : reg_do <= {C_MAJOR_VERSION};
      8'hF6 : reg_do <= reg_test;
      8'hF7 : reg_do <= C_NEXT_SLAVE;
      default : reg_do <= C_XSDB_SLAVE_TYPE;
    endcase
  end
  
  //////////////////////////////////////////////////////////////////////////////
  // clk and rst always attached to port directly
  assign s_dclk_o  = dclk;
  assign s_rst_o   = rst;
  
  //////////////////////////////////////////////////////////////////////////////
  // Attach non info slave signals to the bus
  //  This is the non-piped connection
  generate
    if (C_PIPE_IFACE == 0)
    begin : G_NOPIPE_IFACE
      assign s_den_o   = den && !status_addr_range;
      assign s_dwe_o   = dwe;
      assign s_daddr_o = daddr;
      assign s_di_o    = di;
      assign drdy      = reg_drdy == 1'b1 ? 1'b1 : s_drdy_i;
      assign do_i      = reg_drdy == 1'b1 ? reg_do : s_do_i;
    end
    else
    begin : G_1PIPE_IFACE
      reg s_den_r = 1'b0;
      reg s_dwe_r = 1'b0;
      reg s_drdy_r = 1'b0;
      reg [`GC_XSDB_S_ADDR_WIDTH-1:0] s_daddr_r = 'h0;
      reg [`GC_XSDB_S_DATA_WIDTH-1:0] s_di_r = 'h0;
      reg [`GC_XSDB_S_DATA_WIDTH-1:0] s_do_r = 'h0;
       
      always @(posedge dclk)
      begin : P_PIPE_DELAY
        if (rst == 1'b1)
        begin
          s_den_r <= 1'b0;
          s_dwe_r <= 1'b0;
          s_drdy_r <= 1'b0;
        end
        else
        begin
          s_den_r <= den && !status_addr_range;
          s_dwe_r <= dwe;
          if (reg_drdy == 1'b1)
            s_drdy_r <= 1'b1;
          else
            s_drdy_r <= s_drdy_i;
        end
        s_daddr_r <= daddr;
        s_di_r <= di;
        if (reg_drdy == 1'b1)
          s_do_r <= reg_do;
        else
          s_do_r <= s_do_i;
      end
              
      assign s_den_o   = s_den_r;
      assign s_dwe_o   = s_dwe_r;
      assign s_daddr_o = s_daddr_r;
      assign s_di_o    = s_di_r;
      assign drdy      = s_drdy_r;
      assign do_i      = s_do_r;
    end
  endgenerate    
     
                                     
endmodule
  

