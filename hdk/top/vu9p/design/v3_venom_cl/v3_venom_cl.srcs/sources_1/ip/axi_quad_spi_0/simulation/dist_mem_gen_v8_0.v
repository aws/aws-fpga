/*
 *******************************************************************************
 *
 * Distributed Memory Generator - Verilog Behavioral Model
 *
 *******************************************************************************
 *
 * (c) Copyright 1995 - 2009 Xilinx, Inc. All rights reserved.
 *
 * This file contains confidential and proprietary information
 * of Xilinx, Inc. and is protected under U.S. and
 * international copyright and other intellectual property
 * laws.
 *
 * DISCLAIMER
 * This disclaimer is not a license and does not grant any
 * rights to the materials distributed herewith. Except as
 * otherwise provided in a valid license issued to you by
 * Xilinx, and to the maximum extent permitted by applicable
 * law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
 * WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
 * AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
 * BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
 * INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
 * (2) Xilinx shall not be liable (whether in contract or tort,
 * including negligence, or under any other theory of
 * liability) for any loss or damage of any kind or nature
 * related to, arising under or in connection with these
 * materials, including for any direct, or any indirect,
 * special, incidental, or consequential loss or damage
 * (including loss of data, profits, goodwill, or any type of
 * loss or damage suffered as a result of any action brought
 * by a third party) even if such damage or loss was
 * reasonably foreseeable or Xilinx had been advised of the
 * possibility of the same.
 *
 * CRITICAL APPLICATIONS
 * Xilinx products are not designed or intended to be fail-
 * safe, or for use in any application requiring fail-safe
 * performance, such as life-support or safety devices or
 * systems, Class III medical devices, nuclear facilities,
 * applications related to the deployment of airbags, or any
 * other applications that could lead to death, personal
 * injury, or severe property or environmental damage
 * (individually and collectively, "Critical
 * Applications"). Customer assumes the sole risk and
 * liability of any use of Xilinx products in Critical
 * Applications, subject only to applicable laws and
 * regulations governing limitations on product liability.
 *
 * THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
 * PART OF THIS FILE AT ALL TIMES.
 *
 *******************************************************************************
 *******************************************************************************
 *
 * Filename    : dist_mem_gen_v8_0_11.v
 *
 * Author      : Xilinx
 *
 * Description : Distributed Memory Simulation Model
 *
 *******************************************************************************
 */

`timescale 1ps/1ps
`ifndef TCQ
 `define TCQ 100
`endif

`define all0s {C_WIDTH{1'b0}}
`define allXs {C_WIDTH{1'bx}}
`define c_rom 0
`define c_sp_ram 1
`define c_dp_ram 2
`define c_sdp_ram 4

module dist_mem_gen_v8_0_11 (a, d, dpra, clk, we, i_ce, qspo_ce, qdpo_ce, qdpo_clk, qspo_rst, qdpo_rst, qspo_srst, qdpo_srst, spo, dpo, qspo, qdpo);

   parameter C_FAMILY             = "virtex5";
   parameter C_ADDR_WIDTH         = 6;
   parameter C_DEFAULT_DATA       = "0";
   parameter C_ELABORATION_DIR    = "./";
   parameter C_DEPTH              = 64;
   parameter C_HAS_CLK            = 1;
   parameter C_HAS_D              = 1;
   parameter C_HAS_DPO            = 0;
   parameter C_HAS_DPRA           = 0;
   parameter C_HAS_I_CE           = 0;
   parameter C_HAS_QDPO           = 0;
   parameter C_HAS_QDPO_CE        = 0;
   parameter C_HAS_QDPO_CLK       = 0;
   parameter C_HAS_QDPO_RST       = 0;
   parameter C_HAS_QDPO_SRST      = 0;
   parameter C_HAS_QSPO           = 0;
   parameter C_HAS_QSPO_CE        = 0;
   parameter C_HAS_QSPO_RST       = 0;
   parameter C_HAS_QSPO_SRST      = 0;
   parameter C_HAS_SPO            = 1;
   parameter C_HAS_WE             = 1;
   parameter C_MEM_INIT_FILE      = "null.mif";
   parameter C_MEM_TYPE           = 1;
   parameter C_PIPELINE_STAGES    = 0;
   parameter C_QCE_JOINED         = 0;
   parameter C_QUALIFY_WE         = 0;
   parameter C_READ_MIF           = 0;
   parameter C_REG_A_D_INPUTS     = 0;
   parameter C_REG_DPRA_INPUT     = 0;
   parameter C_SYNC_ENABLE        = 0;
   parameter C_WIDTH              = 16;
   parameter C_PARSER_TYPE        = 1;
     
   input  [C_ADDR_WIDTH-1:0] a;
   input  [C_WIDTH-1 : 0] d;
   input  [C_ADDR_WIDTH-1 : 0] dpra;
   input  clk;
   input  we;
   input  i_ce;
   input  qspo_ce;
   input  qdpo_ce;
   input  qdpo_clk;
   input  qspo_rst;
   input  qdpo_rst;
   input  qspo_srst;
   input  qdpo_srst;
   output [C_WIDTH-1 : 0] spo;
   output [C_WIDTH-1 : 0] qspo;
   output [C_WIDTH-1 : 0] dpo;
   output [C_WIDTH-1 : 0] qdpo;

   // Address signal connected to memory
   wire [C_ADDR_WIDTH - 1 : 0] a_int;
   
   // Input data signal connected to memory
   wire [C_WIDTH - 1 : 0] d_int;

   // Internal Write Enable
   wire 		       we_int;

   // Internal QSPO Clock Enable
   wire 		       qspo_ce_int;

   // Internal QDPO Clock
   wire 		       qdpo_clk_int;

   // Internal Dual Port Read Address connected to memory
   wire [C_ADDR_WIDTH - 1 : 0] dpra_int;

   // Internal QDPO Clock Enable
   wire 		       qdpo_ce_int;

   // Registered Write Enable
   reg 			       we_reg;

   // Registered Address connected to memory
   reg [C_ADDR_WIDTH - 1 : 0]  a_reg;

   // Registered data signal connected to memory
   reg [C_WIDTH-1 : 0] 	       d_reg;

   // Registered QSPO Clock Enable
   reg 			       qspo_ce_reg;

   // Registered Dual Port Read Address connected to memory
   reg [C_ADDR_WIDTH - 1 : 0]  dpra_reg;

   // Registered QDPO Clock Enable
   reg 			       qdpo_ce_reg;

   // Internal Single Port RAM output signal
   wire [C_WIDTH - 1 : 0]       spo_int;

   // Internal Dual Port RAM output signal
   wire [C_WIDTH - 1 : 0]       dpo_int;

   // Internal ROM/Single Port RAM
   //  registered output
   reg [C_WIDTH - 1 : 0]       qspo_int;

   // Pipeline registers
   reg [C_WIDTH - 1 : 0]       qspo_pipe;
   
   // Internal Dual Port RAM registered output
   reg [C_WIDTH - 1 : 0]       qdpo_int;

   // Pipeline registers
   reg [C_WIDTH - 1 : 0]       qdpo_pipe;
   
   reg [C_WIDTH-1 : 0] 	       ram_data [(2**C_ADDR_WIDTH)-1 : 0];
   reg [C_WIDTH-1 : 0] 	       ram_data_tmp[C_DEPTH-1 : 0];
   
  
   reg [C_WIDTH-1 : 0] 	       default_data;
   
   wire [C_WIDTH-1 : 0]        data_sp;  
   wire [C_WIDTH-1 : 0]        data_dp;

   wire [C_WIDTH-1 : 0]        data_sp_over;  
   wire [C_WIDTH-1 : 0]        data_dp_over;

   wire [C_ADDR_WIDTH - 1 : 0] a_over;
   wire [C_ADDR_WIDTH - 1 : 0] dpra_over;   

   wire 		       a_is_over;
   wire 		       dpra_is_over;
   
   reg [C_ADDR_WIDTH-1 : 0]    max_address;
   
   integer 		       i;
   integer 		       j;   

            
   // Initial block - initialise the memory,
   // and when appropriate write content into the given address.
   initial
     begin
	$display("WARNING: This core is supplied with a behavioral model. To model cycle-accurate behavior you must run timing simulation.");
	

	default_data = 'b0;
	default_data = binstr_conv(C_DEFAULT_DATA);       	
	
        // Assign that C_DEFAULT_DATA to each address in the memory.
        for (i = 0; i < C_DEPTH; i = i + 1)
	  begin
	     ram_data[i] = default_data;
	     ram_data_tmp[i] = default_data;
	  end	      

        //Read the MIF file, and use it to initialise the content of ram_data
        //if that is required.
        if (C_READ_MIF)
	  begin
	     $readmemb(C_MEM_INIT_FILE, ram_data_tmp, 0, C_DEPTH-1);
    
	     for (i = 0; i < C_DEPTH; i = i + 1)    
		  ram_data[i] = ram_data_tmp[i];

	  end
	
	if (C_DEPTH != (2**C_ADDR_WIDTH))
          begin
	     for (i = C_DEPTH; i < (2**C_ADDR_WIDTH); i = i + 1)
	       ram_data[i] = 'b0;	     
	  end

	a_reg       = 'b0;
	we_reg      = 1'b0;
	d_reg       = 'b0;
	qspo_ce_reg = 1'b0;
	dpra_reg    = 'b0;
	qdpo_ce_reg = 1'b0;

        qspo_int = default_data;
	qspo_pipe = 'b0;
        qdpo_int = default_data;
	qdpo_pipe = 'b0;

        max_address = C_DEPTH-1;

	
     end // initial begin  
   
   // Now look for writes to the memory (note that this means the
   // memory is not a ROM and that the Write Enable WE is active.
   always@(posedge clk)
     begin
	if (C_MEM_TYPE != `c_rom && we_int)
	  begin
	     if (a_is_over)
	       begin
		  $display("WARNING in %m at time %d ns", $time);
		  $write("Writing to out of range address. ");
		  $display("Max address in %m is %d", C_DEPTH-1);
		  $display("Write will be ignored.");
	       end
	     else
	       ram_data[a_int] <= #`TCQ d_int;
	  end // if (C_MEM_TYPE != `c_rom && we_int)
     end // always@ (posedge CLK)
   	 
   // Model optional input registers, which operate in the CLK clock domain.
   always @(posedge clk)
     begin
        if (C_MEM_TYPE == 0) begin // ROM
          if (C_HAS_QSPO_CE == 1) begin
            if (qspo_ce == 1)
              a_reg  <= #`TCQ a;
          end else
    	     a_reg  <= #`TCQ a;
        end else if (!C_HAS_I_CE)
	  begin
	     we_reg <= #`TCQ we;
    	     a_reg  <= #`TCQ a;
	     d_reg <= #`TCQ d;
	  end
	else if (!C_QUALIFY_WE)
	  begin
	     we_reg <= #`TCQ we;
	     if (i_ce)
	       begin
		  a_reg <= #`TCQ a;
		  d_reg <= #`TCQ d;
	       end
	  end
	else if (C_QUALIFY_WE)
	  if (i_ce)
	    begin
	       we_reg <= #`TCQ we;
	       a_reg <= #`TCQ a;
	       d_reg <= #`TCQ d;
	    end

	qspo_ce_reg <= #`TCQ qspo_ce;
     end // always @ (posedge CLK)
   
      
   assign we_int      = (C_HAS_WE ? (C_REG_A_D_INPUTS ? we_reg : we) : 1'b0);
   assign d_int       = (C_MEM_TYPE > 0 ? (C_REG_A_D_INPUTS ? d_reg : d) : 'b0);   
   assign a_int       = (C_REG_A_D_INPUTS ? a_reg : a);
   
   assign qspo_ce_int = (C_HAS_QSPO_CE ? (C_REG_A_D_INPUTS ? qspo_ce_reg : qspo_ce) : 1'b0);   

   assign qdpo_clk_int = (((C_MEM_TYPE == `c_dp_ram) || (C_MEM_TYPE == `c_sdp_ram)) ? 
      (C_HAS_QDPO_CLK == 1 ? qdpo_clk : clk) : 1'b0);   
   
   always@(posedge qdpo_clk_int)
     begin
        if (C_QCE_JOINED)
	  begin
	     if (!C_HAS_QSPO_CE)
	       dpra_reg <= #`TCQ dpra;
	     else if (qspo_ce)
	       dpra_reg <= #`TCQ dpra;
	  end
	else
	  begin
	     if (!C_HAS_QDPO_CE)
	       dpra_reg <= #`TCQ dpra;
	     else if (qdpo_ce)
	       dpra_reg <= #`TCQ dpra;
	  end // else: !if(C_QCE_JOINED)

	qdpo_ce_reg <= #`TCQ qdpo_ce;

     end // always@ (posedge qdpo_clk_int)

   assign dpra_int    = (((C_MEM_TYPE == `c_dp_ram) || (C_MEM_TYPE == `c_sdp_ram)) ? 
      (C_REG_DPRA_INPUT == 1 ? dpra_reg : dpra) : 1'b0);
     
   assign qdpo_ce_int = (((C_MEM_TYPE == `c_dp_ram) || (C_MEM_TYPE == `c_sdp_ram)) ? 
     (C_HAS_QDPO_CE ? (C_REG_DPRA_INPUT ? qdpo_ce_reg : qdpo_ce) : 1'b0) : 1'b0);
   
   always@(posedge a_is_over)
     begin
	$display("WARNING in %m at time %d ns: ", $time);
	$write("Reading from out-of-range address. ");
	$display("Max address in %m is %d", C_DEPTH-1);
     end // always@ (a_int or posedge CLK)
   
   assign spo = (C_HAS_SPO ? spo_int : `allXs);

   always@(posedge dpra_is_over)
     begin
	if ((C_MEM_TYPE == `c_dp_ram) || (C_MEM_TYPE == `c_sdp_ram))
	  begin
	     $display("WARNING in %m at time %d ns: ", $time);
	     $write("Reading from out-of-range address. ");
	     $display("Max address in %m is %d", C_DEPTH-1);
	  end // if (C_MEM_TYPE == `c_dp_ram)
     end // always@ (dpra_int)

   assign spo_int = (a_is_over ? data_sp_over : data_sp);
   
   assign dpo_int = (((C_MEM_TYPE == `c_dp_ram) || (C_MEM_TYPE == `c_sdp_ram)) ? (dpra_is_over ? data_dp_over : data_dp) : `allXs);	

   assign data_sp  = ram_data[a_int];
   assign data_dp  = ram_data[dpra_int];

   assign a_is_over    = (a_int > max_address ? 1'b1 : 1'b0);
   assign dpra_is_over = (dpra_int > max_address ? 1'b1 : 1'b0);

   assign a_over    = a_int & max_address;
   assign dpra_over = dpra_int & max_address;

   assign data_sp_over = 'bx;
   assign data_dp_over = 'bx;
      
   assign dpo = (C_HAS_DPO ? dpo_int : `allXs);

   always@(posedge clk or posedge qspo_rst)
     begin
	if (C_HAS_QSPO_RST && qspo_rst)
	  begin
	     qspo_pipe <= 'b0;
	     qspo_int <= 'b0;
	  end
	else if (C_HAS_QSPO_SRST && qspo_srst)
	  begin
	     if (!C_HAS_QSPO_CE)
	       begin
		  qspo_pipe <= #`TCQ 'b0;
		  qspo_int <= #`TCQ 'b0;
	       end
	     else if (!C_SYNC_ENABLE)
	       begin
		  qspo_pipe <= #`TCQ 'b0;
		  qspo_int <= #`TCQ 'b0;
	       end
	     else if (C_HAS_QSPO_CE && qspo_ce_int)
	       begin
		  qspo_pipe <= #`TCQ 'b0;
		  qspo_int <= #`TCQ 'b0;
	       end
	  end // if (C_HAS_QSPO_SRST && QSPO_SRST)

	else if (C_HAS_QSPO_CE && qspo_ce_int)
	  begin
	     if (C_PIPELINE_STAGES == 1)
	       begin
		  qspo_int <= #`TCQ qspo_pipe;
	       end
	     else
	       begin
		  qspo_int <= #`TCQ spo_int;
	       end
	     qspo_pipe <= #`TCQ spo_int;
          end
	else if (!C_HAS_QSPO_CE)
	  begin
	     if (C_PIPELINE_STAGES == 1)
	       begin
		  qspo_int <= #`TCQ qspo_pipe;
	       end
	     else
	       begin
		  qspo_int <= #`TCQ spo_int;
	       end
	     qspo_pipe <= #`TCQ spo_int;
	  end // if (!C_HAS_QSPO_CE)
     end // always@ (posedge CLK or QSPO_RST)

   assign qspo = (C_HAS_QSPO == 1 ? qspo_int : `allXs);   

   always@(posedge qdpo_clk_int or posedge qdpo_rst)
     begin
	if (C_HAS_QDPO_RST && qdpo_rst)
	  begin
	     qdpo_pipe <= 'b0;
	     qdpo_int <= 'b0;
	  end
	else if (C_HAS_QDPO_SRST && qdpo_srst)
	  begin
	     if (!C_SYNC_ENABLE)
	       begin
		  qdpo_pipe <= #`TCQ 'b0;
		  qdpo_int <= #`TCQ 'b0;
	       end
	     else if (!C_QCE_JOINED)
	       begin
		  if (!C_HAS_QDPO_CE)
		    begin
		       qdpo_pipe <= #`TCQ 'b0;
		       qdpo_int <= #`TCQ 'b0;
		    end
		  else if (C_HAS_QDPO_CE && qdpo_ce_int)
		    begin
		       qdpo_pipe <= #`TCQ 'b0;
		       qdpo_int <= #`TCQ 'b0;
		    end
	       end
	     else
	       begin
		  if (!C_HAS_QSPO_CE)
		    begin
		       qdpo_pipe <= #`TCQ 'b0;
		       qdpo_int <= #`TCQ 'b0;
		    end
		  else if (C_HAS_QSPO_CE && qspo_ce_int)
		    begin
		       qdpo_pipe <= #`TCQ 'b0;
		       qdpo_int <= #`TCQ 'b0;
		    end
	       end
	  end // if (C_HAS_QDPO_SRST && QDPO_SRST)
	
	else if (!C_QCE_JOINED)
	  begin
	     if (!C_HAS_QDPO_CE)
	       begin
		  qdpo_pipe <= #`TCQ dpo_int;
		  if (C_PIPELINE_STAGES == 1)
		    begin
		       qdpo_int <= #`TCQ qdpo_pipe;
		    end
		  else
		    begin
		       qdpo_int <= #`TCQ dpo_int;
		    end
	       end // if (!C_HAS_QDPO_CE)
	     else if (C_HAS_QDPO_CE && qdpo_ce_int)
	       begin
		  qdpo_pipe <= #`TCQ dpo_int;
		  if (C_PIPELINE_STAGES == 1)
		    begin
		       qdpo_int <= #`TCQ qdpo_pipe;
		    end
		  else
		    begin
		       qdpo_int <= #`TCQ dpo_int;
		    end
	       end // if (C_HAS_QDPO_CE && qdpo_ce_int)
	  end // if (!C_QCE_JOINED)
	else if (C_QCE_JOINED)
	  begin
	     if (C_HAS_QSPO_CE && qspo_ce_int)
	       begin
		  qdpo_pipe <= #`TCQ dpo_int;
		  if (C_PIPELINE_STAGES == 1)
		    begin
		       qdpo_int <= #`TCQ qdpo_pipe;
		    end
		  else
		    begin
		       qdpo_int <= #`TCQ dpo_int;
		    end
	       end // if (C_HAS_QSPO_CE && qspo_ce_int)
	     else if (!C_HAS_QSPO_CE)
	       begin
		  qdpo_pipe <= #`TCQ dpo_int;
		  if (C_PIPELINE_STAGES == 1)
		    begin
		       qdpo_int <= #`TCQ qdpo_pipe;
		    end
		  else
		    begin
		       qdpo_int <= #`TCQ dpo_int;
		    end
	       end // if (!C_HAS_QSPO_CE)
	  end // if (C_QCE_JOINED)
     end // always@ (posedge qdpo_clk_int or posedge QDPO_RST)

   assign qdpo = (C_HAS_QDPO == 1 ? qdpo_int : `allXs);

   function [C_WIDTH - 1 : 0] binstr_conv;
      input [(C_WIDTH * 8) - 1 : 0] def_data;
      integer index,i;
      begin
	 index = 0;
	 binstr_conv = 'b0;	 
	 
         for (i=C_WIDTH-1; i>=0; i=i-1)
	   begin
	      case (def_data[7:0])
		8'b00000000 : i = -1;
		8'b00110000 : binstr_conv[index] = 1'b0;
		8'b00110001 : binstr_conv[index] = 1'b1;
		default :
		  begin
		     $display("ERROR in %m at time %d ns: NOT A BINARY CHARACTER", $time);
		     binstr_conv[index] = 1'bx;
		  end
	      endcase // case(def_data[7:0])

	      index = index + 1;
	      def_data = def_data >> 8;
	   end // for (i=C_WIDTH-1; i>=0; i=i-1)	 
	 
      end
   endfunction // binstr_conv      

endmodule // dist_mem_gen_v8_0_11

`undef all0s
`undef allXs
`undef c_rom
`undef c_sp_ram
`undef c_dp_ram
`undef c_sdp_ram
