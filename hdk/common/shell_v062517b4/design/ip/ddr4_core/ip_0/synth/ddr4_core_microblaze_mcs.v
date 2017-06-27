// (c) Copyright 1995-2017 Xilinx, Inc. All rights reserved.
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
// DO NOT MODIFY THIS FILE.


// IP VLNV: xilinx.com:ip:microblaze_mcs:3.0
// IP Revision: 4

(* X_CORE_INFO = "bd_bf3f,Vivado 2017.1_sdxop" *)
(* CHECK_LICENSE_TYPE = "ddr4_core_microblaze_mcs,bd_bf3f,{}" *)
(* CORE_GENERATION_INFO = "ddr4_core_microblaze_mcs,bd_bf3f,{x_ipProduct=Vivado 2017.1_sdxop,x_ipVendor=xilinx.com,x_ipLibrary=ip,x_ipName=microblaze_mcs,x_ipVersion=3.0,x_ipCoreRevision=4,x_ipLanguage=VERILOG,x_ipSimLanguage=MIXED,JTAG_CHAIN=2,MICROBLAZE_INSTANCE=microblaze_0,AVOID_PRIMITIVES=0,PATH=mcs_0,FREQ=100.0,OPTIMIZATION=1,DEBUG_ENABLED=0,TRACE=1,ECC=0,MEMSIZE=98304,USE_IO_BUS=1,USE_UART_RX=0,USE_UART_TX=0,UART_BAUDRATE=9600,UART_PROG_BAUDRATE=0,UART_DATA_BITS=8,UART_USE_PARITY=0,UART_ODD_PARITY=0,UART_RX_INTERRU\
PT=0,UART_TX_INTERRUPT=0,UART_ERROR_INTERRUPT=0,USE_FIT1=0,FIT1_No_CLOCKS=6216,FIT1_INTERRUPT=0,USE_FIT2=0,FIT2_No_CLOCKS=6216,FIT2_INTERRUPT=0,USE_FIT3=0,FIT3_No_CLOCKS=6216,FIT3_INTERRUPT=0,USE_FIT4=0,FIT4_No_CLOCKS=6216,FIT4_INTERRUPT=0,USE_PIT1=0,PIT1_SIZE=32,PIT1_READABLE=1,PIT1_PRESCALER=0,PIT1_INTERRUPT=0,USE_PIT2=0,PIT2_SIZE=32,PIT2_READABLE=1,PIT2_PRESCALER=0,PIT2_INTERRUPT=0,USE_PIT3=0,PIT3_SIZE=32,PIT3_READABLE=1,PIT3_PRESCALER=0,PIT3_INTERRUPT=0,USE_PIT4=0,PIT4_SIZE=32,PIT4_READABLE=\
1,PIT4_PRESCALER=0,PIT4_INTERRUPT=0,USE_GPO1=0,GPO1_SIZE=32,GPO1_INIT=0x00000000,USE_GPO2=0,GPO2_SIZE=32,GPO2_INIT=0x00000000,USE_GPO3=0,GPO3_SIZE=32,GPO3_INIT=0x00000000,USE_GPO4=0,GPO4_SIZE=32,GPO4_INIT=0x00000000,USE_GPI1=0,GPI1_SIZE=32,GPI1_INTERRUPT=0,USE_GPI2=0,GPI2_SIZE=32,GPI2_INTERRUPT=0,USE_GPI3=0,GPI3_SIZE=32,GPI3_INTERRUPT=0,USE_GPI4=0,GPI4_SIZE=32,GPI4_INTERRUPT=0,INTC_USE_EXT_INTR=0,INTC_INTR_SIZE=1,INTC_LEVEL_EDGE=0x0000,INTC_POSITIVE=0xFFFF,INTC_ASYNC_INTR=0xFFFF,INTC_NUM_SYNC_FF\
=2,Component_Name=ddr4_core_microblaze_mcs,USE_BOARD_FLOW=false,CLK_BOARD_INTERFACE=Custom,RESET_BOARD_INTERFACE=Custom,GPIO1_BOARD_INTERFACE=Custom,GPIO2_BOARD_INTERFACE=Custom,GPIO3_BOARD_INTERFACE=Custom,GPIO4_BOARD_INTERFACE=Custom,UART_BOARD_INTERFACE=Custom}" *)
(* DowngradeIPIdentifiedWarnings = "yes" *)
module ddr4_core_microblaze_mcs (
  Clk,
  Reset,
  TRACE_data_access,
  TRACE_data_address,
  TRACE_data_byte_enable,
  TRACE_data_read,
  TRACE_data_write,
  TRACE_data_write_value,
  TRACE_dcache_hit,
  TRACE_dcache_rdy,
  TRACE_dcache_read,
  TRACE_dcache_req,
  TRACE_delay_slot,
  TRACE_ex_piperun,
  TRACE_exception_kind,
  TRACE_exception_taken,
  TRACE_icache_hit,
  TRACE_icache_rdy,
  TRACE_icache_req,
  TRACE_instruction,
  TRACE_jump_hit,
  TRACE_jump_taken,
  TRACE_mb_halted,
  TRACE_mem_piperun,
  TRACE_msr_reg,
  TRACE_new_reg_value,
  TRACE_of_piperun,
  TRACE_pc,
  TRACE_pid_reg,
  TRACE_reg_addr,
  TRACE_reg_write,
  TRACE_valid_instr,
  IO_addr_strobe,
  IO_address,
  IO_byte_enable,
  IO_read_data,
  IO_read_strobe,
  IO_ready,
  IO_write_data,
  IO_write_strobe
);

(* X_INTERFACE_INFO = "xilinx.com:signal:clock:1.0 CLK.Clk CLK" *)
input wire Clk;
(* X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 RST.Reset RST" *)
input wire Reset;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_ACCESS" *)
output wire TRACE_data_access;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_ADDRESS" *)
output wire [0 : 31] TRACE_data_address;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_BYTE_ENABLE" *)
output wire [0 : 3] TRACE_data_byte_enable;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_READ" *)
output wire TRACE_data_read;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_WRITE" *)
output wire TRACE_data_write;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DATA_WRITE_VALUE" *)
output wire [0 : 31] TRACE_data_write_value;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DCACHE_HIT" *)
output wire TRACE_dcache_hit;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DCACHE_RDY" *)
output wire TRACE_dcache_rdy;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DCACHE_READ" *)
output wire TRACE_dcache_read;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DCACHE_REQ" *)
output wire TRACE_dcache_req;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE DELAY_SLOT" *)
output wire TRACE_delay_slot;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE EX_PIPERUN" *)
output wire TRACE_ex_piperun;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE EXCEPTION_KIND" *)
output wire [0 : 4] TRACE_exception_kind;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE EXCEPTION_TAKEN" *)
output wire TRACE_exception_taken;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE ICACHE_HIT" *)
output wire TRACE_icache_hit;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE ICACHE_RDY" *)
output wire TRACE_icache_rdy;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE ICACHE_REQ" *)
output wire TRACE_icache_req;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE INSTRUCTION" *)
output wire [0 : 31] TRACE_instruction;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE JUMP_HIT" *)
output wire TRACE_jump_hit;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE JUMP_TAKEN" *)
output wire TRACE_jump_taken;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE MB_HALTED" *)
output wire TRACE_mb_halted;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE MEM_PIPERUN" *)
output wire TRACE_mem_piperun;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE MSR_REG" *)
output wire [0 : 14] TRACE_msr_reg;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE NEW_REG_VALUE" *)
output wire [0 : 31] TRACE_new_reg_value;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE OF_PIPERUN" *)
output wire TRACE_of_piperun;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE PC" *)
output wire [0 : 31] TRACE_pc;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE PID_REG" *)
output wire [0 : 7] TRACE_pid_reg;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE REG_ADDR" *)
output wire [0 : 4] TRACE_reg_addr;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE REG_WRITE" *)
output wire TRACE_reg_write;
(* X_INTERFACE_INFO = "xilinx.com:interface:mbtrace:2.0 TRACE VALID_INSTR" *)
output wire TRACE_valid_instr;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO ADDR_STROBE" *)
output wire IO_addr_strobe;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO ADDRESS" *)
output wire [31 : 0] IO_address;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO BYTE_ENABLE" *)
output wire [3 : 0] IO_byte_enable;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO READ_DATA" *)
input wire [31 : 0] IO_read_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO READ_STROBE" *)
output wire IO_read_strobe;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO READY" *)
input wire IO_ready;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO WRITE_DATA" *)
output wire [31 : 0] IO_write_data;
(* X_INTERFACE_INFO = "xilinx.com:interface:mcsio_bus:1.0 IO WRITE_STROBE" *)
output wire IO_write_strobe;

  bd_bf3f inst (
    .Clk(Clk),
    .Reset(Reset),
    .TRACE_data_access(TRACE_data_access),
    .TRACE_data_address(TRACE_data_address),
    .TRACE_data_byte_enable(TRACE_data_byte_enable),
    .TRACE_data_read(TRACE_data_read),
    .TRACE_data_write(TRACE_data_write),
    .TRACE_data_write_value(TRACE_data_write_value),
    .TRACE_dcache_hit(TRACE_dcache_hit),
    .TRACE_dcache_rdy(TRACE_dcache_rdy),
    .TRACE_dcache_read(TRACE_dcache_read),
    .TRACE_dcache_req(TRACE_dcache_req),
    .TRACE_delay_slot(TRACE_delay_slot),
    .TRACE_ex_piperun(TRACE_ex_piperun),
    .TRACE_exception_kind(TRACE_exception_kind),
    .TRACE_exception_taken(TRACE_exception_taken),
    .TRACE_icache_hit(TRACE_icache_hit),
    .TRACE_icache_rdy(TRACE_icache_rdy),
    .TRACE_icache_req(TRACE_icache_req),
    .TRACE_instruction(TRACE_instruction),
    .TRACE_jump_hit(TRACE_jump_hit),
    .TRACE_jump_taken(TRACE_jump_taken),
    .TRACE_mb_halted(TRACE_mb_halted),
    .TRACE_mem_piperun(TRACE_mem_piperun),
    .TRACE_msr_reg(TRACE_msr_reg),
    .TRACE_new_reg_value(TRACE_new_reg_value),
    .TRACE_of_piperun(TRACE_of_piperun),
    .TRACE_pc(TRACE_pc),
    .TRACE_pid_reg(TRACE_pid_reg),
    .TRACE_reg_addr(TRACE_reg_addr),
    .TRACE_reg_write(TRACE_reg_write),
    .TRACE_valid_instr(TRACE_valid_instr),
    .IO_addr_strobe(IO_addr_strobe),
    .IO_address(IO_address),
    .IO_byte_enable(IO_byte_enable),
    .IO_read_data(IO_read_data),
    .IO_read_strobe(IO_read_strobe),
    .IO_ready(IO_ready),
    .IO_write_data(IO_write_data),
    .IO_write_strobe(IO_write_strobe)
  );
endmodule
