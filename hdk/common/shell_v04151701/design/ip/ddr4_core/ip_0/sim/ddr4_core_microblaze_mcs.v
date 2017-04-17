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

`timescale 1ns/1ps

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
