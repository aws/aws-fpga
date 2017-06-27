//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1_sdxop (lin64) Build 1893406 Sat May 27 14:00:24 MDT 2017
//Date        : Fri Jun  9 11:26:54 2017
//Host        : ip-10-206-20-5 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_bf3f_wrapper.bd
//Design      : bd_bf3f_wrapper
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

module bd_bf3f_wrapper
   (Clk,
    IO_addr_strobe,
    IO_address,
    IO_byte_enable,
    IO_read_data,
    IO_read_strobe,
    IO_ready,
    IO_write_data,
    IO_write_strobe,
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
    TRACE_valid_instr);
  input Clk;
  output IO_addr_strobe;
  output [31:0]IO_address;
  output [3:0]IO_byte_enable;
  input [31:0]IO_read_data;
  output IO_read_strobe;
  input IO_ready;
  output [31:0]IO_write_data;
  output IO_write_strobe;
  input Reset;
  output TRACE_data_access;
  output [0:31]TRACE_data_address;
  output [0:3]TRACE_data_byte_enable;
  output TRACE_data_read;
  output TRACE_data_write;
  output [0:31]TRACE_data_write_value;
  output TRACE_dcache_hit;
  output TRACE_dcache_rdy;
  output TRACE_dcache_read;
  output TRACE_dcache_req;
  output TRACE_delay_slot;
  output TRACE_ex_piperun;
  output [0:4]TRACE_exception_kind;
  output TRACE_exception_taken;
  output TRACE_icache_hit;
  output TRACE_icache_rdy;
  output TRACE_icache_req;
  output [0:31]TRACE_instruction;
  output TRACE_jump_hit;
  output TRACE_jump_taken;
  output TRACE_mb_halted;
  output TRACE_mem_piperun;
  output [0:14]TRACE_msr_reg;
  output [0:31]TRACE_new_reg_value;
  output TRACE_of_piperun;
  output [0:31]TRACE_pc;
  output [0:7]TRACE_pid_reg;
  output [0:4]TRACE_reg_addr;
  output TRACE_reg_write;
  output TRACE_valid_instr;

  wire Clk;
  wire IO_addr_strobe;
  wire [31:0]IO_address;
  wire [3:0]IO_byte_enable;
  wire [31:0]IO_read_data;
  wire IO_read_strobe;
  wire IO_ready;
  wire [31:0]IO_write_data;
  wire IO_write_strobe;
  wire Reset;
  wire TRACE_data_access;
  wire [0:31]TRACE_data_address;
  wire [0:3]TRACE_data_byte_enable;
  wire TRACE_data_read;
  wire TRACE_data_write;
  wire [0:31]TRACE_data_write_value;
  wire TRACE_dcache_hit;
  wire TRACE_dcache_rdy;
  wire TRACE_dcache_read;
  wire TRACE_dcache_req;
  wire TRACE_delay_slot;
  wire TRACE_ex_piperun;
  wire [0:4]TRACE_exception_kind;
  wire TRACE_exception_taken;
  wire TRACE_icache_hit;
  wire TRACE_icache_rdy;
  wire TRACE_icache_req;
  wire [0:31]TRACE_instruction;
  wire TRACE_jump_hit;
  wire TRACE_jump_taken;
  wire TRACE_mb_halted;
  wire TRACE_mem_piperun;
  wire [0:14]TRACE_msr_reg;
  wire [0:31]TRACE_new_reg_value;
  wire TRACE_of_piperun;
  wire [0:31]TRACE_pc;
  wire [0:7]TRACE_pid_reg;
  wire [0:4]TRACE_reg_addr;
  wire TRACE_reg_write;
  wire TRACE_valid_instr;

  bd_bf3f bd_bf3f_i
       (.Clk(Clk),
        .IO_addr_strobe(IO_addr_strobe),
        .IO_address(IO_address),
        .IO_byte_enable(IO_byte_enable),
        .IO_read_data(IO_read_data),
        .IO_read_strobe(IO_read_strobe),
        .IO_ready(IO_ready),
        .IO_write_data(IO_write_data),
        .IO_write_strobe(IO_write_strobe),
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
        .TRACE_valid_instr(TRACE_valid_instr));
endmodule
