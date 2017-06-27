//Copyright 1986-2017 Xilinx, Inc. All Rights Reserved.
//--------------------------------------------------------------------------------
//Tool Version: Vivado v.2017.1_sdxop (lin64) Build 1893406 Sat May 27 14:00:24 MDT 2017
//Date        : Fri Jun  9 11:26:54 2017
//Host        : ip-10-206-20-5 running 64-bit CentOS release 6.5 (Final)
//Command     : generate_target bd_bf3f.bd
//Design      : bd_bf3f
//Purpose     : IP block netlist
//--------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* CORE_GENERATION_INFO = "bd_bf3f,IP_Integrator,{x_ipVendor=xilinx.com,x_ipLibrary=BlockDiagram,x_ipName=bd_bf3f,x_ipVersion=1.00.a,x_ipLanguage=VERILOG,numBlks=11,numReposBlks=11,numNonXlnxBlks=0,numHierBlks=0,maxHierDepth=0,numSysgenBlks=0,numHlsBlks=0,numHdlrefBlks=0,numPkgbdBlks=0,bdsource=SBD,synth_mode=OOC_per_IP}" *) (* HW_HANDOFF = "ddr4_core_microblaze_mcs.hwdef" *) 
module bd_bf3f
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

  wire Clk2;
  wire [0:0]IO_Rst;
  wire [0:0]LMB_Rst2;
  wire MB_Reset;
  wire Reset;
  wire [0:31]dlmb_ABUS;
  wire dlmb_ADDRSTROBE;
  wire [0:3]dlmb_BE;
  wire dlmb_CE;
  wire [0:31]dlmb_READDBUS;
  wire dlmb_READSTROBE;
  wire dlmb_READY;
  wire dlmb_UE;
  wire dlmb_WAIT;
  wire [0:31]dlmb_WRITEDBUS;
  wire dlmb_WRITESTROBE;
  wire [0:31]dlmb_port_2_ADDR;
  wire dlmb_port_2_CLK;
  wire [0:31]dlmb_port_2_DIN;
  wire [31:0]dlmb_port_2_DOUT;
  wire dlmb_port_2_EN;
  wire dlmb_port_2_RST;
  wire [0:3]dlmb_port_2_WE;
  wire [0:31]dlmb_port_ADDR;
  wire dlmb_port_CLK;
  wire [0:31]dlmb_port_DIN;
  wire [31:0]dlmb_port_DOUT;
  wire dlmb_port_EN;
  wire dlmb_port_RST;
  wire [0:3]dlmb_port_WE;
  wire [0:31]dlmb_sl_0_ABUS;
  wire dlmb_sl_0_ADDRSTROBE;
  wire [0:3]dlmb_sl_0_BE;
  wire dlmb_sl_0_CE;
  wire [0:31]dlmb_sl_0_READDBUS;
  wire dlmb_sl_0_READSTROBE;
  wire dlmb_sl_0_READY;
  wire dlmb_sl_0_UE;
  wire dlmb_sl_0_WAIT;
  wire [0:31]dlmb_sl_0_WRITEDBUS;
  wire dlmb_sl_0_WRITESTROBE;
  wire dlmb_sl_1_CE;
  wire [0:31]dlmb_sl_1_READDBUS;
  wire dlmb_sl_1_READY;
  wire dlmb_sl_1_UE;
  wire dlmb_sl_1_WAIT;
  wire dlmb_sl_2_CE;
  wire [0:31]dlmb_sl_2_READDBUS;
  wire dlmb_sl_2_READY;
  wire dlmb_sl_2_UE;
  wire dlmb_sl_2_WAIT;
  wire [0:31]ilmb_ABUS;
  wire ilmb_ADDRSTROBE;
  wire ilmb_CE;
  wire [0:31]ilmb_READDBUS;
  wire ilmb_READSTROBE;
  wire ilmb_READY;
  wire ilmb_UE;
  wire ilmb_WAIT;
  wire [0:31]ilmb_port_2_ADDR;
  wire ilmb_port_2_CLK;
  wire [0:31]ilmb_port_2_DIN;
  wire [31:0]ilmb_port_2_DOUT;
  wire ilmb_port_2_EN;
  wire ilmb_port_2_RST;
  wire [0:3]ilmb_port_2_WE;
  wire [0:31]ilmb_port_ADDR;
  wire ilmb_port_CLK;
  wire [0:31]ilmb_port_DIN;
  wire [31:0]ilmb_port_DOUT;
  wire ilmb_port_EN;
  wire ilmb_port_RST;
  wire [0:3]ilmb_port_WE;
  wire [0:31]ilmb_sl_0_ABUS;
  wire ilmb_sl_0_ADDRSTROBE;
  wire [0:3]ilmb_sl_0_BE;
  wire ilmb_sl_0_CE;
  wire [0:31]ilmb_sl_0_READDBUS;
  wire ilmb_sl_0_READSTROBE;
  wire ilmb_sl_0_READY;
  wire ilmb_sl_0_UE;
  wire ilmb_sl_0_WAIT;
  wire [0:31]ilmb_sl_0_WRITEDBUS;
  wire ilmb_sl_0_WRITESTROBE;
  wire ilmb_sl_1_CE;
  wire [0:31]ilmb_sl_1_READDBUS;
  wire ilmb_sl_1_READY;
  wire ilmb_sl_1_UE;
  wire ilmb_sl_1_WAIT;
  wire [31:0]iomodule_0_IO_ADDRESS;
  wire iomodule_0_IO_ADDR_STROBE;
  wire [3:0]iomodule_0_IO_BYTE_ENABLE;
  wire iomodule_0_IO_READY;
  wire [31:0]iomodule_0_IO_READ_DATA;
  wire iomodule_0_IO_READ_STROBE;
  wire [31:0]iomodule_0_IO_WRITE_DATA;
  wire iomodule_0_IO_WRITE_STROBE;
  wire microblaze_I_Trace_DATA_ACCESS;
  wire [0:31]microblaze_I_Trace_DATA_ADDRESS;
  wire [0:3]microblaze_I_Trace_DATA_BYTE_ENABLE;
  wire microblaze_I_Trace_DATA_READ;
  wire microblaze_I_Trace_DATA_WRITE;
  wire [0:31]microblaze_I_Trace_DATA_WRITE_VALUE;
  wire microblaze_I_Trace_DCACHE_HIT;
  wire microblaze_I_Trace_DCACHE_RDY;
  wire microblaze_I_Trace_DCACHE_READ;
  wire microblaze_I_Trace_DCACHE_REQ;
  wire microblaze_I_Trace_DELAY_SLOT;
  wire [0:4]microblaze_I_Trace_EXCEPTION_KIND;
  wire microblaze_I_Trace_EXCEPTION_TAKEN;
  wire microblaze_I_Trace_EX_PIPERUN;
  wire microblaze_I_Trace_ICACHE_HIT;
  wire microblaze_I_Trace_ICACHE_RDY;
  wire microblaze_I_Trace_ICACHE_REQ;
  wire [0:31]microblaze_I_Trace_INSTRUCTION;
  wire microblaze_I_Trace_JUMP_HIT;
  wire microblaze_I_Trace_JUMP_TAKEN;
  wire microblaze_I_Trace_MB_HALTED;
  wire microblaze_I_Trace_MEM_PIPERUN;
  wire [0:14]microblaze_I_Trace_MSR_REG;
  wire [0:31]microblaze_I_Trace_NEW_REG_VALUE;
  wire microblaze_I_Trace_OF_PIPERUN;
  wire [0:31]microblaze_I_Trace_PC;
  wire [0:7]microblaze_I_Trace_PID_REG;
  wire [0:4]microblaze_I_Trace_REG_ADDR;
  wire microblaze_I_Trace_REG_WRITE;
  wire microblaze_I_Trace_VALID_INSTR;

  assign Clk2 = Clk;
  assign IO_addr_strobe = iomodule_0_IO_ADDR_STROBE;
  assign IO_address[31:0] = iomodule_0_IO_ADDRESS;
  assign IO_byte_enable[3:0] = iomodule_0_IO_BYTE_ENABLE;
  assign IO_read_strobe = iomodule_0_IO_READ_STROBE;
  assign IO_write_data[31:0] = iomodule_0_IO_WRITE_DATA;
  assign IO_write_strobe = iomodule_0_IO_WRITE_STROBE;
  assign TRACE_data_access = microblaze_I_Trace_DATA_ACCESS;
  assign TRACE_data_address[0:31] = microblaze_I_Trace_DATA_ADDRESS;
  assign TRACE_data_byte_enable[0:3] = microblaze_I_Trace_DATA_BYTE_ENABLE;
  assign TRACE_data_read = microblaze_I_Trace_DATA_READ;
  assign TRACE_data_write = microblaze_I_Trace_DATA_WRITE;
  assign TRACE_data_write_value[0:31] = microblaze_I_Trace_DATA_WRITE_VALUE;
  assign TRACE_dcache_hit = microblaze_I_Trace_DCACHE_HIT;
  assign TRACE_dcache_rdy = microblaze_I_Trace_DCACHE_RDY;
  assign TRACE_dcache_read = microblaze_I_Trace_DCACHE_READ;
  assign TRACE_dcache_req = microblaze_I_Trace_DCACHE_REQ;
  assign TRACE_delay_slot = microblaze_I_Trace_DELAY_SLOT;
  assign TRACE_ex_piperun = microblaze_I_Trace_EX_PIPERUN;
  assign TRACE_exception_kind[0:4] = microblaze_I_Trace_EXCEPTION_KIND;
  assign TRACE_exception_taken = microblaze_I_Trace_EXCEPTION_TAKEN;
  assign TRACE_icache_hit = microblaze_I_Trace_ICACHE_HIT;
  assign TRACE_icache_rdy = microblaze_I_Trace_ICACHE_RDY;
  assign TRACE_icache_req = microblaze_I_Trace_ICACHE_REQ;
  assign TRACE_instruction[0:31] = microblaze_I_Trace_INSTRUCTION;
  assign TRACE_jump_hit = microblaze_I_Trace_JUMP_HIT;
  assign TRACE_jump_taken = microblaze_I_Trace_JUMP_TAKEN;
  assign TRACE_mb_halted = microblaze_I_Trace_MB_HALTED;
  assign TRACE_mem_piperun = microblaze_I_Trace_MEM_PIPERUN;
  assign TRACE_msr_reg[0:14] = microblaze_I_Trace_MSR_REG;
  assign TRACE_new_reg_value[0:31] = microblaze_I_Trace_NEW_REG_VALUE;
  assign TRACE_of_piperun = microblaze_I_Trace_OF_PIPERUN;
  assign TRACE_pc[0:31] = microblaze_I_Trace_PC;
  assign TRACE_pid_reg[0:7] = microblaze_I_Trace_PID_REG;
  assign TRACE_reg_addr[0:4] = microblaze_I_Trace_REG_ADDR;
  assign TRACE_reg_write = microblaze_I_Trace_REG_WRITE;
  assign TRACE_valid_instr = microblaze_I_Trace_VALID_INSTR;
  assign iomodule_0_IO_READY = IO_ready;
  assign iomodule_0_IO_READ_DATA = IO_read_data[31:0];
  bd_bf3f_dlmb_0 dlmb
       (.LMB_ABus(dlmb_sl_0_ABUS),
        .LMB_AddrStrobe(dlmb_sl_0_ADDRSTROBE),
        .LMB_BE(dlmb_sl_0_BE),
        .LMB_CE(dlmb_CE),
        .LMB_Clk(Clk2),
        .LMB_ReadDBus(dlmb_READDBUS),
        .LMB_ReadStrobe(dlmb_sl_0_READSTROBE),
        .LMB_Ready(dlmb_READY),
        .LMB_UE(dlmb_UE),
        .LMB_Wait(dlmb_WAIT),
        .LMB_WriteDBus(dlmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(dlmb_sl_0_WRITESTROBE),
        .M_ABus(dlmb_ABUS),
        .M_AddrStrobe(dlmb_ADDRSTROBE),
        .M_BE(dlmb_BE),
        .M_DBus(dlmb_WRITEDBUS),
        .M_ReadStrobe(dlmb_READSTROBE),
        .M_WriteStrobe(dlmb_WRITESTROBE),
        .SYS_Rst(LMB_Rst2),
        .Sl_CE({dlmb_sl_0_CE,dlmb_sl_1_CE,dlmb_sl_2_CE}),
        .Sl_DBus({dlmb_sl_0_READDBUS,dlmb_sl_1_READDBUS,dlmb_sl_2_READDBUS}),
        .Sl_Ready({dlmb_sl_0_READY,dlmb_sl_1_READY,dlmb_sl_2_READY}),
        .Sl_UE({dlmb_sl_0_UE,dlmb_sl_1_UE,dlmb_sl_2_UE}),
        .Sl_Wait({dlmb_sl_0_WAIT,dlmb_sl_1_WAIT,dlmb_sl_2_WAIT}));
  (* BMM_INFO_ADDRESS_SPACE = "byte  0x00000000 32 >  bd_bf3f lmb_bram_I bd_bf3f second_lmb_bram_I" *) 
  (* KEEP_HIERARCHY = "yes" *) 
  bd_bf3f_dlmb_cntlr_0 dlmb_cntlr
       (.BRAM_Addr_A(dlmb_port_ADDR),
        .BRAM_Clk_A(dlmb_port_CLK),
        .BRAM_Din_A({dlmb_port_DOUT[31],dlmb_port_DOUT[30],dlmb_port_DOUT[29],dlmb_port_DOUT[28],dlmb_port_DOUT[27],dlmb_port_DOUT[26],dlmb_port_DOUT[25],dlmb_port_DOUT[24],dlmb_port_DOUT[23],dlmb_port_DOUT[22],dlmb_port_DOUT[21],dlmb_port_DOUT[20],dlmb_port_DOUT[19],dlmb_port_DOUT[18],dlmb_port_DOUT[17],dlmb_port_DOUT[16],dlmb_port_DOUT[15],dlmb_port_DOUT[14],dlmb_port_DOUT[13],dlmb_port_DOUT[12],dlmb_port_DOUT[11],dlmb_port_DOUT[10],dlmb_port_DOUT[9],dlmb_port_DOUT[8],dlmb_port_DOUT[7],dlmb_port_DOUT[6],dlmb_port_DOUT[5],dlmb_port_DOUT[4],dlmb_port_DOUT[3],dlmb_port_DOUT[2],dlmb_port_DOUT[1],dlmb_port_DOUT[0]}),
        .BRAM_Dout_A(dlmb_port_DIN),
        .BRAM_EN_A(dlmb_port_EN),
        .BRAM_Rst_A(dlmb_port_RST),
        .BRAM_WEN_A(dlmb_port_WE),
        .LMB_ABus(dlmb_sl_0_ABUS),
        .LMB_AddrStrobe(dlmb_sl_0_ADDRSTROBE),
        .LMB_BE(dlmb_sl_0_BE),
        .LMB_Clk(Clk2),
        .LMB_ReadStrobe(dlmb_sl_0_READSTROBE),
        .LMB_Rst(LMB_Rst2),
        .LMB_WriteDBus(dlmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(dlmb_sl_0_WRITESTROBE),
        .Sl_CE(dlmb_sl_0_CE),
        .Sl_DBus(dlmb_sl_0_READDBUS),
        .Sl_Ready(dlmb_sl_0_READY),
        .Sl_UE(dlmb_sl_0_UE),
        .Sl_Wait(dlmb_sl_0_WAIT));
  bd_bf3f_ilmb_0 ilmb
       (.LMB_ABus(ilmb_sl_0_ABUS),
        .LMB_AddrStrobe(ilmb_sl_0_ADDRSTROBE),
        .LMB_BE(ilmb_sl_0_BE),
        .LMB_CE(ilmb_CE),
        .LMB_Clk(Clk2),
        .LMB_ReadDBus(ilmb_READDBUS),
        .LMB_ReadStrobe(ilmb_sl_0_READSTROBE),
        .LMB_Ready(ilmb_READY),
        .LMB_UE(ilmb_UE),
        .LMB_Wait(ilmb_WAIT),
        .LMB_WriteDBus(ilmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(ilmb_sl_0_WRITESTROBE),
        .M_ABus(ilmb_ABUS),
        .M_AddrStrobe(ilmb_ADDRSTROBE),
        .M_BE({1'b0,1'b0,1'b0,1'b0}),
        .M_DBus({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .M_ReadStrobe(ilmb_READSTROBE),
        .M_WriteStrobe(1'b0),
        .SYS_Rst(LMB_Rst2),
        .Sl_CE({ilmb_sl_0_CE,ilmb_sl_1_CE}),
        .Sl_DBus({ilmb_sl_0_READDBUS,ilmb_sl_1_READDBUS}),
        .Sl_Ready({ilmb_sl_0_READY,ilmb_sl_1_READY}),
        .Sl_UE({ilmb_sl_0_UE,ilmb_sl_1_UE}),
        .Sl_Wait({ilmb_sl_0_WAIT,ilmb_sl_1_WAIT}));
  bd_bf3f_ilmb_cntlr_0 ilmb_cntlr
       (.BRAM_Addr_A(ilmb_port_ADDR),
        .BRAM_Clk_A(ilmb_port_CLK),
        .BRAM_Din_A({ilmb_port_DOUT[31],ilmb_port_DOUT[30],ilmb_port_DOUT[29],ilmb_port_DOUT[28],ilmb_port_DOUT[27],ilmb_port_DOUT[26],ilmb_port_DOUT[25],ilmb_port_DOUT[24],ilmb_port_DOUT[23],ilmb_port_DOUT[22],ilmb_port_DOUT[21],ilmb_port_DOUT[20],ilmb_port_DOUT[19],ilmb_port_DOUT[18],ilmb_port_DOUT[17],ilmb_port_DOUT[16],ilmb_port_DOUT[15],ilmb_port_DOUT[14],ilmb_port_DOUT[13],ilmb_port_DOUT[12],ilmb_port_DOUT[11],ilmb_port_DOUT[10],ilmb_port_DOUT[9],ilmb_port_DOUT[8],ilmb_port_DOUT[7],ilmb_port_DOUT[6],ilmb_port_DOUT[5],ilmb_port_DOUT[4],ilmb_port_DOUT[3],ilmb_port_DOUT[2],ilmb_port_DOUT[1],ilmb_port_DOUT[0]}),
        .BRAM_Dout_A(ilmb_port_DIN),
        .BRAM_EN_A(ilmb_port_EN),
        .BRAM_Rst_A(ilmb_port_RST),
        .BRAM_WEN_A(ilmb_port_WE),
        .LMB_ABus(ilmb_sl_0_ABUS),
        .LMB_AddrStrobe(ilmb_sl_0_ADDRSTROBE),
        .LMB_BE(ilmb_sl_0_BE),
        .LMB_Clk(Clk2),
        .LMB_ReadStrobe(ilmb_sl_0_READSTROBE),
        .LMB_Rst(LMB_Rst2),
        .LMB_WriteDBus(ilmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(ilmb_sl_0_WRITESTROBE),
        .Sl_CE(ilmb_sl_0_CE),
        .Sl_DBus(ilmb_sl_0_READDBUS),
        .Sl_Ready(ilmb_sl_0_READY),
        .Sl_UE(ilmb_sl_0_UE),
        .Sl_Wait(ilmb_sl_0_WAIT));
  bd_bf3f_iomodule_0_0 iomodule_0
       (.Clk(Clk2),
        .IO_Addr_Strobe(iomodule_0_IO_ADDR_STROBE),
        .IO_Address(iomodule_0_IO_ADDRESS),
        .IO_Byte_Enable(iomodule_0_IO_BYTE_ENABLE),
        .IO_Read_Data(iomodule_0_IO_READ_DATA),
        .IO_Read_Strobe(iomodule_0_IO_READ_STROBE),
        .IO_Ready(iomodule_0_IO_READY),
        .IO_Write_Data(iomodule_0_IO_WRITE_DATA),
        .IO_Write_Strobe(iomodule_0_IO_WRITE_STROBE),
        .LMB_ABus(dlmb_sl_0_ABUS),
        .LMB_AddrStrobe(dlmb_sl_0_ADDRSTROBE),
        .LMB_BE(dlmb_sl_0_BE),
        .LMB_ReadStrobe(dlmb_sl_0_READSTROBE),
        .LMB_WriteDBus(dlmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(dlmb_sl_0_WRITESTROBE),
        .Rst(IO_Rst),
        .Sl_CE(dlmb_sl_1_CE),
        .Sl_DBus(dlmb_sl_1_READDBUS),
        .Sl_Ready(dlmb_sl_1_READY),
        .Sl_UE(dlmb_sl_1_UE),
        .Sl_Wait(dlmb_sl_1_WAIT));
  bd_bf3f_lmb_bram_I_0 lmb_bram_I
       (.addra({dlmb_port_ADDR[0],dlmb_port_ADDR[1],dlmb_port_ADDR[2],dlmb_port_ADDR[3],dlmb_port_ADDR[4],dlmb_port_ADDR[5],dlmb_port_ADDR[6],dlmb_port_ADDR[7],dlmb_port_ADDR[8],dlmb_port_ADDR[9],dlmb_port_ADDR[10],dlmb_port_ADDR[11],dlmb_port_ADDR[12],dlmb_port_ADDR[13],dlmb_port_ADDR[14],dlmb_port_ADDR[15],dlmb_port_ADDR[16],dlmb_port_ADDR[17],dlmb_port_ADDR[18],dlmb_port_ADDR[19],dlmb_port_ADDR[20],dlmb_port_ADDR[21],dlmb_port_ADDR[22],dlmb_port_ADDR[23],dlmb_port_ADDR[24],dlmb_port_ADDR[25],dlmb_port_ADDR[26],dlmb_port_ADDR[27],dlmb_port_ADDR[28],dlmb_port_ADDR[29],dlmb_port_ADDR[30],dlmb_port_ADDR[31]}),
        .addrb({ilmb_port_ADDR[0],ilmb_port_ADDR[1],ilmb_port_ADDR[2],ilmb_port_ADDR[3],ilmb_port_ADDR[4],ilmb_port_ADDR[5],ilmb_port_ADDR[6],ilmb_port_ADDR[7],ilmb_port_ADDR[8],ilmb_port_ADDR[9],ilmb_port_ADDR[10],ilmb_port_ADDR[11],ilmb_port_ADDR[12],ilmb_port_ADDR[13],ilmb_port_ADDR[14],ilmb_port_ADDR[15],ilmb_port_ADDR[16],ilmb_port_ADDR[17],ilmb_port_ADDR[18],ilmb_port_ADDR[19],ilmb_port_ADDR[20],ilmb_port_ADDR[21],ilmb_port_ADDR[22],ilmb_port_ADDR[23],ilmb_port_ADDR[24],ilmb_port_ADDR[25],ilmb_port_ADDR[26],ilmb_port_ADDR[27],ilmb_port_ADDR[28],ilmb_port_ADDR[29],ilmb_port_ADDR[30],ilmb_port_ADDR[31]}),
        .clka(dlmb_port_CLK),
        .clkb(ilmb_port_CLK),
        .dina({dlmb_port_DIN[0],dlmb_port_DIN[1],dlmb_port_DIN[2],dlmb_port_DIN[3],dlmb_port_DIN[4],dlmb_port_DIN[5],dlmb_port_DIN[6],dlmb_port_DIN[7],dlmb_port_DIN[8],dlmb_port_DIN[9],dlmb_port_DIN[10],dlmb_port_DIN[11],dlmb_port_DIN[12],dlmb_port_DIN[13],dlmb_port_DIN[14],dlmb_port_DIN[15],dlmb_port_DIN[16],dlmb_port_DIN[17],dlmb_port_DIN[18],dlmb_port_DIN[19],dlmb_port_DIN[20],dlmb_port_DIN[21],dlmb_port_DIN[22],dlmb_port_DIN[23],dlmb_port_DIN[24],dlmb_port_DIN[25],dlmb_port_DIN[26],dlmb_port_DIN[27],dlmb_port_DIN[28],dlmb_port_DIN[29],dlmb_port_DIN[30],dlmb_port_DIN[31]}),
        .dinb({ilmb_port_DIN[0],ilmb_port_DIN[1],ilmb_port_DIN[2],ilmb_port_DIN[3],ilmb_port_DIN[4],ilmb_port_DIN[5],ilmb_port_DIN[6],ilmb_port_DIN[7],ilmb_port_DIN[8],ilmb_port_DIN[9],ilmb_port_DIN[10],ilmb_port_DIN[11],ilmb_port_DIN[12],ilmb_port_DIN[13],ilmb_port_DIN[14],ilmb_port_DIN[15],ilmb_port_DIN[16],ilmb_port_DIN[17],ilmb_port_DIN[18],ilmb_port_DIN[19],ilmb_port_DIN[20],ilmb_port_DIN[21],ilmb_port_DIN[22],ilmb_port_DIN[23],ilmb_port_DIN[24],ilmb_port_DIN[25],ilmb_port_DIN[26],ilmb_port_DIN[27],ilmb_port_DIN[28],ilmb_port_DIN[29],ilmb_port_DIN[30],ilmb_port_DIN[31]}),
        .douta(dlmb_port_DOUT),
        .doutb(ilmb_port_DOUT),
        .ena(dlmb_port_EN),
        .enb(ilmb_port_EN),
        .rsta(dlmb_port_RST),
        .rstb(ilmb_port_RST),
        .wea({dlmb_port_WE[0],dlmb_port_WE[1],dlmb_port_WE[2],dlmb_port_WE[3]}),
        .web({ilmb_port_WE[0],ilmb_port_WE[1],ilmb_port_WE[2],ilmb_port_WE[3]}));
  (* BMM_INFO_PROCESSOR = "microblaze-le > bd_bf3f dlmb_cntlr" *) 
  (* KEEP_HIERARCHY = "yes" *) 
  bd_bf3f_microblaze_I_0 microblaze_I
       (.Byte_Enable(dlmb_BE),
        .Clk(Clk2),
        .DCE(dlmb_CE),
        .DReady(dlmb_READY),
        .DUE(dlmb_UE),
        .DWait(dlmb_WAIT),
        .D_AS(dlmb_ADDRSTROBE),
        .Data_Addr(dlmb_ABUS),
        .Data_Read(dlmb_READDBUS),
        .Data_Write(dlmb_WRITEDBUS),
        .ICE(ilmb_CE),
        .IFetch(ilmb_READSTROBE),
        .IReady(ilmb_READY),
        .IUE(ilmb_UE),
        .IWAIT(ilmb_WAIT),
        .I_AS(ilmb_ADDRSTROBE),
        .Instr(ilmb_READDBUS),
        .Instr_Addr(ilmb_ABUS),
        .Interrupt(1'b0),
        .Interrupt_Address({1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0,1'b0}),
        .Read_Strobe(dlmb_READSTROBE),
        .Reset(MB_Reset),
        .Trace_DCache_Hit(microblaze_I_Trace_DCACHE_HIT),
        .Trace_DCache_Rdy(microblaze_I_Trace_DCACHE_RDY),
        .Trace_DCache_Read(microblaze_I_Trace_DCACHE_READ),
        .Trace_DCache_Req(microblaze_I_Trace_DCACHE_REQ),
        .Trace_Data_Access(microblaze_I_Trace_DATA_ACCESS),
        .Trace_Data_Address(microblaze_I_Trace_DATA_ADDRESS),
        .Trace_Data_Byte_Enable(microblaze_I_Trace_DATA_BYTE_ENABLE),
        .Trace_Data_Read(microblaze_I_Trace_DATA_READ),
        .Trace_Data_Write(microblaze_I_Trace_DATA_WRITE),
        .Trace_Data_Write_Value(microblaze_I_Trace_DATA_WRITE_VALUE),
        .Trace_Delay_Slot(microblaze_I_Trace_DELAY_SLOT),
        .Trace_EX_PipeRun(microblaze_I_Trace_EX_PIPERUN),
        .Trace_Exception_Kind(microblaze_I_Trace_EXCEPTION_KIND),
        .Trace_Exception_Taken(microblaze_I_Trace_EXCEPTION_TAKEN),
        .Trace_ICache_Hit(microblaze_I_Trace_ICACHE_HIT),
        .Trace_ICache_Rdy(microblaze_I_Trace_ICACHE_RDY),
        .Trace_ICache_Req(microblaze_I_Trace_ICACHE_REQ),
        .Trace_Instruction(microblaze_I_Trace_INSTRUCTION),
        .Trace_Jump_Hit(microblaze_I_Trace_JUMP_HIT),
        .Trace_Jump_Taken(microblaze_I_Trace_JUMP_TAKEN),
        .Trace_MB_Halted(microblaze_I_Trace_MB_HALTED),
        .Trace_MEM_PipeRun(microblaze_I_Trace_MEM_PIPERUN),
        .Trace_MSR_Reg(microblaze_I_Trace_MSR_REG),
        .Trace_New_Reg_Value(microblaze_I_Trace_NEW_REG_VALUE),
        .Trace_OF_PipeRun(microblaze_I_Trace_OF_PIPERUN),
        .Trace_PC(microblaze_I_Trace_PC),
        .Trace_PID_Reg(microblaze_I_Trace_PID_REG),
        .Trace_Reg_Addr(microblaze_I_Trace_REG_ADDR),
        .Trace_Reg_Write(microblaze_I_Trace_REG_WRITE),
        .Trace_Valid_Instr(microblaze_I_Trace_VALID_INSTR),
        .Write_Strobe(dlmb_WRITESTROBE));
  bd_bf3f_rst_0_0 rst_0
       (.aux_reset_in(1'b1),
        .bus_struct_reset(LMB_Rst2),
        .dcm_locked(1'b1),
        .ext_reset_in(Reset),
        .mb_debug_sys_rst(1'b0),
        .mb_reset(MB_Reset),
        .peripheral_reset(IO_Rst),
        .slowest_sync_clk(Clk2));
  (* BMM_INFO_ADDRESS_RANGE = " " *) 
  bd_bf3f_second_dlmb_cntlr_0 second_dlmb_cntlr
       (.BRAM_Addr_A(dlmb_port_2_ADDR),
        .BRAM_Clk_A(dlmb_port_2_CLK),
        .BRAM_Din_A({dlmb_port_2_DOUT[31],dlmb_port_2_DOUT[30],dlmb_port_2_DOUT[29],dlmb_port_2_DOUT[28],dlmb_port_2_DOUT[27],dlmb_port_2_DOUT[26],dlmb_port_2_DOUT[25],dlmb_port_2_DOUT[24],dlmb_port_2_DOUT[23],dlmb_port_2_DOUT[22],dlmb_port_2_DOUT[21],dlmb_port_2_DOUT[20],dlmb_port_2_DOUT[19],dlmb_port_2_DOUT[18],dlmb_port_2_DOUT[17],dlmb_port_2_DOUT[16],dlmb_port_2_DOUT[15],dlmb_port_2_DOUT[14],dlmb_port_2_DOUT[13],dlmb_port_2_DOUT[12],dlmb_port_2_DOUT[11],dlmb_port_2_DOUT[10],dlmb_port_2_DOUT[9],dlmb_port_2_DOUT[8],dlmb_port_2_DOUT[7],dlmb_port_2_DOUT[6],dlmb_port_2_DOUT[5],dlmb_port_2_DOUT[4],dlmb_port_2_DOUT[3],dlmb_port_2_DOUT[2],dlmb_port_2_DOUT[1],dlmb_port_2_DOUT[0]}),
        .BRAM_Dout_A(dlmb_port_2_DIN),
        .BRAM_EN_A(dlmb_port_2_EN),
        .BRAM_Rst_A(dlmb_port_2_RST),
        .BRAM_WEN_A(dlmb_port_2_WE),
        .LMB_ABus(dlmb_sl_0_ABUS),
        .LMB_AddrStrobe(dlmb_sl_0_ADDRSTROBE),
        .LMB_BE(dlmb_sl_0_BE),
        .LMB_Clk(Clk2),
        .LMB_ReadStrobe(dlmb_sl_0_READSTROBE),
        .LMB_Rst(LMB_Rst2),
        .LMB_WriteDBus(dlmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(dlmb_sl_0_WRITESTROBE),
        .Sl_CE(dlmb_sl_2_CE),
        .Sl_DBus(dlmb_sl_2_READDBUS),
        .Sl_Ready(dlmb_sl_2_READY),
        .Sl_UE(dlmb_sl_2_UE),
        .Sl_Wait(dlmb_sl_2_WAIT));
  bd_bf3f_second_ilmb_cntlr_0 second_ilmb_cntlr
       (.BRAM_Addr_A(ilmb_port_2_ADDR),
        .BRAM_Clk_A(ilmb_port_2_CLK),
        .BRAM_Din_A({ilmb_port_2_DOUT[31],ilmb_port_2_DOUT[30],ilmb_port_2_DOUT[29],ilmb_port_2_DOUT[28],ilmb_port_2_DOUT[27],ilmb_port_2_DOUT[26],ilmb_port_2_DOUT[25],ilmb_port_2_DOUT[24],ilmb_port_2_DOUT[23],ilmb_port_2_DOUT[22],ilmb_port_2_DOUT[21],ilmb_port_2_DOUT[20],ilmb_port_2_DOUT[19],ilmb_port_2_DOUT[18],ilmb_port_2_DOUT[17],ilmb_port_2_DOUT[16],ilmb_port_2_DOUT[15],ilmb_port_2_DOUT[14],ilmb_port_2_DOUT[13],ilmb_port_2_DOUT[12],ilmb_port_2_DOUT[11],ilmb_port_2_DOUT[10],ilmb_port_2_DOUT[9],ilmb_port_2_DOUT[8],ilmb_port_2_DOUT[7],ilmb_port_2_DOUT[6],ilmb_port_2_DOUT[5],ilmb_port_2_DOUT[4],ilmb_port_2_DOUT[3],ilmb_port_2_DOUT[2],ilmb_port_2_DOUT[1],ilmb_port_2_DOUT[0]}),
        .BRAM_Dout_A(ilmb_port_2_DIN),
        .BRAM_EN_A(ilmb_port_2_EN),
        .BRAM_Rst_A(ilmb_port_2_RST),
        .BRAM_WEN_A(ilmb_port_2_WE),
        .LMB_ABus(ilmb_sl_0_ABUS),
        .LMB_AddrStrobe(ilmb_sl_0_ADDRSTROBE),
        .LMB_BE(ilmb_sl_0_BE),
        .LMB_Clk(Clk2),
        .LMB_ReadStrobe(ilmb_sl_0_READSTROBE),
        .LMB_Rst(LMB_Rst2),
        .LMB_WriteDBus(ilmb_sl_0_WRITEDBUS),
        .LMB_WriteStrobe(ilmb_sl_0_WRITESTROBE),
        .Sl_CE(ilmb_sl_1_CE),
        .Sl_DBus(ilmb_sl_1_READDBUS),
        .Sl_Ready(ilmb_sl_1_READY),
        .Sl_UE(ilmb_sl_1_UE),
        .Sl_Wait(ilmb_sl_1_WAIT));
  bd_bf3f_second_lmb_bram_I_0 second_lmb_bram_I
       (.addra({dlmb_port_2_ADDR[0],dlmb_port_2_ADDR[1],dlmb_port_2_ADDR[2],dlmb_port_2_ADDR[3],dlmb_port_2_ADDR[4],dlmb_port_2_ADDR[5],dlmb_port_2_ADDR[6],dlmb_port_2_ADDR[7],dlmb_port_2_ADDR[8],dlmb_port_2_ADDR[9],dlmb_port_2_ADDR[10],dlmb_port_2_ADDR[11],dlmb_port_2_ADDR[12],dlmb_port_2_ADDR[13],dlmb_port_2_ADDR[14],dlmb_port_2_ADDR[15],dlmb_port_2_ADDR[16],dlmb_port_2_ADDR[17],dlmb_port_2_ADDR[18],dlmb_port_2_ADDR[19],dlmb_port_2_ADDR[20],dlmb_port_2_ADDR[21],dlmb_port_2_ADDR[22],dlmb_port_2_ADDR[23],dlmb_port_2_ADDR[24],dlmb_port_2_ADDR[25],dlmb_port_2_ADDR[26],dlmb_port_2_ADDR[27],dlmb_port_2_ADDR[28],dlmb_port_2_ADDR[29],dlmb_port_2_ADDR[30],dlmb_port_2_ADDR[31]}),
        .addrb({ilmb_port_2_ADDR[0],ilmb_port_2_ADDR[1],ilmb_port_2_ADDR[2],ilmb_port_2_ADDR[3],ilmb_port_2_ADDR[4],ilmb_port_2_ADDR[5],ilmb_port_2_ADDR[6],ilmb_port_2_ADDR[7],ilmb_port_2_ADDR[8],ilmb_port_2_ADDR[9],ilmb_port_2_ADDR[10],ilmb_port_2_ADDR[11],ilmb_port_2_ADDR[12],ilmb_port_2_ADDR[13],ilmb_port_2_ADDR[14],ilmb_port_2_ADDR[15],ilmb_port_2_ADDR[16],ilmb_port_2_ADDR[17],ilmb_port_2_ADDR[18],ilmb_port_2_ADDR[19],ilmb_port_2_ADDR[20],ilmb_port_2_ADDR[21],ilmb_port_2_ADDR[22],ilmb_port_2_ADDR[23],ilmb_port_2_ADDR[24],ilmb_port_2_ADDR[25],ilmb_port_2_ADDR[26],ilmb_port_2_ADDR[27],ilmb_port_2_ADDR[28],ilmb_port_2_ADDR[29],ilmb_port_2_ADDR[30],ilmb_port_2_ADDR[31]}),
        .clka(dlmb_port_2_CLK),
        .clkb(ilmb_port_2_CLK),
        .dina({dlmb_port_2_DIN[0],dlmb_port_2_DIN[1],dlmb_port_2_DIN[2],dlmb_port_2_DIN[3],dlmb_port_2_DIN[4],dlmb_port_2_DIN[5],dlmb_port_2_DIN[6],dlmb_port_2_DIN[7],dlmb_port_2_DIN[8],dlmb_port_2_DIN[9],dlmb_port_2_DIN[10],dlmb_port_2_DIN[11],dlmb_port_2_DIN[12],dlmb_port_2_DIN[13],dlmb_port_2_DIN[14],dlmb_port_2_DIN[15],dlmb_port_2_DIN[16],dlmb_port_2_DIN[17],dlmb_port_2_DIN[18],dlmb_port_2_DIN[19],dlmb_port_2_DIN[20],dlmb_port_2_DIN[21],dlmb_port_2_DIN[22],dlmb_port_2_DIN[23],dlmb_port_2_DIN[24],dlmb_port_2_DIN[25],dlmb_port_2_DIN[26],dlmb_port_2_DIN[27],dlmb_port_2_DIN[28],dlmb_port_2_DIN[29],dlmb_port_2_DIN[30],dlmb_port_2_DIN[31]}),
        .dinb({ilmb_port_2_DIN[0],ilmb_port_2_DIN[1],ilmb_port_2_DIN[2],ilmb_port_2_DIN[3],ilmb_port_2_DIN[4],ilmb_port_2_DIN[5],ilmb_port_2_DIN[6],ilmb_port_2_DIN[7],ilmb_port_2_DIN[8],ilmb_port_2_DIN[9],ilmb_port_2_DIN[10],ilmb_port_2_DIN[11],ilmb_port_2_DIN[12],ilmb_port_2_DIN[13],ilmb_port_2_DIN[14],ilmb_port_2_DIN[15],ilmb_port_2_DIN[16],ilmb_port_2_DIN[17],ilmb_port_2_DIN[18],ilmb_port_2_DIN[19],ilmb_port_2_DIN[20],ilmb_port_2_DIN[21],ilmb_port_2_DIN[22],ilmb_port_2_DIN[23],ilmb_port_2_DIN[24],ilmb_port_2_DIN[25],ilmb_port_2_DIN[26],ilmb_port_2_DIN[27],ilmb_port_2_DIN[28],ilmb_port_2_DIN[29],ilmb_port_2_DIN[30],ilmb_port_2_DIN[31]}),
        .douta(dlmb_port_2_DOUT),
        .doutb(ilmb_port_2_DOUT),
        .ena(dlmb_port_2_EN),
        .enb(ilmb_port_2_EN),
        .rsta(dlmb_port_2_RST),
        .rstb(ilmb_port_2_RST),
        .wea({dlmb_port_2_WE[0],dlmb_port_2_WE[1],dlmb_port_2_WE[2],dlmb_port_2_WE[3]}),
        .web({ilmb_port_2_WE[0],ilmb_port_2_WE[1],ilmb_port_2_WE[2],ilmb_port_2_WE[3]}));
endmodule
