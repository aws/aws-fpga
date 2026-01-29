module MCRFile(
  input         clock,
  input         reset,
  output        io_nasti_aw_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_aw_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_aw_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_aw_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_w_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_w_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_nasti_w_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_b_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_b_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_b_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_ar_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_ar_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_ar_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_ar_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_r_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_r_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_nasti_r_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_r_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_0_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_1_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_2_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_0_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_0_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_1_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_1_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_2_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_2_bits // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
`endif // RANDOMIZE_REG_INIT
  reg  arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
  reg  awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
  reg  wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
  reg  wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
  reg [11:0] bId; // @[midas/src/main/scala/midas/widgets/Lib.scala 323:22]
  reg [11:0] rId; // @[midas/src/main/scala/midas/widgets/Lib.scala 324:22]
  reg [31:0] wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 326:22]
  reg [1:0] wIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 327:22]
  reg [1:0] rIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 328:22]
  wire  _T = io_nasti_aw_ready & io_nasti_aw_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_3 = ~reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
  wire  _GEN_0 = _T | awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 332:13 320:26]
  wire [22:0] _GEN_1 = _T ? io_nasti_aw_bits_addr[24:2] : {{21'd0}, wIndex}; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 333:13 327:22]
  wire  _T_5 = io_nasti_w_ready & io_nasti_w_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_3 = _T_5 | wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25 339:12 321:26]
  wire  _T_6 = io_nasti_ar_ready & io_nasti_ar_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_6 = _T_6 | arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26 345:13 319:26]
  wire  _T_11 = io_nasti_r_ready & io_nasti_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_12 = io_nasti_b_ready & io_nasti_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_12 = _T_12 ? 1'h0 : wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25 358:15 322:26]
  wire  _GEN_17 = 2'h1 == wIndex ? io_mcr_write_1_valid : io_mcr_write_0_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_18 = 2'h2 == wIndex ? io_mcr_write_2_valid : _GEN_17; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_19 = _GEN_18 | _GEN_12; // @[midas/src/main/scala/midas/widgets/Lib.scala 361:35 362:15]
  wire  _io_mcr_write_valid_T = awFired & wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 366:41]
  wire [31:0] _GEN_24 = 2'h1 == rIndex ? io_mcr_read_1_bits : io_mcr_read_0_bits; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  assign io_nasti_aw_ready = ~awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 380:24]
  assign io_nasti_w_ready = ~wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 381:24]
  assign io_nasti_b_valid = _io_mcr_write_valid_T & wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 377:41]
  assign io_nasti_b_bits_id = bId; // @[midas/src/main/scala/junctions/nasti.scala 129:17 130:12]
  assign io_nasti_ar_ready = ~arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 379:24]
  assign io_nasti_r_valid = arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 374:31]
  assign io_nasti_r_bits_data = 2'h2 == rIndex ? io_mcr_read_2_bits : _GEN_24; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  assign io_nasti_r_bits_id = rId; // @[midas/src/main/scala/junctions/nasti.scala 117:17 118:12]
  assign io_mcr_write_0_valid = 2'h0 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_0_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_1_valid = 2'h1 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_1_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_2_valid = 2'h2 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_2_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
    end else if (_T_11) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 351:25]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 352:13]
    end else begin
      arFired <= _GEN_6;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 356:15]
    end else begin
      awFired <= _GEN_0;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 357:15]
    end else begin
      wFired <= _GEN_3;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
      wCommited <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
    end else begin
      wCommited <= _GEN_19;
    end
    if (_T) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26]
      bId <= io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 334:13]
    end
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rId <= io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 347:13]
    end
    if (_T_5) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25]
      wData <= io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Lib.scala 340:12]
    end
    wIndex <= _GEN_1[1:0];
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rIndex <= io_nasti_ar_bits_addr[3:2]; // @[midas/src/main/scala/midas/widgets/Lib.scala 346:13]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~reset & ~(io_nasti_aw_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Lib.scala:335 assert(io.nasti.aw.bits.len === 0.U)\n"); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_6 & _T_3 & ~(io_nasti_ar_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,
            "Assertion failed: MCRFile only support single beat reads\n    at Lib.scala:348 assert(io.nasti.ar.bits.len === 0.U, \"MCRFile only support single beat reads\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  arFired = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  awFired = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  wFired = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  wCommited = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  bId = _RAND_4[11:0];
  _RAND_5 = {1{`RANDOM}};
  rId = _RAND_5[11:0];
  _RAND_6 = {1{`RANDOM}};
  wData = _RAND_6[31:0];
  _RAND_7 = {1{`RANDOM}};
  wIndex = _RAND_7[1:0];
  _RAND_8 = {1{`RANDOM}};
  rIndex = _RAND_8[1:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (_T & ~reset) begin
      assert(io_nasti_aw_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
    end
    //
    if (_T_6 & _T_3) begin
      assert(io_nasti_ar_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
    end
  end
endmodule
module SimulationMaster(
  input         clock,
  input         reset,
  output        io_ctrl_aw_ready, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input         io_ctrl_aw_valid, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [24:0] io_ctrl_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [7:0]  io_ctrl_aw_bits_len, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [11:0] io_ctrl_aw_bits_id, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output        io_ctrl_w_ready, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input         io_ctrl_w_valid, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [31:0] io_ctrl_w_bits_data, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input         io_ctrl_b_ready, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output        io_ctrl_b_valid, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output [11:0] io_ctrl_b_bits_id, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output        io_ctrl_ar_ready, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input         io_ctrl_ar_valid, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [24:0] io_ctrl_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [7:0]  io_ctrl_ar_bits_len, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input  [11:0] io_ctrl_ar_bits_id, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  input         io_ctrl_r_ready, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output        io_ctrl_r_valid, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output [31:0] io_ctrl_r_bits_data, // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
  output [11:0] io_ctrl_r_bits_id // @[midas/src/main/scala/midas/widgets/Master.scala 13:16]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_REG_INIT
  wire  crFile_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_0_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_1_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_2_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  reg [6:0] initDelay; // @[midas/src/main/scala/midas/widgets/Master.scala 15:28]
  wire [6:0] _initDelay_T_1 = initDelay - 7'h1; // @[midas/src/main/scala/midas/widgets/Master.scala 16:54]
  wire  _T_1 = initDelay == 7'h0; // @[midas/src/main/scala/midas/widgets/Master.scala 17:28]
  reg [31:0] INIT_DONE; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  reg [31:0] rFingerprint; // @[midas/src/main/scala/midas/widgets/Master.scala 21:31]
  reg [31:0] PRESENCE_READ; // @[midas/src/main/scala/midas/widgets/Widget.scala 130:29]
  reg [31:0] PRESENCE_WRITE; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  MCRFile crFile ( // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
    .clock(crFile_clock),
    .reset(crFile_reset),
    .io_nasti_aw_ready(crFile_io_nasti_aw_ready),
    .io_nasti_aw_valid(crFile_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(crFile_io_nasti_aw_bits_addr),
    .io_nasti_aw_bits_len(crFile_io_nasti_aw_bits_len),
    .io_nasti_aw_bits_id(crFile_io_nasti_aw_bits_id),
    .io_nasti_w_ready(crFile_io_nasti_w_ready),
    .io_nasti_w_valid(crFile_io_nasti_w_valid),
    .io_nasti_w_bits_data(crFile_io_nasti_w_bits_data),
    .io_nasti_b_ready(crFile_io_nasti_b_ready),
    .io_nasti_b_valid(crFile_io_nasti_b_valid),
    .io_nasti_b_bits_id(crFile_io_nasti_b_bits_id),
    .io_nasti_ar_ready(crFile_io_nasti_ar_ready),
    .io_nasti_ar_valid(crFile_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(crFile_io_nasti_ar_bits_addr),
    .io_nasti_ar_bits_len(crFile_io_nasti_ar_bits_len),
    .io_nasti_ar_bits_id(crFile_io_nasti_ar_bits_id),
    .io_nasti_r_ready(crFile_io_nasti_r_ready),
    .io_nasti_r_valid(crFile_io_nasti_r_valid),
    .io_nasti_r_bits_data(crFile_io_nasti_r_bits_data),
    .io_nasti_r_bits_id(crFile_io_nasti_r_bits_id),
    .io_mcr_read_0_bits(crFile_io_mcr_read_0_bits),
    .io_mcr_read_1_bits(crFile_io_mcr_read_1_bits),
    .io_mcr_read_2_bits(crFile_io_mcr_read_2_bits),
    .io_mcr_write_0_valid(crFile_io_mcr_write_0_valid),
    .io_mcr_write_0_bits(crFile_io_mcr_write_0_bits),
    .io_mcr_write_1_valid(crFile_io_mcr_write_1_valid),
    .io_mcr_write_1_bits(crFile_io_mcr_write_1_bits),
    .io_mcr_write_2_valid(crFile_io_mcr_write_2_valid),
    .io_mcr_write_2_bits(crFile_io_mcr_write_2_bits)
  );
  assign io_ctrl_aw_ready = crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_w_ready = crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_valid = crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_bits_id = crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_ar_ready = crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_valid = crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_data = crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_id = crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_clock = clock;
  assign crFile_reset = reset;
  assign crFile_io_nasti_aw_valid = io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_addr = io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_len = io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_id = io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_valid = io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_bits_data = io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_b_ready = io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_valid = io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_addr = io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_len = io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_id = io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_r_ready = io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_mcr_read_0_bits = INIT_DONE; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_1_bits = PRESENCE_READ; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_2_bits = PRESENCE_WRITE; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Master.scala 15:28]
      initDelay <= 7'h40; // @[midas/src/main/scala/midas/widgets/Master.scala 15:28]
    end else if (initDelay != 7'h0) begin // @[midas/src/main/scala/midas/widgets/Master.scala 16:29]
      initDelay <= _initDelay_T_1; // @[midas/src/main/scala/midas/widgets/Master.scala 16:41]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
      INIT_DONE <= 32'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
    end else if (crFile_io_mcr_write_0_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      INIT_DONE <= crFile_io_mcr_write_0_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      INIT_DONE <= {{31'd0}, _T_1}; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Master.scala 21:31]
      rFingerprint <= 32'h46697265; // @[midas/src/main/scala/midas/widgets/Master.scala 21:31]
    end else if (PRESENCE_WRITE != rFingerprint) begin // @[midas/src/main/scala/midas/widgets/Master.scala 25:41]
      rFingerprint <= PRESENCE_WRITE; // @[midas/src/main/scala/midas/widgets/Master.scala 26:20]
    end
    if (crFile_io_mcr_write_1_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      PRESENCE_READ <= crFile_io_mcr_write_1_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      PRESENCE_READ <= rFingerprint; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
      PRESENCE_WRITE <= 32'h46697265; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
    end else if (crFile_io_mcr_write_2_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      PRESENCE_WRITE <= crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  initDelay = _RAND_0[6:0];
  _RAND_1 = {1{`RANDOM}};
  INIT_DONE = _RAND_1[31:0];
  _RAND_2 = {1{`RANDOM}};
  rFingerprint = _RAND_2[31:0];
  _RAND_3 = {1{`RANDOM}};
  PRESENCE_READ = _RAND_3[31:0];
  _RAND_4 = {1{`RANDOM}};
  PRESENCE_WRITE = _RAND_4[31:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module MCRFile_1(
  input         clock,
  input         reset,
  output        io_nasti_aw_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_aw_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_aw_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_aw_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_w_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_w_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_nasti_w_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_b_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_b_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_b_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_ar_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_ar_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_ar_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_ar_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_r_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_r_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_nasti_r_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_r_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_0_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_1_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_read_2_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_2_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_3_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_4_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_read_5_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_5_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_0_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_0_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_1_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_1_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_2_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_2_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_3_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_3_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_4_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_4_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_5_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_5_bits // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
`endif // RANDOMIZE_REG_INIT
  reg  arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
  reg  awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
  reg  wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
  reg  wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
  reg [11:0] bId; // @[midas/src/main/scala/midas/widgets/Lib.scala 323:22]
  reg [11:0] rId; // @[midas/src/main/scala/midas/widgets/Lib.scala 324:22]
  reg [31:0] wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 326:22]
  reg [2:0] wIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 327:22]
  reg [2:0] rIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 328:22]
  wire  _T = io_nasti_aw_ready & io_nasti_aw_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_3 = ~reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
  wire  _GEN_0 = _T | awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 332:13 320:26]
  wire [22:0] _GEN_1 = _T ? io_nasti_aw_bits_addr[24:2] : {{20'd0}, wIndex}; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 333:13 327:22]
  wire  _T_5 = io_nasti_w_ready & io_nasti_w_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_3 = _T_5 | wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25 339:12 321:26]
  wire  _T_6 = io_nasti_ar_ready & io_nasti_ar_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_6 = _T_6 | arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26 345:13 319:26]
  wire  _T_11 = io_nasti_r_ready & io_nasti_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_12 = io_nasti_b_ready & io_nasti_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_12 = _T_12 ? 1'h0 : wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25 358:15 322:26]
  wire  _GEN_20 = 3'h1 == wIndex ? io_mcr_write_1_valid : io_mcr_write_0_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_21 = 3'h2 == wIndex ? io_mcr_write_2_valid : _GEN_20; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_22 = 3'h3 == wIndex ? io_mcr_write_3_valid : _GEN_21; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_23 = 3'h4 == wIndex ? io_mcr_write_4_valid : _GEN_22; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_24 = 3'h5 == wIndex ? io_mcr_write_5_valid : _GEN_23; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_25 = _GEN_24 | _GEN_12; // @[midas/src/main/scala/midas/widgets/Lib.scala 361:35 362:15]
  wire  _io_mcr_write_valid_T = awFired & wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 366:41]
  wire [31:0] _GEN_33 = 3'h1 == rIndex ? io_mcr_read_1_bits : io_mcr_read_0_bits; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_34 = 3'h2 == rIndex ? io_mcr_read_2_bits : _GEN_33; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_35 = 3'h3 == rIndex ? io_mcr_read_3_bits : _GEN_34; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_36 = 3'h4 == rIndex ? io_mcr_read_4_bits : _GEN_35; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  assign io_nasti_aw_ready = ~awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 380:24]
  assign io_nasti_w_ready = ~wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 381:24]
  assign io_nasti_b_valid = _io_mcr_write_valid_T & wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 377:41]
  assign io_nasti_b_bits_id = bId; // @[midas/src/main/scala/junctions/nasti.scala 129:17 130:12]
  assign io_nasti_ar_ready = ~arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 379:24]
  assign io_nasti_r_valid = arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 374:31]
  assign io_nasti_r_bits_data = 3'h5 == rIndex ? io_mcr_read_5_bits : _GEN_36; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  assign io_nasti_r_bits_id = rId; // @[midas/src/main/scala/junctions/nasti.scala 117:17 118:12]
  assign io_mcr_read_2_ready = rIndex == 3'h2 & arFired & io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Lib.scala 368:54]
  assign io_mcr_read_5_ready = rIndex == 3'h5 & arFired & io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Lib.scala 368:54]
  assign io_mcr_write_0_valid = 3'h0 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_0_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_1_valid = 3'h1 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_1_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_2_valid = 3'h2 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_2_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_3_valid = 3'h3 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_3_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_4_valid = 3'h4 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_4_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_5_valid = 3'h5 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_5_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
    end else if (_T_11) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 351:25]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 352:13]
    end else begin
      arFired <= _GEN_6;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 356:15]
    end else begin
      awFired <= _GEN_0;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 357:15]
    end else begin
      wFired <= _GEN_3;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
      wCommited <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
    end else begin
      wCommited <= _GEN_25;
    end
    if (_T) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26]
      bId <= io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 334:13]
    end
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rId <= io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 347:13]
    end
    if (_T_5) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25]
      wData <= io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Lib.scala 340:12]
    end
    wIndex <= _GEN_1[2:0];
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rIndex <= io_nasti_ar_bits_addr[4:2]; // @[midas/src/main/scala/midas/widgets/Lib.scala 346:13]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~reset & ~(io_nasti_aw_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Lib.scala:335 assert(io.nasti.aw.bits.len === 0.U)\n"); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_6 & _T_3 & ~(io_nasti_ar_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,
            "Assertion failed: MCRFile only support single beat reads\n    at Lib.scala:348 assert(io.nasti.ar.bits.len === 0.U, \"MCRFile only support single beat reads\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  arFired = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  awFired = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  wFired = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  wCommited = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  bId = _RAND_4[11:0];
  _RAND_5 = {1{`RANDOM}};
  rId = _RAND_5[11:0];
  _RAND_6 = {1{`RANDOM}};
  wData = _RAND_6[31:0];
  _RAND_7 = {1{`RANDOM}};
  wIndex = _RAND_7[2:0];
  _RAND_8 = {1{`RANDOM}};
  rIndex = _RAND_8[2:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (_T & ~reset) begin
      assert(io_nasti_aw_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
    end
    //
    if (_T_6 & _T_3) begin
      assert(io_nasti_ar_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
    end
  end
endmodule
module ClockBridgeModule(
  input         clock,
  input         reset,
  output        io_ctrl_aw_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         io_ctrl_aw_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [24:0] io_ctrl_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [7:0]  io_ctrl_aw_bits_len, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [11:0] io_ctrl_aw_bits_id, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output        io_ctrl_w_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         io_ctrl_w_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [31:0] io_ctrl_w_bits_data, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         io_ctrl_b_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output        io_ctrl_b_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output [11:0] io_ctrl_b_bits_id, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output        io_ctrl_ar_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         io_ctrl_ar_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [24:0] io_ctrl_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [7:0]  io_ctrl_ar_bits_len, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input  [11:0] io_ctrl_ar_bits_id, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         io_ctrl_r_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output        io_ctrl_r_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output [31:0] io_ctrl_r_bits_data, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  output [11:0] io_ctrl_r_bits_id, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 48:32]
  input         hPort_clocks_ready, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 49:32]
  output        hPort_clocks_valid, // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 49:32]
  output        hPort_clocks_bits_0 // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 49:32]
);
`ifdef RANDOMIZE_REG_INIT
  reg [63:0] _RAND_0;
  reg [63:0] _RAND_1;
  reg [63:0] _RAND_2;
  reg [63:0] _RAND_3;
`endif // RANDOMIZE_REG_INIT
  wire  crFile_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_2_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_5_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_0_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_1_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_2_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_3_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_4_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_5_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  reg [63:0] hCycle; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
  reg [63:0] hCycle_hCycle_mmreg; // @[midas/src/main/scala/midas/widgets/Widget.scala 151:26]
  wire [31:0] _GEN_3 = crFile_io_mcr_write_2_valid ? crFile_io_mcr_write_2_bits : 32'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  wire  hCycle_hCycle_latchEnable = _GEN_3[0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  wire [63:0] _hCycle_T_1 = hCycle + 64'h1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 56:22]
  reg [63:0] tCycleFastest; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
  reg [63:0] tCycleFastest_tCycle_mmreg; // @[midas/src/main/scala/midas/widgets/Widget.scala 151:26]
  wire [31:0] _GEN_4 = crFile_io_mcr_write_5_valid ? crFile_io_mcr_write_5_bits : 32'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  wire  tCycleFastest_tCycle_latchEnable = _GEN_4[0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  wire  _T = hPort_clocks_ready & hPort_clocks_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire [63:0] _tCycleFastest_T_1 = tCycleFastest + 64'h1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 69:38]
  wire  _T_4 = ~reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
  MCRFile_1 crFile ( // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
    .clock(crFile_clock),
    .reset(crFile_reset),
    .io_nasti_aw_ready(crFile_io_nasti_aw_ready),
    .io_nasti_aw_valid(crFile_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(crFile_io_nasti_aw_bits_addr),
    .io_nasti_aw_bits_len(crFile_io_nasti_aw_bits_len),
    .io_nasti_aw_bits_id(crFile_io_nasti_aw_bits_id),
    .io_nasti_w_ready(crFile_io_nasti_w_ready),
    .io_nasti_w_valid(crFile_io_nasti_w_valid),
    .io_nasti_w_bits_data(crFile_io_nasti_w_bits_data),
    .io_nasti_b_ready(crFile_io_nasti_b_ready),
    .io_nasti_b_valid(crFile_io_nasti_b_valid),
    .io_nasti_b_bits_id(crFile_io_nasti_b_bits_id),
    .io_nasti_ar_ready(crFile_io_nasti_ar_ready),
    .io_nasti_ar_valid(crFile_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(crFile_io_nasti_ar_bits_addr),
    .io_nasti_ar_bits_len(crFile_io_nasti_ar_bits_len),
    .io_nasti_ar_bits_id(crFile_io_nasti_ar_bits_id),
    .io_nasti_r_ready(crFile_io_nasti_r_ready),
    .io_nasti_r_valid(crFile_io_nasti_r_valid),
    .io_nasti_r_bits_data(crFile_io_nasti_r_bits_data),
    .io_nasti_r_bits_id(crFile_io_nasti_r_bits_id),
    .io_mcr_read_0_bits(crFile_io_mcr_read_0_bits),
    .io_mcr_read_1_bits(crFile_io_mcr_read_1_bits),
    .io_mcr_read_2_ready(crFile_io_mcr_read_2_ready),
    .io_mcr_read_2_bits(crFile_io_mcr_read_2_bits),
    .io_mcr_read_3_bits(crFile_io_mcr_read_3_bits),
    .io_mcr_read_4_bits(crFile_io_mcr_read_4_bits),
    .io_mcr_read_5_ready(crFile_io_mcr_read_5_ready),
    .io_mcr_read_5_bits(crFile_io_mcr_read_5_bits),
    .io_mcr_write_0_valid(crFile_io_mcr_write_0_valid),
    .io_mcr_write_0_bits(crFile_io_mcr_write_0_bits),
    .io_mcr_write_1_valid(crFile_io_mcr_write_1_valid),
    .io_mcr_write_1_bits(crFile_io_mcr_write_1_bits),
    .io_mcr_write_2_valid(crFile_io_mcr_write_2_valid),
    .io_mcr_write_2_bits(crFile_io_mcr_write_2_bits),
    .io_mcr_write_3_valid(crFile_io_mcr_write_3_valid),
    .io_mcr_write_3_bits(crFile_io_mcr_write_3_bits),
    .io_mcr_write_4_valid(crFile_io_mcr_write_4_valid),
    .io_mcr_write_4_bits(crFile_io_mcr_write_4_bits),
    .io_mcr_write_5_valid(crFile_io_mcr_write_5_valid),
    .io_mcr_write_5_bits(crFile_io_mcr_write_5_bits)
  );
  assign io_ctrl_aw_ready = crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_w_ready = crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_valid = crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_bits_id = crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_ar_ready = crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_valid = crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_data = crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_id = crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign hPort_clocks_valid = 1'h1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 52:18]
  assign hPort_clocks_bits_0 = 1'h1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 52:18]
  assign crFile_clock = clock;
  assign crFile_reset = reset;
  assign crFile_io_nasti_aw_valid = io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_addr = io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_len = io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_id = io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_valid = io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_bits_data = io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_b_ready = io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_valid = io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_addr = io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_len = io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_id = io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_r_ready = io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_mcr_read_0_bits = hCycle_hCycle_mmreg[31:0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_1_bits = hCycle_hCycle_mmreg[63:32]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_2_bits = 32'h0;
  assign crFile_io_mcr_read_3_bits = tCycleFastest_tCycle_mmreg[31:0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_4_bits = tCycleFastest_tCycle_mmreg[63:32]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_5_bits = 32'h0;
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
      hCycle <= 64'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
    end else begin
      hCycle <= _hCycle_T_1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 56:12]
    end
    if (hCycle_hCycle_latchEnable) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 161:23]
      hCycle_hCycle_mmreg <= hCycle; // @[midas/src/main/scala/midas/widgets/Widget.scala 162:17]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
      tCycleFastest <= 64'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
    end else if (_T & hPort_clocks_bits_0) begin // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 68:67]
      tCycleFastest <= _tCycleFastest_T_1; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 69:21]
    end
    if (tCycleFastest_tCycle_latchEnable) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 161:23]
      tCycleFastest_tCycle_mmreg <= tCycleFastest; // @[midas/src/main/scala/midas/widgets/Widget.scala 162:17]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_0_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register hCycle_0 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_1_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register hCycle_1 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_4 & ~(~crFile_io_mcr_read_2_ready)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register ${reg.name} is write only\n    at Lib.scala:293 assert(read(index).ready === false.B, \"Register ${reg.name} is write only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_3_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register tCycle_0 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_4_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register tCycle_1 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_4 & ~(~crFile_io_mcr_read_5_ready)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register ${reg.name} is write only\n    at Lib.scala:293 assert(read(index).ready === false.B, \"Register ${reg.name} is write only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {2{`RANDOM}};
  hCycle = _RAND_0[63:0];
  _RAND_1 = {2{`RANDOM}};
  hCycle_hCycle_mmreg = _RAND_1[63:0];
  _RAND_2 = {2{`RANDOM}};
  tCycleFastest = _RAND_2[63:0];
  _RAND_3 = {2{`RANDOM}};
  tCycleFastest_tCycle_mmreg = _RAND_3[63:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_0_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_1_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (_T_4) begin
      assert(~crFile_io_mcr_read_2_ready); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_3_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_4_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (_T_4) begin
      assert(~crFile_io_mcr_read_5_ready); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
    end
  end
endmodule
module Queue(
  input         clock,
  input         reset,
  output        io_enq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_enq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input  [31:0] io_enq_bits, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_deq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output        io_deq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output [31:0] io_deq_bits // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
`endif // RANDOMIZE_REG_INIT
  reg [31:0] ram [0:1]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [31:0] ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire [31:0] ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg  enq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg  deq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg  maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
  wire  ptr_match = enq_ptr_value == deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 283:33]
  wire  empty = ptr_match & ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 284:25]
  wire  full = ptr_match & maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 285:24]
  wire  do_enq = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  do_deq = io_deq_ready & io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_addr = deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_data = ram[ram_io_deq_bits_MPORT_addr]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_MPORT_data = io_enq_bits; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_addr = enq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign io_enq_ready = ~full; // @[src/main/scala/chisel3/util/Decoupled.scala 309:19]
  assign io_deq_valid = ~empty; // @[src/main/scala/chisel3/util/Decoupled.scala 308:19]
  assign io_deq_bits = ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  always @(posedge clock) begin
    if (ram_MPORT_en & ram_MPORT_mask) begin
      ram[ram_MPORT_addr] <= ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      enq_ptr_value <= 1'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_enq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 292:16]
      enq_ptr_value <= enq_ptr_value + 1'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      deq_ptr_value <= 1'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 296:16]
      deq_ptr_value <= deq_ptr_value + 1'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
      maybe_full <= 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
    end else if (do_enq != do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 299:27]
      maybe_full <= do_enq; // @[src/main/scala/chisel3/util/Decoupled.scala 300:16]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 2; initvar = initvar+1)
    ram[initvar] = _RAND_0[31:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  enq_ptr_value = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  deq_ptr_value = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  maybe_full = _RAND_3[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module SatUpDownCounter(
  input        clock,
  input        reset,
  input        io_inc, // @[midas/src/main/scala/midas/widgets/Lib.scala 73:17]
  input        io_dec, // @[midas/src/main/scala/midas/widgets/Lib.scala 73:17]
  output [1:0] io_value, // @[midas/src/main/scala/midas/widgets/Lib.scala 73:17]
  output       io_full, // @[midas/src/main/scala/midas/widgets/Lib.scala 73:17]
  output       io_empty // @[midas/src/main/scala/midas/widgets/Lib.scala 73:17]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_REG_INIT
  reg [1:0] value; // @[midas/src/main/scala/midas/widgets/Lib.scala 74:22]
  wire [1:0] _value_T_1 = value + 2'h1; // @[midas/src/main/scala/midas/widgets/Lib.scala 82:20]
  wire [1:0] _value_T_3 = value - 2'h1; // @[midas/src/main/scala/midas/widgets/Lib.scala 84:20]
  assign io_value = value; // @[midas/src/main/scala/midas/widgets/Lib.scala 75:12 79:22 80:14]
  assign io_full = value >= 2'h2; // @[midas/src/main/scala/midas/widgets/Lib.scala 76:21]
  assign io_empty = value == 2'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 77:21]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 74:22]
      value <= 2'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 74:22]
    end else if (io_inc & ~io_dec & ~io_full) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 81:45]
      value <= _value_T_1; // @[midas/src/main/scala/midas/widgets/Lib.scala 82:11]
    end else if (~io_inc & io_dec & ~io_empty) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 83:46]
      value <= _value_T_3; // @[midas/src/main/scala/midas/widgets/Lib.scala 84:11]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  value = _RAND_0[1:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module MCRFile_2(
  input         clock,
  input         reset,
  output        io_nasti_aw_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_aw_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_aw_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_aw_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_w_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_w_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_nasti_w_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_b_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_b_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_b_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_ar_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_ar_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [24:0] io_nasti_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [7:0]  io_nasti_ar_bits_len, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [11:0] io_nasti_ar_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_nasti_r_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_nasti_r_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_nasti_r_bits_data, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [11:0] io_nasti_r_bits_id, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_0_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_1_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_read_2_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_read_3_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_4_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_5_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_6_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_7_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_8_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_9_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_10_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input  [31:0] io_mcr_read_11_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_0_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_1_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_2_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_2_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  input         io_mcr_write_3_ready, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_3_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_3_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_4_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_4_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_5_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_5_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_6_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_6_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_7_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_7_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_8_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_8_bits, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_9_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_10_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output        io_mcr_write_11_valid, // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
  output [31:0] io_mcr_write_11_bits // @[midas/src/main/scala/midas/widgets/Lib.scala 312:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
`endif // RANDOMIZE_REG_INIT
  reg  arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
  reg  awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
  reg  wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
  reg  wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
  reg [11:0] bId; // @[midas/src/main/scala/midas/widgets/Lib.scala 323:22]
  reg [11:0] rId; // @[midas/src/main/scala/midas/widgets/Lib.scala 324:22]
  reg [31:0] wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 326:22]
  reg [3:0] wIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 327:22]
  reg [3:0] rIndex; // @[midas/src/main/scala/midas/widgets/Lib.scala 328:22]
  wire  _T = io_nasti_aw_ready & io_nasti_aw_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_3 = ~reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
  wire  _GEN_0 = _T | awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 332:13 320:26]
  wire [22:0] _GEN_1 = _T ? io_nasti_aw_bits_addr[24:2] : {{19'd0}, wIndex}; // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26 333:13 327:22]
  wire  _T_5 = io_nasti_w_ready & io_nasti_w_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_3 = _T_5 | wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25 339:12 321:26]
  wire  _T_6 = io_nasti_ar_ready & io_nasti_ar_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_6 = _T_6 | arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26 345:13 319:26]
  wire  _T_11 = io_nasti_r_ready & io_nasti_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_12 = io_nasti_b_ready & io_nasti_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_12 = _T_12 ? 1'h0 : wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25 358:15 322:26]
  wire  _GEN_16 = 4'h3 == wIndex ? io_mcr_write_3_ready : 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_74 = 4'h4 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_75 = 4'h5 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_76 = 4'h6 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_77 = 4'h7 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_78 = 4'h8 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_79 = 4'h9 == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_80 = 4'ha == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_81 = 4'hb == wIndex; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_26 = 4'h1 == wIndex ? io_mcr_write_1_valid : io_mcr_write_0_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_27 = 4'h2 == wIndex ? io_mcr_write_2_valid : _GEN_26; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_28 = 4'h3 == wIndex ? io_mcr_write_3_valid : _GEN_27; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_29 = 4'h4 == wIndex ? io_mcr_write_4_valid : _GEN_28; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_30 = 4'h5 == wIndex ? io_mcr_write_5_valid : _GEN_29; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_31 = 4'h6 == wIndex ? io_mcr_write_6_valid : _GEN_30; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_32 = 4'h7 == wIndex ? io_mcr_write_7_valid : _GEN_31; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_33 = 4'h8 == wIndex ? io_mcr_write_8_valid : _GEN_32; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_34 = 4'h9 == wIndex ? io_mcr_write_9_valid : _GEN_33; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_35 = 4'ha == wIndex ? io_mcr_write_10_valid : _GEN_34; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _GEN_36 = 4'hb == wIndex ? io_mcr_write_11_valid : _GEN_35; // @[src/main/scala/chisel3/util/Decoupled.scala 57:{35,35}]
  wire  _T_13 = (4'hb == wIndex | (4'ha == wIndex | (4'h9 == wIndex | (4'h8 == wIndex | (4'h7 == wIndex | (4'h6 ==
    wIndex | (4'h5 == wIndex | (4'h4 == wIndex | _GEN_16)))))))) & _GEN_36; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_37 = _T_13 | _GEN_12; // @[midas/src/main/scala/midas/widgets/Lib.scala 361:35 362:15]
  wire  _io_mcr_write_valid_T = awFired & wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 366:41]
  wire [31:0] _GEN_51 = 4'h1 == rIndex ? io_mcr_read_1_bits : io_mcr_read_0_bits; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_52 = 4'h2 == rIndex ? 32'h0 : _GEN_51; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_53 = 4'h3 == rIndex ? 32'h0 : _GEN_52; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_54 = 4'h4 == rIndex ? io_mcr_read_4_bits : _GEN_53; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_55 = 4'h5 == rIndex ? io_mcr_read_5_bits : _GEN_54; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_56 = 4'h6 == rIndex ? io_mcr_read_6_bits : _GEN_55; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_57 = 4'h7 == rIndex ? io_mcr_read_7_bits : _GEN_56; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_58 = 4'h8 == rIndex ? io_mcr_read_8_bits : _GEN_57; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_59 = 4'h9 == rIndex ? io_mcr_read_9_bits : _GEN_58; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire [31:0] _GEN_60 = 4'ha == rIndex ? io_mcr_read_10_bits : _GEN_59; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  wire  _GEN_65 = 4'h3 == rIndex ? 1'h0 : 1'h1; // @[midas/src/main/scala/midas/widgets/Lib.scala 374:{31,31}]
  assign io_nasti_aw_ready = ~awFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 380:24]
  assign io_nasti_w_ready = ~wFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 381:24]
  assign io_nasti_b_valid = _io_mcr_write_valid_T & wCommited; // @[midas/src/main/scala/midas/widgets/Lib.scala 377:41]
  assign io_nasti_b_bits_id = bId; // @[midas/src/main/scala/junctions/nasti.scala 129:17 130:12]
  assign io_nasti_ar_ready = ~arFired; // @[midas/src/main/scala/midas/widgets/Lib.scala 379:24]
  assign io_nasti_r_valid = arFired & (4'hb == rIndex | (4'ha == rIndex | (4'h9 == rIndex | (4'h8 == rIndex | (4'h7 ==
    rIndex | (4'h6 == rIndex | (4'h5 == rIndex | (4'h4 == rIndex | _GEN_65)))))))); // @[midas/src/main/scala/midas/widgets/Lib.scala 374:31]
  assign io_nasti_r_bits_data = 4'hb == rIndex ? io_mcr_read_11_bits : _GEN_60; // @[midas/src/main/scala/junctions/nasti.scala 119:{12,12}]
  assign io_nasti_r_bits_id = rId; // @[midas/src/main/scala/junctions/nasti.scala 117:17 118:12]
  assign io_mcr_read_2_ready = rIndex == 4'h2 & arFired & io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Lib.scala 368:54]
  assign io_mcr_read_3_ready = rIndex == 4'h3 & arFired & io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Lib.scala 368:54]
  assign io_mcr_write_0_valid = 4'h0 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_1_valid = 4'h1 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_2_valid = 4'h2 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_2_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_3_valid = 4'h3 == wIndex & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_3_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_4_valid = _GEN_74 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_4_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_5_valid = _GEN_75 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_5_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_6_valid = _GEN_76 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_6_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_7_valid = _GEN_77 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_7_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_8_valid = _GEN_78 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_8_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  assign io_mcr_write_9_valid = _GEN_79 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_10_valid = _GEN_80 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_11_valid = _GEN_81 & (awFired & wFired & ~wCommited); // @[midas/src/main/scala/midas/widgets/Lib.scala 366:{30,30} 365:39]
  assign io_mcr_write_11_bits = wData; // @[midas/src/main/scala/midas/widgets/Lib.scala 365:58]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 319:26]
    end else if (_T_11) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 351:25]
      arFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 352:13]
    end else begin
      arFired <= _GEN_6;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 320:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      awFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 356:15]
    end else begin
      awFired <= _GEN_0;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 321:26]
    end else if (_T_12) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 355:25]
      wFired <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 357:15]
    end else begin
      wFired <= _GEN_3;
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
      wCommited <= 1'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 322:26]
    end else begin
      wCommited <= _GEN_37;
    end
    if (_T) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 331:26]
      bId <= io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 334:13]
    end
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rId <= io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Lib.scala 347:13]
    end
    if (_T_5) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 338:25]
      wData <= io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Lib.scala 340:12]
    end
    wIndex <= _GEN_1[3:0];
    if (_T_6) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 344:26]
      rIndex <= io_nasti_ar_bits_addr[5:2]; // @[midas/src/main/scala/midas/widgets/Lib.scala 346:13]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~reset & ~(io_nasti_aw_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Lib.scala:335 assert(io.nasti.aw.bits.len === 0.U)\n"); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_6 & _T_3 & ~(io_nasti_ar_bits_len == 8'h0)) begin
          $fwrite(32'h80000002,
            "Assertion failed: MCRFile only support single beat reads\n    at Lib.scala:348 assert(io.nasti.ar.bits.len === 0.U, \"MCRFile only support single beat reads\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  arFired = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  awFired = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  wFired = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  wCommited = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  bId = _RAND_4[11:0];
  _RAND_5 = {1{`RANDOM}};
  rId = _RAND_5[11:0];
  _RAND_6 = {1{`RANDOM}};
  wData = _RAND_6[31:0];
  _RAND_7 = {1{`RANDOM}};
  wIndex = _RAND_7[3:0];
  _RAND_8 = {1{`RANDOM}};
  rIndex = _RAND_8[3:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (_T & ~reset) begin
      assert(io_nasti_aw_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 335:11]
    end
    //
    if (_T_6 & _T_3) begin
      assert(io_nasti_ar_bits_len == 8'h0); // @[midas/src/main/scala/midas/widgets/Lib.scala 348:11]
    end
  end
endmodule
module PeekPokeBridgeModule(
  input         clock,
  input         reset,
  output        io_ctrl_aw_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input         io_ctrl_aw_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [24:0] io_ctrl_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [7:0]  io_ctrl_aw_bits_len, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [11:0] io_ctrl_aw_bits_id, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output        io_ctrl_w_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input         io_ctrl_w_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [31:0] io_ctrl_w_bits_data, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input         io_ctrl_b_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output        io_ctrl_b_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output [11:0] io_ctrl_b_bits_id, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output        io_ctrl_ar_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input         io_ctrl_ar_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [24:0] io_ctrl_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [7:0]  io_ctrl_ar_bits_len, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input  [11:0] io_ctrl_ar_bits_id, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  input         io_ctrl_r_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output        io_ctrl_r_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output [31:0] io_ctrl_r_bits_data, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output [11:0] io_ctrl_r_bits_id, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 21:19]
  output        hPort_io_z_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_z_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input  [15:0] hPort_io_z_bits, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_io_v_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_v_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_v_bits, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_a_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_io_a_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output [15:0] hPort_io_a_bits, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_b_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_io_b_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output [15:0] hPort_io_b_bits, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_io_e_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_io_e_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_io_e_bits, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  input         hPort_reset_ready, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_reset_valid, // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
  output        hPort_reset_bits // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 22:19]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [63:0] _RAND_1;
  reg [63:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [31:0] _RAND_14;
`endif // RANDOMIZE_REG_INIT
  wire  step_q_clock; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  step_q_reset; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  step_q_io_enq_ready; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  step_q_io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire [31:0] step_q_io_enq_bits; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  step_q_io_deq_ready; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  step_q_io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire [31:0] step_q_io_deq_bits; // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
  wire  SatUpDownCounter_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_1_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_1_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_2_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_2_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_3_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_3_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_4_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_4_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_clock; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_io_inc; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_io_dec; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire [1:0] SatUpDownCounter_5_io_value; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_io_full; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  SatUpDownCounter_5_io_empty; // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
  wire  crFile_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_2_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_3_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_6_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_7_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_8_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_9_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_10_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_11_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_0_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_1_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_2_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_3_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_3_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_4_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_5_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_6_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_6_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_7_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_7_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_8_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_8_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_9_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_10_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_11_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_11_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  reg [31:0] cycleHorizon; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 27:34]
  reg [63:0] tCycle; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
  reg [63:0] tCycle_tCycle_mmreg; // @[midas/src/main/scala/midas/widgets/Widget.scala 151:26]
  wire [31:0] _GEN_15 = crFile_io_mcr_write_2_valid ? crFile_io_mcr_write_2_bits : 32'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  wire  tCycle_tCycle_latchEnable = _GEN_15[0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 159:31]
  reg [31:0] DONE; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  wire  done = cycleHorizon == 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 38:26]
  reg  target_reset_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_1 = hPort_reset_ready & hPort_reset_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead = ~SatUpDownCounter_io_empty | _isAhead_T_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 55:44]
  reg  wordsReceived; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
  wire  reset_poke = crFile_io_mcr_write_5_valid; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 133:13 63:32]
  wire [31:0] _GEN_22 = {{30'd0}, SatUpDownCounter_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:63]
  reg  target_io_e_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_3 = hPort_io_e_ready & hPort_io_e_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead_1 = ~SatUpDownCounter_1_io_empty | _isAhead_T_3; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 55:44]
  reg  wordsReceived_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
  wire  io_e_poke = crFile_io_mcr_write_6_valid; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 133:13 63:32]
  wire [31:0] _GEN_23 = {{30'd0}, SatUpDownCounter_1_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:63]
  reg [15:0] target_io_b_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_5 = hPort_io_b_ready & hPort_io_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead_2 = ~SatUpDownCounter_2_io_empty | _isAhead_T_5; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 55:44]
  reg  wordsReceived_2; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
  wire  io_b_poke = crFile_io_mcr_write_7_valid; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 133:13 63:32]
  wire [31:0] _GEN_24 = {{30'd0}, SatUpDownCounter_2_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:63]
  reg [15:0] target_io_a_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_7 = hPort_io_a_ready & hPort_io_a_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead_3 = ~SatUpDownCounter_3_io_empty | _isAhead_T_7; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 55:44]
  reg  wordsReceived_3; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
  wire  io_a_poke = crFile_io_mcr_write_8_valid; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 133:13 63:32]
  wire [31:0] _GEN_25 = {{30'd0}, SatUpDownCounter_3_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:63]
  reg  target_io_v_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_9 = hPort_io_v_ready & hPort_io_v_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead_4 = ~SatUpDownCounter_4_io_empty | _isAhead_T_9; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 87:44]
  wire [31:0] _hPort_io_v_ready_T_1 = cycleHorizon + 32'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 95:58]
  wire [31:0] _GEN_26 = {{30'd0}, SatUpDownCounter_4_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 95:42]
  wire  _T_10 = SatUpDownCounter_4_io_value == 2'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 104:55]
  reg [15:0] target_io_z_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire  _isAhead_T_11 = hPort_io_z_ready & hPort_io_z_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  isAhead_5 = ~SatUpDownCounter_5_io_empty | _isAhead_T_11; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 87:44]
  wire [31:0] _GEN_27 = {{30'd0}, SatUpDownCounter_5_io_value}; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 95:42]
  wire  _T_13 = SatUpDownCounter_5_io_value == 2'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 104:55]
  wire  _T_15 = done & _T_10 & _T_13; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 112:64]
  reg [31:0] PRECISE_PEEKABLE; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  wire  tCycleWouldAdvance = isAhead & isAhead_1 & isAhead_2 & isAhead_3 & isAhead_4 & isAhead_5; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 114:62]
  wire  tCycleAdvancing = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  wire [63:0] _tCycle_T_1 = tCycle + 64'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 118:33]
  wire [31:0] _cycleHorizon_T_1 = cycleHorizon - 32'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 119:39]
  wire  step_valid = step_q_io_deq_valid; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 33:20 midas/src/main/scala/midas/widgets/Widget.scala 116:13]
  wire  _T_18 = done & step_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire [31:0] step_bits = step_q_io_deq_bits; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 33:20 midas/src/main/scala/midas/widgets/Widget.scala 116:13]
  wire  _T_21 = ~reset; // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
  wire [31:0] _GEN_17 = crFile_io_mcr_write_5_valid ? crFile_io_mcr_write_5_bits : {{31'd0}, target_reset_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire [31:0] _GEN_18 = crFile_io_mcr_write_6_valid ? crFile_io_mcr_write_6_bits : {{31'd0}, target_io_e_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire [31:0] _GEN_19 = crFile_io_mcr_write_7_valid ? crFile_io_mcr_write_7_bits : {{16'd0}, target_io_b_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  wire [31:0] _GEN_20 = crFile_io_mcr_write_8_valid ? crFile_io_mcr_write_8_bits : {{16'd0}, target_io_a_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/PeekPokeIO.scala 43:12]
  Queue step_q ( // @[src/main/scala/chisel3/util/Decoupled.scala 381:21]
    .clock(step_q_clock),
    .reset(step_q_reset),
    .io_enq_ready(step_q_io_enq_ready),
    .io_enq_valid(step_q_io_enq_valid),
    .io_enq_bits(step_q_io_enq_bits),
    .io_deq_ready(step_q_io_deq_ready),
    .io_deq_valid(step_q_io_deq_valid),
    .io_deq_bits(step_q_io_deq_bits)
  );
  SatUpDownCounter SatUpDownCounter ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_clock),
    .reset(SatUpDownCounter_reset),
    .io_inc(SatUpDownCounter_io_inc),
    .io_dec(SatUpDownCounter_io_dec),
    .io_value(SatUpDownCounter_io_value),
    .io_full(SatUpDownCounter_io_full),
    .io_empty(SatUpDownCounter_io_empty)
  );
  SatUpDownCounter SatUpDownCounter_1 ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_1_clock),
    .reset(SatUpDownCounter_1_reset),
    .io_inc(SatUpDownCounter_1_io_inc),
    .io_dec(SatUpDownCounter_1_io_dec),
    .io_value(SatUpDownCounter_1_io_value),
    .io_full(SatUpDownCounter_1_io_full),
    .io_empty(SatUpDownCounter_1_io_empty)
  );
  SatUpDownCounter SatUpDownCounter_2 ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_2_clock),
    .reset(SatUpDownCounter_2_reset),
    .io_inc(SatUpDownCounter_2_io_inc),
    .io_dec(SatUpDownCounter_2_io_dec),
    .io_value(SatUpDownCounter_2_io_value),
    .io_full(SatUpDownCounter_2_io_full),
    .io_empty(SatUpDownCounter_2_io_empty)
  );
  SatUpDownCounter SatUpDownCounter_3 ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_3_clock),
    .reset(SatUpDownCounter_3_reset),
    .io_inc(SatUpDownCounter_3_io_inc),
    .io_dec(SatUpDownCounter_3_io_dec),
    .io_value(SatUpDownCounter_3_io_value),
    .io_full(SatUpDownCounter_3_io_full),
    .io_empty(SatUpDownCounter_3_io_empty)
  );
  SatUpDownCounter SatUpDownCounter_4 ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_4_clock),
    .reset(SatUpDownCounter_4_reset),
    .io_inc(SatUpDownCounter_4_io_inc),
    .io_dec(SatUpDownCounter_4_io_dec),
    .io_value(SatUpDownCounter_4_io_value),
    .io_full(SatUpDownCounter_4_io_full),
    .io_empty(SatUpDownCounter_4_io_empty)
  );
  SatUpDownCounter SatUpDownCounter_5 ( // @[midas/src/main/scala/midas/widgets/Lib.scala 90:20]
    .clock(SatUpDownCounter_5_clock),
    .reset(SatUpDownCounter_5_reset),
    .io_inc(SatUpDownCounter_5_io_inc),
    .io_dec(SatUpDownCounter_5_io_dec),
    .io_value(SatUpDownCounter_5_io_value),
    .io_full(SatUpDownCounter_5_io_full),
    .io_empty(SatUpDownCounter_5_io_empty)
  );
  MCRFile_2 crFile ( // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
    .clock(crFile_clock),
    .reset(crFile_reset),
    .io_nasti_aw_ready(crFile_io_nasti_aw_ready),
    .io_nasti_aw_valid(crFile_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(crFile_io_nasti_aw_bits_addr),
    .io_nasti_aw_bits_len(crFile_io_nasti_aw_bits_len),
    .io_nasti_aw_bits_id(crFile_io_nasti_aw_bits_id),
    .io_nasti_w_ready(crFile_io_nasti_w_ready),
    .io_nasti_w_valid(crFile_io_nasti_w_valid),
    .io_nasti_w_bits_data(crFile_io_nasti_w_bits_data),
    .io_nasti_b_ready(crFile_io_nasti_b_ready),
    .io_nasti_b_valid(crFile_io_nasti_b_valid),
    .io_nasti_b_bits_id(crFile_io_nasti_b_bits_id),
    .io_nasti_ar_ready(crFile_io_nasti_ar_ready),
    .io_nasti_ar_valid(crFile_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(crFile_io_nasti_ar_bits_addr),
    .io_nasti_ar_bits_len(crFile_io_nasti_ar_bits_len),
    .io_nasti_ar_bits_id(crFile_io_nasti_ar_bits_id),
    .io_nasti_r_ready(crFile_io_nasti_r_ready),
    .io_nasti_r_valid(crFile_io_nasti_r_valid),
    .io_nasti_r_bits_data(crFile_io_nasti_r_bits_data),
    .io_nasti_r_bits_id(crFile_io_nasti_r_bits_id),
    .io_mcr_read_0_bits(crFile_io_mcr_read_0_bits),
    .io_mcr_read_1_bits(crFile_io_mcr_read_1_bits),
    .io_mcr_read_2_ready(crFile_io_mcr_read_2_ready),
    .io_mcr_read_3_ready(crFile_io_mcr_read_3_ready),
    .io_mcr_read_4_bits(crFile_io_mcr_read_4_bits),
    .io_mcr_read_5_bits(crFile_io_mcr_read_5_bits),
    .io_mcr_read_6_bits(crFile_io_mcr_read_6_bits),
    .io_mcr_read_7_bits(crFile_io_mcr_read_7_bits),
    .io_mcr_read_8_bits(crFile_io_mcr_read_8_bits),
    .io_mcr_read_9_bits(crFile_io_mcr_read_9_bits),
    .io_mcr_read_10_bits(crFile_io_mcr_read_10_bits),
    .io_mcr_read_11_bits(crFile_io_mcr_read_11_bits),
    .io_mcr_write_0_valid(crFile_io_mcr_write_0_valid),
    .io_mcr_write_1_valid(crFile_io_mcr_write_1_valid),
    .io_mcr_write_2_valid(crFile_io_mcr_write_2_valid),
    .io_mcr_write_2_bits(crFile_io_mcr_write_2_bits),
    .io_mcr_write_3_ready(crFile_io_mcr_write_3_ready),
    .io_mcr_write_3_valid(crFile_io_mcr_write_3_valid),
    .io_mcr_write_3_bits(crFile_io_mcr_write_3_bits),
    .io_mcr_write_4_valid(crFile_io_mcr_write_4_valid),
    .io_mcr_write_4_bits(crFile_io_mcr_write_4_bits),
    .io_mcr_write_5_valid(crFile_io_mcr_write_5_valid),
    .io_mcr_write_5_bits(crFile_io_mcr_write_5_bits),
    .io_mcr_write_6_valid(crFile_io_mcr_write_6_valid),
    .io_mcr_write_6_bits(crFile_io_mcr_write_6_bits),
    .io_mcr_write_7_valid(crFile_io_mcr_write_7_valid),
    .io_mcr_write_7_bits(crFile_io_mcr_write_7_bits),
    .io_mcr_write_8_valid(crFile_io_mcr_write_8_valid),
    .io_mcr_write_8_bits(crFile_io_mcr_write_8_bits),
    .io_mcr_write_9_valid(crFile_io_mcr_write_9_valid),
    .io_mcr_write_10_valid(crFile_io_mcr_write_10_valid),
    .io_mcr_write_11_valid(crFile_io_mcr_write_11_valid),
    .io_mcr_write_11_bits(crFile_io_mcr_write_11_bits)
  );
  assign io_ctrl_aw_ready = crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_w_ready = crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_valid = crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_bits_id = crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_ar_ready = crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_valid = crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_data = crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_id = crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign hPort_io_z_ready = _GEN_27 < _hPort_io_v_ready_T_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 95:42]
  assign hPort_io_v_ready = _GEN_26 < _hPort_io_v_ready_T_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 95:42]
  assign hPort_io_a_valid = ~SatUpDownCounter_3_io_full & _GEN_25 < cycleHorizon | wordsReceived_3; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:78]
  assign hPort_io_a_bits = target_io_a_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 74:{49,49}]
  assign hPort_io_b_valid = ~SatUpDownCounter_2_io_full & _GEN_24 < cycleHorizon | wordsReceived_2; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:78]
  assign hPort_io_b_bits = target_io_b_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 74:{49,49}]
  assign hPort_io_e_valid = ~SatUpDownCounter_1_io_full & _GEN_23 < cycleHorizon | wordsReceived_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:78]
  assign hPort_io_e_bits = target_io_e_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 74:{49,49}]
  assign hPort_reset_valid = ~SatUpDownCounter_io_full & _GEN_22 < cycleHorizon | wordsReceived; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 75:78]
  assign hPort_reset_bits = target_reset_i; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 74:{49,49}]
  assign step_q_clock = clock;
  assign step_q_reset = reset;
  assign step_q_io_enq_valid = crFile_io_mcr_write_3_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 115:19 midas/src/main/scala/midas/widgets/Lib.scala 301:18]
  assign step_q_io_enq_bits = crFile_io_mcr_write_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 115:19 midas/src/main/scala/midas/widgets/Lib.scala 301:18]
  assign step_q_io_deq_ready = cycleHorizon == 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 38:26]
  assign SatUpDownCounter_clock = clock;
  assign SatUpDownCounter_reset = reset;
  assign SatUpDownCounter_io_inc = hPort_reset_ready & hPort_reset_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign SatUpDownCounter_1_clock = clock;
  assign SatUpDownCounter_1_reset = reset;
  assign SatUpDownCounter_1_io_inc = hPort_io_e_ready & hPort_io_e_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_1_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign SatUpDownCounter_2_clock = clock;
  assign SatUpDownCounter_2_reset = reset;
  assign SatUpDownCounter_2_io_inc = hPort_io_b_ready & hPort_io_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_2_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign SatUpDownCounter_3_clock = clock;
  assign SatUpDownCounter_3_reset = reset;
  assign SatUpDownCounter_3_io_inc = hPort_io_a_ready & hPort_io_a_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_3_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign SatUpDownCounter_4_clock = clock;
  assign SatUpDownCounter_4_reset = reset;
  assign SatUpDownCounter_4_io_inc = hPort_io_v_ready & hPort_io_v_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_4_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign SatUpDownCounter_5_clock = clock;
  assign SatUpDownCounter_5_reset = reset;
  assign SatUpDownCounter_5_io_inc = hPort_io_z_ready & hPort_io_z_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign SatUpDownCounter_5_io_dec = tCycleWouldAdvance & cycleHorizon > 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:29]
  assign crFile_clock = clock;
  assign crFile_reset = reset;
  assign crFile_io_nasti_aw_valid = io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_addr = io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_len = io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_id = io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_valid = io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_bits_data = io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_b_ready = io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_valid = io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_addr = io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_len = io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_id = io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_r_ready = io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_mcr_read_0_bits = tCycle_tCycle_mmreg[31:0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_1_bits = tCycle_tCycle_mmreg[63:32]; // @[midas/src/main/scala/midas/widgets/Widget.scala 155:28]
  assign crFile_io_mcr_read_4_bits = DONE; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_5_bits = {{31'd0}, target_reset_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_6_bits = {{31'd0}, target_io_e_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_7_bits = {{16'd0}, target_io_b_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_8_bits = {{16'd0}, target_io_a_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_9_bits = {{31'd0}, target_io_v_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_10_bits = {{16'd0}, target_io_z_i}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_11_bits = PRECISE_PEEKABLE; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_write_3_ready = step_q_io_enq_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 115:19 src/main/scala/chisel3/util/Decoupled.scala 385:17]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 27:34]
      cycleHorizon <= 32'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 27:34]
    end else if (_T_18) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 123:21]
      cycleHorizon <= step_bits; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 124:20]
    end else if (tCycleAdvancing) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:52]
      cycleHorizon <= _cycleHorizon_T_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 119:23]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
      tCycle <= 64'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 150:30]
    end else if (tCycleAdvancing) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 117:52]
      tCycle <= _tCycle_T_1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 118:23]
    end
    if (tCycle_tCycle_latchEnable) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 161:23]
      tCycle_tCycle_mmreg <= tCycle; // @[midas/src/main/scala/midas/widgets/Widget.scala 162:17]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
      DONE <= 32'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
    end else if (crFile_io_mcr_write_4_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      DONE <= crFile_io_mcr_write_4_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      DONE <= {{31'd0}, done}; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
    target_reset_i <= _GEN_17[0];
    if (reset) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
      wordsReceived <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
    end else if (reset_poke) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 68:18]
      wordsReceived <= wordsReceived + 1'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 69:23]
    end else if (_isAhead_T_1) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 70:32]
      wordsReceived <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 71:23]
    end
    target_io_e_i <= _GEN_18[0];
    if (reset) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
      wordsReceived_1 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
    end else if (io_e_poke) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 68:18]
      wordsReceived_1 <= wordsReceived_1 + 1'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 69:23]
    end else if (_isAhead_T_3) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 70:32]
      wordsReceived_1 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 71:23]
    end
    target_io_b_i <= _GEN_19[15:0];
    if (reset) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
      wordsReceived_2 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
    end else if (io_b_poke) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 68:18]
      wordsReceived_2 <= wordsReceived_2 + 1'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 69:23]
    end else if (_isAhead_T_5) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 70:32]
      wordsReceived_2 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 71:23]
    end
    target_io_a_i <= _GEN_20[15:0];
    if (reset) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
      wordsReceived_3 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 65:35]
    end else if (io_a_poke) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 68:18]
      wordsReceived_3 <= wordsReceived_3 + 1'h1; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 69:23]
    end else if (_isAhead_T_7) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 70:32]
      wordsReceived_3 <= 1'h0; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 71:23]
    end
    if (_isAhead_T_9) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 96:26]
      target_io_v_i <= hPort_io_v_bits; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 99:15]
    end
    if (_isAhead_T_11) begin // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 96:26]
      target_io_z_i <= hPort_io_z_bits; // @[midas/src/main/scala/midas/widgets/PeekPokeIO.scala 99:15]
    end
    if (reset) begin // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
      PRECISE_PEEKABLE <= 32'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
    end else if (crFile_io_mcr_write_11_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      PRECISE_PEEKABLE <= crFile_io_mcr_write_11_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      PRECISE_PEEKABLE <= {{31'd0}, _T_15}; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_0_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register tCycle_0 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_1_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register tCycle_1 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_21 & ~(~crFile_io_mcr_read_2_ready)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register ${reg.name} is write only\n    at Lib.scala:293 assert(read(index).ready === false.B, \"Register ${reg.name} is write only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_21 & ~(~crFile_io_mcr_read_3_ready)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Can only write to this decoupled sink\n    at Lib.scala:302 assert(read(index).ready === false.B, \"Can only write to this decoupled sink\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 302:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_9_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register io_v_0 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~crFile_io_mcr_write_10_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Register io_z_0 is read only\n    at Lib.scala:287 assert(write(index).valid =/= true.B, s\"Register ${reg.name} is read only\")\n"
            ); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  cycleHorizon = _RAND_0[31:0];
  _RAND_1 = {2{`RANDOM}};
  tCycle = _RAND_1[63:0];
  _RAND_2 = {2{`RANDOM}};
  tCycle_tCycle_mmreg = _RAND_2[63:0];
  _RAND_3 = {1{`RANDOM}};
  DONE = _RAND_3[31:0];
  _RAND_4 = {1{`RANDOM}};
  target_reset_i = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  wordsReceived = _RAND_5[0:0];
  _RAND_6 = {1{`RANDOM}};
  target_io_e_i = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  wordsReceived_1 = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  target_io_b_i = _RAND_8[15:0];
  _RAND_9 = {1{`RANDOM}};
  wordsReceived_2 = _RAND_9[0:0];
  _RAND_10 = {1{`RANDOM}};
  target_io_a_i = _RAND_10[15:0];
  _RAND_11 = {1{`RANDOM}};
  wordsReceived_3 = _RAND_11[0:0];
  _RAND_12 = {1{`RANDOM}};
  target_io_v_i = _RAND_12[0:0];
  _RAND_13 = {1{`RANDOM}};
  target_io_z_i = _RAND_13[15:0];
  _RAND_14 = {1{`RANDOM}};
  PRECISE_PEEKABLE = _RAND_14[31:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_0_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_1_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (_T_21) begin
      assert(~crFile_io_mcr_read_2_ready); // @[midas/src/main/scala/midas/widgets/Lib.scala 293:13]
    end
    //
    if (_T_21) begin
      assert(~crFile_io_mcr_read_3_ready); // @[midas/src/main/scala/midas/widgets/Lib.scala 302:11]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_9_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
    //
    if (~reset) begin
      assert(~crFile_io_mcr_write_10_valid); // @[midas/src/main/scala/midas/widgets/Lib.scala 287:13]
    end
  end
endmodule
module Queue_1(
  input   clock,
  input   reset,
  output  io_enq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input   io_enq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input   io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input   io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input   io_deq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output  io_deq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output  io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output  io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_REG_INIT
  reg  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition [0:1]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg  ram_midasAsserts_RationalClockBridge_clocks_0_asserts [0:1]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg  enq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg  deq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg  maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
  wire  ptr_match = enq_ptr_value == deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 283:33]
  wire  empty = ptr_match & ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 284:25]
  wire  full = ptr_match & maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 285:24]
  wire  do_enq = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  do_deq = io_deq_ready & io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_addr = deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_data =
    ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition[ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_addr]
    ; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_data =
    io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_addr = enq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_addr = deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_data =
    ram_midasAsserts_RationalClockBridge_clocks_0_asserts[ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_addr]
    ; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_data =
    io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_addr = enq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign io_enq_ready = ~full; // @[src/main/scala/chisel3/util/Decoupled.scala 309:19]
  assign io_deq_valid = ~empty; // @[src/main/scala/chisel3/util/Decoupled.scala 308:19]
  assign io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition =
    ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  assign io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts =
    ram_midasAsserts_RationalClockBridge_clocks_0_asserts_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  always @(posedge clock) begin
    if (ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_en &
      ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_mask) begin

        ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition[ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_addr]
         <= ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_en &
      ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_mask) begin

        ram_midasAsserts_RationalClockBridge_clocks_0_asserts[ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_addr]
         <= ram_midasAsserts_RationalClockBridge_clocks_0_asserts_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      enq_ptr_value <= 1'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_enq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 292:16]
      enq_ptr_value <= enq_ptr_value + 1'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      deq_ptr_value <= 1'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 296:16]
      deq_ptr_value <= deq_ptr_value + 1'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
      maybe_full <= 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
    end else if (do_enq != do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 299:27]
      maybe_full <= do_enq; // @[src/main/scala/chisel3/util/Decoupled.scala 300:16]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 2; initvar = initvar+1)
    ram_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition[initvar] = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  for (initvar = 0; initvar < 2; initvar = initvar+1)
    ram_midasAsserts_RationalClockBridge_clocks_0_asserts[initvar] = _RAND_1[0:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  enq_ptr_value = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  deq_ptr_value = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  maybe_full = _RAND_4[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module AssertBridgeModule(
  input         clock,
  input         reset,
  output        io_ctrl_aw_ready, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         io_ctrl_aw_valid, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [24:0] io_ctrl_aw_bits_addr, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [7:0]  io_ctrl_aw_bits_len, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [11:0] io_ctrl_aw_bits_id, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output        io_ctrl_w_ready, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         io_ctrl_w_valid, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [31:0] io_ctrl_w_bits_data, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         io_ctrl_b_ready, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output        io_ctrl_b_valid, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output [11:0] io_ctrl_b_bits_id, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output        io_ctrl_ar_ready, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         io_ctrl_ar_valid, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [24:0] io_ctrl_ar_bits_addr, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [7:0]  io_ctrl_ar_bits_len, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input  [11:0] io_ctrl_ar_bits_id, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         io_ctrl_r_ready, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output        io_ctrl_r_valid, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output [31:0] io_ctrl_r_bits_data, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  output [11:0] io_ctrl_r_bits_id, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 30:24]
  input         hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 31:24]
  input         hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 31:24]
  output        hPort_toHost_hReady, // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 31:24]
  input         hPort_toHost_hValid // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 31:24]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [63:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
`endif // RANDOMIZE_REG_INIT
  wire  q_clock; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_reset; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_enq_ready; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_enq_valid; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_deq_ready; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_deq_valid; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
  wire  crFile_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [24:0] crFile_io_nasti_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [7:0] crFile_io_nasti_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [11:0] crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_2_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_read_5_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_read_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_0_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_0_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_1_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_1_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_2_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_3_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_3_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_4_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_4_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire  crFile_io_mcr_write_5_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  wire [31:0] crFile_io_mcr_write_5_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
  reg  enable; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 33:29]
  reg [63:0] cycles; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 34:29]
  wire  assertFire = |q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts & ~
    q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 46:34]
  reg  resume_1; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  wire  stallN = ~assertFire | resume_1 | ~enable; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 50:41]
  wire  targetFire = q_io_deq_valid & stallN; // @[rocket-chip/src/main/scala/util/Misc.scala 29:18]
  wire [63:0] _cycles_T_1 = cycles + 64'h1; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 56:24]
  reg  id; // @[midas/src/main/scala/midas/widgets/Widget.scala 130:29]
  wire  _T = assertFire & q_io_deq_valid; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 60:25]
  reg  fire; // @[midas/src/main/scala/midas/widgets/Widget.scala 130:29]
  reg [31:0] cycle_low; // @[midas/src/main/scala/midas/widgets/Widget.scala 130:29]
  reg [31:0] cycle_high; // @[midas/src/main/scala/midas/widgets/Widget.scala 130:29]
  wire  _GEN_1 = resume_1 ? 1'h0 : resume_1; // @[midas/src/main/scala/midas/widgets/Pulsify.scala 29:{16,21} midas/src/main/scala/midas/widgets/Widget.scala 131:33]
  wire [31:0] _GEN_2 = crFile_io_mcr_write_0_valid ? crFile_io_mcr_write_0_bits : 32'h0; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/Widget.scala 133:44]
  wire [31:0] _GEN_3 = crFile_io_mcr_write_1_valid ? crFile_io_mcr_write_1_bits : {{31'd0}, _T}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/Widget.scala 133:44]
  wire [31:0] _GEN_6 = crFile_io_mcr_write_4_valid ? crFile_io_mcr_write_4_bits : {{31'd0}, _GEN_1}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18]
  wire [31:0] _GEN_7 = crFile_io_mcr_write_5_valid ? crFile_io_mcr_write_5_bits : {{31'd0}, enable}; // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32 284:18 midas/src/main/scala/midas/widgets/AssertBridge.scala 33:29]
  wire [31:0] _GEN_8 = reset ? 32'h0 : _GEN_7; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 33:{29,29}]
  wire [31:0] _GEN_9 = reset ? 32'h0 : _GEN_6; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:{33,33}]
  Queue_1 q ( // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 35:28]
    .clock(q_clock),
    .reset(q_reset),
    .io_enq_ready(q_io_enq_ready),
    .io_enq_valid(q_io_enq_valid),
    .io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition(
      q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition),
    .io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts(
      q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts),
    .io_deq_ready(q_io_deq_ready),
    .io_deq_valid(q_io_deq_valid),
    .io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition(
      q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition),
    .io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts(
      q_io_deq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts)
  );
  MCRFile_1 crFile ( // @[midas/src/main/scala/midas/widgets/Widget.scala 168:24]
    .clock(crFile_clock),
    .reset(crFile_reset),
    .io_nasti_aw_ready(crFile_io_nasti_aw_ready),
    .io_nasti_aw_valid(crFile_io_nasti_aw_valid),
    .io_nasti_aw_bits_addr(crFile_io_nasti_aw_bits_addr),
    .io_nasti_aw_bits_len(crFile_io_nasti_aw_bits_len),
    .io_nasti_aw_bits_id(crFile_io_nasti_aw_bits_id),
    .io_nasti_w_ready(crFile_io_nasti_w_ready),
    .io_nasti_w_valid(crFile_io_nasti_w_valid),
    .io_nasti_w_bits_data(crFile_io_nasti_w_bits_data),
    .io_nasti_b_ready(crFile_io_nasti_b_ready),
    .io_nasti_b_valid(crFile_io_nasti_b_valid),
    .io_nasti_b_bits_id(crFile_io_nasti_b_bits_id),
    .io_nasti_ar_ready(crFile_io_nasti_ar_ready),
    .io_nasti_ar_valid(crFile_io_nasti_ar_valid),
    .io_nasti_ar_bits_addr(crFile_io_nasti_ar_bits_addr),
    .io_nasti_ar_bits_len(crFile_io_nasti_ar_bits_len),
    .io_nasti_ar_bits_id(crFile_io_nasti_ar_bits_id),
    .io_nasti_r_ready(crFile_io_nasti_r_ready),
    .io_nasti_r_valid(crFile_io_nasti_r_valid),
    .io_nasti_r_bits_data(crFile_io_nasti_r_bits_data),
    .io_nasti_r_bits_id(crFile_io_nasti_r_bits_id),
    .io_mcr_read_0_bits(crFile_io_mcr_read_0_bits),
    .io_mcr_read_1_bits(crFile_io_mcr_read_1_bits),
    .io_mcr_read_2_ready(crFile_io_mcr_read_2_ready),
    .io_mcr_read_2_bits(crFile_io_mcr_read_2_bits),
    .io_mcr_read_3_bits(crFile_io_mcr_read_3_bits),
    .io_mcr_read_4_bits(crFile_io_mcr_read_4_bits),
    .io_mcr_read_5_ready(crFile_io_mcr_read_5_ready),
    .io_mcr_read_5_bits(crFile_io_mcr_read_5_bits),
    .io_mcr_write_0_valid(crFile_io_mcr_write_0_valid),
    .io_mcr_write_0_bits(crFile_io_mcr_write_0_bits),
    .io_mcr_write_1_valid(crFile_io_mcr_write_1_valid),
    .io_mcr_write_1_bits(crFile_io_mcr_write_1_bits),
    .io_mcr_write_2_valid(crFile_io_mcr_write_2_valid),
    .io_mcr_write_2_bits(crFile_io_mcr_write_2_bits),
    .io_mcr_write_3_valid(crFile_io_mcr_write_3_valid),
    .io_mcr_write_3_bits(crFile_io_mcr_write_3_bits),
    .io_mcr_write_4_valid(crFile_io_mcr_write_4_valid),
    .io_mcr_write_4_bits(crFile_io_mcr_write_4_bits),
    .io_mcr_write_5_valid(crFile_io_mcr_write_5_valid),
    .io_mcr_write_5_bits(crFile_io_mcr_write_5_bits)
  );
  assign io_ctrl_aw_ready = crFile_io_nasti_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_w_ready = crFile_io_nasti_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_valid = crFile_io_nasti_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_b_bits_id = crFile_io_nasti_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_ar_ready = crFile_io_nasti_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_valid = crFile_io_nasti_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_data = crFile_io_nasti_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign io_ctrl_r_bits_id = crFile_io_nasti_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign hPort_toHost_hReady = q_io_enq_ready; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 37:27]
  assign q_clock = clock;
  assign q_reset = reset;
  assign q_io_enq_valid = hPort_toHost_hValid; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 36:27]
  assign q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition =
    hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 38:27]
  assign q_io_enq_bits_midasAsserts_RationalClockBridge_clocks_0_asserts =
    hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 38:27]
  assign q_io_deq_ready = ~assertFire | resume_1 | ~enable; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 50:41]
  assign crFile_clock = clock;
  assign crFile_reset = reset;
  assign crFile_io_nasti_aw_valid = io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_addr = io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_len = io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_aw_bits_id = io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_valid = io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_w_bits_data = io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_b_ready = io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_valid = io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_addr = io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_len = io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_ar_bits_id = io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_nasti_r_ready = io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 170:21]
  assign crFile_io_mcr_read_0_bits = {{31'd0}, id}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_1_bits = {{31'd0}, fire}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_2_bits = cycle_low; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_3_bits = cycle_high; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_4_bits = {{31'd0}, resume_1}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  assign crFile_io_mcr_read_5_bits = {{31'd0}, enable}; // @[midas/src/main/scala/midas/widgets/Lib.scala 291:24]
  always @(posedge clock) begin
    enable <= _GEN_8[0]; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 33:{29,29}]
    if (reset) begin // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 34:29]
      cycles <= 64'h0; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 34:29]
    end else if (targetFire) begin // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 55:22]
      cycles <= _cycles_T_1; // @[midas/src/main/scala/midas/widgets/AssertBridge.scala 56:14]
    end
    resume_1 <= _GEN_9[0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 131:{33,33}]
    id <= _GEN_2[0];
    fire <= _GEN_3[0];
    if (crFile_io_mcr_write_2_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      cycle_low <= crFile_io_mcr_write_2_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      cycle_low <= cycles[31:0]; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
    if (crFile_io_mcr_write_3_valid) begin // @[midas/src/main/scala/midas/widgets/Lib.scala 283:32]
      cycle_high <= crFile_io_mcr_write_3_bits; // @[midas/src/main/scala/midas/widgets/Lib.scala 284:18]
    end else begin
      cycle_high <= cycles[63:32]; // @[midas/src/main/scala/midas/widgets/Widget.scala 133:44]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  enable = _RAND_0[0:0];
  _RAND_1 = {2{`RANDOM}};
  cycles = _RAND_1[63:0];
  _RAND_2 = {1{`RANDOM}};
  resume_1 = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  id = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  fire = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  cycle_low = _RAND_5[31:0];
  _RAND_6 = {1{`RANDOM}};
  cycle_high = _RAND_6[31:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module ShiftQueue(
  input   clock,
  input   reset,
  output  io_enq_ready, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input   io_enq_valid, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input   io_enq_bits, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input   io_deq_ready, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  output  io_deq_valid, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  output  io_deq_bits // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
`endif // RANDOMIZE_REG_INIT
  reg  valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
  reg  valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
  reg  elts_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 22:25]
  reg  elts_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 22:25]
  wire  _wen_T = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _wen_T_3 = valid_1 | _wen_T; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 30:28]
  wire  _wen_T_7 = _wen_T & ~valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:43]
  wire  wen = io_deq_ready ? _wen_T_3 : _wen_T_7; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 29:10]
  wire  _valid_0_T_6 = _wen_T | valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 37:43]
  wire  _wen_T_10 = _wen_T & valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 30:43]
  wire  _wen_T_13 = _wen_T & valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:23]
  wire  _wen_T_15 = _wen_T & valid_0 & ~valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:43]
  wire  wen_1 = io_deq_ready ? _wen_T_10 : _wen_T_15; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 29:10]
  wire  _valid_1_T_6 = _wen_T_13 | valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 37:43]
  assign io_enq_ready = ~valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 40:19]
  assign io_deq_valid = valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 41:16]
  assign io_deq_bits = elts_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 42:15]
  always @(posedge clock) begin
    if (reset) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
      valid_0 <= 1'h0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
    end else if (io_deq_ready) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 35:10]
      valid_0 <= _wen_T_3;
    end else begin
      valid_0 <= _valid_0_T_6;
    end
    if (reset) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
      valid_1 <= 1'h0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
    end else if (io_deq_ready) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 35:10]
      valid_1 <= _wen_T_10;
    end else begin
      valid_1 <= _valid_1_T_6;
    end
    if (wen) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:16]
      if (valid_1) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 27:57]
        elts_0 <= elts_1;
      end else begin
        elts_0 <= io_enq_bits;
      end
    end
    if (wen_1) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:16]
      elts_1 <= io_enq_bits; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:26]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  valid_0 = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  valid_1 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  elts_0 = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  elts_1 = _RAND_3[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module PipeChannel(
  input   clock,
  input   reset,
  output  io_in_ready, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input   io_in_valid, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input   io_in_bits, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input   io_out_ready, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  output  io_out_valid, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  output  io_out_bits // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
`endif // RANDOMIZE_REG_INIT
  wire  tokens_clock; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_reset; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_enq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_enq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_enq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_deq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_deq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_deq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  reg  validPrev; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
  reg  bitsPrev; // @[midas/src/main/scala/midas/core/Channel.scala 56:28]
  reg  firePrev; // @[midas/src/main/scala/midas/core/Channel.scala 57:28]
  wire  _T_1 = ~validPrev | firePrev; // @[midas/src/main/scala/midas/core/Channel.scala 58:23]
  wire  _T_4 = ~reset; // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
  wire  _T_9 = _T_1 | bitsPrev == io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 60:30]
  ShiftQueue tokens ( // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
    .clock(tokens_clock),
    .reset(tokens_reset),
    .io_enq_ready(tokens_io_enq_ready),
    .io_enq_valid(tokens_io_enq_valid),
    .io_enq_bits(tokens_io_enq_bits),
    .io_deq_ready(tokens_io_deq_ready),
    .io_deq_valid(tokens_io_deq_valid),
    .io_deq_bits(tokens_io_deq_bits)
  );
  assign io_in_ready = tokens_io_enq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign io_out_valid = tokens_io_deq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  assign io_out_bits = tokens_io_deq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  assign tokens_clock = clock;
  assign tokens_reset = reset;
  assign tokens_io_enq_valid = io_in_valid; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign tokens_io_enq_bits = io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign tokens_io_deq_ready = io_out_ready; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
      validPrev <= 1'h0; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
    end else begin
      validPrev <= io_in_valid; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
    end
    bitsPrev <= io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 56:28]
    firePrev <= io_in_valid & io_in_ready; // @[midas/src/main/scala/midas/core/Channel.scala 57:35]
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~validPrev | firePrev | io_in_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: valid de-asserted without handshake, violating irrevocability\n    at Channel.scala:58 assert(!validPrev || firePrev || valid, s\"${prefix}valid de-asserted without handshake, violating irrevocability\")\n"
            ); // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_4 & ~_T_9) begin
          $fwrite(32'h80000002,
            "Assertion failed: bits changed without handshake, violating irrevocability\n    at Channel.scala:59 assert(\n"
            ); // @[midas/src/main/scala/midas/core/Channel.scala 59:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  validPrev = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  bitsPrev = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  firePrev = _RAND_2[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(~validPrev | firePrev | io_in_valid); // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
    end
    //
    if (_T_4) begin
      assert(_T_9); // @[midas/src/main/scala/midas/core/Channel.scala 59:11]
    end
  end
endmodule
module ShiftQueue_4(
  input         clock,
  input         reset,
  output        io_enq_ready, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input         io_enq_valid, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input  [15:0] io_enq_bits, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  input         io_deq_ready, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  output        io_deq_valid, // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
  output [15:0] io_deq_bits // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 17:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
`endif // RANDOMIZE_REG_INIT
  reg  valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
  reg  valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
  reg [15:0] elts_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 22:25]
  reg [15:0] elts_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 22:25]
  wire  _wen_T = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _wen_T_3 = valid_1 | _wen_T; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 30:28]
  wire  _wen_T_7 = _wen_T & ~valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:43]
  wire  wen = io_deq_ready ? _wen_T_3 : _wen_T_7; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 29:10]
  wire  _valid_0_T_6 = _wen_T | valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 37:43]
  wire  _wen_T_10 = _wen_T & valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 30:43]
  wire  _wen_T_13 = _wen_T & valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:23]
  wire  _wen_T_15 = _wen_T & valid_0 & ~valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 31:43]
  wire  wen_1 = io_deq_ready ? _wen_T_10 : _wen_T_15; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 29:10]
  wire  _valid_1_T_6 = _wen_T_13 | valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 37:43]
  assign io_enq_ready = ~valid_1; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 40:19]
  assign io_deq_valid = valid_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 41:16]
  assign io_deq_bits = elts_0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 42:15]
  always @(posedge clock) begin
    if (reset) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
      valid_0 <= 1'h0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
    end else if (io_deq_ready) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 35:10]
      valid_0 <= _wen_T_3;
    end else begin
      valid_0 <= _valid_0_T_6;
    end
    if (reset) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
      valid_1 <= 1'h0; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 21:30]
    end else if (io_deq_ready) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 35:10]
      valid_1 <= _wen_T_10;
    end else begin
      valid_1 <= _valid_1_T_6;
    end
    if (wen) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:16]
      if (valid_1) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 27:57]
        elts_0 <= elts_1;
      end else begin
        elts_0 <= io_enq_bits;
      end
    end
    if (wen_1) begin // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:16]
      elts_1 <= io_enq_bits; // @[rocket-chip/src/main/scala/util/ShiftQueue.scala 32:26]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  valid_0 = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  valid_1 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  elts_0 = _RAND_2[15:0];
  _RAND_3 = {1{`RANDOM}};
  elts_1 = _RAND_3[15:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module PipeChannel_4(
  input         clock,
  input         reset,
  output        io_in_ready, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input         io_in_valid, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input  [15:0] io_in_bits, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  input         io_out_ready, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  output        io_out_valid, // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
  output [15:0] io_out_bits // @[midas/src/main/scala/midas/core/Channel.scala 31:18]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
`endif // RANDOMIZE_REG_INIT
  wire  tokens_clock; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_reset; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_enq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_enq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire [15:0] tokens_io_enq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_deq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire  tokens_io_deq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  wire [15:0] tokens_io_deq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
  reg  validPrev; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
  reg [15:0] bitsPrev; // @[midas/src/main/scala/midas/core/Channel.scala 56:28]
  reg  firePrev; // @[midas/src/main/scala/midas/core/Channel.scala 57:28]
  wire  _T_1 = ~validPrev | firePrev; // @[midas/src/main/scala/midas/core/Channel.scala 58:23]
  wire  _T_4 = ~reset; // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
  wire  _T_9 = _T_1 | bitsPrev == io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 60:30]
  ShiftQueue_4 tokens ( // @[midas/src/main/scala/midas/core/Channel.scala 32:22]
    .clock(tokens_clock),
    .reset(tokens_reset),
    .io_enq_ready(tokens_io_enq_ready),
    .io_enq_valid(tokens_io_enq_valid),
    .io_enq_bits(tokens_io_enq_bits),
    .io_deq_ready(tokens_io_deq_ready),
    .io_deq_valid(tokens_io_deq_valid),
    .io_deq_bits(tokens_io_deq_bits)
  );
  assign io_in_ready = tokens_io_enq_ready; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign io_out_valid = tokens_io_deq_valid; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  assign io_out_bits = tokens_io_deq_bits; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  assign tokens_clock = clock;
  assign tokens_reset = reset;
  assign tokens_io_enq_valid = io_in_valid; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign tokens_io_enq_bits = io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 33:17]
  assign tokens_io_deq_ready = io_out_ready; // @[midas/src/main/scala/midas/core/Channel.scala 34:17]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
      validPrev <= 1'h0; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
    end else begin
      validPrev <= io_in_valid; // @[midas/src/main/scala/midas/core/Channel.scala 55:28]
    end
    bitsPrev <= io_in_bits; // @[midas/src/main/scala/midas/core/Channel.scala 56:28]
    firePrev <= io_in_valid & io_in_ready; // @[midas/src/main/scala/midas/core/Channel.scala 57:35]
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~validPrev | firePrev | io_in_valid)) begin
          $fwrite(32'h80000002,
            "Assertion failed: valid de-asserted without handshake, violating irrevocability\n    at Channel.scala:58 assert(!validPrev || firePrev || valid, s\"${prefix}valid de-asserted without handshake, violating irrevocability\")\n"
            ); // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_4 & ~_T_9) begin
          $fwrite(32'h80000002,
            "Assertion failed: bits changed without handshake, violating irrevocability\n    at Channel.scala:59 assert(\n"
            ); // @[midas/src/main/scala/midas/core/Channel.scala 59:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  validPrev = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  bitsPrev = _RAND_1[15:0];
  _RAND_2 = {1{`RANDOM}};
  firePrev = _RAND_2[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(~validPrev | firePrev | io_in_valid); // @[midas/src/main/scala/midas/core/Channel.scala 58:11]
    end
    //
    if (_T_4) begin
      assert(_T_9); // @[midas/src/main/scala/midas/core/Channel.scala 59:11]
    end
  end
endmodule
module SimWrapper(
  input         clock,
  input         reset,
  input         channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_a_sink_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_a_sink_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input  [15:0] channelPorts_GCD__peekPokeBridge_io_a_sink_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_b_sink_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_b_sink_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input  [15:0] channelPorts_GCD__peekPokeBridge_io_b_sink_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_e_sink_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_e_sink_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_e_sink_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_reset_sink_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_reset_sink_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_reset_sink_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_z_source_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_z_source_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output [15:0] channelPorts_GCD__peekPokeBridge_io_z_source_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  input         channelPorts_GCD__peekPokeBridge_io_v_source_ready, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_v_source_valid, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__peekPokeBridge_io_v_source_bits, // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
  output        channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready // @[midas/src/main/scala/midas/core/SimWrapper.scala 267:24]
);
  wire  target_hostClock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_hostReset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__RationalClockBridge_clocks_0_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__RationalClockBridge_clocks_0_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_reset_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_e_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_b_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_a_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner2_io_z_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner2_io_z_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD__dut_inner2_io_z_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner2_io_v_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner2_io_v_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner2_io_v_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner1_io_z_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner1_io_z_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD__dut_inner1_io_z_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner1_io_v_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner1_io_v_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__dut_inner1_io_v_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_reset_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_reset_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_e_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_e_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_e_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_e_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_b_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner1_io_b_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_a_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner2_io_a_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_a_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner1_io_a_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_b_sink_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner2_io_b_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_v_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_v_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_z_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__peekPokeBridge_io_z_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD__peekPokeBridge_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_z_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_z_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner2_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_v_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_v_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner2_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_z_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_z_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire [15:0] target_GCD_dut_inner1_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_v_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_v_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  target_GCD_dut_inner1_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
  wire  PipeChannel_peekPokeBridge_reset_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_reset_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_z_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_z_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_1_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_2_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_a_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_a_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_1_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_2_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_b_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire [15:0] PipeChannel_peekPokeBridge_io_b_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_in_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_in_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_out_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  wire  PipeChannel_peekPokeBridge_io_e_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
  FAMETop target ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 268:28]
    .hostClock(target_hostClock),
    .hostReset(target_hostReset),
    .GCD__RationalClockBridge_clocks_0_sink_ready(target_GCD__RationalClockBridge_clocks_0_sink_ready),
    .GCD__RationalClockBridge_clocks_0_sink_bits(target_GCD__RationalClockBridge_clocks_0_sink_bits),
    .GCD__peekPokeBridge_reset_sink_ready(target_GCD__peekPokeBridge_reset_sink_ready),
    .GCD__peekPokeBridge_reset_sink_valid(target_GCD__peekPokeBridge_reset_sink_valid),
    .GCD__peekPokeBridge_reset_sink_bits(target_GCD__peekPokeBridge_reset_sink_bits),
    .GCD__peekPokeBridge_io_e_sink_ready(target_GCD__peekPokeBridge_io_e_sink_ready),
    .GCD__peekPokeBridge_io_e_sink_valid(target_GCD__peekPokeBridge_io_e_sink_valid),
    .GCD__peekPokeBridge_io_b_sink_ready(target_GCD__peekPokeBridge_io_b_sink_ready),
    .GCD__peekPokeBridge_io_b_sink_valid(target_GCD__peekPokeBridge_io_b_sink_valid),
    .GCD__peekPokeBridge_io_a_sink_ready(target_GCD__peekPokeBridge_io_a_sink_ready),
    .GCD__peekPokeBridge_io_a_sink_valid(target_GCD__peekPokeBridge_io_a_sink_valid),
    .GCD__dut_inner2_io_z_sink_ready(target_GCD__dut_inner2_io_z_sink_ready),
    .GCD__dut_inner2_io_z_sink_valid(target_GCD__dut_inner2_io_z_sink_valid),
    .GCD__dut_inner2_io_z_sink_bits(target_GCD__dut_inner2_io_z_sink_bits),
    .GCD__dut_inner2_io_v_sink_ready(target_GCD__dut_inner2_io_v_sink_ready),
    .GCD__dut_inner2_io_v_sink_valid(target_GCD__dut_inner2_io_v_sink_valid),
    .GCD__dut_inner2_io_v_sink_bits(target_GCD__dut_inner2_io_v_sink_bits),
    .GCD__dut_inner1_io_z_sink_ready(target_GCD__dut_inner1_io_z_sink_ready),
    .GCD__dut_inner1_io_z_sink_valid(target_GCD__dut_inner1_io_z_sink_valid),
    .GCD__dut_inner1_io_z_sink_bits(target_GCD__dut_inner1_io_z_sink_bits),
    .GCD__dut_inner1_io_v_sink_ready(target_GCD__dut_inner1_io_v_sink_ready),
    .GCD__dut_inner1_io_v_sink_valid(target_GCD__dut_inner1_io_v_sink_valid),
    .GCD__dut_inner1_io_v_sink_bits(target_GCD__dut_inner1_io_v_sink_bits),
    .GCD_dut_inner1_reset_sink_ready(target_GCD_dut_inner1_reset_sink_ready),
    .GCD_dut_inner1_reset_sink_valid(target_GCD_dut_inner1_reset_sink_valid),
    .GCD_dut_inner1_reset_sink_bits(target_GCD_dut_inner1_reset_sink_bits),
    .GCD_dut_inner2_reset_sink_ready(target_GCD_dut_inner2_reset_sink_ready),
    .GCD_dut_inner2_reset_sink_valid(target_GCD_dut_inner2_reset_sink_valid),
    .GCD_dut_inner2_reset_sink_bits(target_GCD_dut_inner2_reset_sink_bits),
    .GCD_dut_inner1_io_e_sink_ready(target_GCD_dut_inner1_io_e_sink_ready),
    .GCD_dut_inner1_io_e_sink_valid(target_GCD_dut_inner1_io_e_sink_valid),
    .GCD_dut_inner1_io_e_sink_bits(target_GCD_dut_inner1_io_e_sink_bits),
    .GCD_dut_inner2_io_e_sink_ready(target_GCD_dut_inner2_io_e_sink_ready),
    .GCD_dut_inner2_io_e_sink_valid(target_GCD_dut_inner2_io_e_sink_valid),
    .GCD_dut_inner2_io_e_sink_bits(target_GCD_dut_inner2_io_e_sink_bits),
    .GCD_dut_inner1_io_b_sink_ready(target_GCD_dut_inner1_io_b_sink_ready),
    .GCD_dut_inner1_io_b_sink_valid(target_GCD_dut_inner1_io_b_sink_valid),
    .GCD_dut_inner1_io_b_sink_bits(target_GCD_dut_inner1_io_b_sink_bits),
    .GCD_dut_inner2_io_a_sink_ready(target_GCD_dut_inner2_io_a_sink_ready),
    .GCD_dut_inner2_io_a_sink_valid(target_GCD_dut_inner2_io_a_sink_valid),
    .GCD_dut_inner2_io_a_sink_bits(target_GCD_dut_inner2_io_a_sink_bits),
    .GCD_dut_inner1_io_a_sink_ready(target_GCD_dut_inner1_io_a_sink_ready),
    .GCD_dut_inner1_io_a_sink_valid(target_GCD_dut_inner1_io_a_sink_valid),
    .GCD_dut_inner1_io_a_sink_bits(target_GCD_dut_inner1_io_a_sink_bits),
    .GCD_dut_inner2_io_b_sink_ready(target_GCD_dut_inner2_io_b_sink_ready),
    .GCD_dut_inner2_io_b_sink_valid(target_GCD_dut_inner2_io_b_sink_valid),
    .GCD_dut_inner2_io_b_sink_bits(target_GCD_dut_inner2_io_b_sink_bits),
    .GCD__peekPokeBridge_io_v_source_ready(target_GCD__peekPokeBridge_io_v_source_ready),
    .GCD__peekPokeBridge_io_v_source_valid(target_GCD__peekPokeBridge_io_v_source_valid),
    .GCD__peekPokeBridge_io_v_source_bits(target_GCD__peekPokeBridge_io_v_source_bits),
    .GCD__peekPokeBridge_io_z_source_ready(target_GCD__peekPokeBridge_io_z_source_ready),
    .GCD__peekPokeBridge_io_z_source_valid(target_GCD__peekPokeBridge_io_z_source_valid),
    .GCD__peekPokeBridge_io_z_source_bits(target_GCD__peekPokeBridge_io_z_source_bits),
    .GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready(
      target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready),
    .GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid(
      target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid),
    .GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits(
      target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits),
    .GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready(
      target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready),
    .GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid(
      target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid),
    .GCD_dut_inner2_io_z_source_ready(target_GCD_dut_inner2_io_z_source_ready),
    .GCD_dut_inner2_io_z_source_valid(target_GCD_dut_inner2_io_z_source_valid),
    .GCD_dut_inner2_io_z_source_bits(target_GCD_dut_inner2_io_z_source_bits),
    .GCD_dut_inner2_io_v_source_ready(target_GCD_dut_inner2_io_v_source_ready),
    .GCD_dut_inner2_io_v_source_valid(target_GCD_dut_inner2_io_v_source_valid),
    .GCD_dut_inner2_io_v_source_bits(target_GCD_dut_inner2_io_v_source_bits),
    .GCD_dut_inner1_io_z_source_ready(target_GCD_dut_inner1_io_z_source_ready),
    .GCD_dut_inner1_io_z_source_valid(target_GCD_dut_inner1_io_z_source_valid),
    .GCD_dut_inner1_io_z_source_bits(target_GCD_dut_inner1_io_z_source_bits),
    .GCD_dut_inner1_io_v_source_ready(target_GCD_dut_inner1_io_v_source_ready),
    .GCD_dut_inner1_io_v_source_valid(target_GCD_dut_inner1_io_v_source_valid),
    .GCD_dut_inner1_io_v_source_bits(target_GCD_dut_inner1_io_v_source_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_reset ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_reset_clock),
    .reset(PipeChannel_peekPokeBridge_reset_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_reset_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_reset_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_reset_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_reset_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_reset_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_reset_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_reset_1 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_reset_1_clock),
    .reset(PipeChannel_peekPokeBridge_reset_1_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_reset_1_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_reset_1_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_reset_1_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_reset_1_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_reset_1_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_reset_1_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_reset_2 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_reset_2_clock),
    .reset(PipeChannel_peekPokeBridge_reset_2_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_reset_2_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_reset_2_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_reset_2_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_reset_2_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_reset_2_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_reset_2_io_out_bits)
  );
  PipeChannel PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_clock),
    .reset(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_reset),
    .io_in_ready(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_ready),
    .io_in_valid(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_valid),
    .io_in_bits(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_bits),
    .io_out_ready(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_ready),
    .io_out_valid(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_valid),
    .io_out_bits(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_z ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_z_clock),
    .reset(PipeChannel_peekPokeBridge_io_z_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_z_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_z_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_z_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_z_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_z_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_z_io_out_bits)
  );
  PipeChannel_4 PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_clock),
    .reset(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_reset),
    .io_in_ready(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_ready),
    .io_in_valid(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_valid),
    .io_in_bits(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_bits),
    .io_out_ready(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_ready),
    .io_out_valid(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_valid),
    .io_out_bits(PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_bits)
  );
  PipeChannel PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_clock),
    .reset(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_reset),
    .io_in_ready(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_ready),
    .io_in_valid(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_valid),
    .io_in_bits(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_bits),
    .io_out_ready(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_ready),
    .io_out_valid(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_valid),
    .io_out_bits(PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_bits)
  );
  PipeChannel_4 PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_clock),
    .reset(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_reset),
    .io_in_ready(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_ready),
    .io_in_valid(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_valid),
    .io_in_bits(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_bits),
    .io_out_ready(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_ready),
    .io_out_valid(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_valid),
    .io_out_bits(PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_bits)
  );
  PipeChannel PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_clock),
    .reset(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_reset),
    .io_in_ready(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_ready),
    .io_in_valid(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_valid),
    .io_in_bits(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_bits),
    .io_out_ready(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_ready),
    .io_out_valid(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_valid),
    .io_out_bits(PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_io_v ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_v_clock),
    .reset(PipeChannel_peekPokeBridge_io_v_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_v_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_v_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_v_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_v_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_v_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_v_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_a ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_a_clock),
    .reset(PipeChannel_peekPokeBridge_io_a_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_a_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_a_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_a_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_a_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_a_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_a_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_a_1 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_a_1_clock),
    .reset(PipeChannel_peekPokeBridge_io_a_1_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_a_1_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_a_1_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_a_1_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_a_1_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_a_1_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_a_1_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_a_2 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_a_2_clock),
    .reset(PipeChannel_peekPokeBridge_io_a_2_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_a_2_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_a_2_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_a_2_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_a_2_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_a_2_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_a_2_io_out_bits)
  );
  PipeChannel PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_clock),
    .reset(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_reset),
    .io_in_ready(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_ready),
    .io_in_valid(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_valid),
    .io_in_bits(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_bits),
    .io_out_ready(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_ready),
    .io_out_valid(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_valid),
    .io_out_bits(PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_b ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_b_clock),
    .reset(PipeChannel_peekPokeBridge_io_b_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_b_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_b_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_b_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_b_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_b_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_b_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_b_1 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_b_1_clock),
    .reset(PipeChannel_peekPokeBridge_io_b_1_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_b_1_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_b_1_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_b_1_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_b_1_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_b_1_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_b_1_io_out_bits)
  );
  PipeChannel_4 PipeChannel_peekPokeBridge_io_b_2 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_b_2_clock),
    .reset(PipeChannel_peekPokeBridge_io_b_2_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_b_2_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_b_2_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_b_2_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_b_2_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_b_2_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_b_2_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_io_e ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_e_clock),
    .reset(PipeChannel_peekPokeBridge_io_e_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_e_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_e_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_e_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_e_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_e_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_e_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_io_e_1 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_e_1_clock),
    .reset(PipeChannel_peekPokeBridge_io_e_1_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_e_1_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_e_1_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_e_1_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_e_1_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_e_1_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_e_1_io_out_bits)
  );
  PipeChannel PipeChannel_peekPokeBridge_io_e_2 ( // @[midas/src/main/scala/midas/core/SimWrapper.scala 303:27]
    .clock(PipeChannel_peekPokeBridge_io_e_2_clock),
    .reset(PipeChannel_peekPokeBridge_io_e_2_reset),
    .io_in_ready(PipeChannel_peekPokeBridge_io_e_2_io_in_ready),
    .io_in_valid(PipeChannel_peekPokeBridge_io_e_2_io_in_valid),
    .io_in_bits(PipeChannel_peekPokeBridge_io_e_2_io_in_bits),
    .io_out_ready(PipeChannel_peekPokeBridge_io_e_2_io_out_ready),
    .io_out_valid(PipeChannel_peekPokeBridge_io_e_2_io_out_valid),
    .io_out_bits(PipeChannel_peekPokeBridge_io_e_2_io_out_bits)
  );
  assign channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__peekPokeBridge_io_a_sink_ready = PipeChannel_peekPokeBridge_io_a_io_in_ready &
    PipeChannel_peekPokeBridge_io_a_1_io_in_ready & PipeChannel_peekPokeBridge_io_a_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign channelPorts_GCD__peekPokeBridge_io_b_sink_ready = PipeChannel_peekPokeBridge_io_b_io_in_ready &
    PipeChannel_peekPokeBridge_io_b_1_io_in_ready & PipeChannel_peekPokeBridge_io_b_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign channelPorts_GCD__peekPokeBridge_io_e_sink_ready = PipeChannel_peekPokeBridge_io_e_io_in_ready &
    PipeChannel_peekPokeBridge_io_e_1_io_in_ready & PipeChannel_peekPokeBridge_io_e_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign channelPorts_GCD__peekPokeBridge_reset_sink_ready = PipeChannel_peekPokeBridge_reset_io_in_ready &
    PipeChannel_peekPokeBridge_reset_1_io_in_ready & PipeChannel_peekPokeBridge_reset_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign channelPorts_GCD__peekPokeBridge_io_z_source_valid = PipeChannel_peekPokeBridge_io_z_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__peekPokeBridge_io_z_source_bits = PipeChannel_peekPokeBridge_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__peekPokeBridge_io_v_source_valid = PipeChannel_peekPokeBridge_io_v_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__peekPokeBridge_io_v_source_bits = PipeChannel_peekPokeBridge_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready = target_GCD__RationalClockBridge_clocks_0_sink_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 334:37]
  assign target_hostClock = clock; // @[midas/src/main/scala/midas/core/SimWrapper.scala 277:23]
  assign target_hostReset = reset; // @[midas/src/main/scala/midas/core/SimWrapper.scala 276:32]
  assign target_GCD__RationalClockBridge_clocks_0_sink_bits = 1'h1; // @[midas/src/main/scala/midas/core/SimWrapper.scala 336:61]
  assign target_GCD__peekPokeBridge_reset_sink_valid = PipeChannel_peekPokeBridge_reset_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__peekPokeBridge_reset_sink_bits = PipeChannel_peekPokeBridge_reset_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__peekPokeBridge_io_e_sink_valid = PipeChannel_peekPokeBridge_io_e_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__peekPokeBridge_io_b_sink_valid = PipeChannel_peekPokeBridge_io_b_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__peekPokeBridge_io_a_sink_valid = PipeChannel_peekPokeBridge_io_a_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner2_io_z_sink_valid = PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner2_io_z_sink_bits = PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner2_io_v_sink_valid = PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner2_io_v_sink_bits = PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner1_io_z_sink_valid = PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner1_io_z_sink_bits = PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner1_io_v_sink_valid = PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__dut_inner1_io_v_sink_bits = PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_reset_sink_valid = PipeChannel_peekPokeBridge_reset_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_reset_sink_bits = PipeChannel_peekPokeBridge_reset_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_reset_sink_valid = PipeChannel_peekPokeBridge_reset_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_reset_sink_bits = PipeChannel_peekPokeBridge_reset_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_e_sink_valid = PipeChannel_peekPokeBridge_io_e_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_e_sink_bits = PipeChannel_peekPokeBridge_io_e_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_e_sink_valid = PipeChannel_peekPokeBridge_io_e_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_e_sink_bits = PipeChannel_peekPokeBridge_io_e_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_b_sink_valid = PipeChannel_peekPokeBridge_io_b_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_b_sink_bits = PipeChannel_peekPokeBridge_io_b_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_a_sink_valid = PipeChannel_peekPokeBridge_io_b_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_a_sink_bits = PipeChannel_peekPokeBridge_io_b_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_a_sink_valid = PipeChannel_peekPokeBridge_io_a_1_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner1_io_a_sink_bits = PipeChannel_peekPokeBridge_io_a_1_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_b_sink_valid = PipeChannel_peekPokeBridge_io_a_2_io_out_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD_dut_inner2_io_b_sink_bits = PipeChannel_peekPokeBridge_io_a_2_io_out_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign target_GCD__peekPokeBridge_io_v_source_ready = PipeChannel_peekPokeBridge_io_v_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD__peekPokeBridge_io_z_source_ready = PipeChannel_peekPokeBridge_io_z_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready =
    PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD_dut_inner2_io_z_source_ready = PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD_dut_inner2_io_v_source_ready = PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD_dut_inner1_io_z_source_ready = PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign target_GCD_dut_inner1_io_v_source_ready = PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 326:16]
  assign PipeChannel_peekPokeBridge_reset_clock = clock;
  assign PipeChannel_peekPokeBridge_reset_reset = reset;
  assign PipeChannel_peekPokeBridge_reset_io_in_valid = channelPorts_GCD__peekPokeBridge_reset_sink_valid &
    PipeChannel_peekPokeBridge_reset_1_io_in_ready & PipeChannel_peekPokeBridge_reset_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_reset_io_in_bits = channelPorts_GCD__peekPokeBridge_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_reset_io_out_ready = target_GCD__peekPokeBridge_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_reset_1_clock = clock;
  assign PipeChannel_peekPokeBridge_reset_1_reset = reset;
  assign PipeChannel_peekPokeBridge_reset_1_io_in_valid = channelPorts_GCD__peekPokeBridge_reset_sink_valid &
    PipeChannel_peekPokeBridge_reset_io_in_ready & PipeChannel_peekPokeBridge_reset_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_reset_1_io_in_bits = channelPorts_GCD__peekPokeBridge_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_reset_1_io_out_ready = target_GCD_dut_inner1_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_reset_2_clock = clock;
  assign PipeChannel_peekPokeBridge_reset_2_reset = reset;
  assign PipeChannel_peekPokeBridge_reset_2_io_in_valid = channelPorts_GCD__peekPokeBridge_reset_sink_valid &
    PipeChannel_peekPokeBridge_reset_io_in_ready & PipeChannel_peekPokeBridge_reset_1_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_reset_2_io_in_bits = channelPorts_GCD__peekPokeBridge_reset_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_reset_2_io_out_ready = target_GCD_dut_inner2_reset_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_clock = clock;
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_reset = reset;
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_valid =
    target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_in_bits =
    target_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_asserts_io_out_ready =
    channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign PipeChannel_peekPokeBridge_io_z_clock = clock;
  assign PipeChannel_peekPokeBridge_io_z_reset = reset;
  assign PipeChannel_peekPokeBridge_io_z_io_in_valid = target_GCD__peekPokeBridge_io_z_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_peekPokeBridge_io_z_io_in_bits = target_GCD__peekPokeBridge_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_z_io_out_ready = channelPorts_GCD__peekPokeBridge_io_z_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_clock = clock;
  assign PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_reset = reset;
  assign PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_valid = target_GCD_dut_inner2_io_z_source_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_in_bits = target_GCD_dut_inner2_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_GCD_dut_inner2_io_z__to__GCD__dut_inner2_io_z_io_out_ready = target_GCD__dut_inner2_io_z_sink_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_clock = clock;
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_reset = reset;
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_valid =
    target_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_in_bits = 1'h0; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_io_out_ready =
    channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_clock = clock;
  assign PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_reset = reset;
  assign PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_valid = target_GCD_dut_inner1_io_z_source_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_in_bits = target_GCD_dut_inner1_io_z_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_GCD_dut_inner1_io_z__to__GCD__dut_inner1_io_z_io_out_ready = target_GCD__dut_inner1_io_z_sink_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_clock = clock;
  assign PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_reset = reset;
  assign PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_valid = target_GCD_dut_inner2_io_v_source_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_in_bits = target_GCD_dut_inner2_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_GCD_dut_inner2_io_v__to__GCD__dut_inner2_io_v_io_out_ready = target_GCD__dut_inner2_io_v_sink_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_v_clock = clock;
  assign PipeChannel_peekPokeBridge_io_v_reset = reset;
  assign PipeChannel_peekPokeBridge_io_v_io_in_valid = target_GCD__peekPokeBridge_io_v_source_valid; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_peekPokeBridge_io_v_io_in_bits = target_GCD__peekPokeBridge_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_v_io_out_ready = channelPorts_GCD__peekPokeBridge_io_v_source_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 308:79]
  assign PipeChannel_peekPokeBridge_io_a_clock = clock;
  assign PipeChannel_peekPokeBridge_io_a_reset = reset;
  assign PipeChannel_peekPokeBridge_io_a_io_in_valid = channelPorts_GCD__peekPokeBridge_io_a_sink_valid &
    PipeChannel_peekPokeBridge_io_a_1_io_in_ready & PipeChannel_peekPokeBridge_io_a_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_a_io_in_bits = channelPorts_GCD__peekPokeBridge_io_a_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_a_io_out_ready = target_GCD__peekPokeBridge_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_a_1_clock = clock;
  assign PipeChannel_peekPokeBridge_io_a_1_reset = reset;
  assign PipeChannel_peekPokeBridge_io_a_1_io_in_valid = channelPorts_GCD__peekPokeBridge_io_a_sink_valid &
    PipeChannel_peekPokeBridge_io_a_io_in_ready & PipeChannel_peekPokeBridge_io_a_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_a_1_io_in_bits = channelPorts_GCD__peekPokeBridge_io_a_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_a_1_io_out_ready = target_GCD_dut_inner1_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_a_2_clock = clock;
  assign PipeChannel_peekPokeBridge_io_a_2_reset = reset;
  assign PipeChannel_peekPokeBridge_io_a_2_io_in_valid = channelPorts_GCD__peekPokeBridge_io_a_sink_valid &
    PipeChannel_peekPokeBridge_io_a_io_in_ready & PipeChannel_peekPokeBridge_io_a_1_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_a_2_io_in_bits = channelPorts_GCD__peekPokeBridge_io_a_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_a_2_io_out_ready = target_GCD_dut_inner2_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_clock = clock;
  assign PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_reset = reset;
  assign PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_valid = target_GCD_dut_inner1_io_v_source_valid
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 324:21]
  assign PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_in_bits = target_GCD_dut_inner1_io_v_source_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_GCD_dut_inner1_io_v__to__GCD__dut_inner1_io_v_io_out_ready = target_GCD__dut_inner1_io_v_sink_ready
    ; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_b_clock = clock;
  assign PipeChannel_peekPokeBridge_io_b_reset = reset;
  assign PipeChannel_peekPokeBridge_io_b_io_in_valid = channelPorts_GCD__peekPokeBridge_io_b_sink_valid &
    PipeChannel_peekPokeBridge_io_b_1_io_in_ready & PipeChannel_peekPokeBridge_io_b_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_b_io_in_bits = channelPorts_GCD__peekPokeBridge_io_b_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_b_io_out_ready = target_GCD__peekPokeBridge_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_b_1_clock = clock;
  assign PipeChannel_peekPokeBridge_io_b_1_reset = reset;
  assign PipeChannel_peekPokeBridge_io_b_1_io_in_valid = channelPorts_GCD__peekPokeBridge_io_b_sink_valid &
    PipeChannel_peekPokeBridge_io_b_io_in_ready & PipeChannel_peekPokeBridge_io_b_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_b_1_io_in_bits = channelPorts_GCD__peekPokeBridge_io_b_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_b_1_io_out_ready = target_GCD_dut_inner1_io_b_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_b_2_clock = clock;
  assign PipeChannel_peekPokeBridge_io_b_2_reset = reset;
  assign PipeChannel_peekPokeBridge_io_b_2_io_in_valid = channelPorts_GCD__peekPokeBridge_io_b_sink_valid &
    PipeChannel_peekPokeBridge_io_b_io_in_ready & PipeChannel_peekPokeBridge_io_b_1_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_b_2_io_in_bits = channelPorts_GCD__peekPokeBridge_io_b_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_b_2_io_out_ready = target_GCD_dut_inner2_io_a_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_e_clock = clock;
  assign PipeChannel_peekPokeBridge_io_e_reset = reset;
  assign PipeChannel_peekPokeBridge_io_e_io_in_valid = channelPorts_GCD__peekPokeBridge_io_e_sink_valid &
    PipeChannel_peekPokeBridge_io_e_1_io_in_ready & PipeChannel_peekPokeBridge_io_e_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_e_io_in_bits = channelPorts_GCD__peekPokeBridge_io_e_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_e_io_out_ready = target_GCD__peekPokeBridge_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_e_1_clock = clock;
  assign PipeChannel_peekPokeBridge_io_e_1_reset = reset;
  assign PipeChannel_peekPokeBridge_io_e_1_io_in_valid = channelPorts_GCD__peekPokeBridge_io_e_sink_valid &
    PipeChannel_peekPokeBridge_io_e_io_in_ready & PipeChannel_peekPokeBridge_io_e_2_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_e_1_io_in_bits = channelPorts_GCD__peekPokeBridge_io_e_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_e_1_io_out_ready = target_GCD_dut_inner1_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
  assign PipeChannel_peekPokeBridge_io_e_2_clock = clock;
  assign PipeChannel_peekPokeBridge_io_e_2_reset = reset;
  assign PipeChannel_peekPokeBridge_io_e_2_io_in_valid = channelPorts_GCD__peekPokeBridge_io_e_sink_valid &
    PipeChannel_peekPokeBridge_io_e_io_in_ready & PipeChannel_peekPokeBridge_io_e_1_io_in_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign PipeChannel_peekPokeBridge_io_e_2_io_in_bits = channelPorts_GCD__peekPokeBridge_io_e_sink_bits; // @[midas/src/main/scala/midas/core/SimWrapper.scala 323:21]
  assign PipeChannel_peekPokeBridge_io_e_2_io_out_ready = target_GCD_dut_inner2_io_e_sink_ready; // @[midas/src/main/scala/midas/core/SimWrapper.scala 307:79]
endmodule
module ReorderQueue(
  input         clock,
  input         reset,
  output        io_enq_ready,
  input         io_enq_valid,
  input  [11:0] io_enq_bits_tag,
  input         io_deq_0_valid,
  input  [11:0] io_deq_0_tag,
  output        io_deq_0_matches,
  input         io_deq_1_valid,
  input  [11:0] io_deq_1_tag,
  output        io_deq_1_matches,
  input         io_deq_2_valid,
  input  [11:0] io_deq_2_tag,
  output        io_deq_2_matches,
  input         io_deq_3_valid,
  input  [11:0] io_deq_3_tag,
  output        io_deq_3_matches,
  input         io_deq_4_valid,
  input  [11:0] io_deq_4_tag,
  output        io_deq_4_matches
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [31:0] _RAND_14;
  reg [31:0] _RAND_15;
  reg [31:0] _RAND_16;
  reg [31:0] _RAND_17;
  reg [31:0] _RAND_18;
  reg [31:0] _RAND_19;
  reg [31:0] _RAND_20;
  reg [31:0] _RAND_21;
  reg [31:0] _RAND_22;
  reg [31:0] _RAND_23;
  reg [31:0] _RAND_24;
  reg [31:0] _RAND_25;
  reg [31:0] _RAND_26;
  reg [31:0] _RAND_27;
  reg [31:0] _RAND_28;
  reg [31:0] _RAND_29;
  reg [31:0] _RAND_30;
  reg [31:0] _RAND_31;
  reg [31:0] _RAND_32;
  reg [31:0] _RAND_33;
  reg [31:0] _RAND_34;
  reg [31:0] _RAND_35;
  reg [31:0] _RAND_36;
  reg [31:0] _RAND_37;
  reg [31:0] _RAND_38;
  reg [31:0] _RAND_39;
  reg [31:0] _RAND_40;
  reg [31:0] _RAND_41;
  reg [31:0] _RAND_42;
  reg [31:0] _RAND_43;
  reg [31:0] _RAND_44;
  reg [31:0] _RAND_45;
  reg [31:0] _RAND_46;
  reg [31:0] _RAND_47;
  reg [31:0] _RAND_48;
  reg [31:0] _RAND_49;
  reg [31:0] _RAND_50;
  reg [31:0] _RAND_51;
  reg [31:0] _RAND_52;
  reg [31:0] _RAND_53;
  reg [31:0] _RAND_54;
  reg [31:0] _RAND_55;
  reg [31:0] _RAND_56;
  reg [31:0] _RAND_57;
  reg [31:0] _RAND_58;
  reg [31:0] _RAND_59;
  reg [31:0] _RAND_60;
  reg [31:0] _RAND_61;
  reg [31:0] _RAND_62;
  reg [31:0] _RAND_63;
  reg [31:0] _RAND_64;
  reg [31:0] _RAND_65;
  reg [31:0] _RAND_66;
  reg [31:0] _RAND_67;
  reg [31:0] _RAND_68;
  reg [31:0] _RAND_69;
  reg [31:0] _RAND_70;
  reg [31:0] _RAND_71;
  reg [31:0] _RAND_72;
  reg [31:0] _RAND_73;
  reg [31:0] _RAND_74;
  reg [31:0] _RAND_75;
  reg [31:0] _RAND_76;
  reg [31:0] _RAND_77;
  reg [31:0] _RAND_78;
  reg [31:0] _RAND_79;
  reg [31:0] _RAND_80;
  reg [31:0] _RAND_81;
  reg [31:0] _RAND_82;
  reg [31:0] _RAND_83;
  reg [31:0] _RAND_84;
  reg [31:0] _RAND_85;
  reg [31:0] _RAND_86;
  reg [31:0] _RAND_87;
  reg [31:0] _RAND_88;
  reg [31:0] _RAND_89;
  reg [31:0] _RAND_90;
  reg [31:0] _RAND_91;
  reg [31:0] _RAND_92;
  reg [31:0] _RAND_93;
  reg [31:0] _RAND_94;
  reg [31:0] _RAND_95;
  reg [31:0] _RAND_96;
  reg [31:0] _RAND_97;
  reg [31:0] _RAND_98;
  reg [31:0] _RAND_99;
  reg [31:0] _RAND_100;
  reg [31:0] _RAND_101;
  reg [31:0] _RAND_102;
  reg [31:0] _RAND_103;
  reg [31:0] _RAND_104;
  reg [31:0] _RAND_105;
  reg [31:0] _RAND_106;
  reg [31:0] _RAND_107;
  reg [31:0] _RAND_108;
  reg [31:0] _RAND_109;
  reg [31:0] _RAND_110;
  reg [31:0] _RAND_111;
  reg [31:0] _RAND_112;
  reg [31:0] _RAND_113;
  reg [31:0] _RAND_114;
  reg [31:0] _RAND_115;
  reg [31:0] _RAND_116;
  reg [31:0] _RAND_117;
  reg [31:0] _RAND_118;
  reg [31:0] _RAND_119;
  reg [31:0] _RAND_120;
  reg [31:0] _RAND_121;
  reg [31:0] _RAND_122;
  reg [31:0] _RAND_123;
  reg [31:0] _RAND_124;
  reg [31:0] _RAND_125;
  reg [31:0] _RAND_126;
  reg [31:0] _RAND_127;
`endif // RANDOMIZE_REG_INIT
  reg [5:0] roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_2; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_3; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_4; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_5; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_6; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_7; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_8; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_9; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_10; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_11; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_12; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_13; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_14; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_15; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_16; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_17; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_18; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_19; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_20; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_21; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_22; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_23; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_24; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_25; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_26; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_27; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_28; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_29; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_30; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_31; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_32; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_33; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_34; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_35; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_36; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_37; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_38; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_39; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_40; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_41; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_42; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_43; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_44; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_45; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_46; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_47; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_48; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_49; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_50; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_51; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_52; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_53; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_54; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_55; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_56; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_57; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_58; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_59; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_60; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_61; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_62; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg [5:0] roq_tags_63; // @[midas/src/main/scala/junctions/ReorderQueue.scala 35:27]
  reg  roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_2; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_3; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_4; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_5; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_6; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_7; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_8; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_9; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_10; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_11; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_12; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_13; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_14; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_15; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_16; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_17; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_18; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_19; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_20; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_21; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_22; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_23; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_24; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_25; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_26; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_27; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_28; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_29; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_30; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_31; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_32; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_33; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_34; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_35; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_36; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_37; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_38; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_39; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_40; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_41; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_42; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_43; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_44; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_45; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_46; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_47; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_48; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_49; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_50; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_51; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_52; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_53; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_54; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_55; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_56; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_57; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_58; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_59; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_60; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_61; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_62; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  reg  roq_free_63; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27]
  wire [5:0] roq_enq_addr = io_enq_bits_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 37:39]
  wire  _GEN_1 = 6'h1 == roq_enq_addr ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_2 = 6'h2 == roq_enq_addr ? roq_free_2 : _GEN_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_3 = 6'h3 == roq_enq_addr ? roq_free_3 : _GEN_2; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_4 = 6'h4 == roq_enq_addr ? roq_free_4 : _GEN_3; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_5 = 6'h5 == roq_enq_addr ? roq_free_5 : _GEN_4; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_6 = 6'h6 == roq_enq_addr ? roq_free_6 : _GEN_5; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_7 = 6'h7 == roq_enq_addr ? roq_free_7 : _GEN_6; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_8 = 6'h8 == roq_enq_addr ? roq_free_8 : _GEN_7; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_9 = 6'h9 == roq_enq_addr ? roq_free_9 : _GEN_8; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_10 = 6'ha == roq_enq_addr ? roq_free_10 : _GEN_9; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_11 = 6'hb == roq_enq_addr ? roq_free_11 : _GEN_10; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_12 = 6'hc == roq_enq_addr ? roq_free_12 : _GEN_11; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_13 = 6'hd == roq_enq_addr ? roq_free_13 : _GEN_12; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_14 = 6'he == roq_enq_addr ? roq_free_14 : _GEN_13; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_15 = 6'hf == roq_enq_addr ? roq_free_15 : _GEN_14; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_16 = 6'h10 == roq_enq_addr ? roq_free_16 : _GEN_15; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_17 = 6'h11 == roq_enq_addr ? roq_free_17 : _GEN_16; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_18 = 6'h12 == roq_enq_addr ? roq_free_18 : _GEN_17; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_19 = 6'h13 == roq_enq_addr ? roq_free_19 : _GEN_18; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_20 = 6'h14 == roq_enq_addr ? roq_free_20 : _GEN_19; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_21 = 6'h15 == roq_enq_addr ? roq_free_21 : _GEN_20; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_22 = 6'h16 == roq_enq_addr ? roq_free_22 : _GEN_21; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_23 = 6'h17 == roq_enq_addr ? roq_free_23 : _GEN_22; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_24 = 6'h18 == roq_enq_addr ? roq_free_24 : _GEN_23; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_25 = 6'h19 == roq_enq_addr ? roq_free_25 : _GEN_24; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_26 = 6'h1a == roq_enq_addr ? roq_free_26 : _GEN_25; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_27 = 6'h1b == roq_enq_addr ? roq_free_27 : _GEN_26; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_28 = 6'h1c == roq_enq_addr ? roq_free_28 : _GEN_27; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_29 = 6'h1d == roq_enq_addr ? roq_free_29 : _GEN_28; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_30 = 6'h1e == roq_enq_addr ? roq_free_30 : _GEN_29; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_31 = 6'h1f == roq_enq_addr ? roq_free_31 : _GEN_30; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_32 = 6'h20 == roq_enq_addr ? roq_free_32 : _GEN_31; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_33 = 6'h21 == roq_enq_addr ? roq_free_33 : _GEN_32; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_34 = 6'h22 == roq_enq_addr ? roq_free_34 : _GEN_33; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_35 = 6'h23 == roq_enq_addr ? roq_free_35 : _GEN_34; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_36 = 6'h24 == roq_enq_addr ? roq_free_36 : _GEN_35; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_37 = 6'h25 == roq_enq_addr ? roq_free_37 : _GEN_36; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_38 = 6'h26 == roq_enq_addr ? roq_free_38 : _GEN_37; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_39 = 6'h27 == roq_enq_addr ? roq_free_39 : _GEN_38; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_40 = 6'h28 == roq_enq_addr ? roq_free_40 : _GEN_39; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_41 = 6'h29 == roq_enq_addr ? roq_free_41 : _GEN_40; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_42 = 6'h2a == roq_enq_addr ? roq_free_42 : _GEN_41; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_43 = 6'h2b == roq_enq_addr ? roq_free_43 : _GEN_42; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_44 = 6'h2c == roq_enq_addr ? roq_free_44 : _GEN_43; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_45 = 6'h2d == roq_enq_addr ? roq_free_45 : _GEN_44; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_46 = 6'h2e == roq_enq_addr ? roq_free_46 : _GEN_45; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_47 = 6'h2f == roq_enq_addr ? roq_free_47 : _GEN_46; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_48 = 6'h30 == roq_enq_addr ? roq_free_48 : _GEN_47; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_49 = 6'h31 == roq_enq_addr ? roq_free_49 : _GEN_48; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_50 = 6'h32 == roq_enq_addr ? roq_free_50 : _GEN_49; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_51 = 6'h33 == roq_enq_addr ? roq_free_51 : _GEN_50; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_52 = 6'h34 == roq_enq_addr ? roq_free_52 : _GEN_51; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_53 = 6'h35 == roq_enq_addr ? roq_free_53 : _GEN_52; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_54 = 6'h36 == roq_enq_addr ? roq_free_54 : _GEN_53; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_55 = 6'h37 == roq_enq_addr ? roq_free_55 : _GEN_54; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_56 = 6'h38 == roq_enq_addr ? roq_free_56 : _GEN_55; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_57 = 6'h39 == roq_enq_addr ? roq_free_57 : _GEN_56; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_58 = 6'h3a == roq_enq_addr ? roq_free_58 : _GEN_57; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_59 = 6'h3b == roq_enq_addr ? roq_free_59 : _GEN_58; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_60 = 6'h3c == roq_enq_addr ? roq_free_60 : _GEN_59; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_61 = 6'h3d == roq_enq_addr ? roq_free_61 : _GEN_60; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire  _GEN_62 = 6'h3e == roq_enq_addr ? roq_free_62 : _GEN_61; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  wire [11:0] _roq_tags_T = {{6'd0}, io_enq_bits_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:49]
  wire  _GEN_192 = 6'h0 == roq_enq_addr ? 1'h0 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_193 = 6'h1 == roq_enq_addr ? 1'h0 : roq_free_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_194 = 6'h2 == roq_enq_addr ? 1'h0 : roq_free_2; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_195 = 6'h3 == roq_enq_addr ? 1'h0 : roq_free_3; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_196 = 6'h4 == roq_enq_addr ? 1'h0 : roq_free_4; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_197 = 6'h5 == roq_enq_addr ? 1'h0 : roq_free_5; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_198 = 6'h6 == roq_enq_addr ? 1'h0 : roq_free_6; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_199 = 6'h7 == roq_enq_addr ? 1'h0 : roq_free_7; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_200 = 6'h8 == roq_enq_addr ? 1'h0 : roq_free_8; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_201 = 6'h9 == roq_enq_addr ? 1'h0 : roq_free_9; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_202 = 6'ha == roq_enq_addr ? 1'h0 : roq_free_10; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_203 = 6'hb == roq_enq_addr ? 1'h0 : roq_free_11; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_204 = 6'hc == roq_enq_addr ? 1'h0 : roq_free_12; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_205 = 6'hd == roq_enq_addr ? 1'h0 : roq_free_13; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_206 = 6'he == roq_enq_addr ? 1'h0 : roq_free_14; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_207 = 6'hf == roq_enq_addr ? 1'h0 : roq_free_15; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_208 = 6'h10 == roq_enq_addr ? 1'h0 : roq_free_16; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_209 = 6'h11 == roq_enq_addr ? 1'h0 : roq_free_17; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_210 = 6'h12 == roq_enq_addr ? 1'h0 : roq_free_18; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_211 = 6'h13 == roq_enq_addr ? 1'h0 : roq_free_19; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_212 = 6'h14 == roq_enq_addr ? 1'h0 : roq_free_20; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_213 = 6'h15 == roq_enq_addr ? 1'h0 : roq_free_21; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_214 = 6'h16 == roq_enq_addr ? 1'h0 : roq_free_22; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_215 = 6'h17 == roq_enq_addr ? 1'h0 : roq_free_23; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_216 = 6'h18 == roq_enq_addr ? 1'h0 : roq_free_24; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_217 = 6'h19 == roq_enq_addr ? 1'h0 : roq_free_25; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_218 = 6'h1a == roq_enq_addr ? 1'h0 : roq_free_26; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_219 = 6'h1b == roq_enq_addr ? 1'h0 : roq_free_27; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_220 = 6'h1c == roq_enq_addr ? 1'h0 : roq_free_28; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_221 = 6'h1d == roq_enq_addr ? 1'h0 : roq_free_29; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_222 = 6'h1e == roq_enq_addr ? 1'h0 : roq_free_30; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_223 = 6'h1f == roq_enq_addr ? 1'h0 : roq_free_31; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_224 = 6'h20 == roq_enq_addr ? 1'h0 : roq_free_32; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_225 = 6'h21 == roq_enq_addr ? 1'h0 : roq_free_33; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_226 = 6'h22 == roq_enq_addr ? 1'h0 : roq_free_34; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_227 = 6'h23 == roq_enq_addr ? 1'h0 : roq_free_35; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_228 = 6'h24 == roq_enq_addr ? 1'h0 : roq_free_36; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_229 = 6'h25 == roq_enq_addr ? 1'h0 : roq_free_37; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_230 = 6'h26 == roq_enq_addr ? 1'h0 : roq_free_38; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_231 = 6'h27 == roq_enq_addr ? 1'h0 : roq_free_39; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_232 = 6'h28 == roq_enq_addr ? 1'h0 : roq_free_40; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_233 = 6'h29 == roq_enq_addr ? 1'h0 : roq_free_41; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_234 = 6'h2a == roq_enq_addr ? 1'h0 : roq_free_42; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_235 = 6'h2b == roq_enq_addr ? 1'h0 : roq_free_43; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_236 = 6'h2c == roq_enq_addr ? 1'h0 : roq_free_44; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_237 = 6'h2d == roq_enq_addr ? 1'h0 : roq_free_45; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_238 = 6'h2e == roq_enq_addr ? 1'h0 : roq_free_46; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_239 = 6'h2f == roq_enq_addr ? 1'h0 : roq_free_47; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_240 = 6'h30 == roq_enq_addr ? 1'h0 : roq_free_48; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_241 = 6'h31 == roq_enq_addr ? 1'h0 : roq_free_49; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_242 = 6'h32 == roq_enq_addr ? 1'h0 : roq_free_50; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_243 = 6'h33 == roq_enq_addr ? 1'h0 : roq_free_51; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_244 = 6'h34 == roq_enq_addr ? 1'h0 : roq_free_52; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_245 = 6'h35 == roq_enq_addr ? 1'h0 : roq_free_53; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_246 = 6'h36 == roq_enq_addr ? 1'h0 : roq_free_54; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_247 = 6'h37 == roq_enq_addr ? 1'h0 : roq_free_55; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_248 = 6'h38 == roq_enq_addr ? 1'h0 : roq_free_56; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_249 = 6'h39 == roq_enq_addr ? 1'h0 : roq_free_57; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_250 = 6'h3a == roq_enq_addr ? 1'h0 : roq_free_58; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_251 = 6'h3b == roq_enq_addr ? 1'h0 : roq_free_59; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_252 = 6'h3c == roq_enq_addr ? 1'h0 : roq_free_60; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_253 = 6'h3d == roq_enq_addr ? 1'h0 : roq_free_61; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_254 = 6'h3e == roq_enq_addr ? 1'h0 : roq_free_62; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_255 = 6'h3f == roq_enq_addr ? 1'h0 : roq_free_63; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 44:{30,30}]
  wire  _GEN_384 = io_enq_valid & io_enq_ready ? _GEN_192 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_385 = io_enq_valid & io_enq_ready ? _GEN_193 : roq_free_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_386 = io_enq_valid & io_enq_ready ? _GEN_194 : roq_free_2; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_387 = io_enq_valid & io_enq_ready ? _GEN_195 : roq_free_3; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_388 = io_enq_valid & io_enq_ready ? _GEN_196 : roq_free_4; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_389 = io_enq_valid & io_enq_ready ? _GEN_197 : roq_free_5; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_390 = io_enq_valid & io_enq_ready ? _GEN_198 : roq_free_6; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_391 = io_enq_valid & io_enq_ready ? _GEN_199 : roq_free_7; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_392 = io_enq_valid & io_enq_ready ? _GEN_200 : roq_free_8; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_393 = io_enq_valid & io_enq_ready ? _GEN_201 : roq_free_9; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_394 = io_enq_valid & io_enq_ready ? _GEN_202 : roq_free_10; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_395 = io_enq_valid & io_enq_ready ? _GEN_203 : roq_free_11; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_396 = io_enq_valid & io_enq_ready ? _GEN_204 : roq_free_12; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_397 = io_enq_valid & io_enq_ready ? _GEN_205 : roq_free_13; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_398 = io_enq_valid & io_enq_ready ? _GEN_206 : roq_free_14; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_399 = io_enq_valid & io_enq_ready ? _GEN_207 : roq_free_15; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_400 = io_enq_valid & io_enq_ready ? _GEN_208 : roq_free_16; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_401 = io_enq_valid & io_enq_ready ? _GEN_209 : roq_free_17; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_402 = io_enq_valid & io_enq_ready ? _GEN_210 : roq_free_18; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_403 = io_enq_valid & io_enq_ready ? _GEN_211 : roq_free_19; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_404 = io_enq_valid & io_enq_ready ? _GEN_212 : roq_free_20; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_405 = io_enq_valid & io_enq_ready ? _GEN_213 : roq_free_21; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_406 = io_enq_valid & io_enq_ready ? _GEN_214 : roq_free_22; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_407 = io_enq_valid & io_enq_ready ? _GEN_215 : roq_free_23; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_408 = io_enq_valid & io_enq_ready ? _GEN_216 : roq_free_24; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_409 = io_enq_valid & io_enq_ready ? _GEN_217 : roq_free_25; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_410 = io_enq_valid & io_enq_ready ? _GEN_218 : roq_free_26; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_411 = io_enq_valid & io_enq_ready ? _GEN_219 : roq_free_27; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_412 = io_enq_valid & io_enq_ready ? _GEN_220 : roq_free_28; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_413 = io_enq_valid & io_enq_ready ? _GEN_221 : roq_free_29; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_414 = io_enq_valid & io_enq_ready ? _GEN_222 : roq_free_30; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_415 = io_enq_valid & io_enq_ready ? _GEN_223 : roq_free_31; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_416 = io_enq_valid & io_enq_ready ? _GEN_224 : roq_free_32; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_417 = io_enq_valid & io_enq_ready ? _GEN_225 : roq_free_33; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_418 = io_enq_valid & io_enq_ready ? _GEN_226 : roq_free_34; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_419 = io_enq_valid & io_enq_ready ? _GEN_227 : roq_free_35; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_420 = io_enq_valid & io_enq_ready ? _GEN_228 : roq_free_36; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_421 = io_enq_valid & io_enq_ready ? _GEN_229 : roq_free_37; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_422 = io_enq_valid & io_enq_ready ? _GEN_230 : roq_free_38; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_423 = io_enq_valid & io_enq_ready ? _GEN_231 : roq_free_39; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_424 = io_enq_valid & io_enq_ready ? _GEN_232 : roq_free_40; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_425 = io_enq_valid & io_enq_ready ? _GEN_233 : roq_free_41; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_426 = io_enq_valid & io_enq_ready ? _GEN_234 : roq_free_42; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_427 = io_enq_valid & io_enq_ready ? _GEN_235 : roq_free_43; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_428 = io_enq_valid & io_enq_ready ? _GEN_236 : roq_free_44; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_429 = io_enq_valid & io_enq_ready ? _GEN_237 : roq_free_45; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_430 = io_enq_valid & io_enq_ready ? _GEN_238 : roq_free_46; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_431 = io_enq_valid & io_enq_ready ? _GEN_239 : roq_free_47; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_432 = io_enq_valid & io_enq_ready ? _GEN_240 : roq_free_48; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_433 = io_enq_valid & io_enq_ready ? _GEN_241 : roq_free_49; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_434 = io_enq_valid & io_enq_ready ? _GEN_242 : roq_free_50; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_435 = io_enq_valid & io_enq_ready ? _GEN_243 : roq_free_51; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_436 = io_enq_valid & io_enq_ready ? _GEN_244 : roq_free_52; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_437 = io_enq_valid & io_enq_ready ? _GEN_245 : roq_free_53; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_438 = io_enq_valid & io_enq_ready ? _GEN_246 : roq_free_54; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_439 = io_enq_valid & io_enq_ready ? _GEN_247 : roq_free_55; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_440 = io_enq_valid & io_enq_ready ? _GEN_248 : roq_free_56; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_441 = io_enq_valid & io_enq_ready ? _GEN_249 : roq_free_57; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_442 = io_enq_valid & io_enq_ready ? _GEN_250 : roq_free_58; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_443 = io_enq_valid & io_enq_ready ? _GEN_251 : roq_free_59; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_444 = io_enq_valid & io_enq_ready ? _GEN_252 : roq_free_60; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_445 = io_enq_valid & io_enq_ready ? _GEN_253 : roq_free_61; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_446 = io_enq_valid & io_enq_ready ? _GEN_254 : roq_free_62; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire  _GEN_447 = io_enq_valid & io_enq_ready ? _GEN_255 : roq_free_63; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:27 41:40]
  wire [5:0] roq_deq_addr = io_deq_0_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 48:33]
  wire  _GEN_513 = 6'h1 == roq_deq_addr ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_514 = 6'h2 == roq_deq_addr ? roq_free_2 : _GEN_513; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_515 = 6'h3 == roq_deq_addr ? roq_free_3 : _GEN_514; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_516 = 6'h4 == roq_deq_addr ? roq_free_4 : _GEN_515; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_517 = 6'h5 == roq_deq_addr ? roq_free_5 : _GEN_516; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_518 = 6'h6 == roq_deq_addr ? roq_free_6 : _GEN_517; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_519 = 6'h7 == roq_deq_addr ? roq_free_7 : _GEN_518; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_520 = 6'h8 == roq_deq_addr ? roq_free_8 : _GEN_519; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_521 = 6'h9 == roq_deq_addr ? roq_free_9 : _GEN_520; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_522 = 6'ha == roq_deq_addr ? roq_free_10 : _GEN_521; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_523 = 6'hb == roq_deq_addr ? roq_free_11 : _GEN_522; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_524 = 6'hc == roq_deq_addr ? roq_free_12 : _GEN_523; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_525 = 6'hd == roq_deq_addr ? roq_free_13 : _GEN_524; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_526 = 6'he == roq_deq_addr ? roq_free_14 : _GEN_525; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_527 = 6'hf == roq_deq_addr ? roq_free_15 : _GEN_526; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_528 = 6'h10 == roq_deq_addr ? roq_free_16 : _GEN_527; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_529 = 6'h11 == roq_deq_addr ? roq_free_17 : _GEN_528; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_530 = 6'h12 == roq_deq_addr ? roq_free_18 : _GEN_529; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_531 = 6'h13 == roq_deq_addr ? roq_free_19 : _GEN_530; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_532 = 6'h14 == roq_deq_addr ? roq_free_20 : _GEN_531; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_533 = 6'h15 == roq_deq_addr ? roq_free_21 : _GEN_532; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_534 = 6'h16 == roq_deq_addr ? roq_free_22 : _GEN_533; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_535 = 6'h17 == roq_deq_addr ? roq_free_23 : _GEN_534; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_536 = 6'h18 == roq_deq_addr ? roq_free_24 : _GEN_535; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_537 = 6'h19 == roq_deq_addr ? roq_free_25 : _GEN_536; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_538 = 6'h1a == roq_deq_addr ? roq_free_26 : _GEN_537; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_539 = 6'h1b == roq_deq_addr ? roq_free_27 : _GEN_538; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_540 = 6'h1c == roq_deq_addr ? roq_free_28 : _GEN_539; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_541 = 6'h1d == roq_deq_addr ? roq_free_29 : _GEN_540; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_542 = 6'h1e == roq_deq_addr ? roq_free_30 : _GEN_541; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_543 = 6'h1f == roq_deq_addr ? roq_free_31 : _GEN_542; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_544 = 6'h20 == roq_deq_addr ? roq_free_32 : _GEN_543; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_545 = 6'h21 == roq_deq_addr ? roq_free_33 : _GEN_544; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_546 = 6'h22 == roq_deq_addr ? roq_free_34 : _GEN_545; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_547 = 6'h23 == roq_deq_addr ? roq_free_35 : _GEN_546; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_548 = 6'h24 == roq_deq_addr ? roq_free_36 : _GEN_547; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_549 = 6'h25 == roq_deq_addr ? roq_free_37 : _GEN_548; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_550 = 6'h26 == roq_deq_addr ? roq_free_38 : _GEN_549; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_551 = 6'h27 == roq_deq_addr ? roq_free_39 : _GEN_550; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_552 = 6'h28 == roq_deq_addr ? roq_free_40 : _GEN_551; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_553 = 6'h29 == roq_deq_addr ? roq_free_41 : _GEN_552; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_554 = 6'h2a == roq_deq_addr ? roq_free_42 : _GEN_553; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_555 = 6'h2b == roq_deq_addr ? roq_free_43 : _GEN_554; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_556 = 6'h2c == roq_deq_addr ? roq_free_44 : _GEN_555; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_557 = 6'h2d == roq_deq_addr ? roq_free_45 : _GEN_556; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_558 = 6'h2e == roq_deq_addr ? roq_free_46 : _GEN_557; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_559 = 6'h2f == roq_deq_addr ? roq_free_47 : _GEN_558; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_560 = 6'h30 == roq_deq_addr ? roq_free_48 : _GEN_559; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_561 = 6'h31 == roq_deq_addr ? roq_free_49 : _GEN_560; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_562 = 6'h32 == roq_deq_addr ? roq_free_50 : _GEN_561; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_563 = 6'h33 == roq_deq_addr ? roq_free_51 : _GEN_562; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_564 = 6'h34 == roq_deq_addr ? roq_free_52 : _GEN_563; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_565 = 6'h35 == roq_deq_addr ? roq_free_53 : _GEN_564; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_566 = 6'h36 == roq_deq_addr ? roq_free_54 : _GEN_565; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_567 = 6'h37 == roq_deq_addr ? roq_free_55 : _GEN_566; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_568 = 6'h38 == roq_deq_addr ? roq_free_56 : _GEN_567; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_569 = 6'h39 == roq_deq_addr ? roq_free_57 : _GEN_568; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_570 = 6'h3a == roq_deq_addr ? roq_free_58 : _GEN_569; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_571 = 6'h3b == roq_deq_addr ? roq_free_59 : _GEN_570; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_572 = 6'h3c == roq_deq_addr ? roq_free_60 : _GEN_571; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_573 = 6'h3d == roq_deq_addr ? roq_free_61 : _GEN_572; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_574 = 6'h3e == roq_deq_addr ? roq_free_62 : _GEN_573; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_575 = 6'h3f == roq_deq_addr ? roq_free_63 : _GEN_574; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire [11:0] _io_deq_0_matches_T_1 = {{6'd0}, io_deq_0_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:85]
  wire [5:0] _GEN_577 = 6'h1 == roq_deq_addr ? roq_tags_1 : roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_578 = 6'h2 == roq_deq_addr ? roq_tags_2 : _GEN_577; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_579 = 6'h3 == roq_deq_addr ? roq_tags_3 : _GEN_578; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_580 = 6'h4 == roq_deq_addr ? roq_tags_4 : _GEN_579; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_581 = 6'h5 == roq_deq_addr ? roq_tags_5 : _GEN_580; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_582 = 6'h6 == roq_deq_addr ? roq_tags_6 : _GEN_581; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_583 = 6'h7 == roq_deq_addr ? roq_tags_7 : _GEN_582; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_584 = 6'h8 == roq_deq_addr ? roq_tags_8 : _GEN_583; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_585 = 6'h9 == roq_deq_addr ? roq_tags_9 : _GEN_584; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_586 = 6'ha == roq_deq_addr ? roq_tags_10 : _GEN_585; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_587 = 6'hb == roq_deq_addr ? roq_tags_11 : _GEN_586; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_588 = 6'hc == roq_deq_addr ? roq_tags_12 : _GEN_587; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_589 = 6'hd == roq_deq_addr ? roq_tags_13 : _GEN_588; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_590 = 6'he == roq_deq_addr ? roq_tags_14 : _GEN_589; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_591 = 6'hf == roq_deq_addr ? roq_tags_15 : _GEN_590; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_592 = 6'h10 == roq_deq_addr ? roq_tags_16 : _GEN_591; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_593 = 6'h11 == roq_deq_addr ? roq_tags_17 : _GEN_592; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_594 = 6'h12 == roq_deq_addr ? roq_tags_18 : _GEN_593; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_595 = 6'h13 == roq_deq_addr ? roq_tags_19 : _GEN_594; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_596 = 6'h14 == roq_deq_addr ? roq_tags_20 : _GEN_595; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_597 = 6'h15 == roq_deq_addr ? roq_tags_21 : _GEN_596; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_598 = 6'h16 == roq_deq_addr ? roq_tags_22 : _GEN_597; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_599 = 6'h17 == roq_deq_addr ? roq_tags_23 : _GEN_598; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_600 = 6'h18 == roq_deq_addr ? roq_tags_24 : _GEN_599; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_601 = 6'h19 == roq_deq_addr ? roq_tags_25 : _GEN_600; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_602 = 6'h1a == roq_deq_addr ? roq_tags_26 : _GEN_601; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_603 = 6'h1b == roq_deq_addr ? roq_tags_27 : _GEN_602; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_604 = 6'h1c == roq_deq_addr ? roq_tags_28 : _GEN_603; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_605 = 6'h1d == roq_deq_addr ? roq_tags_29 : _GEN_604; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_606 = 6'h1e == roq_deq_addr ? roq_tags_30 : _GEN_605; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_607 = 6'h1f == roq_deq_addr ? roq_tags_31 : _GEN_606; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_608 = 6'h20 == roq_deq_addr ? roq_tags_32 : _GEN_607; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_609 = 6'h21 == roq_deq_addr ? roq_tags_33 : _GEN_608; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_610 = 6'h22 == roq_deq_addr ? roq_tags_34 : _GEN_609; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_611 = 6'h23 == roq_deq_addr ? roq_tags_35 : _GEN_610; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_612 = 6'h24 == roq_deq_addr ? roq_tags_36 : _GEN_611; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_613 = 6'h25 == roq_deq_addr ? roq_tags_37 : _GEN_612; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_614 = 6'h26 == roq_deq_addr ? roq_tags_38 : _GEN_613; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_615 = 6'h27 == roq_deq_addr ? roq_tags_39 : _GEN_614; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_616 = 6'h28 == roq_deq_addr ? roq_tags_40 : _GEN_615; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_617 = 6'h29 == roq_deq_addr ? roq_tags_41 : _GEN_616; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_618 = 6'h2a == roq_deq_addr ? roq_tags_42 : _GEN_617; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_619 = 6'h2b == roq_deq_addr ? roq_tags_43 : _GEN_618; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_620 = 6'h2c == roq_deq_addr ? roq_tags_44 : _GEN_619; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_621 = 6'h2d == roq_deq_addr ? roq_tags_45 : _GEN_620; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_622 = 6'h2e == roq_deq_addr ? roq_tags_46 : _GEN_621; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_623 = 6'h2f == roq_deq_addr ? roq_tags_47 : _GEN_622; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_624 = 6'h30 == roq_deq_addr ? roq_tags_48 : _GEN_623; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_625 = 6'h31 == roq_deq_addr ? roq_tags_49 : _GEN_624; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_626 = 6'h32 == roq_deq_addr ? roq_tags_50 : _GEN_625; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_627 = 6'h33 == roq_deq_addr ? roq_tags_51 : _GEN_626; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_628 = 6'h34 == roq_deq_addr ? roq_tags_52 : _GEN_627; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_629 = 6'h35 == roq_deq_addr ? roq_tags_53 : _GEN_628; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_630 = 6'h36 == roq_deq_addr ? roq_tags_54 : _GEN_629; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_631 = 6'h37 == roq_deq_addr ? roq_tags_55 : _GEN_630; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_632 = 6'h38 == roq_deq_addr ? roq_tags_56 : _GEN_631; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_633 = 6'h39 == roq_deq_addr ? roq_tags_57 : _GEN_632; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_634 = 6'h3a == roq_deq_addr ? roq_tags_58 : _GEN_633; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_635 = 6'h3b == roq_deq_addr ? roq_tags_59 : _GEN_634; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_636 = 6'h3c == roq_deq_addr ? roq_tags_60 : _GEN_635; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_637 = 6'h3d == roq_deq_addr ? roq_tags_61 : _GEN_636; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_638 = 6'h3e == roq_deq_addr ? roq_tags_62 : _GEN_637; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_639 = 6'h3f == roq_deq_addr ? roq_tags_63 : _GEN_638; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [11:0] _GEN_2050 = {{6'd0}, _GEN_639}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:72]
  wire  _GEN_640 = 6'h0 == roq_deq_addr | _GEN_384; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_641 = 6'h1 == roq_deq_addr | _GEN_385; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_642 = 6'h2 == roq_deq_addr | _GEN_386; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_643 = 6'h3 == roq_deq_addr | _GEN_387; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_644 = 6'h4 == roq_deq_addr | _GEN_388; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_645 = 6'h5 == roq_deq_addr | _GEN_389; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_646 = 6'h6 == roq_deq_addr | _GEN_390; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_647 = 6'h7 == roq_deq_addr | _GEN_391; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_648 = 6'h8 == roq_deq_addr | _GEN_392; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_649 = 6'h9 == roq_deq_addr | _GEN_393; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_650 = 6'ha == roq_deq_addr | _GEN_394; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_651 = 6'hb == roq_deq_addr | _GEN_395; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_652 = 6'hc == roq_deq_addr | _GEN_396; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_653 = 6'hd == roq_deq_addr | _GEN_397; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_654 = 6'he == roq_deq_addr | _GEN_398; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_655 = 6'hf == roq_deq_addr | _GEN_399; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_656 = 6'h10 == roq_deq_addr | _GEN_400; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_657 = 6'h11 == roq_deq_addr | _GEN_401; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_658 = 6'h12 == roq_deq_addr | _GEN_402; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_659 = 6'h13 == roq_deq_addr | _GEN_403; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_660 = 6'h14 == roq_deq_addr | _GEN_404; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_661 = 6'h15 == roq_deq_addr | _GEN_405; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_662 = 6'h16 == roq_deq_addr | _GEN_406; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_663 = 6'h17 == roq_deq_addr | _GEN_407; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_664 = 6'h18 == roq_deq_addr | _GEN_408; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_665 = 6'h19 == roq_deq_addr | _GEN_409; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_666 = 6'h1a == roq_deq_addr | _GEN_410; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_667 = 6'h1b == roq_deq_addr | _GEN_411; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_668 = 6'h1c == roq_deq_addr | _GEN_412; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_669 = 6'h1d == roq_deq_addr | _GEN_413; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_670 = 6'h1e == roq_deq_addr | _GEN_414; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_671 = 6'h1f == roq_deq_addr | _GEN_415; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_672 = 6'h20 == roq_deq_addr | _GEN_416; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_673 = 6'h21 == roq_deq_addr | _GEN_417; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_674 = 6'h22 == roq_deq_addr | _GEN_418; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_675 = 6'h23 == roq_deq_addr | _GEN_419; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_676 = 6'h24 == roq_deq_addr | _GEN_420; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_677 = 6'h25 == roq_deq_addr | _GEN_421; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_678 = 6'h26 == roq_deq_addr | _GEN_422; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_679 = 6'h27 == roq_deq_addr | _GEN_423; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_680 = 6'h28 == roq_deq_addr | _GEN_424; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_681 = 6'h29 == roq_deq_addr | _GEN_425; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_682 = 6'h2a == roq_deq_addr | _GEN_426; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_683 = 6'h2b == roq_deq_addr | _GEN_427; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_684 = 6'h2c == roq_deq_addr | _GEN_428; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_685 = 6'h2d == roq_deq_addr | _GEN_429; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_686 = 6'h2e == roq_deq_addr | _GEN_430; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_687 = 6'h2f == roq_deq_addr | _GEN_431; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_688 = 6'h30 == roq_deq_addr | _GEN_432; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_689 = 6'h31 == roq_deq_addr | _GEN_433; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_690 = 6'h32 == roq_deq_addr | _GEN_434; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_691 = 6'h33 == roq_deq_addr | _GEN_435; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_692 = 6'h34 == roq_deq_addr | _GEN_436; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_693 = 6'h35 == roq_deq_addr | _GEN_437; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_694 = 6'h36 == roq_deq_addr | _GEN_438; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_695 = 6'h37 == roq_deq_addr | _GEN_439; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_696 = 6'h38 == roq_deq_addr | _GEN_440; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_697 = 6'h39 == roq_deq_addr | _GEN_441; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_698 = 6'h3a == roq_deq_addr | _GEN_442; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_699 = 6'h3b == roq_deq_addr | _GEN_443; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_700 = 6'h3c == roq_deq_addr | _GEN_444; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_701 = 6'h3d == roq_deq_addr | _GEN_445; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_702 = 6'h3e == roq_deq_addr | _GEN_446; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_703 = 6'h3f == roq_deq_addr | _GEN_447; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_704 = io_deq_0_valid ? _GEN_640 : _GEN_384; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_705 = io_deq_0_valid ? _GEN_641 : _GEN_385; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_706 = io_deq_0_valid ? _GEN_642 : _GEN_386; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_707 = io_deq_0_valid ? _GEN_643 : _GEN_387; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_708 = io_deq_0_valid ? _GEN_644 : _GEN_388; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_709 = io_deq_0_valid ? _GEN_645 : _GEN_389; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_710 = io_deq_0_valid ? _GEN_646 : _GEN_390; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_711 = io_deq_0_valid ? _GEN_647 : _GEN_391; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_712 = io_deq_0_valid ? _GEN_648 : _GEN_392; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_713 = io_deq_0_valid ? _GEN_649 : _GEN_393; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_714 = io_deq_0_valid ? _GEN_650 : _GEN_394; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_715 = io_deq_0_valid ? _GEN_651 : _GEN_395; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_716 = io_deq_0_valid ? _GEN_652 : _GEN_396; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_717 = io_deq_0_valid ? _GEN_653 : _GEN_397; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_718 = io_deq_0_valid ? _GEN_654 : _GEN_398; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_719 = io_deq_0_valid ? _GEN_655 : _GEN_399; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_720 = io_deq_0_valid ? _GEN_656 : _GEN_400; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_721 = io_deq_0_valid ? _GEN_657 : _GEN_401; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_722 = io_deq_0_valid ? _GEN_658 : _GEN_402; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_723 = io_deq_0_valid ? _GEN_659 : _GEN_403; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_724 = io_deq_0_valid ? _GEN_660 : _GEN_404; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_725 = io_deq_0_valid ? _GEN_661 : _GEN_405; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_726 = io_deq_0_valid ? _GEN_662 : _GEN_406; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_727 = io_deq_0_valid ? _GEN_663 : _GEN_407; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_728 = io_deq_0_valid ? _GEN_664 : _GEN_408; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_729 = io_deq_0_valid ? _GEN_665 : _GEN_409; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_730 = io_deq_0_valid ? _GEN_666 : _GEN_410; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_731 = io_deq_0_valid ? _GEN_667 : _GEN_411; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_732 = io_deq_0_valid ? _GEN_668 : _GEN_412; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_733 = io_deq_0_valid ? _GEN_669 : _GEN_413; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_734 = io_deq_0_valid ? _GEN_670 : _GEN_414; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_735 = io_deq_0_valid ? _GEN_671 : _GEN_415; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_736 = io_deq_0_valid ? _GEN_672 : _GEN_416; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_737 = io_deq_0_valid ? _GEN_673 : _GEN_417; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_738 = io_deq_0_valid ? _GEN_674 : _GEN_418; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_739 = io_deq_0_valid ? _GEN_675 : _GEN_419; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_740 = io_deq_0_valid ? _GEN_676 : _GEN_420; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_741 = io_deq_0_valid ? _GEN_677 : _GEN_421; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_742 = io_deq_0_valid ? _GEN_678 : _GEN_422; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_743 = io_deq_0_valid ? _GEN_679 : _GEN_423; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_744 = io_deq_0_valid ? _GEN_680 : _GEN_424; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_745 = io_deq_0_valid ? _GEN_681 : _GEN_425; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_746 = io_deq_0_valid ? _GEN_682 : _GEN_426; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_747 = io_deq_0_valid ? _GEN_683 : _GEN_427; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_748 = io_deq_0_valid ? _GEN_684 : _GEN_428; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_749 = io_deq_0_valid ? _GEN_685 : _GEN_429; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_750 = io_deq_0_valid ? _GEN_686 : _GEN_430; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_751 = io_deq_0_valid ? _GEN_687 : _GEN_431; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_752 = io_deq_0_valid ? _GEN_688 : _GEN_432; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_753 = io_deq_0_valid ? _GEN_689 : _GEN_433; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_754 = io_deq_0_valid ? _GEN_690 : _GEN_434; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_755 = io_deq_0_valid ? _GEN_691 : _GEN_435; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_756 = io_deq_0_valid ? _GEN_692 : _GEN_436; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_757 = io_deq_0_valid ? _GEN_693 : _GEN_437; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_758 = io_deq_0_valid ? _GEN_694 : _GEN_438; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_759 = io_deq_0_valid ? _GEN_695 : _GEN_439; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_760 = io_deq_0_valid ? _GEN_696 : _GEN_440; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_761 = io_deq_0_valid ? _GEN_697 : _GEN_441; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_762 = io_deq_0_valid ? _GEN_698 : _GEN_442; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_763 = io_deq_0_valid ? _GEN_699 : _GEN_443; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_764 = io_deq_0_valid ? _GEN_700 : _GEN_444; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_765 = io_deq_0_valid ? _GEN_701 : _GEN_445; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_766 = io_deq_0_valid ? _GEN_702 : _GEN_446; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_767 = io_deq_0_valid ? _GEN_703 : _GEN_447; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire [5:0] roq_deq_addr_1 = io_deq_1_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 48:33]
  wire  _GEN_833 = 6'h1 == roq_deq_addr_1 ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_834 = 6'h2 == roq_deq_addr_1 ? roq_free_2 : _GEN_833; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_835 = 6'h3 == roq_deq_addr_1 ? roq_free_3 : _GEN_834; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_836 = 6'h4 == roq_deq_addr_1 ? roq_free_4 : _GEN_835; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_837 = 6'h5 == roq_deq_addr_1 ? roq_free_5 : _GEN_836; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_838 = 6'h6 == roq_deq_addr_1 ? roq_free_6 : _GEN_837; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_839 = 6'h7 == roq_deq_addr_1 ? roq_free_7 : _GEN_838; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_840 = 6'h8 == roq_deq_addr_1 ? roq_free_8 : _GEN_839; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_841 = 6'h9 == roq_deq_addr_1 ? roq_free_9 : _GEN_840; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_842 = 6'ha == roq_deq_addr_1 ? roq_free_10 : _GEN_841; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_843 = 6'hb == roq_deq_addr_1 ? roq_free_11 : _GEN_842; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_844 = 6'hc == roq_deq_addr_1 ? roq_free_12 : _GEN_843; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_845 = 6'hd == roq_deq_addr_1 ? roq_free_13 : _GEN_844; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_846 = 6'he == roq_deq_addr_1 ? roq_free_14 : _GEN_845; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_847 = 6'hf == roq_deq_addr_1 ? roq_free_15 : _GEN_846; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_848 = 6'h10 == roq_deq_addr_1 ? roq_free_16 : _GEN_847; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_849 = 6'h11 == roq_deq_addr_1 ? roq_free_17 : _GEN_848; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_850 = 6'h12 == roq_deq_addr_1 ? roq_free_18 : _GEN_849; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_851 = 6'h13 == roq_deq_addr_1 ? roq_free_19 : _GEN_850; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_852 = 6'h14 == roq_deq_addr_1 ? roq_free_20 : _GEN_851; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_853 = 6'h15 == roq_deq_addr_1 ? roq_free_21 : _GEN_852; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_854 = 6'h16 == roq_deq_addr_1 ? roq_free_22 : _GEN_853; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_855 = 6'h17 == roq_deq_addr_1 ? roq_free_23 : _GEN_854; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_856 = 6'h18 == roq_deq_addr_1 ? roq_free_24 : _GEN_855; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_857 = 6'h19 == roq_deq_addr_1 ? roq_free_25 : _GEN_856; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_858 = 6'h1a == roq_deq_addr_1 ? roq_free_26 : _GEN_857; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_859 = 6'h1b == roq_deq_addr_1 ? roq_free_27 : _GEN_858; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_860 = 6'h1c == roq_deq_addr_1 ? roq_free_28 : _GEN_859; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_861 = 6'h1d == roq_deq_addr_1 ? roq_free_29 : _GEN_860; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_862 = 6'h1e == roq_deq_addr_1 ? roq_free_30 : _GEN_861; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_863 = 6'h1f == roq_deq_addr_1 ? roq_free_31 : _GEN_862; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_864 = 6'h20 == roq_deq_addr_1 ? roq_free_32 : _GEN_863; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_865 = 6'h21 == roq_deq_addr_1 ? roq_free_33 : _GEN_864; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_866 = 6'h22 == roq_deq_addr_1 ? roq_free_34 : _GEN_865; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_867 = 6'h23 == roq_deq_addr_1 ? roq_free_35 : _GEN_866; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_868 = 6'h24 == roq_deq_addr_1 ? roq_free_36 : _GEN_867; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_869 = 6'h25 == roq_deq_addr_1 ? roq_free_37 : _GEN_868; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_870 = 6'h26 == roq_deq_addr_1 ? roq_free_38 : _GEN_869; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_871 = 6'h27 == roq_deq_addr_1 ? roq_free_39 : _GEN_870; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_872 = 6'h28 == roq_deq_addr_1 ? roq_free_40 : _GEN_871; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_873 = 6'h29 == roq_deq_addr_1 ? roq_free_41 : _GEN_872; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_874 = 6'h2a == roq_deq_addr_1 ? roq_free_42 : _GEN_873; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_875 = 6'h2b == roq_deq_addr_1 ? roq_free_43 : _GEN_874; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_876 = 6'h2c == roq_deq_addr_1 ? roq_free_44 : _GEN_875; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_877 = 6'h2d == roq_deq_addr_1 ? roq_free_45 : _GEN_876; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_878 = 6'h2e == roq_deq_addr_1 ? roq_free_46 : _GEN_877; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_879 = 6'h2f == roq_deq_addr_1 ? roq_free_47 : _GEN_878; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_880 = 6'h30 == roq_deq_addr_1 ? roq_free_48 : _GEN_879; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_881 = 6'h31 == roq_deq_addr_1 ? roq_free_49 : _GEN_880; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_882 = 6'h32 == roq_deq_addr_1 ? roq_free_50 : _GEN_881; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_883 = 6'h33 == roq_deq_addr_1 ? roq_free_51 : _GEN_882; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_884 = 6'h34 == roq_deq_addr_1 ? roq_free_52 : _GEN_883; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_885 = 6'h35 == roq_deq_addr_1 ? roq_free_53 : _GEN_884; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_886 = 6'h36 == roq_deq_addr_1 ? roq_free_54 : _GEN_885; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_887 = 6'h37 == roq_deq_addr_1 ? roq_free_55 : _GEN_886; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_888 = 6'h38 == roq_deq_addr_1 ? roq_free_56 : _GEN_887; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_889 = 6'h39 == roq_deq_addr_1 ? roq_free_57 : _GEN_888; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_890 = 6'h3a == roq_deq_addr_1 ? roq_free_58 : _GEN_889; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_891 = 6'h3b == roq_deq_addr_1 ? roq_free_59 : _GEN_890; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_892 = 6'h3c == roq_deq_addr_1 ? roq_free_60 : _GEN_891; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_893 = 6'h3d == roq_deq_addr_1 ? roq_free_61 : _GEN_892; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_894 = 6'h3e == roq_deq_addr_1 ? roq_free_62 : _GEN_893; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_895 = 6'h3f == roq_deq_addr_1 ? roq_free_63 : _GEN_894; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire [11:0] _io_deq_1_matches_T_1 = {{6'd0}, io_deq_1_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:85]
  wire [5:0] _GEN_897 = 6'h1 == roq_deq_addr_1 ? roq_tags_1 : roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_898 = 6'h2 == roq_deq_addr_1 ? roq_tags_2 : _GEN_897; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_899 = 6'h3 == roq_deq_addr_1 ? roq_tags_3 : _GEN_898; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_900 = 6'h4 == roq_deq_addr_1 ? roq_tags_4 : _GEN_899; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_901 = 6'h5 == roq_deq_addr_1 ? roq_tags_5 : _GEN_900; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_902 = 6'h6 == roq_deq_addr_1 ? roq_tags_6 : _GEN_901; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_903 = 6'h7 == roq_deq_addr_1 ? roq_tags_7 : _GEN_902; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_904 = 6'h8 == roq_deq_addr_1 ? roq_tags_8 : _GEN_903; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_905 = 6'h9 == roq_deq_addr_1 ? roq_tags_9 : _GEN_904; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_906 = 6'ha == roq_deq_addr_1 ? roq_tags_10 : _GEN_905; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_907 = 6'hb == roq_deq_addr_1 ? roq_tags_11 : _GEN_906; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_908 = 6'hc == roq_deq_addr_1 ? roq_tags_12 : _GEN_907; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_909 = 6'hd == roq_deq_addr_1 ? roq_tags_13 : _GEN_908; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_910 = 6'he == roq_deq_addr_1 ? roq_tags_14 : _GEN_909; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_911 = 6'hf == roq_deq_addr_1 ? roq_tags_15 : _GEN_910; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_912 = 6'h10 == roq_deq_addr_1 ? roq_tags_16 : _GEN_911; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_913 = 6'h11 == roq_deq_addr_1 ? roq_tags_17 : _GEN_912; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_914 = 6'h12 == roq_deq_addr_1 ? roq_tags_18 : _GEN_913; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_915 = 6'h13 == roq_deq_addr_1 ? roq_tags_19 : _GEN_914; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_916 = 6'h14 == roq_deq_addr_1 ? roq_tags_20 : _GEN_915; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_917 = 6'h15 == roq_deq_addr_1 ? roq_tags_21 : _GEN_916; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_918 = 6'h16 == roq_deq_addr_1 ? roq_tags_22 : _GEN_917; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_919 = 6'h17 == roq_deq_addr_1 ? roq_tags_23 : _GEN_918; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_920 = 6'h18 == roq_deq_addr_1 ? roq_tags_24 : _GEN_919; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_921 = 6'h19 == roq_deq_addr_1 ? roq_tags_25 : _GEN_920; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_922 = 6'h1a == roq_deq_addr_1 ? roq_tags_26 : _GEN_921; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_923 = 6'h1b == roq_deq_addr_1 ? roq_tags_27 : _GEN_922; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_924 = 6'h1c == roq_deq_addr_1 ? roq_tags_28 : _GEN_923; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_925 = 6'h1d == roq_deq_addr_1 ? roq_tags_29 : _GEN_924; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_926 = 6'h1e == roq_deq_addr_1 ? roq_tags_30 : _GEN_925; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_927 = 6'h1f == roq_deq_addr_1 ? roq_tags_31 : _GEN_926; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_928 = 6'h20 == roq_deq_addr_1 ? roq_tags_32 : _GEN_927; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_929 = 6'h21 == roq_deq_addr_1 ? roq_tags_33 : _GEN_928; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_930 = 6'h22 == roq_deq_addr_1 ? roq_tags_34 : _GEN_929; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_931 = 6'h23 == roq_deq_addr_1 ? roq_tags_35 : _GEN_930; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_932 = 6'h24 == roq_deq_addr_1 ? roq_tags_36 : _GEN_931; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_933 = 6'h25 == roq_deq_addr_1 ? roq_tags_37 : _GEN_932; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_934 = 6'h26 == roq_deq_addr_1 ? roq_tags_38 : _GEN_933; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_935 = 6'h27 == roq_deq_addr_1 ? roq_tags_39 : _GEN_934; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_936 = 6'h28 == roq_deq_addr_1 ? roq_tags_40 : _GEN_935; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_937 = 6'h29 == roq_deq_addr_1 ? roq_tags_41 : _GEN_936; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_938 = 6'h2a == roq_deq_addr_1 ? roq_tags_42 : _GEN_937; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_939 = 6'h2b == roq_deq_addr_1 ? roq_tags_43 : _GEN_938; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_940 = 6'h2c == roq_deq_addr_1 ? roq_tags_44 : _GEN_939; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_941 = 6'h2d == roq_deq_addr_1 ? roq_tags_45 : _GEN_940; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_942 = 6'h2e == roq_deq_addr_1 ? roq_tags_46 : _GEN_941; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_943 = 6'h2f == roq_deq_addr_1 ? roq_tags_47 : _GEN_942; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_944 = 6'h30 == roq_deq_addr_1 ? roq_tags_48 : _GEN_943; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_945 = 6'h31 == roq_deq_addr_1 ? roq_tags_49 : _GEN_944; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_946 = 6'h32 == roq_deq_addr_1 ? roq_tags_50 : _GEN_945; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_947 = 6'h33 == roq_deq_addr_1 ? roq_tags_51 : _GEN_946; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_948 = 6'h34 == roq_deq_addr_1 ? roq_tags_52 : _GEN_947; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_949 = 6'h35 == roq_deq_addr_1 ? roq_tags_53 : _GEN_948; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_950 = 6'h36 == roq_deq_addr_1 ? roq_tags_54 : _GEN_949; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_951 = 6'h37 == roq_deq_addr_1 ? roq_tags_55 : _GEN_950; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_952 = 6'h38 == roq_deq_addr_1 ? roq_tags_56 : _GEN_951; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_953 = 6'h39 == roq_deq_addr_1 ? roq_tags_57 : _GEN_952; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_954 = 6'h3a == roq_deq_addr_1 ? roq_tags_58 : _GEN_953; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_955 = 6'h3b == roq_deq_addr_1 ? roq_tags_59 : _GEN_954; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_956 = 6'h3c == roq_deq_addr_1 ? roq_tags_60 : _GEN_955; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_957 = 6'h3d == roq_deq_addr_1 ? roq_tags_61 : _GEN_956; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_958 = 6'h3e == roq_deq_addr_1 ? roq_tags_62 : _GEN_957; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_959 = 6'h3f == roq_deq_addr_1 ? roq_tags_63 : _GEN_958; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [11:0] _GEN_2116 = {{6'd0}, _GEN_959}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:72]
  wire  _GEN_960 = 6'h0 == roq_deq_addr_1 | _GEN_704; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_961 = 6'h1 == roq_deq_addr_1 | _GEN_705; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_962 = 6'h2 == roq_deq_addr_1 | _GEN_706; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_963 = 6'h3 == roq_deq_addr_1 | _GEN_707; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_964 = 6'h4 == roq_deq_addr_1 | _GEN_708; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_965 = 6'h5 == roq_deq_addr_1 | _GEN_709; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_966 = 6'h6 == roq_deq_addr_1 | _GEN_710; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_967 = 6'h7 == roq_deq_addr_1 | _GEN_711; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_968 = 6'h8 == roq_deq_addr_1 | _GEN_712; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_969 = 6'h9 == roq_deq_addr_1 | _GEN_713; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_970 = 6'ha == roq_deq_addr_1 | _GEN_714; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_971 = 6'hb == roq_deq_addr_1 | _GEN_715; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_972 = 6'hc == roq_deq_addr_1 | _GEN_716; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_973 = 6'hd == roq_deq_addr_1 | _GEN_717; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_974 = 6'he == roq_deq_addr_1 | _GEN_718; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_975 = 6'hf == roq_deq_addr_1 | _GEN_719; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_976 = 6'h10 == roq_deq_addr_1 | _GEN_720; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_977 = 6'h11 == roq_deq_addr_1 | _GEN_721; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_978 = 6'h12 == roq_deq_addr_1 | _GEN_722; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_979 = 6'h13 == roq_deq_addr_1 | _GEN_723; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_980 = 6'h14 == roq_deq_addr_1 | _GEN_724; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_981 = 6'h15 == roq_deq_addr_1 | _GEN_725; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_982 = 6'h16 == roq_deq_addr_1 | _GEN_726; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_983 = 6'h17 == roq_deq_addr_1 | _GEN_727; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_984 = 6'h18 == roq_deq_addr_1 | _GEN_728; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_985 = 6'h19 == roq_deq_addr_1 | _GEN_729; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_986 = 6'h1a == roq_deq_addr_1 | _GEN_730; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_987 = 6'h1b == roq_deq_addr_1 | _GEN_731; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_988 = 6'h1c == roq_deq_addr_1 | _GEN_732; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_989 = 6'h1d == roq_deq_addr_1 | _GEN_733; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_990 = 6'h1e == roq_deq_addr_1 | _GEN_734; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_991 = 6'h1f == roq_deq_addr_1 | _GEN_735; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_992 = 6'h20 == roq_deq_addr_1 | _GEN_736; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_993 = 6'h21 == roq_deq_addr_1 | _GEN_737; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_994 = 6'h22 == roq_deq_addr_1 | _GEN_738; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_995 = 6'h23 == roq_deq_addr_1 | _GEN_739; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_996 = 6'h24 == roq_deq_addr_1 | _GEN_740; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_997 = 6'h25 == roq_deq_addr_1 | _GEN_741; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_998 = 6'h26 == roq_deq_addr_1 | _GEN_742; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_999 = 6'h27 == roq_deq_addr_1 | _GEN_743; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1000 = 6'h28 == roq_deq_addr_1 | _GEN_744; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1001 = 6'h29 == roq_deq_addr_1 | _GEN_745; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1002 = 6'h2a == roq_deq_addr_1 | _GEN_746; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1003 = 6'h2b == roq_deq_addr_1 | _GEN_747; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1004 = 6'h2c == roq_deq_addr_1 | _GEN_748; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1005 = 6'h2d == roq_deq_addr_1 | _GEN_749; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1006 = 6'h2e == roq_deq_addr_1 | _GEN_750; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1007 = 6'h2f == roq_deq_addr_1 | _GEN_751; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1008 = 6'h30 == roq_deq_addr_1 | _GEN_752; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1009 = 6'h31 == roq_deq_addr_1 | _GEN_753; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1010 = 6'h32 == roq_deq_addr_1 | _GEN_754; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1011 = 6'h33 == roq_deq_addr_1 | _GEN_755; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1012 = 6'h34 == roq_deq_addr_1 | _GEN_756; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1013 = 6'h35 == roq_deq_addr_1 | _GEN_757; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1014 = 6'h36 == roq_deq_addr_1 | _GEN_758; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1015 = 6'h37 == roq_deq_addr_1 | _GEN_759; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1016 = 6'h38 == roq_deq_addr_1 | _GEN_760; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1017 = 6'h39 == roq_deq_addr_1 | _GEN_761; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1018 = 6'h3a == roq_deq_addr_1 | _GEN_762; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1019 = 6'h3b == roq_deq_addr_1 | _GEN_763; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1020 = 6'h3c == roq_deq_addr_1 | _GEN_764; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1021 = 6'h3d == roq_deq_addr_1 | _GEN_765; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1022 = 6'h3e == roq_deq_addr_1 | _GEN_766; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1023 = 6'h3f == roq_deq_addr_1 | _GEN_767; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1024 = io_deq_1_valid ? _GEN_960 : _GEN_704; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1025 = io_deq_1_valid ? _GEN_961 : _GEN_705; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1026 = io_deq_1_valid ? _GEN_962 : _GEN_706; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1027 = io_deq_1_valid ? _GEN_963 : _GEN_707; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1028 = io_deq_1_valid ? _GEN_964 : _GEN_708; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1029 = io_deq_1_valid ? _GEN_965 : _GEN_709; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1030 = io_deq_1_valid ? _GEN_966 : _GEN_710; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1031 = io_deq_1_valid ? _GEN_967 : _GEN_711; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1032 = io_deq_1_valid ? _GEN_968 : _GEN_712; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1033 = io_deq_1_valid ? _GEN_969 : _GEN_713; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1034 = io_deq_1_valid ? _GEN_970 : _GEN_714; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1035 = io_deq_1_valid ? _GEN_971 : _GEN_715; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1036 = io_deq_1_valid ? _GEN_972 : _GEN_716; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1037 = io_deq_1_valid ? _GEN_973 : _GEN_717; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1038 = io_deq_1_valid ? _GEN_974 : _GEN_718; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1039 = io_deq_1_valid ? _GEN_975 : _GEN_719; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1040 = io_deq_1_valid ? _GEN_976 : _GEN_720; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1041 = io_deq_1_valid ? _GEN_977 : _GEN_721; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1042 = io_deq_1_valid ? _GEN_978 : _GEN_722; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1043 = io_deq_1_valid ? _GEN_979 : _GEN_723; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1044 = io_deq_1_valid ? _GEN_980 : _GEN_724; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1045 = io_deq_1_valid ? _GEN_981 : _GEN_725; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1046 = io_deq_1_valid ? _GEN_982 : _GEN_726; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1047 = io_deq_1_valid ? _GEN_983 : _GEN_727; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1048 = io_deq_1_valid ? _GEN_984 : _GEN_728; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1049 = io_deq_1_valid ? _GEN_985 : _GEN_729; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1050 = io_deq_1_valid ? _GEN_986 : _GEN_730; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1051 = io_deq_1_valid ? _GEN_987 : _GEN_731; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1052 = io_deq_1_valid ? _GEN_988 : _GEN_732; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1053 = io_deq_1_valid ? _GEN_989 : _GEN_733; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1054 = io_deq_1_valid ? _GEN_990 : _GEN_734; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1055 = io_deq_1_valid ? _GEN_991 : _GEN_735; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1056 = io_deq_1_valid ? _GEN_992 : _GEN_736; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1057 = io_deq_1_valid ? _GEN_993 : _GEN_737; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1058 = io_deq_1_valid ? _GEN_994 : _GEN_738; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1059 = io_deq_1_valid ? _GEN_995 : _GEN_739; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1060 = io_deq_1_valid ? _GEN_996 : _GEN_740; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1061 = io_deq_1_valid ? _GEN_997 : _GEN_741; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1062 = io_deq_1_valid ? _GEN_998 : _GEN_742; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1063 = io_deq_1_valid ? _GEN_999 : _GEN_743; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1064 = io_deq_1_valid ? _GEN_1000 : _GEN_744; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1065 = io_deq_1_valid ? _GEN_1001 : _GEN_745; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1066 = io_deq_1_valid ? _GEN_1002 : _GEN_746; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1067 = io_deq_1_valid ? _GEN_1003 : _GEN_747; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1068 = io_deq_1_valid ? _GEN_1004 : _GEN_748; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1069 = io_deq_1_valid ? _GEN_1005 : _GEN_749; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1070 = io_deq_1_valid ? _GEN_1006 : _GEN_750; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1071 = io_deq_1_valid ? _GEN_1007 : _GEN_751; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1072 = io_deq_1_valid ? _GEN_1008 : _GEN_752; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1073 = io_deq_1_valid ? _GEN_1009 : _GEN_753; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1074 = io_deq_1_valid ? _GEN_1010 : _GEN_754; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1075 = io_deq_1_valid ? _GEN_1011 : _GEN_755; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1076 = io_deq_1_valid ? _GEN_1012 : _GEN_756; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1077 = io_deq_1_valid ? _GEN_1013 : _GEN_757; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1078 = io_deq_1_valid ? _GEN_1014 : _GEN_758; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1079 = io_deq_1_valid ? _GEN_1015 : _GEN_759; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1080 = io_deq_1_valid ? _GEN_1016 : _GEN_760; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1081 = io_deq_1_valid ? _GEN_1017 : _GEN_761; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1082 = io_deq_1_valid ? _GEN_1018 : _GEN_762; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1083 = io_deq_1_valid ? _GEN_1019 : _GEN_763; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1084 = io_deq_1_valid ? _GEN_1020 : _GEN_764; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1085 = io_deq_1_valid ? _GEN_1021 : _GEN_765; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1086 = io_deq_1_valid ? _GEN_1022 : _GEN_766; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1087 = io_deq_1_valid ? _GEN_1023 : _GEN_767; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire [5:0] roq_deq_addr_2 = io_deq_2_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 48:33]
  wire  _GEN_1153 = 6'h1 == roq_deq_addr_2 ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1154 = 6'h2 == roq_deq_addr_2 ? roq_free_2 : _GEN_1153; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1155 = 6'h3 == roq_deq_addr_2 ? roq_free_3 : _GEN_1154; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1156 = 6'h4 == roq_deq_addr_2 ? roq_free_4 : _GEN_1155; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1157 = 6'h5 == roq_deq_addr_2 ? roq_free_5 : _GEN_1156; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1158 = 6'h6 == roq_deq_addr_2 ? roq_free_6 : _GEN_1157; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1159 = 6'h7 == roq_deq_addr_2 ? roq_free_7 : _GEN_1158; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1160 = 6'h8 == roq_deq_addr_2 ? roq_free_8 : _GEN_1159; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1161 = 6'h9 == roq_deq_addr_2 ? roq_free_9 : _GEN_1160; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1162 = 6'ha == roq_deq_addr_2 ? roq_free_10 : _GEN_1161; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1163 = 6'hb == roq_deq_addr_2 ? roq_free_11 : _GEN_1162; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1164 = 6'hc == roq_deq_addr_2 ? roq_free_12 : _GEN_1163; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1165 = 6'hd == roq_deq_addr_2 ? roq_free_13 : _GEN_1164; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1166 = 6'he == roq_deq_addr_2 ? roq_free_14 : _GEN_1165; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1167 = 6'hf == roq_deq_addr_2 ? roq_free_15 : _GEN_1166; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1168 = 6'h10 == roq_deq_addr_2 ? roq_free_16 : _GEN_1167; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1169 = 6'h11 == roq_deq_addr_2 ? roq_free_17 : _GEN_1168; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1170 = 6'h12 == roq_deq_addr_2 ? roq_free_18 : _GEN_1169; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1171 = 6'h13 == roq_deq_addr_2 ? roq_free_19 : _GEN_1170; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1172 = 6'h14 == roq_deq_addr_2 ? roq_free_20 : _GEN_1171; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1173 = 6'h15 == roq_deq_addr_2 ? roq_free_21 : _GEN_1172; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1174 = 6'h16 == roq_deq_addr_2 ? roq_free_22 : _GEN_1173; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1175 = 6'h17 == roq_deq_addr_2 ? roq_free_23 : _GEN_1174; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1176 = 6'h18 == roq_deq_addr_2 ? roq_free_24 : _GEN_1175; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1177 = 6'h19 == roq_deq_addr_2 ? roq_free_25 : _GEN_1176; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1178 = 6'h1a == roq_deq_addr_2 ? roq_free_26 : _GEN_1177; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1179 = 6'h1b == roq_deq_addr_2 ? roq_free_27 : _GEN_1178; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1180 = 6'h1c == roq_deq_addr_2 ? roq_free_28 : _GEN_1179; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1181 = 6'h1d == roq_deq_addr_2 ? roq_free_29 : _GEN_1180; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1182 = 6'h1e == roq_deq_addr_2 ? roq_free_30 : _GEN_1181; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1183 = 6'h1f == roq_deq_addr_2 ? roq_free_31 : _GEN_1182; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1184 = 6'h20 == roq_deq_addr_2 ? roq_free_32 : _GEN_1183; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1185 = 6'h21 == roq_deq_addr_2 ? roq_free_33 : _GEN_1184; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1186 = 6'h22 == roq_deq_addr_2 ? roq_free_34 : _GEN_1185; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1187 = 6'h23 == roq_deq_addr_2 ? roq_free_35 : _GEN_1186; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1188 = 6'h24 == roq_deq_addr_2 ? roq_free_36 : _GEN_1187; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1189 = 6'h25 == roq_deq_addr_2 ? roq_free_37 : _GEN_1188; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1190 = 6'h26 == roq_deq_addr_2 ? roq_free_38 : _GEN_1189; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1191 = 6'h27 == roq_deq_addr_2 ? roq_free_39 : _GEN_1190; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1192 = 6'h28 == roq_deq_addr_2 ? roq_free_40 : _GEN_1191; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1193 = 6'h29 == roq_deq_addr_2 ? roq_free_41 : _GEN_1192; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1194 = 6'h2a == roq_deq_addr_2 ? roq_free_42 : _GEN_1193; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1195 = 6'h2b == roq_deq_addr_2 ? roq_free_43 : _GEN_1194; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1196 = 6'h2c == roq_deq_addr_2 ? roq_free_44 : _GEN_1195; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1197 = 6'h2d == roq_deq_addr_2 ? roq_free_45 : _GEN_1196; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1198 = 6'h2e == roq_deq_addr_2 ? roq_free_46 : _GEN_1197; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1199 = 6'h2f == roq_deq_addr_2 ? roq_free_47 : _GEN_1198; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1200 = 6'h30 == roq_deq_addr_2 ? roq_free_48 : _GEN_1199; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1201 = 6'h31 == roq_deq_addr_2 ? roq_free_49 : _GEN_1200; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1202 = 6'h32 == roq_deq_addr_2 ? roq_free_50 : _GEN_1201; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1203 = 6'h33 == roq_deq_addr_2 ? roq_free_51 : _GEN_1202; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1204 = 6'h34 == roq_deq_addr_2 ? roq_free_52 : _GEN_1203; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1205 = 6'h35 == roq_deq_addr_2 ? roq_free_53 : _GEN_1204; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1206 = 6'h36 == roq_deq_addr_2 ? roq_free_54 : _GEN_1205; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1207 = 6'h37 == roq_deq_addr_2 ? roq_free_55 : _GEN_1206; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1208 = 6'h38 == roq_deq_addr_2 ? roq_free_56 : _GEN_1207; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1209 = 6'h39 == roq_deq_addr_2 ? roq_free_57 : _GEN_1208; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1210 = 6'h3a == roq_deq_addr_2 ? roq_free_58 : _GEN_1209; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1211 = 6'h3b == roq_deq_addr_2 ? roq_free_59 : _GEN_1210; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1212 = 6'h3c == roq_deq_addr_2 ? roq_free_60 : _GEN_1211; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1213 = 6'h3d == roq_deq_addr_2 ? roq_free_61 : _GEN_1212; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1214 = 6'h3e == roq_deq_addr_2 ? roq_free_62 : _GEN_1213; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1215 = 6'h3f == roq_deq_addr_2 ? roq_free_63 : _GEN_1214; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire [11:0] _io_deq_2_matches_T_1 = {{6'd0}, io_deq_2_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:85]
  wire [5:0] _GEN_1217 = 6'h1 == roq_deq_addr_2 ? roq_tags_1 : roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1218 = 6'h2 == roq_deq_addr_2 ? roq_tags_2 : _GEN_1217; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1219 = 6'h3 == roq_deq_addr_2 ? roq_tags_3 : _GEN_1218; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1220 = 6'h4 == roq_deq_addr_2 ? roq_tags_4 : _GEN_1219; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1221 = 6'h5 == roq_deq_addr_2 ? roq_tags_5 : _GEN_1220; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1222 = 6'h6 == roq_deq_addr_2 ? roq_tags_6 : _GEN_1221; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1223 = 6'h7 == roq_deq_addr_2 ? roq_tags_7 : _GEN_1222; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1224 = 6'h8 == roq_deq_addr_2 ? roq_tags_8 : _GEN_1223; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1225 = 6'h9 == roq_deq_addr_2 ? roq_tags_9 : _GEN_1224; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1226 = 6'ha == roq_deq_addr_2 ? roq_tags_10 : _GEN_1225; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1227 = 6'hb == roq_deq_addr_2 ? roq_tags_11 : _GEN_1226; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1228 = 6'hc == roq_deq_addr_2 ? roq_tags_12 : _GEN_1227; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1229 = 6'hd == roq_deq_addr_2 ? roq_tags_13 : _GEN_1228; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1230 = 6'he == roq_deq_addr_2 ? roq_tags_14 : _GEN_1229; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1231 = 6'hf == roq_deq_addr_2 ? roq_tags_15 : _GEN_1230; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1232 = 6'h10 == roq_deq_addr_2 ? roq_tags_16 : _GEN_1231; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1233 = 6'h11 == roq_deq_addr_2 ? roq_tags_17 : _GEN_1232; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1234 = 6'h12 == roq_deq_addr_2 ? roq_tags_18 : _GEN_1233; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1235 = 6'h13 == roq_deq_addr_2 ? roq_tags_19 : _GEN_1234; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1236 = 6'h14 == roq_deq_addr_2 ? roq_tags_20 : _GEN_1235; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1237 = 6'h15 == roq_deq_addr_2 ? roq_tags_21 : _GEN_1236; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1238 = 6'h16 == roq_deq_addr_2 ? roq_tags_22 : _GEN_1237; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1239 = 6'h17 == roq_deq_addr_2 ? roq_tags_23 : _GEN_1238; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1240 = 6'h18 == roq_deq_addr_2 ? roq_tags_24 : _GEN_1239; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1241 = 6'h19 == roq_deq_addr_2 ? roq_tags_25 : _GEN_1240; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1242 = 6'h1a == roq_deq_addr_2 ? roq_tags_26 : _GEN_1241; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1243 = 6'h1b == roq_deq_addr_2 ? roq_tags_27 : _GEN_1242; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1244 = 6'h1c == roq_deq_addr_2 ? roq_tags_28 : _GEN_1243; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1245 = 6'h1d == roq_deq_addr_2 ? roq_tags_29 : _GEN_1244; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1246 = 6'h1e == roq_deq_addr_2 ? roq_tags_30 : _GEN_1245; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1247 = 6'h1f == roq_deq_addr_2 ? roq_tags_31 : _GEN_1246; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1248 = 6'h20 == roq_deq_addr_2 ? roq_tags_32 : _GEN_1247; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1249 = 6'h21 == roq_deq_addr_2 ? roq_tags_33 : _GEN_1248; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1250 = 6'h22 == roq_deq_addr_2 ? roq_tags_34 : _GEN_1249; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1251 = 6'h23 == roq_deq_addr_2 ? roq_tags_35 : _GEN_1250; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1252 = 6'h24 == roq_deq_addr_2 ? roq_tags_36 : _GEN_1251; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1253 = 6'h25 == roq_deq_addr_2 ? roq_tags_37 : _GEN_1252; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1254 = 6'h26 == roq_deq_addr_2 ? roq_tags_38 : _GEN_1253; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1255 = 6'h27 == roq_deq_addr_2 ? roq_tags_39 : _GEN_1254; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1256 = 6'h28 == roq_deq_addr_2 ? roq_tags_40 : _GEN_1255; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1257 = 6'h29 == roq_deq_addr_2 ? roq_tags_41 : _GEN_1256; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1258 = 6'h2a == roq_deq_addr_2 ? roq_tags_42 : _GEN_1257; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1259 = 6'h2b == roq_deq_addr_2 ? roq_tags_43 : _GEN_1258; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1260 = 6'h2c == roq_deq_addr_2 ? roq_tags_44 : _GEN_1259; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1261 = 6'h2d == roq_deq_addr_2 ? roq_tags_45 : _GEN_1260; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1262 = 6'h2e == roq_deq_addr_2 ? roq_tags_46 : _GEN_1261; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1263 = 6'h2f == roq_deq_addr_2 ? roq_tags_47 : _GEN_1262; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1264 = 6'h30 == roq_deq_addr_2 ? roq_tags_48 : _GEN_1263; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1265 = 6'h31 == roq_deq_addr_2 ? roq_tags_49 : _GEN_1264; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1266 = 6'h32 == roq_deq_addr_2 ? roq_tags_50 : _GEN_1265; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1267 = 6'h33 == roq_deq_addr_2 ? roq_tags_51 : _GEN_1266; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1268 = 6'h34 == roq_deq_addr_2 ? roq_tags_52 : _GEN_1267; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1269 = 6'h35 == roq_deq_addr_2 ? roq_tags_53 : _GEN_1268; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1270 = 6'h36 == roq_deq_addr_2 ? roq_tags_54 : _GEN_1269; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1271 = 6'h37 == roq_deq_addr_2 ? roq_tags_55 : _GEN_1270; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1272 = 6'h38 == roq_deq_addr_2 ? roq_tags_56 : _GEN_1271; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1273 = 6'h39 == roq_deq_addr_2 ? roq_tags_57 : _GEN_1272; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1274 = 6'h3a == roq_deq_addr_2 ? roq_tags_58 : _GEN_1273; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1275 = 6'h3b == roq_deq_addr_2 ? roq_tags_59 : _GEN_1274; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1276 = 6'h3c == roq_deq_addr_2 ? roq_tags_60 : _GEN_1275; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1277 = 6'h3d == roq_deq_addr_2 ? roq_tags_61 : _GEN_1276; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1278 = 6'h3e == roq_deq_addr_2 ? roq_tags_62 : _GEN_1277; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1279 = 6'h3f == roq_deq_addr_2 ? roq_tags_63 : _GEN_1278; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [11:0] _GEN_2182 = {{6'd0}, _GEN_1279}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:72]
  wire  _GEN_1280 = 6'h0 == roq_deq_addr_2 | _GEN_1024; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1281 = 6'h1 == roq_deq_addr_2 | _GEN_1025; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1282 = 6'h2 == roq_deq_addr_2 | _GEN_1026; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1283 = 6'h3 == roq_deq_addr_2 | _GEN_1027; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1284 = 6'h4 == roq_deq_addr_2 | _GEN_1028; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1285 = 6'h5 == roq_deq_addr_2 | _GEN_1029; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1286 = 6'h6 == roq_deq_addr_2 | _GEN_1030; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1287 = 6'h7 == roq_deq_addr_2 | _GEN_1031; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1288 = 6'h8 == roq_deq_addr_2 | _GEN_1032; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1289 = 6'h9 == roq_deq_addr_2 | _GEN_1033; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1290 = 6'ha == roq_deq_addr_2 | _GEN_1034; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1291 = 6'hb == roq_deq_addr_2 | _GEN_1035; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1292 = 6'hc == roq_deq_addr_2 | _GEN_1036; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1293 = 6'hd == roq_deq_addr_2 | _GEN_1037; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1294 = 6'he == roq_deq_addr_2 | _GEN_1038; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1295 = 6'hf == roq_deq_addr_2 | _GEN_1039; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1296 = 6'h10 == roq_deq_addr_2 | _GEN_1040; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1297 = 6'h11 == roq_deq_addr_2 | _GEN_1041; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1298 = 6'h12 == roq_deq_addr_2 | _GEN_1042; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1299 = 6'h13 == roq_deq_addr_2 | _GEN_1043; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1300 = 6'h14 == roq_deq_addr_2 | _GEN_1044; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1301 = 6'h15 == roq_deq_addr_2 | _GEN_1045; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1302 = 6'h16 == roq_deq_addr_2 | _GEN_1046; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1303 = 6'h17 == roq_deq_addr_2 | _GEN_1047; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1304 = 6'h18 == roq_deq_addr_2 | _GEN_1048; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1305 = 6'h19 == roq_deq_addr_2 | _GEN_1049; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1306 = 6'h1a == roq_deq_addr_2 | _GEN_1050; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1307 = 6'h1b == roq_deq_addr_2 | _GEN_1051; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1308 = 6'h1c == roq_deq_addr_2 | _GEN_1052; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1309 = 6'h1d == roq_deq_addr_2 | _GEN_1053; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1310 = 6'h1e == roq_deq_addr_2 | _GEN_1054; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1311 = 6'h1f == roq_deq_addr_2 | _GEN_1055; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1312 = 6'h20 == roq_deq_addr_2 | _GEN_1056; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1313 = 6'h21 == roq_deq_addr_2 | _GEN_1057; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1314 = 6'h22 == roq_deq_addr_2 | _GEN_1058; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1315 = 6'h23 == roq_deq_addr_2 | _GEN_1059; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1316 = 6'h24 == roq_deq_addr_2 | _GEN_1060; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1317 = 6'h25 == roq_deq_addr_2 | _GEN_1061; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1318 = 6'h26 == roq_deq_addr_2 | _GEN_1062; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1319 = 6'h27 == roq_deq_addr_2 | _GEN_1063; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1320 = 6'h28 == roq_deq_addr_2 | _GEN_1064; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1321 = 6'h29 == roq_deq_addr_2 | _GEN_1065; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1322 = 6'h2a == roq_deq_addr_2 | _GEN_1066; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1323 = 6'h2b == roq_deq_addr_2 | _GEN_1067; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1324 = 6'h2c == roq_deq_addr_2 | _GEN_1068; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1325 = 6'h2d == roq_deq_addr_2 | _GEN_1069; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1326 = 6'h2e == roq_deq_addr_2 | _GEN_1070; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1327 = 6'h2f == roq_deq_addr_2 | _GEN_1071; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1328 = 6'h30 == roq_deq_addr_2 | _GEN_1072; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1329 = 6'h31 == roq_deq_addr_2 | _GEN_1073; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1330 = 6'h32 == roq_deq_addr_2 | _GEN_1074; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1331 = 6'h33 == roq_deq_addr_2 | _GEN_1075; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1332 = 6'h34 == roq_deq_addr_2 | _GEN_1076; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1333 = 6'h35 == roq_deq_addr_2 | _GEN_1077; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1334 = 6'h36 == roq_deq_addr_2 | _GEN_1078; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1335 = 6'h37 == roq_deq_addr_2 | _GEN_1079; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1336 = 6'h38 == roq_deq_addr_2 | _GEN_1080; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1337 = 6'h39 == roq_deq_addr_2 | _GEN_1081; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1338 = 6'h3a == roq_deq_addr_2 | _GEN_1082; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1339 = 6'h3b == roq_deq_addr_2 | _GEN_1083; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1340 = 6'h3c == roq_deq_addr_2 | _GEN_1084; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1341 = 6'h3d == roq_deq_addr_2 | _GEN_1085; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1342 = 6'h3e == roq_deq_addr_2 | _GEN_1086; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1343 = 6'h3f == roq_deq_addr_2 | _GEN_1087; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1344 = io_deq_2_valid ? _GEN_1280 : _GEN_1024; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1345 = io_deq_2_valid ? _GEN_1281 : _GEN_1025; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1346 = io_deq_2_valid ? _GEN_1282 : _GEN_1026; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1347 = io_deq_2_valid ? _GEN_1283 : _GEN_1027; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1348 = io_deq_2_valid ? _GEN_1284 : _GEN_1028; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1349 = io_deq_2_valid ? _GEN_1285 : _GEN_1029; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1350 = io_deq_2_valid ? _GEN_1286 : _GEN_1030; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1351 = io_deq_2_valid ? _GEN_1287 : _GEN_1031; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1352 = io_deq_2_valid ? _GEN_1288 : _GEN_1032; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1353 = io_deq_2_valid ? _GEN_1289 : _GEN_1033; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1354 = io_deq_2_valid ? _GEN_1290 : _GEN_1034; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1355 = io_deq_2_valid ? _GEN_1291 : _GEN_1035; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1356 = io_deq_2_valid ? _GEN_1292 : _GEN_1036; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1357 = io_deq_2_valid ? _GEN_1293 : _GEN_1037; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1358 = io_deq_2_valid ? _GEN_1294 : _GEN_1038; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1359 = io_deq_2_valid ? _GEN_1295 : _GEN_1039; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1360 = io_deq_2_valid ? _GEN_1296 : _GEN_1040; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1361 = io_deq_2_valid ? _GEN_1297 : _GEN_1041; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1362 = io_deq_2_valid ? _GEN_1298 : _GEN_1042; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1363 = io_deq_2_valid ? _GEN_1299 : _GEN_1043; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1364 = io_deq_2_valid ? _GEN_1300 : _GEN_1044; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1365 = io_deq_2_valid ? _GEN_1301 : _GEN_1045; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1366 = io_deq_2_valid ? _GEN_1302 : _GEN_1046; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1367 = io_deq_2_valid ? _GEN_1303 : _GEN_1047; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1368 = io_deq_2_valid ? _GEN_1304 : _GEN_1048; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1369 = io_deq_2_valid ? _GEN_1305 : _GEN_1049; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1370 = io_deq_2_valid ? _GEN_1306 : _GEN_1050; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1371 = io_deq_2_valid ? _GEN_1307 : _GEN_1051; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1372 = io_deq_2_valid ? _GEN_1308 : _GEN_1052; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1373 = io_deq_2_valid ? _GEN_1309 : _GEN_1053; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1374 = io_deq_2_valid ? _GEN_1310 : _GEN_1054; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1375 = io_deq_2_valid ? _GEN_1311 : _GEN_1055; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1376 = io_deq_2_valid ? _GEN_1312 : _GEN_1056; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1377 = io_deq_2_valid ? _GEN_1313 : _GEN_1057; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1378 = io_deq_2_valid ? _GEN_1314 : _GEN_1058; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1379 = io_deq_2_valid ? _GEN_1315 : _GEN_1059; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1380 = io_deq_2_valid ? _GEN_1316 : _GEN_1060; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1381 = io_deq_2_valid ? _GEN_1317 : _GEN_1061; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1382 = io_deq_2_valid ? _GEN_1318 : _GEN_1062; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1383 = io_deq_2_valid ? _GEN_1319 : _GEN_1063; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1384 = io_deq_2_valid ? _GEN_1320 : _GEN_1064; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1385 = io_deq_2_valid ? _GEN_1321 : _GEN_1065; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1386 = io_deq_2_valid ? _GEN_1322 : _GEN_1066; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1387 = io_deq_2_valid ? _GEN_1323 : _GEN_1067; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1388 = io_deq_2_valid ? _GEN_1324 : _GEN_1068; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1389 = io_deq_2_valid ? _GEN_1325 : _GEN_1069; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1390 = io_deq_2_valid ? _GEN_1326 : _GEN_1070; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1391 = io_deq_2_valid ? _GEN_1327 : _GEN_1071; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1392 = io_deq_2_valid ? _GEN_1328 : _GEN_1072; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1393 = io_deq_2_valid ? _GEN_1329 : _GEN_1073; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1394 = io_deq_2_valid ? _GEN_1330 : _GEN_1074; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1395 = io_deq_2_valid ? _GEN_1331 : _GEN_1075; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1396 = io_deq_2_valid ? _GEN_1332 : _GEN_1076; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1397 = io_deq_2_valid ? _GEN_1333 : _GEN_1077; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1398 = io_deq_2_valid ? _GEN_1334 : _GEN_1078; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1399 = io_deq_2_valid ? _GEN_1335 : _GEN_1079; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1400 = io_deq_2_valid ? _GEN_1336 : _GEN_1080; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1401 = io_deq_2_valid ? _GEN_1337 : _GEN_1081; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1402 = io_deq_2_valid ? _GEN_1338 : _GEN_1082; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1403 = io_deq_2_valid ? _GEN_1339 : _GEN_1083; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1404 = io_deq_2_valid ? _GEN_1340 : _GEN_1084; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1405 = io_deq_2_valid ? _GEN_1341 : _GEN_1085; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1406 = io_deq_2_valid ? _GEN_1342 : _GEN_1086; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1407 = io_deq_2_valid ? _GEN_1343 : _GEN_1087; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire [5:0] roq_deq_addr_3 = io_deq_3_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 48:33]
  wire  _GEN_1473 = 6'h1 == roq_deq_addr_3 ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1474 = 6'h2 == roq_deq_addr_3 ? roq_free_2 : _GEN_1473; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1475 = 6'h3 == roq_deq_addr_3 ? roq_free_3 : _GEN_1474; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1476 = 6'h4 == roq_deq_addr_3 ? roq_free_4 : _GEN_1475; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1477 = 6'h5 == roq_deq_addr_3 ? roq_free_5 : _GEN_1476; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1478 = 6'h6 == roq_deq_addr_3 ? roq_free_6 : _GEN_1477; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1479 = 6'h7 == roq_deq_addr_3 ? roq_free_7 : _GEN_1478; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1480 = 6'h8 == roq_deq_addr_3 ? roq_free_8 : _GEN_1479; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1481 = 6'h9 == roq_deq_addr_3 ? roq_free_9 : _GEN_1480; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1482 = 6'ha == roq_deq_addr_3 ? roq_free_10 : _GEN_1481; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1483 = 6'hb == roq_deq_addr_3 ? roq_free_11 : _GEN_1482; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1484 = 6'hc == roq_deq_addr_3 ? roq_free_12 : _GEN_1483; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1485 = 6'hd == roq_deq_addr_3 ? roq_free_13 : _GEN_1484; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1486 = 6'he == roq_deq_addr_3 ? roq_free_14 : _GEN_1485; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1487 = 6'hf == roq_deq_addr_3 ? roq_free_15 : _GEN_1486; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1488 = 6'h10 == roq_deq_addr_3 ? roq_free_16 : _GEN_1487; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1489 = 6'h11 == roq_deq_addr_3 ? roq_free_17 : _GEN_1488; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1490 = 6'h12 == roq_deq_addr_3 ? roq_free_18 : _GEN_1489; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1491 = 6'h13 == roq_deq_addr_3 ? roq_free_19 : _GEN_1490; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1492 = 6'h14 == roq_deq_addr_3 ? roq_free_20 : _GEN_1491; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1493 = 6'h15 == roq_deq_addr_3 ? roq_free_21 : _GEN_1492; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1494 = 6'h16 == roq_deq_addr_3 ? roq_free_22 : _GEN_1493; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1495 = 6'h17 == roq_deq_addr_3 ? roq_free_23 : _GEN_1494; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1496 = 6'h18 == roq_deq_addr_3 ? roq_free_24 : _GEN_1495; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1497 = 6'h19 == roq_deq_addr_3 ? roq_free_25 : _GEN_1496; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1498 = 6'h1a == roq_deq_addr_3 ? roq_free_26 : _GEN_1497; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1499 = 6'h1b == roq_deq_addr_3 ? roq_free_27 : _GEN_1498; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1500 = 6'h1c == roq_deq_addr_3 ? roq_free_28 : _GEN_1499; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1501 = 6'h1d == roq_deq_addr_3 ? roq_free_29 : _GEN_1500; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1502 = 6'h1e == roq_deq_addr_3 ? roq_free_30 : _GEN_1501; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1503 = 6'h1f == roq_deq_addr_3 ? roq_free_31 : _GEN_1502; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1504 = 6'h20 == roq_deq_addr_3 ? roq_free_32 : _GEN_1503; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1505 = 6'h21 == roq_deq_addr_3 ? roq_free_33 : _GEN_1504; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1506 = 6'h22 == roq_deq_addr_3 ? roq_free_34 : _GEN_1505; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1507 = 6'h23 == roq_deq_addr_3 ? roq_free_35 : _GEN_1506; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1508 = 6'h24 == roq_deq_addr_3 ? roq_free_36 : _GEN_1507; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1509 = 6'h25 == roq_deq_addr_3 ? roq_free_37 : _GEN_1508; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1510 = 6'h26 == roq_deq_addr_3 ? roq_free_38 : _GEN_1509; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1511 = 6'h27 == roq_deq_addr_3 ? roq_free_39 : _GEN_1510; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1512 = 6'h28 == roq_deq_addr_3 ? roq_free_40 : _GEN_1511; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1513 = 6'h29 == roq_deq_addr_3 ? roq_free_41 : _GEN_1512; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1514 = 6'h2a == roq_deq_addr_3 ? roq_free_42 : _GEN_1513; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1515 = 6'h2b == roq_deq_addr_3 ? roq_free_43 : _GEN_1514; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1516 = 6'h2c == roq_deq_addr_3 ? roq_free_44 : _GEN_1515; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1517 = 6'h2d == roq_deq_addr_3 ? roq_free_45 : _GEN_1516; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1518 = 6'h2e == roq_deq_addr_3 ? roq_free_46 : _GEN_1517; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1519 = 6'h2f == roq_deq_addr_3 ? roq_free_47 : _GEN_1518; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1520 = 6'h30 == roq_deq_addr_3 ? roq_free_48 : _GEN_1519; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1521 = 6'h31 == roq_deq_addr_3 ? roq_free_49 : _GEN_1520; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1522 = 6'h32 == roq_deq_addr_3 ? roq_free_50 : _GEN_1521; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1523 = 6'h33 == roq_deq_addr_3 ? roq_free_51 : _GEN_1522; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1524 = 6'h34 == roq_deq_addr_3 ? roq_free_52 : _GEN_1523; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1525 = 6'h35 == roq_deq_addr_3 ? roq_free_53 : _GEN_1524; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1526 = 6'h36 == roq_deq_addr_3 ? roq_free_54 : _GEN_1525; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1527 = 6'h37 == roq_deq_addr_3 ? roq_free_55 : _GEN_1526; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1528 = 6'h38 == roq_deq_addr_3 ? roq_free_56 : _GEN_1527; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1529 = 6'h39 == roq_deq_addr_3 ? roq_free_57 : _GEN_1528; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1530 = 6'h3a == roq_deq_addr_3 ? roq_free_58 : _GEN_1529; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1531 = 6'h3b == roq_deq_addr_3 ? roq_free_59 : _GEN_1530; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1532 = 6'h3c == roq_deq_addr_3 ? roq_free_60 : _GEN_1531; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1533 = 6'h3d == roq_deq_addr_3 ? roq_free_61 : _GEN_1532; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1534 = 6'h3e == roq_deq_addr_3 ? roq_free_62 : _GEN_1533; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1535 = 6'h3f == roq_deq_addr_3 ? roq_free_63 : _GEN_1534; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire [11:0] _io_deq_3_matches_T_1 = {{6'd0}, io_deq_3_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:85]
  wire [5:0] _GEN_1537 = 6'h1 == roq_deq_addr_3 ? roq_tags_1 : roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1538 = 6'h2 == roq_deq_addr_3 ? roq_tags_2 : _GEN_1537; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1539 = 6'h3 == roq_deq_addr_3 ? roq_tags_3 : _GEN_1538; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1540 = 6'h4 == roq_deq_addr_3 ? roq_tags_4 : _GEN_1539; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1541 = 6'h5 == roq_deq_addr_3 ? roq_tags_5 : _GEN_1540; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1542 = 6'h6 == roq_deq_addr_3 ? roq_tags_6 : _GEN_1541; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1543 = 6'h7 == roq_deq_addr_3 ? roq_tags_7 : _GEN_1542; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1544 = 6'h8 == roq_deq_addr_3 ? roq_tags_8 : _GEN_1543; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1545 = 6'h9 == roq_deq_addr_3 ? roq_tags_9 : _GEN_1544; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1546 = 6'ha == roq_deq_addr_3 ? roq_tags_10 : _GEN_1545; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1547 = 6'hb == roq_deq_addr_3 ? roq_tags_11 : _GEN_1546; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1548 = 6'hc == roq_deq_addr_3 ? roq_tags_12 : _GEN_1547; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1549 = 6'hd == roq_deq_addr_3 ? roq_tags_13 : _GEN_1548; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1550 = 6'he == roq_deq_addr_3 ? roq_tags_14 : _GEN_1549; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1551 = 6'hf == roq_deq_addr_3 ? roq_tags_15 : _GEN_1550; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1552 = 6'h10 == roq_deq_addr_3 ? roq_tags_16 : _GEN_1551; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1553 = 6'h11 == roq_deq_addr_3 ? roq_tags_17 : _GEN_1552; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1554 = 6'h12 == roq_deq_addr_3 ? roq_tags_18 : _GEN_1553; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1555 = 6'h13 == roq_deq_addr_3 ? roq_tags_19 : _GEN_1554; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1556 = 6'h14 == roq_deq_addr_3 ? roq_tags_20 : _GEN_1555; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1557 = 6'h15 == roq_deq_addr_3 ? roq_tags_21 : _GEN_1556; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1558 = 6'h16 == roq_deq_addr_3 ? roq_tags_22 : _GEN_1557; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1559 = 6'h17 == roq_deq_addr_3 ? roq_tags_23 : _GEN_1558; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1560 = 6'h18 == roq_deq_addr_3 ? roq_tags_24 : _GEN_1559; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1561 = 6'h19 == roq_deq_addr_3 ? roq_tags_25 : _GEN_1560; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1562 = 6'h1a == roq_deq_addr_3 ? roq_tags_26 : _GEN_1561; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1563 = 6'h1b == roq_deq_addr_3 ? roq_tags_27 : _GEN_1562; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1564 = 6'h1c == roq_deq_addr_3 ? roq_tags_28 : _GEN_1563; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1565 = 6'h1d == roq_deq_addr_3 ? roq_tags_29 : _GEN_1564; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1566 = 6'h1e == roq_deq_addr_3 ? roq_tags_30 : _GEN_1565; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1567 = 6'h1f == roq_deq_addr_3 ? roq_tags_31 : _GEN_1566; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1568 = 6'h20 == roq_deq_addr_3 ? roq_tags_32 : _GEN_1567; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1569 = 6'h21 == roq_deq_addr_3 ? roq_tags_33 : _GEN_1568; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1570 = 6'h22 == roq_deq_addr_3 ? roq_tags_34 : _GEN_1569; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1571 = 6'h23 == roq_deq_addr_3 ? roq_tags_35 : _GEN_1570; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1572 = 6'h24 == roq_deq_addr_3 ? roq_tags_36 : _GEN_1571; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1573 = 6'h25 == roq_deq_addr_3 ? roq_tags_37 : _GEN_1572; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1574 = 6'h26 == roq_deq_addr_3 ? roq_tags_38 : _GEN_1573; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1575 = 6'h27 == roq_deq_addr_3 ? roq_tags_39 : _GEN_1574; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1576 = 6'h28 == roq_deq_addr_3 ? roq_tags_40 : _GEN_1575; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1577 = 6'h29 == roq_deq_addr_3 ? roq_tags_41 : _GEN_1576; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1578 = 6'h2a == roq_deq_addr_3 ? roq_tags_42 : _GEN_1577; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1579 = 6'h2b == roq_deq_addr_3 ? roq_tags_43 : _GEN_1578; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1580 = 6'h2c == roq_deq_addr_3 ? roq_tags_44 : _GEN_1579; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1581 = 6'h2d == roq_deq_addr_3 ? roq_tags_45 : _GEN_1580; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1582 = 6'h2e == roq_deq_addr_3 ? roq_tags_46 : _GEN_1581; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1583 = 6'h2f == roq_deq_addr_3 ? roq_tags_47 : _GEN_1582; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1584 = 6'h30 == roq_deq_addr_3 ? roq_tags_48 : _GEN_1583; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1585 = 6'h31 == roq_deq_addr_3 ? roq_tags_49 : _GEN_1584; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1586 = 6'h32 == roq_deq_addr_3 ? roq_tags_50 : _GEN_1585; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1587 = 6'h33 == roq_deq_addr_3 ? roq_tags_51 : _GEN_1586; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1588 = 6'h34 == roq_deq_addr_3 ? roq_tags_52 : _GEN_1587; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1589 = 6'h35 == roq_deq_addr_3 ? roq_tags_53 : _GEN_1588; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1590 = 6'h36 == roq_deq_addr_3 ? roq_tags_54 : _GEN_1589; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1591 = 6'h37 == roq_deq_addr_3 ? roq_tags_55 : _GEN_1590; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1592 = 6'h38 == roq_deq_addr_3 ? roq_tags_56 : _GEN_1591; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1593 = 6'h39 == roq_deq_addr_3 ? roq_tags_57 : _GEN_1592; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1594 = 6'h3a == roq_deq_addr_3 ? roq_tags_58 : _GEN_1593; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1595 = 6'h3b == roq_deq_addr_3 ? roq_tags_59 : _GEN_1594; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1596 = 6'h3c == roq_deq_addr_3 ? roq_tags_60 : _GEN_1595; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1597 = 6'h3d == roq_deq_addr_3 ? roq_tags_61 : _GEN_1596; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1598 = 6'h3e == roq_deq_addr_3 ? roq_tags_62 : _GEN_1597; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1599 = 6'h3f == roq_deq_addr_3 ? roq_tags_63 : _GEN_1598; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [11:0] _GEN_2248 = {{6'd0}, _GEN_1599}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:72]
  wire  _GEN_1600 = 6'h0 == roq_deq_addr_3 | _GEN_1344; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1601 = 6'h1 == roq_deq_addr_3 | _GEN_1345; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1602 = 6'h2 == roq_deq_addr_3 | _GEN_1346; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1603 = 6'h3 == roq_deq_addr_3 | _GEN_1347; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1604 = 6'h4 == roq_deq_addr_3 | _GEN_1348; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1605 = 6'h5 == roq_deq_addr_3 | _GEN_1349; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1606 = 6'h6 == roq_deq_addr_3 | _GEN_1350; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1607 = 6'h7 == roq_deq_addr_3 | _GEN_1351; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1608 = 6'h8 == roq_deq_addr_3 | _GEN_1352; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1609 = 6'h9 == roq_deq_addr_3 | _GEN_1353; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1610 = 6'ha == roq_deq_addr_3 | _GEN_1354; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1611 = 6'hb == roq_deq_addr_3 | _GEN_1355; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1612 = 6'hc == roq_deq_addr_3 | _GEN_1356; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1613 = 6'hd == roq_deq_addr_3 | _GEN_1357; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1614 = 6'he == roq_deq_addr_3 | _GEN_1358; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1615 = 6'hf == roq_deq_addr_3 | _GEN_1359; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1616 = 6'h10 == roq_deq_addr_3 | _GEN_1360; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1617 = 6'h11 == roq_deq_addr_3 | _GEN_1361; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1618 = 6'h12 == roq_deq_addr_3 | _GEN_1362; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1619 = 6'h13 == roq_deq_addr_3 | _GEN_1363; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1620 = 6'h14 == roq_deq_addr_3 | _GEN_1364; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1621 = 6'h15 == roq_deq_addr_3 | _GEN_1365; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1622 = 6'h16 == roq_deq_addr_3 | _GEN_1366; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1623 = 6'h17 == roq_deq_addr_3 | _GEN_1367; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1624 = 6'h18 == roq_deq_addr_3 | _GEN_1368; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1625 = 6'h19 == roq_deq_addr_3 | _GEN_1369; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1626 = 6'h1a == roq_deq_addr_3 | _GEN_1370; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1627 = 6'h1b == roq_deq_addr_3 | _GEN_1371; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1628 = 6'h1c == roq_deq_addr_3 | _GEN_1372; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1629 = 6'h1d == roq_deq_addr_3 | _GEN_1373; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1630 = 6'h1e == roq_deq_addr_3 | _GEN_1374; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1631 = 6'h1f == roq_deq_addr_3 | _GEN_1375; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1632 = 6'h20 == roq_deq_addr_3 | _GEN_1376; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1633 = 6'h21 == roq_deq_addr_3 | _GEN_1377; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1634 = 6'h22 == roq_deq_addr_3 | _GEN_1378; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1635 = 6'h23 == roq_deq_addr_3 | _GEN_1379; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1636 = 6'h24 == roq_deq_addr_3 | _GEN_1380; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1637 = 6'h25 == roq_deq_addr_3 | _GEN_1381; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1638 = 6'h26 == roq_deq_addr_3 | _GEN_1382; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1639 = 6'h27 == roq_deq_addr_3 | _GEN_1383; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1640 = 6'h28 == roq_deq_addr_3 | _GEN_1384; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1641 = 6'h29 == roq_deq_addr_3 | _GEN_1385; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1642 = 6'h2a == roq_deq_addr_3 | _GEN_1386; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1643 = 6'h2b == roq_deq_addr_3 | _GEN_1387; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1644 = 6'h2c == roq_deq_addr_3 | _GEN_1388; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1645 = 6'h2d == roq_deq_addr_3 | _GEN_1389; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1646 = 6'h2e == roq_deq_addr_3 | _GEN_1390; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1647 = 6'h2f == roq_deq_addr_3 | _GEN_1391; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1648 = 6'h30 == roq_deq_addr_3 | _GEN_1392; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1649 = 6'h31 == roq_deq_addr_3 | _GEN_1393; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1650 = 6'h32 == roq_deq_addr_3 | _GEN_1394; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1651 = 6'h33 == roq_deq_addr_3 | _GEN_1395; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1652 = 6'h34 == roq_deq_addr_3 | _GEN_1396; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1653 = 6'h35 == roq_deq_addr_3 | _GEN_1397; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1654 = 6'h36 == roq_deq_addr_3 | _GEN_1398; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1655 = 6'h37 == roq_deq_addr_3 | _GEN_1399; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1656 = 6'h38 == roq_deq_addr_3 | _GEN_1400; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1657 = 6'h39 == roq_deq_addr_3 | _GEN_1401; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1658 = 6'h3a == roq_deq_addr_3 | _GEN_1402; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1659 = 6'h3b == roq_deq_addr_3 | _GEN_1403; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1660 = 6'h3c == roq_deq_addr_3 | _GEN_1404; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1661 = 6'h3d == roq_deq_addr_3 | _GEN_1405; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1662 = 6'h3e == roq_deq_addr_3 | _GEN_1406; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1663 = 6'h3f == roq_deq_addr_3 | _GEN_1407; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1664 = io_deq_3_valid ? _GEN_1600 : _GEN_1344; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1665 = io_deq_3_valid ? _GEN_1601 : _GEN_1345; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1666 = io_deq_3_valid ? _GEN_1602 : _GEN_1346; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1667 = io_deq_3_valid ? _GEN_1603 : _GEN_1347; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1668 = io_deq_3_valid ? _GEN_1604 : _GEN_1348; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1669 = io_deq_3_valid ? _GEN_1605 : _GEN_1349; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1670 = io_deq_3_valid ? _GEN_1606 : _GEN_1350; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1671 = io_deq_3_valid ? _GEN_1607 : _GEN_1351; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1672 = io_deq_3_valid ? _GEN_1608 : _GEN_1352; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1673 = io_deq_3_valid ? _GEN_1609 : _GEN_1353; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1674 = io_deq_3_valid ? _GEN_1610 : _GEN_1354; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1675 = io_deq_3_valid ? _GEN_1611 : _GEN_1355; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1676 = io_deq_3_valid ? _GEN_1612 : _GEN_1356; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1677 = io_deq_3_valid ? _GEN_1613 : _GEN_1357; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1678 = io_deq_3_valid ? _GEN_1614 : _GEN_1358; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1679 = io_deq_3_valid ? _GEN_1615 : _GEN_1359; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1680 = io_deq_3_valid ? _GEN_1616 : _GEN_1360; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1681 = io_deq_3_valid ? _GEN_1617 : _GEN_1361; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1682 = io_deq_3_valid ? _GEN_1618 : _GEN_1362; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1683 = io_deq_3_valid ? _GEN_1619 : _GEN_1363; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1684 = io_deq_3_valid ? _GEN_1620 : _GEN_1364; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1685 = io_deq_3_valid ? _GEN_1621 : _GEN_1365; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1686 = io_deq_3_valid ? _GEN_1622 : _GEN_1366; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1687 = io_deq_3_valid ? _GEN_1623 : _GEN_1367; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1688 = io_deq_3_valid ? _GEN_1624 : _GEN_1368; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1689 = io_deq_3_valid ? _GEN_1625 : _GEN_1369; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1690 = io_deq_3_valid ? _GEN_1626 : _GEN_1370; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1691 = io_deq_3_valid ? _GEN_1627 : _GEN_1371; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1692 = io_deq_3_valid ? _GEN_1628 : _GEN_1372; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1693 = io_deq_3_valid ? _GEN_1629 : _GEN_1373; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1694 = io_deq_3_valid ? _GEN_1630 : _GEN_1374; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1695 = io_deq_3_valid ? _GEN_1631 : _GEN_1375; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1696 = io_deq_3_valid ? _GEN_1632 : _GEN_1376; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1697 = io_deq_3_valid ? _GEN_1633 : _GEN_1377; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1698 = io_deq_3_valid ? _GEN_1634 : _GEN_1378; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1699 = io_deq_3_valid ? _GEN_1635 : _GEN_1379; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1700 = io_deq_3_valid ? _GEN_1636 : _GEN_1380; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1701 = io_deq_3_valid ? _GEN_1637 : _GEN_1381; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1702 = io_deq_3_valid ? _GEN_1638 : _GEN_1382; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1703 = io_deq_3_valid ? _GEN_1639 : _GEN_1383; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1704 = io_deq_3_valid ? _GEN_1640 : _GEN_1384; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1705 = io_deq_3_valid ? _GEN_1641 : _GEN_1385; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1706 = io_deq_3_valid ? _GEN_1642 : _GEN_1386; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1707 = io_deq_3_valid ? _GEN_1643 : _GEN_1387; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1708 = io_deq_3_valid ? _GEN_1644 : _GEN_1388; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1709 = io_deq_3_valid ? _GEN_1645 : _GEN_1389; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1710 = io_deq_3_valid ? _GEN_1646 : _GEN_1390; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1711 = io_deq_3_valid ? _GEN_1647 : _GEN_1391; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1712 = io_deq_3_valid ? _GEN_1648 : _GEN_1392; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1713 = io_deq_3_valid ? _GEN_1649 : _GEN_1393; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1714 = io_deq_3_valid ? _GEN_1650 : _GEN_1394; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1715 = io_deq_3_valid ? _GEN_1651 : _GEN_1395; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1716 = io_deq_3_valid ? _GEN_1652 : _GEN_1396; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1717 = io_deq_3_valid ? _GEN_1653 : _GEN_1397; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1718 = io_deq_3_valid ? _GEN_1654 : _GEN_1398; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1719 = io_deq_3_valid ? _GEN_1655 : _GEN_1399; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1720 = io_deq_3_valid ? _GEN_1656 : _GEN_1400; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1721 = io_deq_3_valid ? _GEN_1657 : _GEN_1401; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1722 = io_deq_3_valid ? _GEN_1658 : _GEN_1402; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1723 = io_deq_3_valid ? _GEN_1659 : _GEN_1403; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1724 = io_deq_3_valid ? _GEN_1660 : _GEN_1404; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1725 = io_deq_3_valid ? _GEN_1661 : _GEN_1405; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1726 = io_deq_3_valid ? _GEN_1662 : _GEN_1406; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1727 = io_deq_3_valid ? _GEN_1663 : _GEN_1407; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire [5:0] roq_deq_addr_4 = io_deq_4_tag[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 48:33]
  wire  _GEN_1793 = 6'h1 == roq_deq_addr_4 ? roq_free_1 : roq_free_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1794 = 6'h2 == roq_deq_addr_4 ? roq_free_2 : _GEN_1793; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1795 = 6'h3 == roq_deq_addr_4 ? roq_free_3 : _GEN_1794; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1796 = 6'h4 == roq_deq_addr_4 ? roq_free_4 : _GEN_1795; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1797 = 6'h5 == roq_deq_addr_4 ? roq_free_5 : _GEN_1796; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1798 = 6'h6 == roq_deq_addr_4 ? roq_free_6 : _GEN_1797; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1799 = 6'h7 == roq_deq_addr_4 ? roq_free_7 : _GEN_1798; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1800 = 6'h8 == roq_deq_addr_4 ? roq_free_8 : _GEN_1799; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1801 = 6'h9 == roq_deq_addr_4 ? roq_free_9 : _GEN_1800; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1802 = 6'ha == roq_deq_addr_4 ? roq_free_10 : _GEN_1801; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1803 = 6'hb == roq_deq_addr_4 ? roq_free_11 : _GEN_1802; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1804 = 6'hc == roq_deq_addr_4 ? roq_free_12 : _GEN_1803; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1805 = 6'hd == roq_deq_addr_4 ? roq_free_13 : _GEN_1804; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1806 = 6'he == roq_deq_addr_4 ? roq_free_14 : _GEN_1805; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1807 = 6'hf == roq_deq_addr_4 ? roq_free_15 : _GEN_1806; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1808 = 6'h10 == roq_deq_addr_4 ? roq_free_16 : _GEN_1807; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1809 = 6'h11 == roq_deq_addr_4 ? roq_free_17 : _GEN_1808; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1810 = 6'h12 == roq_deq_addr_4 ? roq_free_18 : _GEN_1809; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1811 = 6'h13 == roq_deq_addr_4 ? roq_free_19 : _GEN_1810; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1812 = 6'h14 == roq_deq_addr_4 ? roq_free_20 : _GEN_1811; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1813 = 6'h15 == roq_deq_addr_4 ? roq_free_21 : _GEN_1812; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1814 = 6'h16 == roq_deq_addr_4 ? roq_free_22 : _GEN_1813; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1815 = 6'h17 == roq_deq_addr_4 ? roq_free_23 : _GEN_1814; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1816 = 6'h18 == roq_deq_addr_4 ? roq_free_24 : _GEN_1815; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1817 = 6'h19 == roq_deq_addr_4 ? roq_free_25 : _GEN_1816; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1818 = 6'h1a == roq_deq_addr_4 ? roq_free_26 : _GEN_1817; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1819 = 6'h1b == roq_deq_addr_4 ? roq_free_27 : _GEN_1818; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1820 = 6'h1c == roq_deq_addr_4 ? roq_free_28 : _GEN_1819; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1821 = 6'h1d == roq_deq_addr_4 ? roq_free_29 : _GEN_1820; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1822 = 6'h1e == roq_deq_addr_4 ? roq_free_30 : _GEN_1821; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1823 = 6'h1f == roq_deq_addr_4 ? roq_free_31 : _GEN_1822; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1824 = 6'h20 == roq_deq_addr_4 ? roq_free_32 : _GEN_1823; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1825 = 6'h21 == roq_deq_addr_4 ? roq_free_33 : _GEN_1824; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1826 = 6'h22 == roq_deq_addr_4 ? roq_free_34 : _GEN_1825; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1827 = 6'h23 == roq_deq_addr_4 ? roq_free_35 : _GEN_1826; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1828 = 6'h24 == roq_deq_addr_4 ? roq_free_36 : _GEN_1827; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1829 = 6'h25 == roq_deq_addr_4 ? roq_free_37 : _GEN_1828; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1830 = 6'h26 == roq_deq_addr_4 ? roq_free_38 : _GEN_1829; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1831 = 6'h27 == roq_deq_addr_4 ? roq_free_39 : _GEN_1830; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1832 = 6'h28 == roq_deq_addr_4 ? roq_free_40 : _GEN_1831; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1833 = 6'h29 == roq_deq_addr_4 ? roq_free_41 : _GEN_1832; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1834 = 6'h2a == roq_deq_addr_4 ? roq_free_42 : _GEN_1833; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1835 = 6'h2b == roq_deq_addr_4 ? roq_free_43 : _GEN_1834; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1836 = 6'h2c == roq_deq_addr_4 ? roq_free_44 : _GEN_1835; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1837 = 6'h2d == roq_deq_addr_4 ? roq_free_45 : _GEN_1836; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1838 = 6'h2e == roq_deq_addr_4 ? roq_free_46 : _GEN_1837; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1839 = 6'h2f == roq_deq_addr_4 ? roq_free_47 : _GEN_1838; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1840 = 6'h30 == roq_deq_addr_4 ? roq_free_48 : _GEN_1839; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1841 = 6'h31 == roq_deq_addr_4 ? roq_free_49 : _GEN_1840; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1842 = 6'h32 == roq_deq_addr_4 ? roq_free_50 : _GEN_1841; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1843 = 6'h33 == roq_deq_addr_4 ? roq_free_51 : _GEN_1842; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1844 = 6'h34 == roq_deq_addr_4 ? roq_free_52 : _GEN_1843; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1845 = 6'h35 == roq_deq_addr_4 ? roq_free_53 : _GEN_1844; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1846 = 6'h36 == roq_deq_addr_4 ? roq_free_54 : _GEN_1845; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1847 = 6'h37 == roq_deq_addr_4 ? roq_free_55 : _GEN_1846; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1848 = 6'h38 == roq_deq_addr_4 ? roq_free_56 : _GEN_1847; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1849 = 6'h39 == roq_deq_addr_4 ? roq_free_57 : _GEN_1848; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1850 = 6'h3a == roq_deq_addr_4 ? roq_free_58 : _GEN_1849; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1851 = 6'h3b == roq_deq_addr_4 ? roq_free_59 : _GEN_1850; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1852 = 6'h3c == roq_deq_addr_4 ? roq_free_60 : _GEN_1851; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1853 = 6'h3d == roq_deq_addr_4 ? roq_free_61 : _GEN_1852; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1854 = 6'h3e == roq_deq_addr_4 ? roq_free_62 : _GEN_1853; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire  _GEN_1855 = 6'h3f == roq_deq_addr_4 ? roq_free_63 : _GEN_1854; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{22,22}]
  wire [11:0] _io_deq_4_matches_T_1 = {{6'd0}, io_deq_4_tag[11:6]}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:85]
  wire [5:0] _GEN_1857 = 6'h1 == roq_deq_addr_4 ? roq_tags_1 : roq_tags_0; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1858 = 6'h2 == roq_deq_addr_4 ? roq_tags_2 : _GEN_1857; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1859 = 6'h3 == roq_deq_addr_4 ? roq_tags_3 : _GEN_1858; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1860 = 6'h4 == roq_deq_addr_4 ? roq_tags_4 : _GEN_1859; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1861 = 6'h5 == roq_deq_addr_4 ? roq_tags_5 : _GEN_1860; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1862 = 6'h6 == roq_deq_addr_4 ? roq_tags_6 : _GEN_1861; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1863 = 6'h7 == roq_deq_addr_4 ? roq_tags_7 : _GEN_1862; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1864 = 6'h8 == roq_deq_addr_4 ? roq_tags_8 : _GEN_1863; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1865 = 6'h9 == roq_deq_addr_4 ? roq_tags_9 : _GEN_1864; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1866 = 6'ha == roq_deq_addr_4 ? roq_tags_10 : _GEN_1865; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1867 = 6'hb == roq_deq_addr_4 ? roq_tags_11 : _GEN_1866; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1868 = 6'hc == roq_deq_addr_4 ? roq_tags_12 : _GEN_1867; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1869 = 6'hd == roq_deq_addr_4 ? roq_tags_13 : _GEN_1868; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1870 = 6'he == roq_deq_addr_4 ? roq_tags_14 : _GEN_1869; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1871 = 6'hf == roq_deq_addr_4 ? roq_tags_15 : _GEN_1870; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1872 = 6'h10 == roq_deq_addr_4 ? roq_tags_16 : _GEN_1871; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1873 = 6'h11 == roq_deq_addr_4 ? roq_tags_17 : _GEN_1872; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1874 = 6'h12 == roq_deq_addr_4 ? roq_tags_18 : _GEN_1873; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1875 = 6'h13 == roq_deq_addr_4 ? roq_tags_19 : _GEN_1874; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1876 = 6'h14 == roq_deq_addr_4 ? roq_tags_20 : _GEN_1875; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1877 = 6'h15 == roq_deq_addr_4 ? roq_tags_21 : _GEN_1876; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1878 = 6'h16 == roq_deq_addr_4 ? roq_tags_22 : _GEN_1877; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1879 = 6'h17 == roq_deq_addr_4 ? roq_tags_23 : _GEN_1878; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1880 = 6'h18 == roq_deq_addr_4 ? roq_tags_24 : _GEN_1879; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1881 = 6'h19 == roq_deq_addr_4 ? roq_tags_25 : _GEN_1880; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1882 = 6'h1a == roq_deq_addr_4 ? roq_tags_26 : _GEN_1881; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1883 = 6'h1b == roq_deq_addr_4 ? roq_tags_27 : _GEN_1882; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1884 = 6'h1c == roq_deq_addr_4 ? roq_tags_28 : _GEN_1883; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1885 = 6'h1d == roq_deq_addr_4 ? roq_tags_29 : _GEN_1884; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1886 = 6'h1e == roq_deq_addr_4 ? roq_tags_30 : _GEN_1885; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1887 = 6'h1f == roq_deq_addr_4 ? roq_tags_31 : _GEN_1886; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1888 = 6'h20 == roq_deq_addr_4 ? roq_tags_32 : _GEN_1887; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1889 = 6'h21 == roq_deq_addr_4 ? roq_tags_33 : _GEN_1888; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1890 = 6'h22 == roq_deq_addr_4 ? roq_tags_34 : _GEN_1889; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1891 = 6'h23 == roq_deq_addr_4 ? roq_tags_35 : _GEN_1890; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1892 = 6'h24 == roq_deq_addr_4 ? roq_tags_36 : _GEN_1891; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1893 = 6'h25 == roq_deq_addr_4 ? roq_tags_37 : _GEN_1892; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1894 = 6'h26 == roq_deq_addr_4 ? roq_tags_38 : _GEN_1893; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1895 = 6'h27 == roq_deq_addr_4 ? roq_tags_39 : _GEN_1894; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1896 = 6'h28 == roq_deq_addr_4 ? roq_tags_40 : _GEN_1895; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1897 = 6'h29 == roq_deq_addr_4 ? roq_tags_41 : _GEN_1896; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1898 = 6'h2a == roq_deq_addr_4 ? roq_tags_42 : _GEN_1897; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1899 = 6'h2b == roq_deq_addr_4 ? roq_tags_43 : _GEN_1898; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1900 = 6'h2c == roq_deq_addr_4 ? roq_tags_44 : _GEN_1899; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1901 = 6'h2d == roq_deq_addr_4 ? roq_tags_45 : _GEN_1900; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1902 = 6'h2e == roq_deq_addr_4 ? roq_tags_46 : _GEN_1901; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1903 = 6'h2f == roq_deq_addr_4 ? roq_tags_47 : _GEN_1902; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1904 = 6'h30 == roq_deq_addr_4 ? roq_tags_48 : _GEN_1903; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1905 = 6'h31 == roq_deq_addr_4 ? roq_tags_49 : _GEN_1904; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1906 = 6'h32 == roq_deq_addr_4 ? roq_tags_50 : _GEN_1905; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1907 = 6'h33 == roq_deq_addr_4 ? roq_tags_51 : _GEN_1906; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1908 = 6'h34 == roq_deq_addr_4 ? roq_tags_52 : _GEN_1907; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1909 = 6'h35 == roq_deq_addr_4 ? roq_tags_53 : _GEN_1908; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1910 = 6'h36 == roq_deq_addr_4 ? roq_tags_54 : _GEN_1909; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1911 = 6'h37 == roq_deq_addr_4 ? roq_tags_55 : _GEN_1910; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1912 = 6'h38 == roq_deq_addr_4 ? roq_tags_56 : _GEN_1911; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1913 = 6'h39 == roq_deq_addr_4 ? roq_tags_57 : _GEN_1912; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1914 = 6'h3a == roq_deq_addr_4 ? roq_tags_58 : _GEN_1913; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1915 = 6'h3b == roq_deq_addr_4 ? roq_tags_59 : _GEN_1914; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1916 = 6'h3c == roq_deq_addr_4 ? roq_tags_60 : _GEN_1915; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1917 = 6'h3d == roq_deq_addr_4 ? roq_tags_61 : _GEN_1916; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1918 = 6'h3e == roq_deq_addr_4 ? roq_tags_62 : _GEN_1917; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [5:0] _GEN_1919 = 6'h3f == roq_deq_addr_4 ? roq_tags_63 : _GEN_1918; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:{72,72}]
  wire [11:0] _GEN_2314 = {{6'd0}, _GEN_1919}; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:72]
  wire  _GEN_1920 = 6'h0 == roq_deq_addr_4 | _GEN_1664; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1921 = 6'h1 == roq_deq_addr_4 | _GEN_1665; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1922 = 6'h2 == roq_deq_addr_4 | _GEN_1666; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1923 = 6'h3 == roq_deq_addr_4 | _GEN_1667; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1924 = 6'h4 == roq_deq_addr_4 | _GEN_1668; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1925 = 6'h5 == roq_deq_addr_4 | _GEN_1669; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1926 = 6'h6 == roq_deq_addr_4 | _GEN_1670; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1927 = 6'h7 == roq_deq_addr_4 | _GEN_1671; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1928 = 6'h8 == roq_deq_addr_4 | _GEN_1672; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1929 = 6'h9 == roq_deq_addr_4 | _GEN_1673; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1930 = 6'ha == roq_deq_addr_4 | _GEN_1674; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1931 = 6'hb == roq_deq_addr_4 | _GEN_1675; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1932 = 6'hc == roq_deq_addr_4 | _GEN_1676; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1933 = 6'hd == roq_deq_addr_4 | _GEN_1677; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1934 = 6'he == roq_deq_addr_4 | _GEN_1678; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1935 = 6'hf == roq_deq_addr_4 | _GEN_1679; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1936 = 6'h10 == roq_deq_addr_4 | _GEN_1680; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1937 = 6'h11 == roq_deq_addr_4 | _GEN_1681; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1938 = 6'h12 == roq_deq_addr_4 | _GEN_1682; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1939 = 6'h13 == roq_deq_addr_4 | _GEN_1683; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1940 = 6'h14 == roq_deq_addr_4 | _GEN_1684; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1941 = 6'h15 == roq_deq_addr_4 | _GEN_1685; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1942 = 6'h16 == roq_deq_addr_4 | _GEN_1686; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1943 = 6'h17 == roq_deq_addr_4 | _GEN_1687; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1944 = 6'h18 == roq_deq_addr_4 | _GEN_1688; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1945 = 6'h19 == roq_deq_addr_4 | _GEN_1689; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1946 = 6'h1a == roq_deq_addr_4 | _GEN_1690; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1947 = 6'h1b == roq_deq_addr_4 | _GEN_1691; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1948 = 6'h1c == roq_deq_addr_4 | _GEN_1692; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1949 = 6'h1d == roq_deq_addr_4 | _GEN_1693; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1950 = 6'h1e == roq_deq_addr_4 | _GEN_1694; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1951 = 6'h1f == roq_deq_addr_4 | _GEN_1695; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1952 = 6'h20 == roq_deq_addr_4 | _GEN_1696; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1953 = 6'h21 == roq_deq_addr_4 | _GEN_1697; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1954 = 6'h22 == roq_deq_addr_4 | _GEN_1698; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1955 = 6'h23 == roq_deq_addr_4 | _GEN_1699; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1956 = 6'h24 == roq_deq_addr_4 | _GEN_1700; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1957 = 6'h25 == roq_deq_addr_4 | _GEN_1701; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1958 = 6'h26 == roq_deq_addr_4 | _GEN_1702; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1959 = 6'h27 == roq_deq_addr_4 | _GEN_1703; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1960 = 6'h28 == roq_deq_addr_4 | _GEN_1704; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1961 = 6'h29 == roq_deq_addr_4 | _GEN_1705; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1962 = 6'h2a == roq_deq_addr_4 | _GEN_1706; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1963 = 6'h2b == roq_deq_addr_4 | _GEN_1707; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1964 = 6'h2c == roq_deq_addr_4 | _GEN_1708; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1965 = 6'h2d == roq_deq_addr_4 | _GEN_1709; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1966 = 6'h2e == roq_deq_addr_4 | _GEN_1710; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1967 = 6'h2f == roq_deq_addr_4 | _GEN_1711; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1968 = 6'h30 == roq_deq_addr_4 | _GEN_1712; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1969 = 6'h31 == roq_deq_addr_4 | _GEN_1713; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1970 = 6'h32 == roq_deq_addr_4 | _GEN_1714; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1971 = 6'h33 == roq_deq_addr_4 | _GEN_1715; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1972 = 6'h34 == roq_deq_addr_4 | _GEN_1716; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1973 = 6'h35 == roq_deq_addr_4 | _GEN_1717; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1974 = 6'h36 == roq_deq_addr_4 | _GEN_1718; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1975 = 6'h37 == roq_deq_addr_4 | _GEN_1719; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1976 = 6'h38 == roq_deq_addr_4 | _GEN_1720; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1977 = 6'h39 == roq_deq_addr_4 | _GEN_1721; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1978 = 6'h3a == roq_deq_addr_4 | _GEN_1722; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1979 = 6'h3b == roq_deq_addr_4 | _GEN_1723; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1980 = 6'h3c == roq_deq_addr_4 | _GEN_1724; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1981 = 6'h3d == roq_deq_addr_4 | _GEN_1725; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1982 = 6'h3e == roq_deq_addr_4 | _GEN_1726; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1983 = 6'h3f == roq_deq_addr_4 | _GEN_1727; // @[midas/src/main/scala/junctions/ReorderQueue.scala 54:{32,32}]
  wire  _GEN_1984 = io_deq_4_valid ? _GEN_1920 : _GEN_1664; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1985 = io_deq_4_valid ? _GEN_1921 : _GEN_1665; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1986 = io_deq_4_valid ? _GEN_1922 : _GEN_1666; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1987 = io_deq_4_valid ? _GEN_1923 : _GEN_1667; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1988 = io_deq_4_valid ? _GEN_1924 : _GEN_1668; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1989 = io_deq_4_valid ? _GEN_1925 : _GEN_1669; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1990 = io_deq_4_valid ? _GEN_1926 : _GEN_1670; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1991 = io_deq_4_valid ? _GEN_1927 : _GEN_1671; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1992 = io_deq_4_valid ? _GEN_1928 : _GEN_1672; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1993 = io_deq_4_valid ? _GEN_1929 : _GEN_1673; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1994 = io_deq_4_valid ? _GEN_1930 : _GEN_1674; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1995 = io_deq_4_valid ? _GEN_1931 : _GEN_1675; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1996 = io_deq_4_valid ? _GEN_1932 : _GEN_1676; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1997 = io_deq_4_valid ? _GEN_1933 : _GEN_1677; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1998 = io_deq_4_valid ? _GEN_1934 : _GEN_1678; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_1999 = io_deq_4_valid ? _GEN_1935 : _GEN_1679; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2000 = io_deq_4_valid ? _GEN_1936 : _GEN_1680; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2001 = io_deq_4_valid ? _GEN_1937 : _GEN_1681; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2002 = io_deq_4_valid ? _GEN_1938 : _GEN_1682; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2003 = io_deq_4_valid ? _GEN_1939 : _GEN_1683; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2004 = io_deq_4_valid ? _GEN_1940 : _GEN_1684; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2005 = io_deq_4_valid ? _GEN_1941 : _GEN_1685; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2006 = io_deq_4_valid ? _GEN_1942 : _GEN_1686; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2007 = io_deq_4_valid ? _GEN_1943 : _GEN_1687; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2008 = io_deq_4_valid ? _GEN_1944 : _GEN_1688; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2009 = io_deq_4_valid ? _GEN_1945 : _GEN_1689; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2010 = io_deq_4_valid ? _GEN_1946 : _GEN_1690; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2011 = io_deq_4_valid ? _GEN_1947 : _GEN_1691; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2012 = io_deq_4_valid ? _GEN_1948 : _GEN_1692; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2013 = io_deq_4_valid ? _GEN_1949 : _GEN_1693; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2014 = io_deq_4_valid ? _GEN_1950 : _GEN_1694; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2015 = io_deq_4_valid ? _GEN_1951 : _GEN_1695; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2016 = io_deq_4_valid ? _GEN_1952 : _GEN_1696; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2017 = io_deq_4_valid ? _GEN_1953 : _GEN_1697; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2018 = io_deq_4_valid ? _GEN_1954 : _GEN_1698; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2019 = io_deq_4_valid ? _GEN_1955 : _GEN_1699; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2020 = io_deq_4_valid ? _GEN_1956 : _GEN_1700; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2021 = io_deq_4_valid ? _GEN_1957 : _GEN_1701; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2022 = io_deq_4_valid ? _GEN_1958 : _GEN_1702; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2023 = io_deq_4_valid ? _GEN_1959 : _GEN_1703; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2024 = io_deq_4_valid ? _GEN_1960 : _GEN_1704; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2025 = io_deq_4_valid ? _GEN_1961 : _GEN_1705; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2026 = io_deq_4_valid ? _GEN_1962 : _GEN_1706; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2027 = io_deq_4_valid ? _GEN_1963 : _GEN_1707; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2028 = io_deq_4_valid ? _GEN_1964 : _GEN_1708; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2029 = io_deq_4_valid ? _GEN_1965 : _GEN_1709; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2030 = io_deq_4_valid ? _GEN_1966 : _GEN_1710; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2031 = io_deq_4_valid ? _GEN_1967 : _GEN_1711; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2032 = io_deq_4_valid ? _GEN_1968 : _GEN_1712; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2033 = io_deq_4_valid ? _GEN_1969 : _GEN_1713; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2034 = io_deq_4_valid ? _GEN_1970 : _GEN_1714; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2035 = io_deq_4_valid ? _GEN_1971 : _GEN_1715; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2036 = io_deq_4_valid ? _GEN_1972 : _GEN_1716; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2037 = io_deq_4_valid ? _GEN_1973 : _GEN_1717; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2038 = io_deq_4_valid ? _GEN_1974 : _GEN_1718; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2039 = io_deq_4_valid ? _GEN_1975 : _GEN_1719; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2040 = io_deq_4_valid ? _GEN_1976 : _GEN_1720; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2041 = io_deq_4_valid ? _GEN_1977 : _GEN_1721; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2042 = io_deq_4_valid ? _GEN_1978 : _GEN_1722; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2043 = io_deq_4_valid ? _GEN_1979 : _GEN_1723; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2044 = io_deq_4_valid ? _GEN_1980 : _GEN_1724; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2045 = io_deq_4_valid ? _GEN_1981 : _GEN_1725; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2046 = io_deq_4_valid ? _GEN_1982 : _GEN_1726; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  wire  _GEN_2047 = io_deq_4_valid ? _GEN_1983 : _GEN_1727; // @[midas/src/main/scala/junctions/ReorderQueue.scala 53:23]
  assign io_enq_ready = 6'h3f == roq_enq_addr ? roq_free_63 : _GEN_62; // @[midas/src/main/scala/junctions/ReorderQueue.scala 39:{18,18}]
  assign io_deq_0_matches = ~_GEN_575 & _GEN_2050 == _io_deq_0_matches_T_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:46]
  assign io_deq_1_matches = ~_GEN_895 & _GEN_2116 == _io_deq_1_matches_T_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:46]
  assign io_deq_2_matches = ~_GEN_1215 & _GEN_2182 == _io_deq_2_matches_T_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:46]
  assign io_deq_3_matches = ~_GEN_1535 & _GEN_2248 == _io_deq_3_matches_T_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:46]
  assign io_deq_4_matches = ~_GEN_1855 & _GEN_2314 == _io_deq_4_matches_T_1; // @[midas/src/main/scala/junctions/ReorderQueue.scala 51:46]
  always @(posedge clock) begin
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h0 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_0 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_1 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_2 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_3 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h4 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_4 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h5 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_5 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h6 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_6 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h7 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_7 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h8 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_8 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h9 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_9 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'ha == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_10 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'hb == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_11 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'hc == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_12 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'hd == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_13 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'he == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_14 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'hf == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_15 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h10 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_16 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h11 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_17 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h12 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_18 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h13 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_19 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h14 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_20 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h15 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_21 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h16 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_22 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h17 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_23 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h18 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_24 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h19 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_25 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1a == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_26 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1b == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_27 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1c == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_28 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1d == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_29 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1e == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_30 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h1f == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_31 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h20 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_32 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h21 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_33 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h22 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_34 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h23 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_35 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h24 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_36 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h25 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_37 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h26 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_38 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h27 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_39 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h28 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_40 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h29 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_41 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2a == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_42 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2b == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_43 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2c == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_44 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2d == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_45 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2e == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_46 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h2f == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_47 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h30 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_48 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h31 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_49 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h32 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_50 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h33 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_51 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h34 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_52 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h35 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_53 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h36 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_54 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h37 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_55 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h38 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_56 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h39 == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_57 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3a == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_58 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3b == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_59 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3c == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_60 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3d == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_61 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3e == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_62 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    if (io_enq_valid & io_enq_ready) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 41:40]
      if (6'h3f == roq_enq_addr) begin // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
        roq_tags_63 <= _roq_tags_T[5:0]; // @[midas/src/main/scala/junctions/ReorderQueue.scala 43:30]
      end
    end
    roq_free_0 <= reset | _GEN_1984; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_1 <= reset | _GEN_1985; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_2 <= reset | _GEN_1986; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_3 <= reset | _GEN_1987; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_4 <= reset | _GEN_1988; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_5 <= reset | _GEN_1989; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_6 <= reset | _GEN_1990; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_7 <= reset | _GEN_1991; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_8 <= reset | _GEN_1992; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_9 <= reset | _GEN_1993; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_10 <= reset | _GEN_1994; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_11 <= reset | _GEN_1995; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_12 <= reset | _GEN_1996; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_13 <= reset | _GEN_1997; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_14 <= reset | _GEN_1998; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_15 <= reset | _GEN_1999; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_16 <= reset | _GEN_2000; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_17 <= reset | _GEN_2001; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_18 <= reset | _GEN_2002; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_19 <= reset | _GEN_2003; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_20 <= reset | _GEN_2004; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_21 <= reset | _GEN_2005; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_22 <= reset | _GEN_2006; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_23 <= reset | _GEN_2007; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_24 <= reset | _GEN_2008; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_25 <= reset | _GEN_2009; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_26 <= reset | _GEN_2010; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_27 <= reset | _GEN_2011; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_28 <= reset | _GEN_2012; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_29 <= reset | _GEN_2013; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_30 <= reset | _GEN_2014; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_31 <= reset | _GEN_2015; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_32 <= reset | _GEN_2016; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_33 <= reset | _GEN_2017; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_34 <= reset | _GEN_2018; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_35 <= reset | _GEN_2019; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_36 <= reset | _GEN_2020; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_37 <= reset | _GEN_2021; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_38 <= reset | _GEN_2022; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_39 <= reset | _GEN_2023; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_40 <= reset | _GEN_2024; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_41 <= reset | _GEN_2025; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_42 <= reset | _GEN_2026; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_43 <= reset | _GEN_2027; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_44 <= reset | _GEN_2028; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_45 <= reset | _GEN_2029; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_46 <= reset | _GEN_2030; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_47 <= reset | _GEN_2031; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_48 <= reset | _GEN_2032; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_49 <= reset | _GEN_2033; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_50 <= reset | _GEN_2034; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_51 <= reset | _GEN_2035; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_52 <= reset | _GEN_2036; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_53 <= reset | _GEN_2037; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_54 <= reset | _GEN_2038; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_55 <= reset | _GEN_2039; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_56 <= reset | _GEN_2040; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_57 <= reset | _GEN_2041; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_58 <= reset | _GEN_2042; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_59 <= reset | _GEN_2043; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_60 <= reset | _GEN_2044; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_61 <= reset | _GEN_2045; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_62 <= reset | _GEN_2046; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
    roq_free_63 <= reset | _GEN_2047; // @[midas/src/main/scala/junctions/ReorderQueue.scala 36:{27,27}]
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  roq_tags_0 = _RAND_0[5:0];
  _RAND_1 = {1{`RANDOM}};
  roq_tags_1 = _RAND_1[5:0];
  _RAND_2 = {1{`RANDOM}};
  roq_tags_2 = _RAND_2[5:0];
  _RAND_3 = {1{`RANDOM}};
  roq_tags_3 = _RAND_3[5:0];
  _RAND_4 = {1{`RANDOM}};
  roq_tags_4 = _RAND_4[5:0];
  _RAND_5 = {1{`RANDOM}};
  roq_tags_5 = _RAND_5[5:0];
  _RAND_6 = {1{`RANDOM}};
  roq_tags_6 = _RAND_6[5:0];
  _RAND_7 = {1{`RANDOM}};
  roq_tags_7 = _RAND_7[5:0];
  _RAND_8 = {1{`RANDOM}};
  roq_tags_8 = _RAND_8[5:0];
  _RAND_9 = {1{`RANDOM}};
  roq_tags_9 = _RAND_9[5:0];
  _RAND_10 = {1{`RANDOM}};
  roq_tags_10 = _RAND_10[5:0];
  _RAND_11 = {1{`RANDOM}};
  roq_tags_11 = _RAND_11[5:0];
  _RAND_12 = {1{`RANDOM}};
  roq_tags_12 = _RAND_12[5:0];
  _RAND_13 = {1{`RANDOM}};
  roq_tags_13 = _RAND_13[5:0];
  _RAND_14 = {1{`RANDOM}};
  roq_tags_14 = _RAND_14[5:0];
  _RAND_15 = {1{`RANDOM}};
  roq_tags_15 = _RAND_15[5:0];
  _RAND_16 = {1{`RANDOM}};
  roq_tags_16 = _RAND_16[5:0];
  _RAND_17 = {1{`RANDOM}};
  roq_tags_17 = _RAND_17[5:0];
  _RAND_18 = {1{`RANDOM}};
  roq_tags_18 = _RAND_18[5:0];
  _RAND_19 = {1{`RANDOM}};
  roq_tags_19 = _RAND_19[5:0];
  _RAND_20 = {1{`RANDOM}};
  roq_tags_20 = _RAND_20[5:0];
  _RAND_21 = {1{`RANDOM}};
  roq_tags_21 = _RAND_21[5:0];
  _RAND_22 = {1{`RANDOM}};
  roq_tags_22 = _RAND_22[5:0];
  _RAND_23 = {1{`RANDOM}};
  roq_tags_23 = _RAND_23[5:0];
  _RAND_24 = {1{`RANDOM}};
  roq_tags_24 = _RAND_24[5:0];
  _RAND_25 = {1{`RANDOM}};
  roq_tags_25 = _RAND_25[5:0];
  _RAND_26 = {1{`RANDOM}};
  roq_tags_26 = _RAND_26[5:0];
  _RAND_27 = {1{`RANDOM}};
  roq_tags_27 = _RAND_27[5:0];
  _RAND_28 = {1{`RANDOM}};
  roq_tags_28 = _RAND_28[5:0];
  _RAND_29 = {1{`RANDOM}};
  roq_tags_29 = _RAND_29[5:0];
  _RAND_30 = {1{`RANDOM}};
  roq_tags_30 = _RAND_30[5:0];
  _RAND_31 = {1{`RANDOM}};
  roq_tags_31 = _RAND_31[5:0];
  _RAND_32 = {1{`RANDOM}};
  roq_tags_32 = _RAND_32[5:0];
  _RAND_33 = {1{`RANDOM}};
  roq_tags_33 = _RAND_33[5:0];
  _RAND_34 = {1{`RANDOM}};
  roq_tags_34 = _RAND_34[5:0];
  _RAND_35 = {1{`RANDOM}};
  roq_tags_35 = _RAND_35[5:0];
  _RAND_36 = {1{`RANDOM}};
  roq_tags_36 = _RAND_36[5:0];
  _RAND_37 = {1{`RANDOM}};
  roq_tags_37 = _RAND_37[5:0];
  _RAND_38 = {1{`RANDOM}};
  roq_tags_38 = _RAND_38[5:0];
  _RAND_39 = {1{`RANDOM}};
  roq_tags_39 = _RAND_39[5:0];
  _RAND_40 = {1{`RANDOM}};
  roq_tags_40 = _RAND_40[5:0];
  _RAND_41 = {1{`RANDOM}};
  roq_tags_41 = _RAND_41[5:0];
  _RAND_42 = {1{`RANDOM}};
  roq_tags_42 = _RAND_42[5:0];
  _RAND_43 = {1{`RANDOM}};
  roq_tags_43 = _RAND_43[5:0];
  _RAND_44 = {1{`RANDOM}};
  roq_tags_44 = _RAND_44[5:0];
  _RAND_45 = {1{`RANDOM}};
  roq_tags_45 = _RAND_45[5:0];
  _RAND_46 = {1{`RANDOM}};
  roq_tags_46 = _RAND_46[5:0];
  _RAND_47 = {1{`RANDOM}};
  roq_tags_47 = _RAND_47[5:0];
  _RAND_48 = {1{`RANDOM}};
  roq_tags_48 = _RAND_48[5:0];
  _RAND_49 = {1{`RANDOM}};
  roq_tags_49 = _RAND_49[5:0];
  _RAND_50 = {1{`RANDOM}};
  roq_tags_50 = _RAND_50[5:0];
  _RAND_51 = {1{`RANDOM}};
  roq_tags_51 = _RAND_51[5:0];
  _RAND_52 = {1{`RANDOM}};
  roq_tags_52 = _RAND_52[5:0];
  _RAND_53 = {1{`RANDOM}};
  roq_tags_53 = _RAND_53[5:0];
  _RAND_54 = {1{`RANDOM}};
  roq_tags_54 = _RAND_54[5:0];
  _RAND_55 = {1{`RANDOM}};
  roq_tags_55 = _RAND_55[5:0];
  _RAND_56 = {1{`RANDOM}};
  roq_tags_56 = _RAND_56[5:0];
  _RAND_57 = {1{`RANDOM}};
  roq_tags_57 = _RAND_57[5:0];
  _RAND_58 = {1{`RANDOM}};
  roq_tags_58 = _RAND_58[5:0];
  _RAND_59 = {1{`RANDOM}};
  roq_tags_59 = _RAND_59[5:0];
  _RAND_60 = {1{`RANDOM}};
  roq_tags_60 = _RAND_60[5:0];
  _RAND_61 = {1{`RANDOM}};
  roq_tags_61 = _RAND_61[5:0];
  _RAND_62 = {1{`RANDOM}};
  roq_tags_62 = _RAND_62[5:0];
  _RAND_63 = {1{`RANDOM}};
  roq_tags_63 = _RAND_63[5:0];
  _RAND_64 = {1{`RANDOM}};
  roq_free_0 = _RAND_64[0:0];
  _RAND_65 = {1{`RANDOM}};
  roq_free_1 = _RAND_65[0:0];
  _RAND_66 = {1{`RANDOM}};
  roq_free_2 = _RAND_66[0:0];
  _RAND_67 = {1{`RANDOM}};
  roq_free_3 = _RAND_67[0:0];
  _RAND_68 = {1{`RANDOM}};
  roq_free_4 = _RAND_68[0:0];
  _RAND_69 = {1{`RANDOM}};
  roq_free_5 = _RAND_69[0:0];
  _RAND_70 = {1{`RANDOM}};
  roq_free_6 = _RAND_70[0:0];
  _RAND_71 = {1{`RANDOM}};
  roq_free_7 = _RAND_71[0:0];
  _RAND_72 = {1{`RANDOM}};
  roq_free_8 = _RAND_72[0:0];
  _RAND_73 = {1{`RANDOM}};
  roq_free_9 = _RAND_73[0:0];
  _RAND_74 = {1{`RANDOM}};
  roq_free_10 = _RAND_74[0:0];
  _RAND_75 = {1{`RANDOM}};
  roq_free_11 = _RAND_75[0:0];
  _RAND_76 = {1{`RANDOM}};
  roq_free_12 = _RAND_76[0:0];
  _RAND_77 = {1{`RANDOM}};
  roq_free_13 = _RAND_77[0:0];
  _RAND_78 = {1{`RANDOM}};
  roq_free_14 = _RAND_78[0:0];
  _RAND_79 = {1{`RANDOM}};
  roq_free_15 = _RAND_79[0:0];
  _RAND_80 = {1{`RANDOM}};
  roq_free_16 = _RAND_80[0:0];
  _RAND_81 = {1{`RANDOM}};
  roq_free_17 = _RAND_81[0:0];
  _RAND_82 = {1{`RANDOM}};
  roq_free_18 = _RAND_82[0:0];
  _RAND_83 = {1{`RANDOM}};
  roq_free_19 = _RAND_83[0:0];
  _RAND_84 = {1{`RANDOM}};
  roq_free_20 = _RAND_84[0:0];
  _RAND_85 = {1{`RANDOM}};
  roq_free_21 = _RAND_85[0:0];
  _RAND_86 = {1{`RANDOM}};
  roq_free_22 = _RAND_86[0:0];
  _RAND_87 = {1{`RANDOM}};
  roq_free_23 = _RAND_87[0:0];
  _RAND_88 = {1{`RANDOM}};
  roq_free_24 = _RAND_88[0:0];
  _RAND_89 = {1{`RANDOM}};
  roq_free_25 = _RAND_89[0:0];
  _RAND_90 = {1{`RANDOM}};
  roq_free_26 = _RAND_90[0:0];
  _RAND_91 = {1{`RANDOM}};
  roq_free_27 = _RAND_91[0:0];
  _RAND_92 = {1{`RANDOM}};
  roq_free_28 = _RAND_92[0:0];
  _RAND_93 = {1{`RANDOM}};
  roq_free_29 = _RAND_93[0:0];
  _RAND_94 = {1{`RANDOM}};
  roq_free_30 = _RAND_94[0:0];
  _RAND_95 = {1{`RANDOM}};
  roq_free_31 = _RAND_95[0:0];
  _RAND_96 = {1{`RANDOM}};
  roq_free_32 = _RAND_96[0:0];
  _RAND_97 = {1{`RANDOM}};
  roq_free_33 = _RAND_97[0:0];
  _RAND_98 = {1{`RANDOM}};
  roq_free_34 = _RAND_98[0:0];
  _RAND_99 = {1{`RANDOM}};
  roq_free_35 = _RAND_99[0:0];
  _RAND_100 = {1{`RANDOM}};
  roq_free_36 = _RAND_100[0:0];
  _RAND_101 = {1{`RANDOM}};
  roq_free_37 = _RAND_101[0:0];
  _RAND_102 = {1{`RANDOM}};
  roq_free_38 = _RAND_102[0:0];
  _RAND_103 = {1{`RANDOM}};
  roq_free_39 = _RAND_103[0:0];
  _RAND_104 = {1{`RANDOM}};
  roq_free_40 = _RAND_104[0:0];
  _RAND_105 = {1{`RANDOM}};
  roq_free_41 = _RAND_105[0:0];
  _RAND_106 = {1{`RANDOM}};
  roq_free_42 = _RAND_106[0:0];
  _RAND_107 = {1{`RANDOM}};
  roq_free_43 = _RAND_107[0:0];
  _RAND_108 = {1{`RANDOM}};
  roq_free_44 = _RAND_108[0:0];
  _RAND_109 = {1{`RANDOM}};
  roq_free_45 = _RAND_109[0:0];
  _RAND_110 = {1{`RANDOM}};
  roq_free_46 = _RAND_110[0:0];
  _RAND_111 = {1{`RANDOM}};
  roq_free_47 = _RAND_111[0:0];
  _RAND_112 = {1{`RANDOM}};
  roq_free_48 = _RAND_112[0:0];
  _RAND_113 = {1{`RANDOM}};
  roq_free_49 = _RAND_113[0:0];
  _RAND_114 = {1{`RANDOM}};
  roq_free_50 = _RAND_114[0:0];
  _RAND_115 = {1{`RANDOM}};
  roq_free_51 = _RAND_115[0:0];
  _RAND_116 = {1{`RANDOM}};
  roq_free_52 = _RAND_116[0:0];
  _RAND_117 = {1{`RANDOM}};
  roq_free_53 = _RAND_117[0:0];
  _RAND_118 = {1{`RANDOM}};
  roq_free_54 = _RAND_118[0:0];
  _RAND_119 = {1{`RANDOM}};
  roq_free_55 = _RAND_119[0:0];
  _RAND_120 = {1{`RANDOM}};
  roq_free_56 = _RAND_120[0:0];
  _RAND_121 = {1{`RANDOM}};
  roq_free_57 = _RAND_121[0:0];
  _RAND_122 = {1{`RANDOM}};
  roq_free_58 = _RAND_122[0:0];
  _RAND_123 = {1{`RANDOM}};
  roq_free_59 = _RAND_123[0:0];
  _RAND_124 = {1{`RANDOM}};
  roq_free_60 = _RAND_124[0:0];
  _RAND_125 = {1{`RANDOM}};
  roq_free_61 = _RAND_125[0:0];
  _RAND_126 = {1{`RANDOM}};
  roq_free_62 = _RAND_126[0:0];
  _RAND_127 = {1{`RANDOM}};
  roq_free_63 = _RAND_127[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module Queue_2(
  input        clock,
  input        reset,
  output       io_enq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input        io_enq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input  [3:0] io_enq_bits, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input        io_deq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output       io_deq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output [3:0] io_deq_bits // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
`endif // RANDOMIZE_REG_INIT
  reg [3:0] ram [0:3]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [1:0] ram_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [3:0] ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire [3:0] ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire [1:0] ram_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg [1:0] enq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg [1:0] deq_ptr_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  reg  maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
  wire  ptr_match = enq_ptr_value == deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 283:33]
  wire  empty = ptr_match & ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 284:25]
  wire  full = ptr_match & maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 285:24]
  wire  do_enq = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  do_deq = io_deq_ready & io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire [1:0] _value_T_1 = enq_ptr_value + 2'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:24]
  wire [1:0] _value_T_3 = deq_ptr_value + 2'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:24]
  assign ram_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_addr = deq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_data = ram[ram_io_deq_bits_MPORT_addr]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_MPORT_data = io_enq_bits; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_addr = enq_ptr_value; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign io_enq_ready = ~full; // @[src/main/scala/chisel3/util/Decoupled.scala 309:19]
  assign io_deq_valid = ~empty; // @[src/main/scala/chisel3/util/Decoupled.scala 308:19]
  assign io_deq_bits = ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  always @(posedge clock) begin
    if (ram_MPORT_en & ram_MPORT_mask) begin
      ram[ram_MPORT_addr] <= ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      enq_ptr_value <= 2'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_enq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 292:16]
      enq_ptr_value <= _value_T_1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      deq_ptr_value <= 2'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 296:16]
      deq_ptr_value <= _value_T_3; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
      maybe_full <= 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
    end else if (do_enq != do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 299:27]
      maybe_full <= do_enq; // @[src/main/scala/chisel3/util/Decoupled.scala 300:16]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 4; initvar = initvar+1)
    ram[initvar] = _RAND_0[3:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  enq_ptr_value = _RAND_1[1:0];
  _RAND_2 = {1{`RANDOM}};
  deq_ptr_value = _RAND_2[1:0];
  _RAND_3 = {1{`RANDOM}};
  maybe_full = _RAND_3[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module Queue_3(
  input         clock,
  input         reset,
  output        io_enq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_enq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input  [7:0]  io_enq_bits_len, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input  [11:0] io_enq_bits_id, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_deq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output        io_deq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output [7:0]  io_deq_bits_len, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output [11:0] io_deq_bits_id // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_2;
`endif // RANDOMIZE_REG_INIT
  reg [7:0] ram_len [0:0]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_len_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_len_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [7:0] ram_len_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire [7:0] ram_len_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_len_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_len_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_len_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg [11:0] ram_id [0:0]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_id_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_id_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [11:0] ram_id_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire [11:0] ram_id_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_id_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_id_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_id_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg  maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
  wire  empty = ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 284:28]
  wire  do_enq = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  do_deq = io_deq_ready & io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_len_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_len_io_deq_bits_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_len_io_deq_bits_MPORT_data = ram_len[ram_len_io_deq_bits_MPORT_addr]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_len_MPORT_data = io_enq_bits_len; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_len_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_len_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_len_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_id_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_id_io_deq_bits_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_id_io_deq_bits_MPORT_data = ram_id[ram_id_io_deq_bits_MPORT_addr]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_id_MPORT_data = io_enq_bits_id; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_id_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_id_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_id_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign io_enq_ready = ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 309:19]
  assign io_deq_valid = ~empty; // @[src/main/scala/chisel3/util/Decoupled.scala 308:19]
  assign io_deq_bits_len = ram_len_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  assign io_deq_bits_id = ram_id_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  always @(posedge clock) begin
    if (ram_len_MPORT_en & ram_len_MPORT_mask) begin
      ram_len[ram_len_MPORT_addr] <= ram_len_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (ram_id_MPORT_en & ram_id_MPORT_mask) begin
      ram_id[ram_id_MPORT_addr] <= ram_id_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
      maybe_full <= 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
    end else if (do_enq != do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 299:27]
      maybe_full <= do_enq; // @[src/main/scala/chisel3/util/Decoupled.scala 300:16]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    ram_len[initvar] = _RAND_0[7:0];
  _RAND_1 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    ram_id[initvar] = _RAND_1[11:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_2 = {1{`RANDOM}};
  maybe_full = _RAND_2[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module Queue_4(
  input         clock,
  input         reset,
  output        io_enq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_enq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input  [11:0] io_enq_bits, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  input         io_deq_ready, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output        io_deq_valid, // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
  output [11:0] io_deq_bits // @[src/main/scala/chisel3/util/Decoupled.scala 278:14]
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_1;
`endif // RANDOMIZE_REG_INIT
  reg [11:0] ram [0:0]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire  ram_io_deq_bits_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire  ram_io_deq_bits_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 316:23]
  wire [11:0] ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  wire [11:0] ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_MPORT_addr; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:8]
  wire  ram_MPORT_mask; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 292:16 293:24]
  wire  ram_MPORT_en; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95 57:35]
  reg  maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
  wire  empty = ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 284:28]
  wire  do_enq = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  do_deq = io_deq_ready & io_deq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ram_io_deq_bits_MPORT_en = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 316:23]
  assign ram_io_deq_bits_MPORT_data = ram[ram_io_deq_bits_MPORT_addr]; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
  assign ram_MPORT_data = io_enq_bits; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_addr = 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:8]
  assign ram_MPORT_mask = 1'h1; // @[src/main/scala/chisel3/util/Decoupled.scala 292:16 293:24]
  assign ram_MPORT_en = io_enq_ready & io_enq_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign io_enq_ready = ~maybe_full; // @[src/main/scala/chisel3/util/Decoupled.scala 309:19]
  assign io_deq_valid = ~empty; // @[src/main/scala/chisel3/util/Decoupled.scala 308:19]
  assign io_deq_bits = ram_io_deq_bits_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 316:17]
  always @(posedge clock) begin
    if (ram_MPORT_en & ram_MPORT_mask) begin
      ram[ram_MPORT_addr] <= ram_MPORT_data; // @[src/main/scala/chisel3/util/Decoupled.scala 279:95]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
      maybe_full <= 1'h0; // @[src/main/scala/chisel3/util/Decoupled.scala 282:27]
    end else if (do_enq != do_deq) begin // @[src/main/scala/chisel3/util/Decoupled.scala 299:27]
      maybe_full <= do_enq; // @[src/main/scala/chisel3/util/Decoupled.scala 300:16]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    ram[initvar] = _RAND_0[11:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_1 = {1{`RANDOM}};
  maybe_full = _RAND_1[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module NastiErrorSlave(
  input         clock,
  input         reset,
  output        io_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input  [24:0] io_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input  [11:0] io_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output        io_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_w_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output        io_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output [11:0] io_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output        io_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input  [24:0] io_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input  [7:0]  io_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input  [11:0] io_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  input         io_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output        io_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output        io_r_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 251:14]
  output [11:0] io_r_bits_id // @[midas/src/main/scala/junctions/nasti.scala 251:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
`endif // RANDOMIZE_REG_INIT
  wire  r_queue_clock; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  r_queue_reset; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  r_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  r_queue_io_enq_valid; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire [7:0] r_queue_io_enq_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire [11:0] r_queue_io_enq_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  r_queue_io_deq_ready; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  r_queue_io_deq_valid; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire [7:0] r_queue_io_deq_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire [11:0] r_queue_io_deq_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 256:23]
  wire  b_queue_clock; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  b_queue_reset; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  b_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  b_queue_io_enq_valid; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire [11:0] b_queue_io_enq_bits; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  b_queue_io_deq_ready; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  b_queue_io_deq_valid; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire [11:0] b_queue_io_deq_bits; // @[midas/src/main/scala/junctions/nasti.scala 290:23]
  wire  _T = io_ar_ready & io_ar_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_2 = ~reset; // @[midas/src/main/scala/junctions/nasti.scala 253:28]
  wire  _T_3 = io_aw_ready & io_aw_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  reg  responding; // @[midas/src/main/scala/junctions/nasti.scala 259:27]
  reg [7:0] beats_left; // @[midas/src/main/scala/junctions/nasti.scala 260:27]
  wire  _GEN_0 = ~responding & r_queue_io_deq_valid | responding; // @[midas/src/main/scala/junctions/nasti.scala 262:45 263:16 259:27]
  wire [7:0] _GEN_1 = ~responding & r_queue_io_deq_valid ? r_queue_io_deq_bits_len : beats_left; // @[midas/src/main/scala/junctions/nasti.scala 262:45 264:16 260:27]
  wire  _io_r_bits_last_T = beats_left == 8'h0; // @[midas/src/main/scala/junctions/nasti.scala 271:32]
  wire  _r_queue_io_deq_ready_T = io_r_ready & io_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire [7:0] _beats_left_T_1 = beats_left - 8'h1; // @[midas/src/main/scala/junctions/nasti.scala 280:32]
  reg  draining; // @[midas/src/main/scala/junctions/nasti.scala 284:25]
  wire  _GEN_6 = _T_3 | draining; // @[midas/src/main/scala/junctions/nasti.scala 287:20 284:25 287:31]
  wire  _T_11 = io_w_ready & io_w_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _b_queue_io_enq_valid_T = ~draining; // @[midas/src/main/scala/junctions/nasti.scala 291:42]
  Queue_3 r_queue ( // @[midas/src/main/scala/junctions/nasti.scala 256:23]
    .clock(r_queue_clock),
    .reset(r_queue_reset),
    .io_enq_ready(r_queue_io_enq_ready),
    .io_enq_valid(r_queue_io_enq_valid),
    .io_enq_bits_len(r_queue_io_enq_bits_len),
    .io_enq_bits_id(r_queue_io_enq_bits_id),
    .io_deq_ready(r_queue_io_deq_ready),
    .io_deq_valid(r_queue_io_deq_valid),
    .io_deq_bits_len(r_queue_io_deq_bits_len),
    .io_deq_bits_id(r_queue_io_deq_bits_id)
  );
  Queue_4 b_queue ( // @[midas/src/main/scala/junctions/nasti.scala 290:23]
    .clock(b_queue_clock),
    .reset(b_queue_reset),
    .io_enq_ready(b_queue_io_enq_ready),
    .io_enq_valid(b_queue_io_enq_valid),
    .io_enq_bits(b_queue_io_enq_bits),
    .io_deq_ready(b_queue_io_deq_ready),
    .io_deq_valid(b_queue_io_deq_valid),
    .io_deq_bits(b_queue_io_deq_bits)
  );
  assign io_aw_ready = b_queue_io_enq_ready & _b_queue_io_enq_valid_T; // @[midas/src/main/scala/junctions/nasti.scala 293:48]
  assign io_w_ready = draining; // @[midas/src/main/scala/junctions/nasti.scala 285:14]
  assign io_b_valid = b_queue_io_deq_valid & _b_queue_io_enq_valid_T; // @[midas/src/main/scala/junctions/nasti.scala 294:48]
  assign io_b_bits_id = b_queue_io_deq_bits; // @[midas/src/main/scala/junctions/nasti.scala 295:24]
  assign io_ar_ready = r_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 257:18]
  assign io_r_valid = r_queue_io_deq_valid & responding; // @[midas/src/main/scala/junctions/nasti.scala 267:42]
  assign io_r_bits_last = beats_left == 8'h0; // @[midas/src/main/scala/junctions/nasti.scala 271:32]
  assign io_r_bits_id = r_queue_io_deq_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 268:18]
  assign r_queue_clock = clock;
  assign r_queue_reset = reset;
  assign r_queue_io_enq_valid = io_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 257:18]
  assign r_queue_io_enq_bits_len = io_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 257:18]
  assign r_queue_io_enq_bits_id = io_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 257:18]
  assign r_queue_io_deq_ready = _r_queue_io_deq_ready_T & io_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 274:37]
  assign b_queue_clock = clock;
  assign b_queue_reset = reset;
  assign b_queue_io_enq_valid = io_aw_valid & ~draining; // @[midas/src/main/scala/junctions/nasti.scala 291:39]
  assign b_queue_io_enq_bits = io_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 292:24]
  assign b_queue_io_deq_ready = io_b_ready & _b_queue_io_enq_valid_T; // @[midas/src/main/scala/junctions/nasti.scala 298:38]
  always @(posedge clock) begin
    if (reset) begin // @[midas/src/main/scala/junctions/nasti.scala 259:27]
      responding <= 1'h0; // @[midas/src/main/scala/junctions/nasti.scala 259:27]
    end else if (_r_queue_io_deq_ready_T) begin // @[midas/src/main/scala/junctions/nasti.scala 276:19]
      if (_io_r_bits_last_T) begin // @[midas/src/main/scala/junctions/nasti.scala 277:30]
        responding <= 1'h0; // @[midas/src/main/scala/junctions/nasti.scala 278:18]
      end else begin
        responding <= _GEN_0;
      end
    end else begin
      responding <= _GEN_0;
    end
    if (reset) begin // @[midas/src/main/scala/junctions/nasti.scala 260:27]
      beats_left <= 8'h0; // @[midas/src/main/scala/junctions/nasti.scala 260:27]
    end else if (_r_queue_io_deq_ready_T) begin // @[midas/src/main/scala/junctions/nasti.scala 276:19]
      if (_io_r_bits_last_T) begin // @[midas/src/main/scala/junctions/nasti.scala 277:30]
        beats_left <= _GEN_1;
      end else begin
        beats_left <= _beats_left_T_1; // @[midas/src/main/scala/junctions/nasti.scala 280:18]
      end
    end else begin
      beats_left <= _GEN_1;
    end
    if (reset) begin // @[midas/src/main/scala/junctions/nasti.scala 284:25]
      draining <= 1'h0; // @[midas/src/main/scala/junctions/nasti.scala 284:25]
    end else if (_T_11 & io_w_bits_last) begin // @[midas/src/main/scala/junctions/nasti.scala 288:37]
      draining <= 1'h0; // @[midas/src/main/scala/junctions/nasti.scala 288:48]
    end else begin
      draining <= _GEN_6;
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~reset) begin
          $fwrite(32'h80000002,"Invalid read address %x\n",io_ar_bits_addr); // @[midas/src/main/scala/junctions/nasti.scala 253:28]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_3 & _T_2) begin
          $fwrite(32'h80000002,"Invalid write address %x\n",io_aw_bits_addr); // @[midas/src/main/scala/junctions/nasti.scala 254:28]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  responding = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  beats_left = _RAND_1[7:0];
  _RAND_2 = {1{`RANDOM}};
  draining = _RAND_2[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module RRArbiter(
  input         clock,
  output        io_in_0_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_in_0_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input  [11:0] io_in_0_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output        io_in_1_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_in_1_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input  [11:0] io_in_1_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output        io_in_2_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_in_2_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input  [11:0] io_in_2_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output        io_in_3_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_in_3_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input  [11:0] io_in_3_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output        io_in_4_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_in_4_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input  [11:0] io_in_4_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  input         io_out_ready, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output        io_out_valid, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output [1:0]  io_out_bits_resp, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output [11:0] io_out_bits_id, // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
  output [2:0]  io_chosen // @[src/main/scala/chisel3/util/Arbiter.scala 52:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_REG_INIT
  wire  _GEN_1 = 3'h1 == io_chosen ? io_in_1_valid : io_in_0_valid; // @[src/main/scala/chisel3/util/Arbiter.scala 55:{16,16}]
  wire  _GEN_2 = 3'h2 == io_chosen ? io_in_2_valid : _GEN_1; // @[src/main/scala/chisel3/util/Arbiter.scala 55:{16,16}]
  wire  _GEN_3 = 3'h3 == io_chosen ? io_in_3_valid : _GEN_2; // @[src/main/scala/chisel3/util/Arbiter.scala 55:{16,16}]
  wire [11:0] _GEN_11 = 3'h1 == io_chosen ? io_in_1_bits_id : io_in_0_bits_id; // @[src/main/scala/chisel3/util/Arbiter.scala 56:{15,15}]
  wire [11:0] _GEN_12 = 3'h2 == io_chosen ? io_in_2_bits_id : _GEN_11; // @[src/main/scala/chisel3/util/Arbiter.scala 56:{15,15}]
  wire [11:0] _GEN_13 = 3'h3 == io_chosen ? io_in_3_bits_id : _GEN_12; // @[src/main/scala/chisel3/util/Arbiter.scala 56:{15,15}]
  wire  _ctrl_validMask_grantMask_lastGrant_T = io_out_ready & io_out_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  reg [2:0] ctrl_validMask_grantMask_lastGrant; // @[src/main/scala/chisel3/util/Arbiter.scala 81:33]
  wire  ctrl_validMask_grantMask_1 = 3'h1 > ctrl_validMask_grantMask_lastGrant; // @[src/main/scala/chisel3/util/Arbiter.scala 82:49]
  wire  ctrl_validMask_grantMask_2 = 3'h2 > ctrl_validMask_grantMask_lastGrant; // @[src/main/scala/chisel3/util/Arbiter.scala 82:49]
  wire  ctrl_validMask_grantMask_3 = 3'h3 > ctrl_validMask_grantMask_lastGrant; // @[src/main/scala/chisel3/util/Arbiter.scala 82:49]
  wire  ctrl_validMask_grantMask_4 = 3'h4 > ctrl_validMask_grantMask_lastGrant; // @[src/main/scala/chisel3/util/Arbiter.scala 82:49]
  wire  ctrl_validMask_1 = io_in_1_valid & ctrl_validMask_grantMask_1; // @[src/main/scala/chisel3/util/Arbiter.scala 83:76]
  wire  ctrl_validMask_2 = io_in_2_valid & ctrl_validMask_grantMask_2; // @[src/main/scala/chisel3/util/Arbiter.scala 83:76]
  wire  ctrl_validMask_3 = io_in_3_valid & ctrl_validMask_grantMask_3; // @[src/main/scala/chisel3/util/Arbiter.scala 83:76]
  wire  ctrl_validMask_4 = io_in_4_valid & ctrl_validMask_grantMask_4; // @[src/main/scala/chisel3/util/Arbiter.scala 83:76]
  wire  ctrl_2 = ~ctrl_validMask_1; // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_3 = ~(ctrl_validMask_1 | ctrl_validMask_2); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_4 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_5 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3 | ctrl_validMask_4); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_6 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3 | ctrl_validMask_4 | io_in_0_valid); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_7 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3 | ctrl_validMask_4 | io_in_0_valid |
    io_in_1_valid); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_8 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3 | ctrl_validMask_4 | io_in_0_valid |
    io_in_1_valid | io_in_2_valid); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  ctrl_9 = ~(ctrl_validMask_1 | ctrl_validMask_2 | ctrl_validMask_3 | ctrl_validMask_4 | io_in_0_valid |
    io_in_1_valid | io_in_2_valid | io_in_3_valid); // @[src/main/scala/chisel3/util/Arbiter.scala 45:78]
  wire  _T_3 = ctrl_validMask_grantMask_1 | ctrl_6; // @[src/main/scala/chisel3/util/Arbiter.scala 87:50]
  wire  _T_5 = ctrl_2 & ctrl_validMask_grantMask_2 | ctrl_7; // @[src/main/scala/chisel3/util/Arbiter.scala 87:50]
  wire  _T_7 = ctrl_3 & ctrl_validMask_grantMask_3 | ctrl_8; // @[src/main/scala/chisel3/util/Arbiter.scala 87:50]
  wire  _T_9 = ctrl_4 & ctrl_validMask_grantMask_4 | ctrl_9; // @[src/main/scala/chisel3/util/Arbiter.scala 87:50]
  wire [2:0] _GEN_21 = io_in_3_valid ? 3'h3 : 3'h4; // @[src/main/scala/chisel3/util/Arbiter.scala 92:{26,35} 90:41]
  wire [2:0] _GEN_22 = io_in_2_valid ? 3'h2 : _GEN_21; // @[src/main/scala/chisel3/util/Arbiter.scala 92:{26,35}]
  wire [2:0] _GEN_23 = io_in_1_valid ? 3'h1 : _GEN_22; // @[src/main/scala/chisel3/util/Arbiter.scala 92:{26,35}]
  wire [2:0] _GEN_24 = io_in_0_valid ? 3'h0 : _GEN_23; // @[src/main/scala/chisel3/util/Arbiter.scala 92:{26,35}]
  wire [2:0] _GEN_25 = ctrl_validMask_4 ? 3'h4 : _GEN_24; // @[src/main/scala/chisel3/util/Arbiter.scala 94:{24,33}]
  wire [2:0] _GEN_26 = ctrl_validMask_3 ? 3'h3 : _GEN_25; // @[src/main/scala/chisel3/util/Arbiter.scala 94:{24,33}]
  wire [2:0] _GEN_27 = ctrl_validMask_2 ? 3'h2 : _GEN_26; // @[src/main/scala/chisel3/util/Arbiter.scala 94:{24,33}]
  assign io_in_0_ready = ctrl_5 & io_out_ready; // @[src/main/scala/chisel3/util/Arbiter.scala 74:21]
  assign io_in_1_ready = _T_3 & io_out_ready; // @[src/main/scala/chisel3/util/Arbiter.scala 74:21]
  assign io_in_2_ready = _T_5 & io_out_ready; // @[src/main/scala/chisel3/util/Arbiter.scala 74:21]
  assign io_in_3_ready = _T_7 & io_out_ready; // @[src/main/scala/chisel3/util/Arbiter.scala 74:21]
  assign io_in_4_ready = _T_9 & io_out_ready; // @[src/main/scala/chisel3/util/Arbiter.scala 74:21]
  assign io_out_valid = 3'h4 == io_chosen ? io_in_4_valid : _GEN_3; // @[src/main/scala/chisel3/util/Arbiter.scala 55:{16,16}]
  assign io_out_bits_resp = 3'h4 == io_chosen ? 2'h3 : 2'h0; // @[src/main/scala/chisel3/util/Arbiter.scala 56:{15,15}]
  assign io_out_bits_id = 3'h4 == io_chosen ? io_in_4_bits_id : _GEN_13; // @[src/main/scala/chisel3/util/Arbiter.scala 56:{15,15}]
  assign io_chosen = ctrl_validMask_1 ? 3'h1 : _GEN_27; // @[src/main/scala/chisel3/util/Arbiter.scala 94:{24,33}]
  always @(posedge clock) begin
    if (_ctrl_validMask_grantMask_lastGrant_T) begin // @[src/main/scala/chisel3/util/Arbiter.scala 81:33]
      ctrl_validMask_grantMask_lastGrant <= io_chosen; // @[src/main/scala/chisel3/util/Arbiter.scala 81:33]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  ctrl_validMask_grantMask_lastGrant = _RAND_0[2:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module HellaPeekingArbiter(
  input         clock,
  input         reset,
  output        io_in_0_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_0_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [31:0] io_in_0_bits_data, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [11:0] io_in_0_bits_id, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_in_1_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_1_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [31:0] io_in_1_bits_data, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [11:0] io_in_1_bits_id, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_in_2_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_2_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [31:0] io_in_2_bits_data, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [11:0] io_in_2_bits_id, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_in_3_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_3_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [31:0] io_in_3_bits_data, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [11:0] io_in_3_bits_id, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_in_4_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_4_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_in_4_bits_last, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input  [11:0] io_in_4_bits_id, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  input         io_out_ready, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_out_valid, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output [1:0]  io_out_bits_resp, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output [31:0] io_out_bits_data, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output        io_out_bits_last, // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
  output [11:0] io_out_bits_id // @[rocket-chip/src/main/scala/util/Arbiters.scala 14:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
`endif // RANDOMIZE_REG_INIT
  reg [2:0] lockIdx; // @[rocket-chip/src/main/scala/util/Arbiters.scala 26:24]
  reg  locked; // @[rocket-chip/src/main/scala/util/Arbiters.scala 27:23]
  wire [2:0] _choice_T_1 = lockIdx + 3'h1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 31:55]
  wire [3:0] _choice_T_3 = {{1'd0}, _choice_T_1}; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:37]
  wire [2:0] _choice_T_6 = _choice_T_1 - 3'h5; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:54]
  wire  _GEN_1 = 3'h1 == _choice_T_3[2:0] ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_2 = 3'h2 == _choice_T_3[2:0] ? io_in_2_valid : _GEN_1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_3 = 3'h3 == _choice_T_3[2:0] ? io_in_3_valid : _GEN_2; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_4 = 3'h4 == _choice_T_3[2:0] ? io_in_4_valid : _GEN_3; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_6 = 3'h1 == _choice_T_6 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_7 = 3'h2 == _choice_T_6 ? io_in_2_valid : _GEN_6; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_8 = 3'h3 == _choice_T_6 ? io_in_3_valid : _GEN_7; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_9 = 3'h4 == _choice_T_6 ? io_in_4_valid : _GEN_8; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _choice_T_7 = _choice_T_1 < 3'h5 ? _GEN_4 : _GEN_9; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _choice_T_10 = 3'h1 + _choice_T_1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:37]
  wire [2:0] _choice_T_12 = _choice_T_1 - 3'h4; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:54]
  wire  _GEN_11 = 3'h1 == _choice_T_10 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_12 = 3'h2 == _choice_T_10 ? io_in_2_valid : _GEN_11; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_13 = 3'h3 == _choice_T_10 ? io_in_3_valid : _GEN_12; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_14 = 3'h4 == _choice_T_10 ? io_in_4_valid : _GEN_13; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_16 = 3'h1 == _choice_T_12 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_17 = 3'h2 == _choice_T_12 ? io_in_2_valid : _GEN_16; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_18 = 3'h3 == _choice_T_12 ? io_in_3_valid : _GEN_17; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_19 = 3'h4 == _choice_T_12 ? io_in_4_valid : _GEN_18; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _choice_T_13 = _choice_T_1 < 3'h4 ? _GEN_14 : _GEN_19; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _choice_T_16 = 3'h2 + _choice_T_1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:37]
  wire [2:0] _choice_T_18 = _choice_T_1 - 3'h3; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:54]
  wire  _GEN_21 = 3'h1 == _choice_T_16 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_22 = 3'h2 == _choice_T_16 ? io_in_2_valid : _GEN_21; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_23 = 3'h3 == _choice_T_16 ? io_in_3_valid : _GEN_22; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_24 = 3'h4 == _choice_T_16 ? io_in_4_valid : _GEN_23; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_26 = 3'h1 == _choice_T_18 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_27 = 3'h2 == _choice_T_18 ? io_in_2_valid : _GEN_26; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_28 = 3'h3 == _choice_T_18 ? io_in_3_valid : _GEN_27; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_29 = 3'h4 == _choice_T_18 ? io_in_4_valid : _GEN_28; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _choice_T_19 = _choice_T_1 < 3'h3 ? _GEN_24 : _GEN_29; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _choice_T_22 = 3'h3 + _choice_T_1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:37]
  wire [2:0] _choice_T_24 = _choice_T_1 - 3'h2; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:54]
  wire  _GEN_31 = 3'h1 == _choice_T_22 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_32 = 3'h2 == _choice_T_22 ? io_in_2_valid : _GEN_31; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_33 = 3'h3 == _choice_T_22 ? io_in_3_valid : _GEN_32; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_34 = 3'h4 == _choice_T_22 ? io_in_4_valid : _GEN_33; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_36 = 3'h1 == _choice_T_24 ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_37 = 3'h2 == _choice_T_24 ? io_in_2_valid : _GEN_36; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_38 = 3'h3 == _choice_T_24 ? io_in_3_valid : _GEN_37; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _GEN_39 = 3'h4 == _choice_T_24 ? io_in_4_valid : _GEN_38; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire  _choice_T_25 = _choice_T_1 < 3'h2 ? _GEN_34 : _GEN_39; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _choice_T_28 = 3'h4 + _choice_T_1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:37]
  wire [2:0] _choice_T_30 = _choice_T_1 - 3'h1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:54]
  wire [2:0] _GEN_51 = 3'h1 == _choice_T_3[2:0] ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_52 = 3'h2 == _choice_T_3[2:0] ? 3'h2 : _GEN_51; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_53 = 3'h3 == _choice_T_3[2:0] ? 3'h3 : _GEN_52; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_54 = 3'h4 == _choice_T_3[2:0] ? 3'h4 : _GEN_53; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_56 = 3'h1 == _choice_T_6 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_57 = 3'h2 == _choice_T_6 ? 3'h2 : _GEN_56; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_58 = 3'h3 == _choice_T_6 ? 3'h3 : _GEN_57; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_59 = 3'h4 == _choice_T_6 ? 3'h4 : _GEN_58; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _choice_T_39 = _choice_T_1 < 3'h5 ? _GEN_54 : _GEN_59; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _GEN_61 = 3'h1 == _choice_T_10 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_62 = 3'h2 == _choice_T_10 ? 3'h2 : _GEN_61; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_63 = 3'h3 == _choice_T_10 ? 3'h3 : _GEN_62; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_64 = 3'h4 == _choice_T_10 ? 3'h4 : _GEN_63; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_66 = 3'h1 == _choice_T_12 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_67 = 3'h2 == _choice_T_12 ? 3'h2 : _GEN_66; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_68 = 3'h3 == _choice_T_12 ? 3'h3 : _GEN_67; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_69 = 3'h4 == _choice_T_12 ? 3'h4 : _GEN_68; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _choice_T_45 = _choice_T_1 < 3'h4 ? _GEN_64 : _GEN_69; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _GEN_71 = 3'h1 == _choice_T_16 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_72 = 3'h2 == _choice_T_16 ? 3'h2 : _GEN_71; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_73 = 3'h3 == _choice_T_16 ? 3'h3 : _GEN_72; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_74 = 3'h4 == _choice_T_16 ? 3'h4 : _GEN_73; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_76 = 3'h1 == _choice_T_18 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_77 = 3'h2 == _choice_T_18 ? 3'h2 : _GEN_76; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_78 = 3'h3 == _choice_T_18 ? 3'h3 : _GEN_77; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_79 = 3'h4 == _choice_T_18 ? 3'h4 : _GEN_78; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _choice_T_51 = _choice_T_1 < 3'h3 ? _GEN_74 : _GEN_79; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _GEN_81 = 3'h1 == _choice_T_22 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_82 = 3'h2 == _choice_T_22 ? 3'h2 : _GEN_81; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_83 = 3'h3 == _choice_T_22 ? 3'h3 : _GEN_82; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_84 = 3'h4 == _choice_T_22 ? 3'h4 : _GEN_83; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_86 = 3'h1 == _choice_T_24 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_87 = 3'h2 == _choice_T_24 ? 3'h2 : _GEN_86; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_88 = 3'h3 == _choice_T_24 ? 3'h3 : _GEN_87; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_89 = 3'h4 == _choice_T_24 ? 3'h4 : _GEN_88; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _choice_T_57 = _choice_T_1 < 3'h2 ? _GEN_84 : _GEN_89; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _GEN_91 = 3'h1 == _choice_T_28 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_92 = 3'h2 == _choice_T_28 ? 3'h2 : _GEN_91; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_93 = 3'h3 == _choice_T_28 ? 3'h3 : _GEN_92; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_94 = 3'h4 == _choice_T_28 ? 3'h4 : _GEN_93; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_96 = 3'h1 == _choice_T_30 ? 3'h1 : 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_97 = 3'h2 == _choice_T_30 ? 3'h2 : _GEN_96; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_98 = 3'h3 == _choice_T_30 ? 3'h3 : _GEN_97; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _GEN_99 = 3'h4 == _choice_T_30 ? 3'h4 : _GEN_98; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:{10,10}]
  wire [2:0] _choice_T_63 = _choice_T_1 < 3'h1 ? _GEN_94 : _GEN_99; // @[rocket-chip/src/main/scala/util/Arbiters.scala 22:10]
  wire [2:0] _choice_T_64 = _choice_T_25 ? _choice_T_57 : _choice_T_63; // @[src/main/scala/chisel3/util/Mux.scala 50:70]
  wire [2:0] _choice_T_65 = _choice_T_19 ? _choice_T_51 : _choice_T_64; // @[src/main/scala/chisel3/util/Mux.scala 50:70]
  wire [2:0] _choice_T_66 = _choice_T_13 ? _choice_T_45 : _choice_T_65; // @[src/main/scala/chisel3/util/Mux.scala 50:70]
  wire [2:0] choice = _choice_T_7 ? _choice_T_39 : _choice_T_66; // @[src/main/scala/chisel3/util/Mux.scala 50:70]
  wire [2:0] chosen = locked ? lockIdx : choice; // @[rocket-chip/src/main/scala/util/Arbiters.scala 37:19]
  wire  _GEN_101 = 3'h1 == chosen ? io_in_1_valid : io_in_0_valid; // @[rocket-chip/src/main/scala/util/Arbiters.scala 43:{16,16}]
  wire  _GEN_102 = 3'h2 == chosen ? io_in_2_valid : _GEN_101; // @[rocket-chip/src/main/scala/util/Arbiters.scala 43:{16,16}]
  wire  _GEN_103 = 3'h3 == chosen ? io_in_3_valid : _GEN_102; // @[rocket-chip/src/main/scala/util/Arbiters.scala 43:{16,16}]
  wire [31:0] _GEN_111 = 3'h1 == chosen ? io_in_1_bits_data : io_in_0_bits_data; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire [31:0] _GEN_112 = 3'h2 == chosen ? io_in_2_bits_data : _GEN_111; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire [31:0] _GEN_113 = 3'h3 == chosen ? io_in_3_bits_data : _GEN_112; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire [11:0] _GEN_121 = 3'h1 == chosen ? io_in_1_bits_id : io_in_0_bits_id; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire [11:0] _GEN_122 = 3'h2 == chosen ? io_in_2_bits_id : _GEN_121; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire [11:0] _GEN_123 = 3'h3 == chosen ? io_in_3_bits_id : _GEN_122; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  wire  _T = io_out_ready & io_out_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _GEN_131 = ~locked | locked; // @[rocket-chip/src/main/scala/util/Arbiters.scala 60:50 62:14 27:23]
  assign io_in_0_ready = io_out_ready & chosen == 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 40:36]
  assign io_in_1_ready = io_out_ready & chosen == 3'h1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 40:36]
  assign io_in_2_ready = io_out_ready & chosen == 3'h2; // @[rocket-chip/src/main/scala/util/Arbiters.scala 40:36]
  assign io_in_3_ready = io_out_ready & chosen == 3'h3; // @[rocket-chip/src/main/scala/util/Arbiters.scala 40:36]
  assign io_in_4_ready = io_out_ready & chosen == 3'h4; // @[rocket-chip/src/main/scala/util/Arbiters.scala 40:36]
  assign io_out_valid = 3'h4 == chosen ? io_in_4_valid : _GEN_103; // @[rocket-chip/src/main/scala/util/Arbiters.scala 43:{16,16}]
  assign io_out_bits_resp = 3'h4 == chosen ? 2'h3 : 2'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  assign io_out_bits_data = 3'h4 == chosen ? 32'h0 : _GEN_113; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  assign io_out_bits_last = 3'h4 == chosen ? io_in_4_bits_last : 1'h1; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  assign io_out_bits_id = 3'h4 == chosen ? io_in_4_bits_id : _GEN_123; // @[rocket-chip/src/main/scala/util/Arbiters.scala 44:{15,15}]
  always @(posedge clock) begin
    if (reset) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 26:24]
      lockIdx <= 3'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 26:24]
    end else if (_T) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 59:22]
      if (~locked) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 60:50]
        if (_choice_T_7) begin // @[src/main/scala/chisel3/util/Mux.scala 50:70]
          lockIdx <= _choice_T_39;
        end else begin
          lockIdx <= _choice_T_66;
        end
      end
    end
    if (reset) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 27:23]
      locked <= 1'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 27:23]
    end else if (_T) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 59:22]
      if (io_out_bits_last) begin // @[rocket-chip/src/main/scala/util/Arbiters.scala 65:35]
        locked <= 1'h0; // @[rocket-chip/src/main/scala/util/Arbiters.scala 66:14]
      end else begin
        locked <= _GEN_131;
      end
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  lockIdx = _RAND_0[2:0];
  _RAND_1 = {1{`RANDOM}};
  locked = _RAND_1[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module NastiRouter(
  input         clock,
  input         reset,
  output        io_master_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [24:0] io_master_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [7:0]  io_master_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_master_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_master_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [31:0] io_master_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_w_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_master_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [1:0]  io_master_b_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_master_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_master_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [24:0] io_master_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [7:0]  io_master_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_master_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_master_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_master_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [1:0]  io_master_r_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [31:0] io_master_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_master_r_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_master_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_0_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_0_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_0_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_0_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_0_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_0_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_0_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [31:0] io_slave_0_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_0_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_0_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_0_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_0_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_0_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_0_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_0_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_0_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_0_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_0_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [31:0] io_slave_0_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_0_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_1_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_1_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_1_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_1_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_1_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_1_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_1_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [31:0] io_slave_1_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_1_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_1_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_1_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_1_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_1_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_1_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_1_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_1_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_1_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_1_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [31:0] io_slave_1_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_1_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_2_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_2_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_2_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_2_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_2_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_2_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_2_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [31:0] io_slave_2_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_2_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_2_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_2_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_2_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_2_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_2_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_2_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_2_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_2_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_2_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [31:0] io_slave_2_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_2_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_3_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_3_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_3_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_3_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_3_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_3_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_3_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [31:0] io_slave_3_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_3_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_3_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_3_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_3_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_3_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [24:0] io_slave_3_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [7:0]  io_slave_3_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output [11:0] io_slave_3_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  output        io_slave_3_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input         io_slave_3_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [31:0] io_slave_3_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 314:14]
  input  [11:0] io_slave_3_r_bits_id // @[midas/src/main/scala/junctions/nasti.scala 314:14]
);
  wire  ar_queue_clock; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_reset; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_enq_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_enq_bits_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_0_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_deq_0_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_0_matches; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_1_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_deq_1_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_1_matches; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_2_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_deq_2_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_2_matches; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_3_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_deq_3_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_3_matches; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_4_valid; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire [11:0] ar_queue_io_deq_4_tag; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  ar_queue_io_deq_4_matches; // @[midas/src/main/scala/junctions/nasti.scala 327:24]
  wire  aw_queue_clock; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_reset; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_enq_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_enq_bits_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_0_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_deq_0_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_0_matches; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_1_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_deq_1_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_1_matches; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_2_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_deq_2_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_2_matches; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_3_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_deq_3_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_3_matches; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_4_valid; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire [11:0] aw_queue_io_deq_4_tag; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  aw_queue_io_deq_4_matches; // @[midas/src/main/scala/junctions/nasti.scala 328:24]
  wire  w_queue_clock; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  w_queue_reset; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  w_queue_io_enq_ready; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  w_queue_io_enq_valid; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire [3:0] w_queue_io_enq_bits; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  w_queue_io_deq_ready; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  w_queue_io_deq_valid; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire [3:0] w_queue_io_deq_bits; // @[midas/src/main/scala/junctions/nasti.scala 330:24]
  wire  err_slave_clock; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_reset; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [24:0] err_slave_io_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [11:0] err_slave_io_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [11:0] err_slave_io_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [24:0] err_slave_io_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [7:0] err_slave_io_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [11:0] err_slave_io_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  err_slave_io_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire [11:0] err_slave_io_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 379:25]
  wire  b_arb_clock; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_0_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_0_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_in_0_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_1_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_1_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_in_1_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_2_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_2_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_in_2_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_3_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_3_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_in_3_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_4_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_in_4_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_in_4_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_out_ready; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  b_arb_io_out_valid; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [1:0] b_arb_io_out_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [11:0] b_arb_io_out_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire [2:0] b_arb_io_chosen; // @[midas/src/main/scala/junctions/nasti.scala 391:21]
  wire  r_arb_clock; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_reset; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_0_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_0_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [31:0] r_arb_io_in_0_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_in_0_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_1_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_1_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [31:0] r_arb_io_in_1_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_in_1_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_2_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_2_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [31:0] r_arb_io_in_2_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_in_2_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_3_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_3_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [31:0] r_arb_io_in_3_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_in_3_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_4_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_4_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_in_4_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_in_4_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_out_ready; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_out_valid; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [1:0] r_arb_io_out_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [31:0] r_arb_io_out_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  r_arb_io_out_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire [11:0] r_arb_io_out_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 392:21]
  wire  _ar_route_T_1 = io_master_ar_bits_addr < 25'h40; // @[midas/src/main/scala/junctions/addrmap.scala 17:52]
  wire  _ar_route_T_5 = 25'h40 <= io_master_ar_bits_addr & io_master_ar_bits_addr < 25'h60; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire  _ar_route_T_8 = 25'h60 <= io_master_ar_bits_addr & io_master_ar_bits_addr < 25'h80; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire  _ar_route_T_11 = 25'h80 <= io_master_ar_bits_addr & io_master_ar_bits_addr < 25'h90; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire [3:0] ar_route = {_ar_route_T_11,_ar_route_T_8,_ar_route_T_5,_ar_route_T_1}; // @[midas/src/main/scala/junctions/nasti.scala 482:37]
  wire  _aw_route_T_1 = io_master_aw_bits_addr < 25'h40; // @[midas/src/main/scala/junctions/addrmap.scala 17:52]
  wire  _aw_route_T_5 = 25'h40 <= io_master_aw_bits_addr & io_master_aw_bits_addr < 25'h60; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire  _aw_route_T_8 = 25'h60 <= io_master_aw_bits_addr & io_master_aw_bits_addr < 25'h80; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire  _aw_route_T_11 = 25'h80 <= io_master_aw_bits_addr & io_master_aw_bits_addr < 25'h90; // @[midas/src/main/scala/junctions/addrmap.scala 17:47]
  wire [1:0] aw_route_lo = {_aw_route_T_5,_aw_route_T_1}; // @[midas/src/main/scala/junctions/nasti.scala 482:37]
  wire [1:0] aw_route_hi = {_aw_route_T_11,_aw_route_T_8}; // @[midas/src/main/scala/junctions/nasti.scala 482:37]
  wire [3:0] aw_route = {_aw_route_T_11,_aw_route_T_8,_aw_route_T_5,_aw_route_T_1}; // @[midas/src/main/scala/junctions/nasti.scala 482:37]
  wire  ar_noroute = ~(|ar_route); // @[midas/src/main/scala/junctions/nasti.scala 375:20]
  wire  _GEN_0 = ar_route[0] & io_slave_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 364:23 319:26 364:34]
  wire  _GEN_3 = ar_route[1] ? io_slave_1_ar_ready : _GEN_0; // @[midas/src/main/scala/junctions/nasti.scala 364:{23,34}]
  wire  _GEN_6 = ar_route[2] ? io_slave_2_ar_ready : _GEN_3; // @[midas/src/main/scala/junctions/nasti.scala 364:{23,34}]
  wire  _GEN_9 = ar_route[3] ? io_slave_3_ar_ready : _GEN_6; // @[midas/src/main/scala/junctions/nasti.scala 364:{23,34}]
  wire  ar_ready = ar_noroute ? err_slave_io_ar_ready : _GEN_9; // @[midas/src/main/scala/junctions/nasti.scala 387:{20,31}]
  wire  aw_noroute = ~(|aw_route); // @[midas/src/main/scala/junctions/nasti.scala 376:20]
  wire  _GEN_1 = aw_route[0] & io_slave_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 368:23 320:26 368:34]
  wire  _GEN_4 = aw_route[1] ? io_slave_1_aw_ready : _GEN_1; // @[midas/src/main/scala/junctions/nasti.scala 368:{23,34}]
  wire  _GEN_7 = aw_route[2] ? io_slave_2_aw_ready : _GEN_4; // @[midas/src/main/scala/junctions/nasti.scala 368:{23,34}]
  wire  _GEN_10 = aw_route[3] ? io_slave_3_aw_ready : _GEN_7; // @[midas/src/main/scala/junctions/nasti.scala 368:{23,34}]
  wire  aw_ready = aw_noroute ? err_slave_io_aw_ready : _GEN_10; // @[midas/src/main/scala/junctions/nasti.scala 388:{20,31}]
  wire  w_noroute = ~(|w_queue_io_deq_bits); // @[midas/src/main/scala/junctions/nasti.scala 377:20]
  wire  _GEN_2 = w_queue_io_deq_bits[0] & io_slave_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 372:22 321:26 372:32]
  wire  _GEN_5 = w_queue_io_deq_bits[1] ? io_slave_1_w_ready : _GEN_2; // @[midas/src/main/scala/junctions/nasti.scala 372:{22,32}]
  wire  _GEN_8 = w_queue_io_deq_bits[2] ? io_slave_2_w_ready : _GEN_5; // @[midas/src/main/scala/junctions/nasti.scala 372:{22,32}]
  wire  _GEN_11 = w_queue_io_deq_bits[3] ? io_slave_3_w_ready : _GEN_8; // @[midas/src/main/scala/junctions/nasti.scala 372:{22,32}]
  wire  w_ready = w_noroute ? err_slave_io_w_ready : _GEN_11; // @[midas/src/main/scala/junctions/nasti.scala 389:{19,29}]
  wire  ar_valid = io_master_ar_valid & ar_queue_io_enq_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  wire  aw_valid = io_master_aw_valid & w_queue_io_enq_ready & aw_queue_io_enq_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  wire  w_valid = io_master_w_valid & w_queue_io_deq_valid; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  wire  _T_13 = ~aw_queue_io_deq_0_valid | aw_queue_io_deq_0_matches; // @[midas/src/main/scala/junctions/nasti.scala 414:33]
  wire  _T_15 = ~reset; // @[midas/src/main/scala/junctions/nasti.scala 413:11]
  wire  _T_18 = ~ar_queue_io_deq_0_valid | ar_queue_io_deq_0_matches; // @[midas/src/main/scala/junctions/nasti.scala 418:33]
  wire  _T_23 = ~aw_queue_io_deq_1_valid | aw_queue_io_deq_1_matches; // @[midas/src/main/scala/junctions/nasti.scala 414:33]
  wire  _T_28 = ~ar_queue_io_deq_1_valid | ar_queue_io_deq_1_matches; // @[midas/src/main/scala/junctions/nasti.scala 418:33]
  wire  _T_33 = ~aw_queue_io_deq_2_valid | aw_queue_io_deq_2_matches; // @[midas/src/main/scala/junctions/nasti.scala 414:33]
  wire  _T_38 = ~ar_queue_io_deq_2_valid | ar_queue_io_deq_2_matches; // @[midas/src/main/scala/junctions/nasti.scala 418:33]
  wire  _T_43 = ~aw_queue_io_deq_3_valid | aw_queue_io_deq_3_matches; // @[midas/src/main/scala/junctions/nasti.scala 414:33]
  wire  _T_48 = ~ar_queue_io_deq_3_valid | ar_queue_io_deq_3_matches; // @[midas/src/main/scala/junctions/nasti.scala 418:33]
  wire  _ar_queue_io_deq_4_valid_T = err_slave_io_r_ready & err_slave_io_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  wire  _T_53 = ~aw_queue_io_deq_4_valid | aw_queue_io_deq_4_matches; // @[midas/src/main/scala/junctions/nasti.scala 414:33]
  wire  _T_58 = ~ar_queue_io_deq_4_valid | ar_queue_io_deq_4_matches; // @[midas/src/main/scala/junctions/nasti.scala 418:33]
  ReorderQueue ar_queue ( // @[midas/src/main/scala/junctions/nasti.scala 327:24]
    .clock(ar_queue_clock),
    .reset(ar_queue_reset),
    .io_enq_ready(ar_queue_io_enq_ready),
    .io_enq_valid(ar_queue_io_enq_valid),
    .io_enq_bits_tag(ar_queue_io_enq_bits_tag),
    .io_deq_0_valid(ar_queue_io_deq_0_valid),
    .io_deq_0_tag(ar_queue_io_deq_0_tag),
    .io_deq_0_matches(ar_queue_io_deq_0_matches),
    .io_deq_1_valid(ar_queue_io_deq_1_valid),
    .io_deq_1_tag(ar_queue_io_deq_1_tag),
    .io_deq_1_matches(ar_queue_io_deq_1_matches),
    .io_deq_2_valid(ar_queue_io_deq_2_valid),
    .io_deq_2_tag(ar_queue_io_deq_2_tag),
    .io_deq_2_matches(ar_queue_io_deq_2_matches),
    .io_deq_3_valid(ar_queue_io_deq_3_valid),
    .io_deq_3_tag(ar_queue_io_deq_3_tag),
    .io_deq_3_matches(ar_queue_io_deq_3_matches),
    .io_deq_4_valid(ar_queue_io_deq_4_valid),
    .io_deq_4_tag(ar_queue_io_deq_4_tag),
    .io_deq_4_matches(ar_queue_io_deq_4_matches)
  );
  ReorderQueue aw_queue ( // @[midas/src/main/scala/junctions/nasti.scala 328:24]
    .clock(aw_queue_clock),
    .reset(aw_queue_reset),
    .io_enq_ready(aw_queue_io_enq_ready),
    .io_enq_valid(aw_queue_io_enq_valid),
    .io_enq_bits_tag(aw_queue_io_enq_bits_tag),
    .io_deq_0_valid(aw_queue_io_deq_0_valid),
    .io_deq_0_tag(aw_queue_io_deq_0_tag),
    .io_deq_0_matches(aw_queue_io_deq_0_matches),
    .io_deq_1_valid(aw_queue_io_deq_1_valid),
    .io_deq_1_tag(aw_queue_io_deq_1_tag),
    .io_deq_1_matches(aw_queue_io_deq_1_matches),
    .io_deq_2_valid(aw_queue_io_deq_2_valid),
    .io_deq_2_tag(aw_queue_io_deq_2_tag),
    .io_deq_2_matches(aw_queue_io_deq_2_matches),
    .io_deq_3_valid(aw_queue_io_deq_3_valid),
    .io_deq_3_tag(aw_queue_io_deq_3_tag),
    .io_deq_3_matches(aw_queue_io_deq_3_matches),
    .io_deq_4_valid(aw_queue_io_deq_4_valid),
    .io_deq_4_tag(aw_queue_io_deq_4_tag),
    .io_deq_4_matches(aw_queue_io_deq_4_matches)
  );
  Queue_2 w_queue ( // @[midas/src/main/scala/junctions/nasti.scala 330:24]
    .clock(w_queue_clock),
    .reset(w_queue_reset),
    .io_enq_ready(w_queue_io_enq_ready),
    .io_enq_valid(w_queue_io_enq_valid),
    .io_enq_bits(w_queue_io_enq_bits),
    .io_deq_ready(w_queue_io_deq_ready),
    .io_deq_valid(w_queue_io_deq_valid),
    .io_deq_bits(w_queue_io_deq_bits)
  );
  NastiErrorSlave err_slave ( // @[midas/src/main/scala/junctions/nasti.scala 379:25]
    .clock(err_slave_clock),
    .reset(err_slave_reset),
    .io_aw_ready(err_slave_io_aw_ready),
    .io_aw_valid(err_slave_io_aw_valid),
    .io_aw_bits_addr(err_slave_io_aw_bits_addr),
    .io_aw_bits_id(err_slave_io_aw_bits_id),
    .io_w_ready(err_slave_io_w_ready),
    .io_w_valid(err_slave_io_w_valid),
    .io_w_bits_last(err_slave_io_w_bits_last),
    .io_b_ready(err_slave_io_b_ready),
    .io_b_valid(err_slave_io_b_valid),
    .io_b_bits_id(err_slave_io_b_bits_id),
    .io_ar_ready(err_slave_io_ar_ready),
    .io_ar_valid(err_slave_io_ar_valid),
    .io_ar_bits_addr(err_slave_io_ar_bits_addr),
    .io_ar_bits_len(err_slave_io_ar_bits_len),
    .io_ar_bits_id(err_slave_io_ar_bits_id),
    .io_r_ready(err_slave_io_r_ready),
    .io_r_valid(err_slave_io_r_valid),
    .io_r_bits_last(err_slave_io_r_bits_last),
    .io_r_bits_id(err_slave_io_r_bits_id)
  );
  RRArbiter b_arb ( // @[midas/src/main/scala/junctions/nasti.scala 391:21]
    .clock(b_arb_clock),
    .io_in_0_ready(b_arb_io_in_0_ready),
    .io_in_0_valid(b_arb_io_in_0_valid),
    .io_in_0_bits_id(b_arb_io_in_0_bits_id),
    .io_in_1_ready(b_arb_io_in_1_ready),
    .io_in_1_valid(b_arb_io_in_1_valid),
    .io_in_1_bits_id(b_arb_io_in_1_bits_id),
    .io_in_2_ready(b_arb_io_in_2_ready),
    .io_in_2_valid(b_arb_io_in_2_valid),
    .io_in_2_bits_id(b_arb_io_in_2_bits_id),
    .io_in_3_ready(b_arb_io_in_3_ready),
    .io_in_3_valid(b_arb_io_in_3_valid),
    .io_in_3_bits_id(b_arb_io_in_3_bits_id),
    .io_in_4_ready(b_arb_io_in_4_ready),
    .io_in_4_valid(b_arb_io_in_4_valid),
    .io_in_4_bits_id(b_arb_io_in_4_bits_id),
    .io_out_ready(b_arb_io_out_ready),
    .io_out_valid(b_arb_io_out_valid),
    .io_out_bits_resp(b_arb_io_out_bits_resp),
    .io_out_bits_id(b_arb_io_out_bits_id),
    .io_chosen(b_arb_io_chosen)
  );
  HellaPeekingArbiter r_arb ( // @[midas/src/main/scala/junctions/nasti.scala 392:21]
    .clock(r_arb_clock),
    .reset(r_arb_reset),
    .io_in_0_ready(r_arb_io_in_0_ready),
    .io_in_0_valid(r_arb_io_in_0_valid),
    .io_in_0_bits_data(r_arb_io_in_0_bits_data),
    .io_in_0_bits_id(r_arb_io_in_0_bits_id),
    .io_in_1_ready(r_arb_io_in_1_ready),
    .io_in_1_valid(r_arb_io_in_1_valid),
    .io_in_1_bits_data(r_arb_io_in_1_bits_data),
    .io_in_1_bits_id(r_arb_io_in_1_bits_id),
    .io_in_2_ready(r_arb_io_in_2_ready),
    .io_in_2_valid(r_arb_io_in_2_valid),
    .io_in_2_bits_data(r_arb_io_in_2_bits_data),
    .io_in_2_bits_id(r_arb_io_in_2_bits_id),
    .io_in_3_ready(r_arb_io_in_3_ready),
    .io_in_3_valid(r_arb_io_in_3_valid),
    .io_in_3_bits_data(r_arb_io_in_3_bits_data),
    .io_in_3_bits_id(r_arb_io_in_3_bits_id),
    .io_in_4_ready(r_arb_io_in_4_ready),
    .io_in_4_valid(r_arb_io_in_4_valid),
    .io_in_4_bits_last(r_arb_io_in_4_bits_last),
    .io_in_4_bits_id(r_arb_io_in_4_bits_id),
    .io_out_ready(r_arb_io_out_ready),
    .io_out_valid(r_arb_io_out_valid),
    .io_out_bits_resp(r_arb_io_out_bits_resp),
    .io_out_bits_data(r_arb_io_out_bits_data),
    .io_out_bits_last(r_arb_io_out_bits_last),
    .io_out_bits_id(r_arb_io_out_bits_id)
  );
  assign io_master_aw_ready = w_queue_io_enq_ready & aw_queue_io_enq_ready & aw_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign io_master_w_ready = w_queue_io_deq_valid & w_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign io_master_b_valid = b_arb_io_out_valid; // @[midas/src/main/scala/junctions/nasti.scala 423:15]
  assign io_master_b_bits_resp = b_arb_io_out_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 423:15]
  assign io_master_b_bits_id = b_arb_io_out_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 423:15]
  assign io_master_ar_ready = ar_queue_io_enq_ready & ar_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign io_master_r_valid = r_arb_io_out_valid; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  assign io_master_r_bits_resp = r_arb_io_out_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  assign io_master_r_bits_data = r_arb_io_out_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  assign io_master_r_bits_last = r_arb_io_out_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  assign io_master_r_bits_id = r_arb_io_out_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  assign io_slave_0_aw_valid = aw_valid & aw_route[0]; // @[midas/src/main/scala/junctions/nasti.scala 366:28]
  assign io_slave_0_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_0_aw_bits_len = io_master_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_0_aw_bits_id = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_0_w_valid = w_valid & w_queue_io_deq_bits[0]; // @[midas/src/main/scala/junctions/nasti.scala 370:27]
  assign io_slave_0_w_bits_data = io_master_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 371:16]
  assign io_slave_0_b_ready = b_arb_io_in_0_ready; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign io_slave_0_ar_valid = ar_valid & ar_route[0]; // @[midas/src/main/scala/junctions/nasti.scala 362:28]
  assign io_slave_0_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_0_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_0_ar_bits_id = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_0_r_ready = r_arb_io_in_0_ready; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign io_slave_1_aw_valid = aw_valid & aw_route[1]; // @[midas/src/main/scala/junctions/nasti.scala 366:28]
  assign io_slave_1_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_1_aw_bits_len = io_master_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_1_aw_bits_id = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_1_w_valid = w_valid & w_queue_io_deq_bits[1]; // @[midas/src/main/scala/junctions/nasti.scala 370:27]
  assign io_slave_1_w_bits_data = io_master_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 371:16]
  assign io_slave_1_b_ready = b_arb_io_in_1_ready; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign io_slave_1_ar_valid = ar_valid & ar_route[1]; // @[midas/src/main/scala/junctions/nasti.scala 362:28]
  assign io_slave_1_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_1_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_1_ar_bits_id = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_1_r_ready = r_arb_io_in_1_ready; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign io_slave_2_aw_valid = aw_valid & aw_route[2]; // @[midas/src/main/scala/junctions/nasti.scala 366:28]
  assign io_slave_2_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_2_aw_bits_len = io_master_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_2_aw_bits_id = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_2_w_valid = w_valid & w_queue_io_deq_bits[2]; // @[midas/src/main/scala/junctions/nasti.scala 370:27]
  assign io_slave_2_w_bits_data = io_master_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 371:16]
  assign io_slave_2_b_ready = b_arb_io_in_2_ready; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign io_slave_2_ar_valid = ar_valid & ar_route[2]; // @[midas/src/main/scala/junctions/nasti.scala 362:28]
  assign io_slave_2_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_2_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_2_ar_bits_id = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_2_r_ready = r_arb_io_in_2_ready; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign io_slave_3_aw_valid = aw_valid & aw_route[3]; // @[midas/src/main/scala/junctions/nasti.scala 366:28]
  assign io_slave_3_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_3_aw_bits_len = io_master_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_3_aw_bits_id = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 367:16]
  assign io_slave_3_w_valid = w_valid & w_queue_io_deq_bits[3]; // @[midas/src/main/scala/junctions/nasti.scala 370:27]
  assign io_slave_3_w_bits_data = io_master_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 371:16]
  assign io_slave_3_b_ready = b_arb_io_in_3_ready; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign io_slave_3_ar_valid = ar_valid & ar_route[3]; // @[midas/src/main/scala/junctions/nasti.scala 362:28]
  assign io_slave_3_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_3_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_3_ar_bits_id = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 363:16]
  assign io_slave_3_r_ready = r_arb_io_in_3_ready; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign ar_queue_clock = clock;
  assign ar_queue_reset = reset;
  assign ar_queue_io_enq_valid = io_master_ar_valid & ar_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign ar_queue_io_enq_bits_tag = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 341:29]
  assign ar_queue_io_deq_0_valid = io_slave_0_r_ready & io_slave_0_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ar_queue_io_deq_0_tag = io_slave_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 411:30]
  assign ar_queue_io_deq_1_valid = io_slave_1_r_ready & io_slave_1_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ar_queue_io_deq_1_tag = io_slave_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 411:30]
  assign ar_queue_io_deq_2_valid = io_slave_2_r_ready & io_slave_2_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ar_queue_io_deq_2_tag = io_slave_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 411:30]
  assign ar_queue_io_deq_3_valid = io_slave_3_r_ready & io_slave_3_r_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign ar_queue_io_deq_3_tag = io_slave_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 411:30]
  assign ar_queue_io_deq_4_valid = _ar_queue_io_deq_4_valid_T & err_slave_io_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 410:54]
  assign ar_queue_io_deq_4_tag = err_slave_io_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 411:30]
  assign aw_queue_clock = clock;
  assign aw_queue_reset = reset;
  assign aw_queue_io_enq_valid = io_master_aw_valid & w_queue_io_enq_ready & aw_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign aw_queue_io_enq_bits_tag = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 345:29]
  assign aw_queue_io_deq_0_valid = io_slave_0_b_ready & io_slave_0_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign aw_queue_io_deq_0_tag = io_slave_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 407:30]
  assign aw_queue_io_deq_1_valid = io_slave_1_b_ready & io_slave_1_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign aw_queue_io_deq_1_tag = io_slave_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 407:30]
  assign aw_queue_io_deq_2_valid = io_slave_2_b_ready & io_slave_2_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign aw_queue_io_deq_2_tag = io_slave_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 407:30]
  assign aw_queue_io_deq_3_valid = io_slave_3_b_ready & io_slave_3_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign aw_queue_io_deq_3_tag = io_slave_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 407:30]
  assign aw_queue_io_deq_4_valid = err_slave_io_b_ready & err_slave_io_b_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  assign aw_queue_io_deq_4_tag = err_slave_io_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 407:30]
  assign w_queue_clock = clock;
  assign w_queue_reset = reset;
  assign w_queue_io_enq_valid = io_master_aw_valid & aw_queue_io_enq_ready & aw_ready; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign w_queue_io_enq_bits = {aw_route_hi,aw_route_lo}; // @[midas/src/main/scala/junctions/nasti.scala 482:37]
  assign w_queue_io_deq_ready = io_master_w_valid & w_ready & io_master_w_bits_last; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign err_slave_clock = clock;
  assign err_slave_reset = reset;
  assign err_slave_io_aw_valid = aw_valid & aw_noroute; // @[midas/src/main/scala/junctions/nasti.scala 382:37]
  assign err_slave_io_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 383:25]
  assign err_slave_io_aw_bits_id = io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 383:25]
  assign err_slave_io_w_valid = w_valid & w_noroute; // @[midas/src/main/scala/junctions/nasti.scala 384:36]
  assign err_slave_io_w_bits_last = io_master_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 385:25]
  assign err_slave_io_b_ready = b_arb_io_in_4_ready; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign err_slave_io_ar_valid = ar_valid & ar_noroute; // @[midas/src/main/scala/junctions/nasti.scala 380:37]
  assign err_slave_io_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 381:25]
  assign err_slave_io_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 381:25]
  assign err_slave_io_ar_bits_id = io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 381:25]
  assign err_slave_io_r_ready = r_arb_io_in_4_ready; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign b_arb_clock = clock;
  assign b_arb_io_in_0_valid = io_slave_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_0_bits_id = io_slave_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_1_valid = io_slave_1_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_1_bits_id = io_slave_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_2_valid = io_slave_2_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_2_bits_id = io_slave_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_3_valid = io_slave_3_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_3_bits_id = io_slave_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_4_valid = err_slave_io_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_in_4_bits_id = err_slave_io_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 405:30]
  assign b_arb_io_out_ready = io_master_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 423:15]
  assign r_arb_clock = clock;
  assign r_arb_reset = reset;
  assign r_arb_io_in_0_valid = io_slave_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_0_bits_data = io_slave_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_0_bits_id = io_slave_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_1_valid = io_slave_1_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_1_bits_data = io_slave_1_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_1_bits_id = io_slave_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_2_valid = io_slave_2_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_2_bits_data = io_slave_2_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_2_bits_id = io_slave_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_3_valid = io_slave_3_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_3_bits_data = io_slave_3_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_3_bits_id = io_slave_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_4_valid = err_slave_io_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_4_bits_last = err_slave_io_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_in_4_bits_id = err_slave_io_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 409:30]
  assign r_arb_io_out_ready = io_master_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 424:15]
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~_T_13) begin
          $fwrite(32'h80000002,
            "Assertion failed: aw_queue 0 tried to dequeue untracked transaction\n    at nasti.scala:413 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_15 & ~_T_18) begin
          $fwrite(32'h80000002,
            "Assertion failed: ar_queue 0 tried to dequeue untracked transaction\n    at nasti.scala:417 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~_T_23) begin
          $fwrite(32'h80000002,
            "Assertion failed: aw_queue 1 tried to dequeue untracked transaction\n    at nasti.scala:413 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_15 & ~_T_28) begin
          $fwrite(32'h80000002,
            "Assertion failed: ar_queue 1 tried to dequeue untracked transaction\n    at nasti.scala:417 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~_T_33) begin
          $fwrite(32'h80000002,
            "Assertion failed: aw_queue 2 tried to dequeue untracked transaction\n    at nasti.scala:413 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_15 & ~_T_38) begin
          $fwrite(32'h80000002,
            "Assertion failed: ar_queue 2 tried to dequeue untracked transaction\n    at nasti.scala:417 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~_T_43) begin
          $fwrite(32'h80000002,
            "Assertion failed: aw_queue 3 tried to dequeue untracked transaction\n    at nasti.scala:413 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_15 & ~_T_48) begin
          $fwrite(32'h80000002,
            "Assertion failed: ar_queue 3 tried to dequeue untracked transaction\n    at nasti.scala:417 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~_T_53) begin
          $fwrite(32'h80000002,
            "Assertion failed: aw_queue 4 tried to dequeue untracked transaction\n    at nasti.scala:413 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_15 & ~_T_58) begin
          $fwrite(32'h80000002,
            "Assertion failed: ar_queue 4 tried to dequeue untracked transaction\n    at nasti.scala:417 assert(\n"); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(_T_13); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
    end
    //
    if (_T_15) begin
      assert(_T_18); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
    end
    //
    if (~reset) begin
      assert(_T_23); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
    end
    //
    if (_T_15) begin
      assert(_T_28); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
    end
    //
    if (~reset) begin
      assert(_T_33); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
    end
    //
    if (_T_15) begin
      assert(_T_38); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
    end
    //
    if (~reset) begin
      assert(_T_43); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
    end
    //
    if (_T_15) begin
      assert(_T_48); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
    end
    //
    if (~reset) begin
      assert(_T_53); // @[midas/src/main/scala/junctions/nasti.scala 413:11]
    end
    //
    if (_T_15) begin
      assert(_T_58); // @[midas/src/main/scala/junctions/nasti.scala 417:11]
    end
  end
endmodule
module NastiCrossbar(
  input         clock,
  input         reset,
  output        io_masters_0_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [24:0] io_masters_0_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [7:0]  io_masters_0_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_masters_0_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_masters_0_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [31:0] io_masters_0_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_w_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_masters_0_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [1:0]  io_masters_0_b_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_masters_0_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_masters_0_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [24:0] io_masters_0_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [7:0]  io_masters_0_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_masters_0_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_masters_0_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_masters_0_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [1:0]  io_masters_0_r_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [31:0] io_masters_0_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_masters_0_r_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_masters_0_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_0_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_0_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_0_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_0_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_0_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_0_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_0_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [31:0] io_slaves_0_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_0_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_0_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_0_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_0_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_0_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_0_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_0_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_0_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_0_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_0_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [31:0] io_slaves_0_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_0_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_1_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_1_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_1_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_1_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_1_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_1_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_1_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [31:0] io_slaves_1_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_1_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_1_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_1_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_1_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_1_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_1_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_1_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_1_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_1_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_1_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [31:0] io_slaves_1_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_1_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_2_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_2_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_2_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_2_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_2_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_2_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_2_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [31:0] io_slaves_2_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_2_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_2_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_2_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_2_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_2_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_2_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_2_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_2_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_2_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_2_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [31:0] io_slaves_2_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_2_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_3_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_3_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_3_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_3_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_3_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_3_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_3_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [31:0] io_slaves_3_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_3_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_3_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_3_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_3_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_3_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [24:0] io_slaves_3_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [7:0]  io_slaves_3_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output [11:0] io_slaves_3_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  output        io_slaves_3_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input         io_slaves_3_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [31:0] io_slaves_3_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 437:14]
  input  [11:0] io_slaves_3_r_bits_id // @[midas/src/main/scala/junctions/nasti.scala 437:14]
);
  wire  router_clock; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_reset; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_master_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_master_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_master_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_master_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [1:0] router_io_master_b_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_master_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_master_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_master_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_master_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [1:0] router_io_master_r_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_master_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_master_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_master_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_1_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_1_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_1_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_1_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_1_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_1_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_1_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_1_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_1_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_2_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_2_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_2_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_2_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_2_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_2_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_2_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_2_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_2_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_3_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_3_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_3_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_3_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [24:0] router_io_slave_3_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [7:0] router_io_slave_3_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_3_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire  router_io_slave_3_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [31:0] router_io_slave_3_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  wire [11:0] router_io_slave_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 443:24]
  NastiRouter router ( // @[midas/src/main/scala/junctions/nasti.scala 443:24]
    .clock(router_clock),
    .reset(router_reset),
    .io_master_aw_ready(router_io_master_aw_ready),
    .io_master_aw_valid(router_io_master_aw_valid),
    .io_master_aw_bits_addr(router_io_master_aw_bits_addr),
    .io_master_aw_bits_len(router_io_master_aw_bits_len),
    .io_master_aw_bits_id(router_io_master_aw_bits_id),
    .io_master_w_ready(router_io_master_w_ready),
    .io_master_w_valid(router_io_master_w_valid),
    .io_master_w_bits_data(router_io_master_w_bits_data),
    .io_master_w_bits_last(router_io_master_w_bits_last),
    .io_master_b_ready(router_io_master_b_ready),
    .io_master_b_valid(router_io_master_b_valid),
    .io_master_b_bits_resp(router_io_master_b_bits_resp),
    .io_master_b_bits_id(router_io_master_b_bits_id),
    .io_master_ar_ready(router_io_master_ar_ready),
    .io_master_ar_valid(router_io_master_ar_valid),
    .io_master_ar_bits_addr(router_io_master_ar_bits_addr),
    .io_master_ar_bits_len(router_io_master_ar_bits_len),
    .io_master_ar_bits_id(router_io_master_ar_bits_id),
    .io_master_r_ready(router_io_master_r_ready),
    .io_master_r_valid(router_io_master_r_valid),
    .io_master_r_bits_resp(router_io_master_r_bits_resp),
    .io_master_r_bits_data(router_io_master_r_bits_data),
    .io_master_r_bits_last(router_io_master_r_bits_last),
    .io_master_r_bits_id(router_io_master_r_bits_id),
    .io_slave_0_aw_ready(router_io_slave_0_aw_ready),
    .io_slave_0_aw_valid(router_io_slave_0_aw_valid),
    .io_slave_0_aw_bits_addr(router_io_slave_0_aw_bits_addr),
    .io_slave_0_aw_bits_len(router_io_slave_0_aw_bits_len),
    .io_slave_0_aw_bits_id(router_io_slave_0_aw_bits_id),
    .io_slave_0_w_ready(router_io_slave_0_w_ready),
    .io_slave_0_w_valid(router_io_slave_0_w_valid),
    .io_slave_0_w_bits_data(router_io_slave_0_w_bits_data),
    .io_slave_0_b_ready(router_io_slave_0_b_ready),
    .io_slave_0_b_valid(router_io_slave_0_b_valid),
    .io_slave_0_b_bits_id(router_io_slave_0_b_bits_id),
    .io_slave_0_ar_ready(router_io_slave_0_ar_ready),
    .io_slave_0_ar_valid(router_io_slave_0_ar_valid),
    .io_slave_0_ar_bits_addr(router_io_slave_0_ar_bits_addr),
    .io_slave_0_ar_bits_len(router_io_slave_0_ar_bits_len),
    .io_slave_0_ar_bits_id(router_io_slave_0_ar_bits_id),
    .io_slave_0_r_ready(router_io_slave_0_r_ready),
    .io_slave_0_r_valid(router_io_slave_0_r_valid),
    .io_slave_0_r_bits_data(router_io_slave_0_r_bits_data),
    .io_slave_0_r_bits_id(router_io_slave_0_r_bits_id),
    .io_slave_1_aw_ready(router_io_slave_1_aw_ready),
    .io_slave_1_aw_valid(router_io_slave_1_aw_valid),
    .io_slave_1_aw_bits_addr(router_io_slave_1_aw_bits_addr),
    .io_slave_1_aw_bits_len(router_io_slave_1_aw_bits_len),
    .io_slave_1_aw_bits_id(router_io_slave_1_aw_bits_id),
    .io_slave_1_w_ready(router_io_slave_1_w_ready),
    .io_slave_1_w_valid(router_io_slave_1_w_valid),
    .io_slave_1_w_bits_data(router_io_slave_1_w_bits_data),
    .io_slave_1_b_ready(router_io_slave_1_b_ready),
    .io_slave_1_b_valid(router_io_slave_1_b_valid),
    .io_slave_1_b_bits_id(router_io_slave_1_b_bits_id),
    .io_slave_1_ar_ready(router_io_slave_1_ar_ready),
    .io_slave_1_ar_valid(router_io_slave_1_ar_valid),
    .io_slave_1_ar_bits_addr(router_io_slave_1_ar_bits_addr),
    .io_slave_1_ar_bits_len(router_io_slave_1_ar_bits_len),
    .io_slave_1_ar_bits_id(router_io_slave_1_ar_bits_id),
    .io_slave_1_r_ready(router_io_slave_1_r_ready),
    .io_slave_1_r_valid(router_io_slave_1_r_valid),
    .io_slave_1_r_bits_data(router_io_slave_1_r_bits_data),
    .io_slave_1_r_bits_id(router_io_slave_1_r_bits_id),
    .io_slave_2_aw_ready(router_io_slave_2_aw_ready),
    .io_slave_2_aw_valid(router_io_slave_2_aw_valid),
    .io_slave_2_aw_bits_addr(router_io_slave_2_aw_bits_addr),
    .io_slave_2_aw_bits_len(router_io_slave_2_aw_bits_len),
    .io_slave_2_aw_bits_id(router_io_slave_2_aw_bits_id),
    .io_slave_2_w_ready(router_io_slave_2_w_ready),
    .io_slave_2_w_valid(router_io_slave_2_w_valid),
    .io_slave_2_w_bits_data(router_io_slave_2_w_bits_data),
    .io_slave_2_b_ready(router_io_slave_2_b_ready),
    .io_slave_2_b_valid(router_io_slave_2_b_valid),
    .io_slave_2_b_bits_id(router_io_slave_2_b_bits_id),
    .io_slave_2_ar_ready(router_io_slave_2_ar_ready),
    .io_slave_2_ar_valid(router_io_slave_2_ar_valid),
    .io_slave_2_ar_bits_addr(router_io_slave_2_ar_bits_addr),
    .io_slave_2_ar_bits_len(router_io_slave_2_ar_bits_len),
    .io_slave_2_ar_bits_id(router_io_slave_2_ar_bits_id),
    .io_slave_2_r_ready(router_io_slave_2_r_ready),
    .io_slave_2_r_valid(router_io_slave_2_r_valid),
    .io_slave_2_r_bits_data(router_io_slave_2_r_bits_data),
    .io_slave_2_r_bits_id(router_io_slave_2_r_bits_id),
    .io_slave_3_aw_ready(router_io_slave_3_aw_ready),
    .io_slave_3_aw_valid(router_io_slave_3_aw_valid),
    .io_slave_3_aw_bits_addr(router_io_slave_3_aw_bits_addr),
    .io_slave_3_aw_bits_len(router_io_slave_3_aw_bits_len),
    .io_slave_3_aw_bits_id(router_io_slave_3_aw_bits_id),
    .io_slave_3_w_ready(router_io_slave_3_w_ready),
    .io_slave_3_w_valid(router_io_slave_3_w_valid),
    .io_slave_3_w_bits_data(router_io_slave_3_w_bits_data),
    .io_slave_3_b_ready(router_io_slave_3_b_ready),
    .io_slave_3_b_valid(router_io_slave_3_b_valid),
    .io_slave_3_b_bits_id(router_io_slave_3_b_bits_id),
    .io_slave_3_ar_ready(router_io_slave_3_ar_ready),
    .io_slave_3_ar_valid(router_io_slave_3_ar_valid),
    .io_slave_3_ar_bits_addr(router_io_slave_3_ar_bits_addr),
    .io_slave_3_ar_bits_len(router_io_slave_3_ar_bits_len),
    .io_slave_3_ar_bits_id(router_io_slave_3_ar_bits_id),
    .io_slave_3_r_ready(router_io_slave_3_r_ready),
    .io_slave_3_r_valid(router_io_slave_3_r_valid),
    .io_slave_3_r_bits_data(router_io_slave_3_r_bits_data),
    .io_slave_3_r_bits_id(router_io_slave_3_r_bits_id)
  );
  assign io_masters_0_aw_ready = router_io_master_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_w_ready = router_io_master_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_b_valid = router_io_master_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_b_bits_resp = router_io_master_b_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_b_bits_id = router_io_master_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_ar_ready = router_io_master_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_r_valid = router_io_master_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_r_bits_resp = router_io_master_r_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_r_bits_data = router_io_master_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_r_bits_last = router_io_master_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_masters_0_r_bits_id = router_io_master_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign io_slaves_0_aw_valid = router_io_slave_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_aw_bits_addr = router_io_slave_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_aw_bits_len = router_io_slave_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_aw_bits_id = router_io_slave_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_w_valid = router_io_slave_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_w_bits_data = router_io_slave_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_b_ready = router_io_slave_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_ar_valid = router_io_slave_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_ar_bits_addr = router_io_slave_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_ar_bits_len = router_io_slave_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_ar_bits_id = router_io_slave_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_0_r_ready = router_io_slave_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_aw_valid = router_io_slave_1_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_aw_bits_addr = router_io_slave_1_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_aw_bits_len = router_io_slave_1_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_aw_bits_id = router_io_slave_1_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_w_valid = router_io_slave_1_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_w_bits_data = router_io_slave_1_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_b_ready = router_io_slave_1_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_ar_valid = router_io_slave_1_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_ar_bits_addr = router_io_slave_1_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_ar_bits_len = router_io_slave_1_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_ar_bits_id = router_io_slave_1_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_1_r_ready = router_io_slave_1_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_aw_valid = router_io_slave_2_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_aw_bits_addr = router_io_slave_2_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_aw_bits_len = router_io_slave_2_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_aw_bits_id = router_io_slave_2_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_w_valid = router_io_slave_2_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_w_bits_data = router_io_slave_2_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_b_ready = router_io_slave_2_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_ar_valid = router_io_slave_2_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_ar_bits_addr = router_io_slave_2_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_ar_bits_len = router_io_slave_2_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_ar_bits_id = router_io_slave_2_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_2_r_ready = router_io_slave_2_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_aw_valid = router_io_slave_3_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_aw_bits_addr = router_io_slave_3_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_aw_bits_len = router_io_slave_3_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_aw_bits_id = router_io_slave_3_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_w_valid = router_io_slave_3_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_w_bits_data = router_io_slave_3_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_b_ready = router_io_slave_3_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_ar_valid = router_io_slave_3_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_ar_bits_addr = router_io_slave_3_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_ar_bits_len = router_io_slave_3_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_ar_bits_id = router_io_slave_3_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign io_slaves_3_r_ready = router_io_slave_3_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_clock = clock;
  assign router_reset = reset;
  assign router_io_master_aw_valid = io_masters_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_aw_bits_addr = io_masters_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_aw_bits_len = io_masters_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_aw_bits_id = io_masters_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_w_valid = io_masters_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_w_bits_data = io_masters_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_w_bits_last = io_masters_0_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_b_ready = io_masters_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_ar_valid = io_masters_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_ar_bits_addr = io_masters_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_ar_bits_len = io_masters_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_ar_bits_id = io_masters_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_master_r_ready = io_masters_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 444:22]
  assign router_io_slave_0_aw_ready = io_slaves_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_w_ready = io_slaves_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_b_valid = io_slaves_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_b_bits_id = io_slaves_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_ar_ready = io_slaves_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_r_valid = io_slaves_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_r_bits_data = io_slaves_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_0_r_bits_id = io_slaves_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_aw_ready = io_slaves_1_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_w_ready = io_slaves_1_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_b_valid = io_slaves_1_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_b_bits_id = io_slaves_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_ar_ready = io_slaves_1_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_r_valid = io_slaves_1_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_r_bits_data = io_slaves_1_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_1_r_bits_id = io_slaves_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_aw_ready = io_slaves_2_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_w_ready = io_slaves_2_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_b_valid = io_slaves_2_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_b_bits_id = io_slaves_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_ar_ready = io_slaves_2_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_r_valid = io_slaves_2_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_r_bits_data = io_slaves_2_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_2_r_bits_id = io_slaves_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_aw_ready = io_slaves_3_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_w_ready = io_slaves_3_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_b_valid = io_slaves_3_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_b_bits_id = io_slaves_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_ar_ready = io_slaves_3_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_r_valid = io_slaves_3_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_r_bits_data = io_slaves_3_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
  assign router_io_slave_3_r_bits_id = io_slaves_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 445:22]
endmodule
module NastiRecursiveInterconnect(
  input         clock,
  input         reset,
  output        io_masters_0_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [24:0] io_masters_0_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [7:0]  io_masters_0_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_masters_0_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_masters_0_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [31:0] io_masters_0_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_w_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_masters_0_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [1:0]  io_masters_0_b_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_masters_0_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_masters_0_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [24:0] io_masters_0_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [7:0]  io_masters_0_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_masters_0_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_masters_0_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_masters_0_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [1:0]  io_masters_0_r_bits_resp, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [31:0] io_masters_0_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_masters_0_r_bits_last, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_masters_0_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_0_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_0_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_0_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_0_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_0_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_0_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_0_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [31:0] io_slaves_0_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_0_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_0_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_0_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_0_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_0_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_0_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_0_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_0_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_0_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_0_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [31:0] io_slaves_0_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_0_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_1_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_1_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_1_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_1_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_1_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_1_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_1_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [31:0] io_slaves_1_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_1_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_1_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_1_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_1_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_1_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_1_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_1_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_1_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_1_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_1_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [31:0] io_slaves_1_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_1_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_2_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_2_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_2_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_2_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_2_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_2_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_2_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [31:0] io_slaves_2_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_2_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_2_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_2_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_2_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_2_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_2_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_2_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_2_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_2_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_2_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [31:0] io_slaves_2_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_2_r_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_3_aw_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_3_aw_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_3_aw_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_3_aw_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_3_aw_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_3_w_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_3_w_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [31:0] io_slaves_3_w_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_3_b_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_3_b_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_3_b_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_3_ar_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_3_ar_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [24:0] io_slaves_3_ar_bits_addr, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [7:0]  io_slaves_3_ar_bits_len, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output [11:0] io_slaves_3_ar_bits_id, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  output        io_slaves_3_r_ready, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input         io_slaves_3_r_valid, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [31:0] io_slaves_3_r_bits_data, // @[midas/src/main/scala/junctions/nasti.scala 472:19]
  input  [11:0] io_slaves_3_r_bits_id // @[midas/src/main/scala/junctions/nasti.scala 472:19]
);
  wire  xbar_clock; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_reset; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_masters_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_masters_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_masters_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_masters_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [1:0] xbar_io_masters_0_b_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_masters_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_masters_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_masters_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_masters_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [1:0] xbar_io_masters_0_r_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_masters_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_masters_0_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_masters_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_1_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_1_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_1_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_1_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_1_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_1_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_1_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_1_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_1_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_2_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_2_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_2_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_2_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_2_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_2_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_2_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_2_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_2_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_3_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_3_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_3_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_3_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [24:0] xbar_io_slaves_3_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [7:0] xbar_io_slaves_3_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_3_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire  xbar_io_slaves_3_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [31:0] xbar_io_slaves_3_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  wire [11:0] xbar_io_slaves_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 484:20]
  NastiCrossbar xbar ( // @[midas/src/main/scala/junctions/nasti.scala 484:20]
    .clock(xbar_clock),
    .reset(xbar_reset),
    .io_masters_0_aw_ready(xbar_io_masters_0_aw_ready),
    .io_masters_0_aw_valid(xbar_io_masters_0_aw_valid),
    .io_masters_0_aw_bits_addr(xbar_io_masters_0_aw_bits_addr),
    .io_masters_0_aw_bits_len(xbar_io_masters_0_aw_bits_len),
    .io_masters_0_aw_bits_id(xbar_io_masters_0_aw_bits_id),
    .io_masters_0_w_ready(xbar_io_masters_0_w_ready),
    .io_masters_0_w_valid(xbar_io_masters_0_w_valid),
    .io_masters_0_w_bits_data(xbar_io_masters_0_w_bits_data),
    .io_masters_0_w_bits_last(xbar_io_masters_0_w_bits_last),
    .io_masters_0_b_ready(xbar_io_masters_0_b_ready),
    .io_masters_0_b_valid(xbar_io_masters_0_b_valid),
    .io_masters_0_b_bits_resp(xbar_io_masters_0_b_bits_resp),
    .io_masters_0_b_bits_id(xbar_io_masters_0_b_bits_id),
    .io_masters_0_ar_ready(xbar_io_masters_0_ar_ready),
    .io_masters_0_ar_valid(xbar_io_masters_0_ar_valid),
    .io_masters_0_ar_bits_addr(xbar_io_masters_0_ar_bits_addr),
    .io_masters_0_ar_bits_len(xbar_io_masters_0_ar_bits_len),
    .io_masters_0_ar_bits_id(xbar_io_masters_0_ar_bits_id),
    .io_masters_0_r_ready(xbar_io_masters_0_r_ready),
    .io_masters_0_r_valid(xbar_io_masters_0_r_valid),
    .io_masters_0_r_bits_resp(xbar_io_masters_0_r_bits_resp),
    .io_masters_0_r_bits_data(xbar_io_masters_0_r_bits_data),
    .io_masters_0_r_bits_last(xbar_io_masters_0_r_bits_last),
    .io_masters_0_r_bits_id(xbar_io_masters_0_r_bits_id),
    .io_slaves_0_aw_ready(xbar_io_slaves_0_aw_ready),
    .io_slaves_0_aw_valid(xbar_io_slaves_0_aw_valid),
    .io_slaves_0_aw_bits_addr(xbar_io_slaves_0_aw_bits_addr),
    .io_slaves_0_aw_bits_len(xbar_io_slaves_0_aw_bits_len),
    .io_slaves_0_aw_bits_id(xbar_io_slaves_0_aw_bits_id),
    .io_slaves_0_w_ready(xbar_io_slaves_0_w_ready),
    .io_slaves_0_w_valid(xbar_io_slaves_0_w_valid),
    .io_slaves_0_w_bits_data(xbar_io_slaves_0_w_bits_data),
    .io_slaves_0_b_ready(xbar_io_slaves_0_b_ready),
    .io_slaves_0_b_valid(xbar_io_slaves_0_b_valid),
    .io_slaves_0_b_bits_id(xbar_io_slaves_0_b_bits_id),
    .io_slaves_0_ar_ready(xbar_io_slaves_0_ar_ready),
    .io_slaves_0_ar_valid(xbar_io_slaves_0_ar_valid),
    .io_slaves_0_ar_bits_addr(xbar_io_slaves_0_ar_bits_addr),
    .io_slaves_0_ar_bits_len(xbar_io_slaves_0_ar_bits_len),
    .io_slaves_0_ar_bits_id(xbar_io_slaves_0_ar_bits_id),
    .io_slaves_0_r_ready(xbar_io_slaves_0_r_ready),
    .io_slaves_0_r_valid(xbar_io_slaves_0_r_valid),
    .io_slaves_0_r_bits_data(xbar_io_slaves_0_r_bits_data),
    .io_slaves_0_r_bits_id(xbar_io_slaves_0_r_bits_id),
    .io_slaves_1_aw_ready(xbar_io_slaves_1_aw_ready),
    .io_slaves_1_aw_valid(xbar_io_slaves_1_aw_valid),
    .io_slaves_1_aw_bits_addr(xbar_io_slaves_1_aw_bits_addr),
    .io_slaves_1_aw_bits_len(xbar_io_slaves_1_aw_bits_len),
    .io_slaves_1_aw_bits_id(xbar_io_slaves_1_aw_bits_id),
    .io_slaves_1_w_ready(xbar_io_slaves_1_w_ready),
    .io_slaves_1_w_valid(xbar_io_slaves_1_w_valid),
    .io_slaves_1_w_bits_data(xbar_io_slaves_1_w_bits_data),
    .io_slaves_1_b_ready(xbar_io_slaves_1_b_ready),
    .io_slaves_1_b_valid(xbar_io_slaves_1_b_valid),
    .io_slaves_1_b_bits_id(xbar_io_slaves_1_b_bits_id),
    .io_slaves_1_ar_ready(xbar_io_slaves_1_ar_ready),
    .io_slaves_1_ar_valid(xbar_io_slaves_1_ar_valid),
    .io_slaves_1_ar_bits_addr(xbar_io_slaves_1_ar_bits_addr),
    .io_slaves_1_ar_bits_len(xbar_io_slaves_1_ar_bits_len),
    .io_slaves_1_ar_bits_id(xbar_io_slaves_1_ar_bits_id),
    .io_slaves_1_r_ready(xbar_io_slaves_1_r_ready),
    .io_slaves_1_r_valid(xbar_io_slaves_1_r_valid),
    .io_slaves_1_r_bits_data(xbar_io_slaves_1_r_bits_data),
    .io_slaves_1_r_bits_id(xbar_io_slaves_1_r_bits_id),
    .io_slaves_2_aw_ready(xbar_io_slaves_2_aw_ready),
    .io_slaves_2_aw_valid(xbar_io_slaves_2_aw_valid),
    .io_slaves_2_aw_bits_addr(xbar_io_slaves_2_aw_bits_addr),
    .io_slaves_2_aw_bits_len(xbar_io_slaves_2_aw_bits_len),
    .io_slaves_2_aw_bits_id(xbar_io_slaves_2_aw_bits_id),
    .io_slaves_2_w_ready(xbar_io_slaves_2_w_ready),
    .io_slaves_2_w_valid(xbar_io_slaves_2_w_valid),
    .io_slaves_2_w_bits_data(xbar_io_slaves_2_w_bits_data),
    .io_slaves_2_b_ready(xbar_io_slaves_2_b_ready),
    .io_slaves_2_b_valid(xbar_io_slaves_2_b_valid),
    .io_slaves_2_b_bits_id(xbar_io_slaves_2_b_bits_id),
    .io_slaves_2_ar_ready(xbar_io_slaves_2_ar_ready),
    .io_slaves_2_ar_valid(xbar_io_slaves_2_ar_valid),
    .io_slaves_2_ar_bits_addr(xbar_io_slaves_2_ar_bits_addr),
    .io_slaves_2_ar_bits_len(xbar_io_slaves_2_ar_bits_len),
    .io_slaves_2_ar_bits_id(xbar_io_slaves_2_ar_bits_id),
    .io_slaves_2_r_ready(xbar_io_slaves_2_r_ready),
    .io_slaves_2_r_valid(xbar_io_slaves_2_r_valid),
    .io_slaves_2_r_bits_data(xbar_io_slaves_2_r_bits_data),
    .io_slaves_2_r_bits_id(xbar_io_slaves_2_r_bits_id),
    .io_slaves_3_aw_ready(xbar_io_slaves_3_aw_ready),
    .io_slaves_3_aw_valid(xbar_io_slaves_3_aw_valid),
    .io_slaves_3_aw_bits_addr(xbar_io_slaves_3_aw_bits_addr),
    .io_slaves_3_aw_bits_len(xbar_io_slaves_3_aw_bits_len),
    .io_slaves_3_aw_bits_id(xbar_io_slaves_3_aw_bits_id),
    .io_slaves_3_w_ready(xbar_io_slaves_3_w_ready),
    .io_slaves_3_w_valid(xbar_io_slaves_3_w_valid),
    .io_slaves_3_w_bits_data(xbar_io_slaves_3_w_bits_data),
    .io_slaves_3_b_ready(xbar_io_slaves_3_b_ready),
    .io_slaves_3_b_valid(xbar_io_slaves_3_b_valid),
    .io_slaves_3_b_bits_id(xbar_io_slaves_3_b_bits_id),
    .io_slaves_3_ar_ready(xbar_io_slaves_3_ar_ready),
    .io_slaves_3_ar_valid(xbar_io_slaves_3_ar_valid),
    .io_slaves_3_ar_bits_addr(xbar_io_slaves_3_ar_bits_addr),
    .io_slaves_3_ar_bits_len(xbar_io_slaves_3_ar_bits_len),
    .io_slaves_3_ar_bits_id(xbar_io_slaves_3_ar_bits_id),
    .io_slaves_3_r_ready(xbar_io_slaves_3_r_ready),
    .io_slaves_3_r_valid(xbar_io_slaves_3_r_valid),
    .io_slaves_3_r_bits_data(xbar_io_slaves_3_r_bits_data),
    .io_slaves_3_r_bits_id(xbar_io_slaves_3_r_bits_id)
  );
  assign io_masters_0_aw_ready = xbar_io_masters_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_w_ready = xbar_io_masters_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_b_valid = xbar_io_masters_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_b_bits_resp = xbar_io_masters_0_b_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_b_bits_id = xbar_io_masters_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_ar_ready = xbar_io_masters_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_r_valid = xbar_io_masters_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_r_bits_resp = xbar_io_masters_0_r_bits_resp; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_r_bits_data = xbar_io_masters_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_r_bits_last = xbar_io_masters_0_r_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_masters_0_r_bits_id = xbar_io_masters_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign io_slaves_0_aw_valid = xbar_io_slaves_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_aw_bits_addr = xbar_io_slaves_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_aw_bits_len = xbar_io_slaves_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_aw_bits_id = xbar_io_slaves_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_w_valid = xbar_io_slaves_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_w_bits_data = xbar_io_slaves_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_b_ready = xbar_io_slaves_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_ar_valid = xbar_io_slaves_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_ar_bits_addr = xbar_io_slaves_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_ar_bits_len = xbar_io_slaves_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_ar_bits_id = xbar_io_slaves_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_0_r_ready = xbar_io_slaves_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_aw_valid = xbar_io_slaves_1_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_aw_bits_addr = xbar_io_slaves_1_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_aw_bits_len = xbar_io_slaves_1_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_aw_bits_id = xbar_io_slaves_1_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_w_valid = xbar_io_slaves_1_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_w_bits_data = xbar_io_slaves_1_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_b_ready = xbar_io_slaves_1_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_ar_valid = xbar_io_slaves_1_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_ar_bits_addr = xbar_io_slaves_1_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_ar_bits_len = xbar_io_slaves_1_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_ar_bits_id = xbar_io_slaves_1_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_1_r_ready = xbar_io_slaves_1_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_aw_valid = xbar_io_slaves_2_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_aw_bits_addr = xbar_io_slaves_2_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_aw_bits_len = xbar_io_slaves_2_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_aw_bits_id = xbar_io_slaves_2_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_w_valid = xbar_io_slaves_2_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_w_bits_data = xbar_io_slaves_2_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_b_ready = xbar_io_slaves_2_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_ar_valid = xbar_io_slaves_2_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_ar_bits_addr = xbar_io_slaves_2_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_ar_bits_len = xbar_io_slaves_2_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_ar_bits_id = xbar_io_slaves_2_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_2_r_ready = xbar_io_slaves_2_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_aw_valid = xbar_io_slaves_3_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_aw_bits_addr = xbar_io_slaves_3_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_aw_bits_len = xbar_io_slaves_3_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_aw_bits_id = xbar_io_slaves_3_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_w_valid = xbar_io_slaves_3_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_w_bits_data = xbar_io_slaves_3_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_b_ready = xbar_io_slaves_3_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_ar_valid = xbar_io_slaves_3_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_ar_bits_addr = xbar_io_slaves_3_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_ar_bits_len = xbar_io_slaves_3_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_ar_bits_id = xbar_io_slaves_3_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign io_slaves_3_r_ready = xbar_io_slaves_3_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_clock = clock;
  assign xbar_reset = reset;
  assign xbar_io_masters_0_aw_valid = io_masters_0_aw_valid; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_aw_bits_addr = io_masters_0_aw_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_aw_bits_len = io_masters_0_aw_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_aw_bits_id = io_masters_0_aw_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_w_valid = io_masters_0_w_valid; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_w_bits_data = io_masters_0_w_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_w_bits_last = io_masters_0_w_bits_last; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_b_ready = io_masters_0_b_ready; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_ar_valid = io_masters_0_ar_valid; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_ar_bits_addr = io_masters_0_ar_bits_addr; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_ar_bits_len = io_masters_0_ar_bits_len; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_ar_bits_id = io_masters_0_ar_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_masters_0_r_ready = io_masters_0_r_ready; // @[midas/src/main/scala/junctions/nasti.scala 485:19]
  assign xbar_io_slaves_0_aw_ready = io_slaves_0_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_w_ready = io_slaves_0_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_b_valid = io_slaves_0_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_b_bits_id = io_slaves_0_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_ar_ready = io_slaves_0_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_r_valid = io_slaves_0_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_r_bits_data = io_slaves_0_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_0_r_bits_id = io_slaves_0_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_aw_ready = io_slaves_1_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_w_ready = io_slaves_1_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_b_valid = io_slaves_1_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_b_bits_id = io_slaves_1_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_ar_ready = io_slaves_1_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_r_valid = io_slaves_1_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_r_bits_data = io_slaves_1_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_1_r_bits_id = io_slaves_1_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_aw_ready = io_slaves_2_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_w_ready = io_slaves_2_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_b_valid = io_slaves_2_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_b_bits_id = io_slaves_2_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_ar_ready = io_slaves_2_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_r_valid = io_slaves_2_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_r_bits_data = io_slaves_2_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_2_r_bits_id = io_slaves_2_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_aw_ready = io_slaves_3_aw_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_w_ready = io_slaves_3_w_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_b_valid = io_slaves_3_b_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_b_bits_id = io_slaves_3_b_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_ar_ready = io_slaves_3_ar_ready; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_r_valid = io_slaves_3_r_valid; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_r_bits_data = io_slaves_3_r_bits_data; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
  assign xbar_io_slaves_3_r_bits_id = io_slaves_3_r_bits_id; // @[midas/src/main/scala/junctions/nasti.scala 487:13]
endmodule
module FPGATop(
  input         clock,
  input         reset,
  output        ctrl_aw_ready, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_aw_valid, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [24:0] ctrl_aw_bits_addr, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [7:0]  ctrl_aw_bits_len, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [2:0]  ctrl_aw_bits_size, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [1:0]  ctrl_aw_bits_burst, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_aw_bits_lock, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_aw_bits_cache, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [2:0]  ctrl_aw_bits_prot, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_aw_bits_qos, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_aw_bits_region, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [11:0] ctrl_aw_bits_id, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_aw_bits_user, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_w_ready, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_w_valid, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [31:0] ctrl_w_bits_data, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_w_bits_last, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [11:0] ctrl_w_bits_id, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_w_bits_strb, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_w_bits_user, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_b_ready, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_b_valid, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output [1:0]  ctrl_b_bits_resp, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output [11:0] ctrl_b_bits_id, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_b_bits_user, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_ar_ready, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_ar_valid, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [24:0] ctrl_ar_bits_addr, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [7:0]  ctrl_ar_bits_len, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [2:0]  ctrl_ar_bits_size, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [1:0]  ctrl_ar_bits_burst, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_ar_bits_lock, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_ar_bits_cache, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [2:0]  ctrl_ar_bits_prot, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_ar_bits_qos, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [3:0]  ctrl_ar_bits_region, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input  [11:0] ctrl_ar_bits_id, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_ar_bits_user, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  input         ctrl_r_ready, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_r_valid, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output [1:0]  ctrl_r_bits_resp, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output [31:0] ctrl_r_bits_data, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_r_bits_last, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output [11:0] ctrl_r_bits_id, // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
  output        ctrl_r_bits_user // @[midas/src/main/scala/midas/core/FPGATop.scala 509:16]
);
  wire  SimulationMaster_0_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] SimulationMaster_0_io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] SimulationMaster_0_io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] SimulationMaster_0_io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] SimulationMaster_0_io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] SimulationMaster_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] SimulationMaster_0_io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] SimulationMaster_0_io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] SimulationMaster_0_io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  SimulationMaster_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] SimulationMaster_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] SimulationMaster_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] ClockBridgeModule_0_io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] ClockBridgeModule_0_io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] ClockBridgeModule_0_io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] ClockBridgeModule_0_io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] ClockBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] ClockBridgeModule_0_io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] ClockBridgeModule_0_io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] ClockBridgeModule_0_io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] ClockBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] ClockBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_hPort_clocks_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_hPort_clocks_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  ClockBridgeModule_0_hPort_clocks_bits_0; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] PeekPokeBridgeModule_0_io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] PeekPokeBridgeModule_0_io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] PeekPokeBridgeModule_0_io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] PeekPokeBridgeModule_0_io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] PeekPokeBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] PeekPokeBridgeModule_0_io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] PeekPokeBridgeModule_0_io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] PeekPokeBridgeModule_0_io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] PeekPokeBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] PeekPokeBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_z_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_z_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [15:0] PeekPokeBridgeModule_0_hPort_io_z_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_v_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_v_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_v_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_a_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_a_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [15:0] PeekPokeBridgeModule_0_hPort_io_a_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [15:0] PeekPokeBridgeModule_0_hPort_io_b_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_e_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_e_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_io_e_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_reset_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_reset_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  PeekPokeBridgeModule_0_hPort_reset_bits; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] AssertBridgeModule_0_io_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] AssertBridgeModule_0_io_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] AssertBridgeModule_0_io_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] AssertBridgeModule_0_io_ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] AssertBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [24:0] AssertBridgeModule_0_io_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [7:0] AssertBridgeModule_0_io_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] AssertBridgeModule_0_io_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [31:0] AssertBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire [11:0] AssertBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_hPort_toHost_hReady; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  AssertBridgeModule_0_hPort_toHost_hValid; // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
  wire  sim_clock; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_reset; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_a_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_a_sink_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire [15:0] sim_channelPorts_GCD__peekPokeBridge_io_a_sink_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_b_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_b_sink_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire [15:0] sim_channelPorts_GCD__peekPokeBridge_io_b_sink_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_e_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_e_sink_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_e_sink_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_reset_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_reset_sink_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_reset_sink_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_z_source_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_z_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire [15:0] sim_channelPorts_GCD__peekPokeBridge_io_z_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_v_source_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_v_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__peekPokeBridge_io_v_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  sim_channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
  wire  ctrlInterconnect_clock; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_reset; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_masters_0_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_masters_0_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_masters_0_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_masters_0_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_w_bits_last; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [1:0] ctrlInterconnect_io_masters_0_b_bits_resp; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_masters_0_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_masters_0_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_masters_0_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_masters_0_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [1:0] ctrlInterconnect_io_masters_0_r_bits_resp; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_masters_0_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_masters_0_r_bits_last; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_masters_0_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_0_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_0_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_0_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_0_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_0_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_0_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_0_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_0_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_0_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_0_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_0_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_1_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_1_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_1_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_1_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_1_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_1_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_1_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_1_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_1_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_1_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_1_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_2_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_2_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_2_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_2_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_2_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_2_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_2_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_2_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_2_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_2_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_2_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_3_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_3_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_3_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_3_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_3_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [24:0] ctrlInterconnect_io_slaves_3_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [7:0] ctrlInterconnect_io_slaves_3_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_3_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire  ctrlInterconnect_io_slaves_3_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [31:0] ctrlInterconnect_io_slaves_3_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  wire [11:0] ctrlInterconnect_io_slaves_3_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
  SimulationMaster SimulationMaster_0 ( // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
    .clock(SimulationMaster_0_clock),
    .reset(SimulationMaster_0_reset),
    .io_ctrl_aw_ready(SimulationMaster_0_io_ctrl_aw_ready),
    .io_ctrl_aw_valid(SimulationMaster_0_io_ctrl_aw_valid),
    .io_ctrl_aw_bits_addr(SimulationMaster_0_io_ctrl_aw_bits_addr),
    .io_ctrl_aw_bits_len(SimulationMaster_0_io_ctrl_aw_bits_len),
    .io_ctrl_aw_bits_id(SimulationMaster_0_io_ctrl_aw_bits_id),
    .io_ctrl_w_ready(SimulationMaster_0_io_ctrl_w_ready),
    .io_ctrl_w_valid(SimulationMaster_0_io_ctrl_w_valid),
    .io_ctrl_w_bits_data(SimulationMaster_0_io_ctrl_w_bits_data),
    .io_ctrl_b_ready(SimulationMaster_0_io_ctrl_b_ready),
    .io_ctrl_b_valid(SimulationMaster_0_io_ctrl_b_valid),
    .io_ctrl_b_bits_id(SimulationMaster_0_io_ctrl_b_bits_id),
    .io_ctrl_ar_ready(SimulationMaster_0_io_ctrl_ar_ready),
    .io_ctrl_ar_valid(SimulationMaster_0_io_ctrl_ar_valid),
    .io_ctrl_ar_bits_addr(SimulationMaster_0_io_ctrl_ar_bits_addr),
    .io_ctrl_ar_bits_len(SimulationMaster_0_io_ctrl_ar_bits_len),
    .io_ctrl_ar_bits_id(SimulationMaster_0_io_ctrl_ar_bits_id),
    .io_ctrl_r_ready(SimulationMaster_0_io_ctrl_r_ready),
    .io_ctrl_r_valid(SimulationMaster_0_io_ctrl_r_valid),
    .io_ctrl_r_bits_data(SimulationMaster_0_io_ctrl_r_bits_data),
    .io_ctrl_r_bits_id(SimulationMaster_0_io_ctrl_r_bits_id)
  );
  ClockBridgeModule ClockBridgeModule_0 ( // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
    .clock(ClockBridgeModule_0_clock),
    .reset(ClockBridgeModule_0_reset),
    .io_ctrl_aw_ready(ClockBridgeModule_0_io_ctrl_aw_ready),
    .io_ctrl_aw_valid(ClockBridgeModule_0_io_ctrl_aw_valid),
    .io_ctrl_aw_bits_addr(ClockBridgeModule_0_io_ctrl_aw_bits_addr),
    .io_ctrl_aw_bits_len(ClockBridgeModule_0_io_ctrl_aw_bits_len),
    .io_ctrl_aw_bits_id(ClockBridgeModule_0_io_ctrl_aw_bits_id),
    .io_ctrl_w_ready(ClockBridgeModule_0_io_ctrl_w_ready),
    .io_ctrl_w_valid(ClockBridgeModule_0_io_ctrl_w_valid),
    .io_ctrl_w_bits_data(ClockBridgeModule_0_io_ctrl_w_bits_data),
    .io_ctrl_b_ready(ClockBridgeModule_0_io_ctrl_b_ready),
    .io_ctrl_b_valid(ClockBridgeModule_0_io_ctrl_b_valid),
    .io_ctrl_b_bits_id(ClockBridgeModule_0_io_ctrl_b_bits_id),
    .io_ctrl_ar_ready(ClockBridgeModule_0_io_ctrl_ar_ready),
    .io_ctrl_ar_valid(ClockBridgeModule_0_io_ctrl_ar_valid),
    .io_ctrl_ar_bits_addr(ClockBridgeModule_0_io_ctrl_ar_bits_addr),
    .io_ctrl_ar_bits_len(ClockBridgeModule_0_io_ctrl_ar_bits_len),
    .io_ctrl_ar_bits_id(ClockBridgeModule_0_io_ctrl_ar_bits_id),
    .io_ctrl_r_ready(ClockBridgeModule_0_io_ctrl_r_ready),
    .io_ctrl_r_valid(ClockBridgeModule_0_io_ctrl_r_valid),
    .io_ctrl_r_bits_data(ClockBridgeModule_0_io_ctrl_r_bits_data),
    .io_ctrl_r_bits_id(ClockBridgeModule_0_io_ctrl_r_bits_id),
    .hPort_clocks_ready(ClockBridgeModule_0_hPort_clocks_ready),
    .hPort_clocks_valid(ClockBridgeModule_0_hPort_clocks_valid),
    .hPort_clocks_bits_0(ClockBridgeModule_0_hPort_clocks_bits_0)
  );
  PeekPokeBridgeModule PeekPokeBridgeModule_0 ( // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
    .clock(PeekPokeBridgeModule_0_clock),
    .reset(PeekPokeBridgeModule_0_reset),
    .io_ctrl_aw_ready(PeekPokeBridgeModule_0_io_ctrl_aw_ready),
    .io_ctrl_aw_valid(PeekPokeBridgeModule_0_io_ctrl_aw_valid),
    .io_ctrl_aw_bits_addr(PeekPokeBridgeModule_0_io_ctrl_aw_bits_addr),
    .io_ctrl_aw_bits_len(PeekPokeBridgeModule_0_io_ctrl_aw_bits_len),
    .io_ctrl_aw_bits_id(PeekPokeBridgeModule_0_io_ctrl_aw_bits_id),
    .io_ctrl_w_ready(PeekPokeBridgeModule_0_io_ctrl_w_ready),
    .io_ctrl_w_valid(PeekPokeBridgeModule_0_io_ctrl_w_valid),
    .io_ctrl_w_bits_data(PeekPokeBridgeModule_0_io_ctrl_w_bits_data),
    .io_ctrl_b_ready(PeekPokeBridgeModule_0_io_ctrl_b_ready),
    .io_ctrl_b_valid(PeekPokeBridgeModule_0_io_ctrl_b_valid),
    .io_ctrl_b_bits_id(PeekPokeBridgeModule_0_io_ctrl_b_bits_id),
    .io_ctrl_ar_ready(PeekPokeBridgeModule_0_io_ctrl_ar_ready),
    .io_ctrl_ar_valid(PeekPokeBridgeModule_0_io_ctrl_ar_valid),
    .io_ctrl_ar_bits_addr(PeekPokeBridgeModule_0_io_ctrl_ar_bits_addr),
    .io_ctrl_ar_bits_len(PeekPokeBridgeModule_0_io_ctrl_ar_bits_len),
    .io_ctrl_ar_bits_id(PeekPokeBridgeModule_0_io_ctrl_ar_bits_id),
    .io_ctrl_r_ready(PeekPokeBridgeModule_0_io_ctrl_r_ready),
    .io_ctrl_r_valid(PeekPokeBridgeModule_0_io_ctrl_r_valid),
    .io_ctrl_r_bits_data(PeekPokeBridgeModule_0_io_ctrl_r_bits_data),
    .io_ctrl_r_bits_id(PeekPokeBridgeModule_0_io_ctrl_r_bits_id),
    .hPort_io_z_ready(PeekPokeBridgeModule_0_hPort_io_z_ready),
    .hPort_io_z_valid(PeekPokeBridgeModule_0_hPort_io_z_valid),
    .hPort_io_z_bits(PeekPokeBridgeModule_0_hPort_io_z_bits),
    .hPort_io_v_ready(PeekPokeBridgeModule_0_hPort_io_v_ready),
    .hPort_io_v_valid(PeekPokeBridgeModule_0_hPort_io_v_valid),
    .hPort_io_v_bits(PeekPokeBridgeModule_0_hPort_io_v_bits),
    .hPort_io_a_ready(PeekPokeBridgeModule_0_hPort_io_a_ready),
    .hPort_io_a_valid(PeekPokeBridgeModule_0_hPort_io_a_valid),
    .hPort_io_a_bits(PeekPokeBridgeModule_0_hPort_io_a_bits),
    .hPort_io_b_ready(PeekPokeBridgeModule_0_hPort_io_b_ready),
    .hPort_io_b_valid(PeekPokeBridgeModule_0_hPort_io_b_valid),
    .hPort_io_b_bits(PeekPokeBridgeModule_0_hPort_io_b_bits),
    .hPort_io_e_ready(PeekPokeBridgeModule_0_hPort_io_e_ready),
    .hPort_io_e_valid(PeekPokeBridgeModule_0_hPort_io_e_valid),
    .hPort_io_e_bits(PeekPokeBridgeModule_0_hPort_io_e_bits),
    .hPort_reset_ready(PeekPokeBridgeModule_0_hPort_reset_ready),
    .hPort_reset_valid(PeekPokeBridgeModule_0_hPort_reset_valid),
    .hPort_reset_bits(PeekPokeBridgeModule_0_hPort_reset_bits)
  );
  AssertBridgeModule AssertBridgeModule_0 ( // @[midas/src/main/scala/midas/widgets/Widget.scala 309:23]
    .clock(AssertBridgeModule_0_clock),
    .reset(AssertBridgeModule_0_reset),
    .io_ctrl_aw_ready(AssertBridgeModule_0_io_ctrl_aw_ready),
    .io_ctrl_aw_valid(AssertBridgeModule_0_io_ctrl_aw_valid),
    .io_ctrl_aw_bits_addr(AssertBridgeModule_0_io_ctrl_aw_bits_addr),
    .io_ctrl_aw_bits_len(AssertBridgeModule_0_io_ctrl_aw_bits_len),
    .io_ctrl_aw_bits_id(AssertBridgeModule_0_io_ctrl_aw_bits_id),
    .io_ctrl_w_ready(AssertBridgeModule_0_io_ctrl_w_ready),
    .io_ctrl_w_valid(AssertBridgeModule_0_io_ctrl_w_valid),
    .io_ctrl_w_bits_data(AssertBridgeModule_0_io_ctrl_w_bits_data),
    .io_ctrl_b_ready(AssertBridgeModule_0_io_ctrl_b_ready),
    .io_ctrl_b_valid(AssertBridgeModule_0_io_ctrl_b_valid),
    .io_ctrl_b_bits_id(AssertBridgeModule_0_io_ctrl_b_bits_id),
    .io_ctrl_ar_ready(AssertBridgeModule_0_io_ctrl_ar_ready),
    .io_ctrl_ar_valid(AssertBridgeModule_0_io_ctrl_ar_valid),
    .io_ctrl_ar_bits_addr(AssertBridgeModule_0_io_ctrl_ar_bits_addr),
    .io_ctrl_ar_bits_len(AssertBridgeModule_0_io_ctrl_ar_bits_len),
    .io_ctrl_ar_bits_id(AssertBridgeModule_0_io_ctrl_ar_bits_id),
    .io_ctrl_r_ready(AssertBridgeModule_0_io_ctrl_r_ready),
    .io_ctrl_r_valid(AssertBridgeModule_0_io_ctrl_r_valid),
    .io_ctrl_r_bits_data(AssertBridgeModule_0_io_ctrl_r_bits_data),
    .io_ctrl_r_bits_id(AssertBridgeModule_0_io_ctrl_r_bits_id),
    .hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition(
      AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition),
    .hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts(
      AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts),
    .hPort_toHost_hReady(AssertBridgeModule_0_hPort_toHost_hReady),
    .hPort_toHost_hValid(AssertBridgeModule_0_hPort_toHost_hValid)
  );
  SimWrapper sim ( // @[midas/src/main/scala/midas/core/FPGATop.scala 545:21]
    .clock(sim_clock),
    .reset(sim_reset),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid),
    .channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits(
      sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits),
    .channelPorts_GCD__peekPokeBridge_io_a_sink_ready(sim_channelPorts_GCD__peekPokeBridge_io_a_sink_ready),
    .channelPorts_GCD__peekPokeBridge_io_a_sink_valid(sim_channelPorts_GCD__peekPokeBridge_io_a_sink_valid),
    .channelPorts_GCD__peekPokeBridge_io_a_sink_bits(sim_channelPorts_GCD__peekPokeBridge_io_a_sink_bits),
    .channelPorts_GCD__peekPokeBridge_io_b_sink_ready(sim_channelPorts_GCD__peekPokeBridge_io_b_sink_ready),
    .channelPorts_GCD__peekPokeBridge_io_b_sink_valid(sim_channelPorts_GCD__peekPokeBridge_io_b_sink_valid),
    .channelPorts_GCD__peekPokeBridge_io_b_sink_bits(sim_channelPorts_GCD__peekPokeBridge_io_b_sink_bits),
    .channelPorts_GCD__peekPokeBridge_io_e_sink_ready(sim_channelPorts_GCD__peekPokeBridge_io_e_sink_ready),
    .channelPorts_GCD__peekPokeBridge_io_e_sink_valid(sim_channelPorts_GCD__peekPokeBridge_io_e_sink_valid),
    .channelPorts_GCD__peekPokeBridge_io_e_sink_bits(sim_channelPorts_GCD__peekPokeBridge_io_e_sink_bits),
    .channelPorts_GCD__peekPokeBridge_reset_sink_ready(sim_channelPorts_GCD__peekPokeBridge_reset_sink_ready),
    .channelPorts_GCD__peekPokeBridge_reset_sink_valid(sim_channelPorts_GCD__peekPokeBridge_reset_sink_valid),
    .channelPorts_GCD__peekPokeBridge_reset_sink_bits(sim_channelPorts_GCD__peekPokeBridge_reset_sink_bits),
    .channelPorts_GCD__peekPokeBridge_io_z_source_ready(sim_channelPorts_GCD__peekPokeBridge_io_z_source_ready),
    .channelPorts_GCD__peekPokeBridge_io_z_source_valid(sim_channelPorts_GCD__peekPokeBridge_io_z_source_valid),
    .channelPorts_GCD__peekPokeBridge_io_z_source_bits(sim_channelPorts_GCD__peekPokeBridge_io_z_source_bits),
    .channelPorts_GCD__peekPokeBridge_io_v_source_ready(sim_channelPorts_GCD__peekPokeBridge_io_v_source_ready),
    .channelPorts_GCD__peekPokeBridge_io_v_source_valid(sim_channelPorts_GCD__peekPokeBridge_io_v_source_valid),
    .channelPorts_GCD__peekPokeBridge_io_v_source_bits(sim_channelPorts_GCD__peekPokeBridge_io_v_source_bits),
    .channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready(
      sim_channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready)
  );
  NastiRecursiveInterconnect ctrlInterconnect ( // @[midas/src/main/scala/midas/widgets/Widget.scala 330:34]
    .clock(ctrlInterconnect_clock),
    .reset(ctrlInterconnect_reset),
    .io_masters_0_aw_ready(ctrlInterconnect_io_masters_0_aw_ready),
    .io_masters_0_aw_valid(ctrlInterconnect_io_masters_0_aw_valid),
    .io_masters_0_aw_bits_addr(ctrlInterconnect_io_masters_0_aw_bits_addr),
    .io_masters_0_aw_bits_len(ctrlInterconnect_io_masters_0_aw_bits_len),
    .io_masters_0_aw_bits_id(ctrlInterconnect_io_masters_0_aw_bits_id),
    .io_masters_0_w_ready(ctrlInterconnect_io_masters_0_w_ready),
    .io_masters_0_w_valid(ctrlInterconnect_io_masters_0_w_valid),
    .io_masters_0_w_bits_data(ctrlInterconnect_io_masters_0_w_bits_data),
    .io_masters_0_w_bits_last(ctrlInterconnect_io_masters_0_w_bits_last),
    .io_masters_0_b_ready(ctrlInterconnect_io_masters_0_b_ready),
    .io_masters_0_b_valid(ctrlInterconnect_io_masters_0_b_valid),
    .io_masters_0_b_bits_resp(ctrlInterconnect_io_masters_0_b_bits_resp),
    .io_masters_0_b_bits_id(ctrlInterconnect_io_masters_0_b_bits_id),
    .io_masters_0_ar_ready(ctrlInterconnect_io_masters_0_ar_ready),
    .io_masters_0_ar_valid(ctrlInterconnect_io_masters_0_ar_valid),
    .io_masters_0_ar_bits_addr(ctrlInterconnect_io_masters_0_ar_bits_addr),
    .io_masters_0_ar_bits_len(ctrlInterconnect_io_masters_0_ar_bits_len),
    .io_masters_0_ar_bits_id(ctrlInterconnect_io_masters_0_ar_bits_id),
    .io_masters_0_r_ready(ctrlInterconnect_io_masters_0_r_ready),
    .io_masters_0_r_valid(ctrlInterconnect_io_masters_0_r_valid),
    .io_masters_0_r_bits_resp(ctrlInterconnect_io_masters_0_r_bits_resp),
    .io_masters_0_r_bits_data(ctrlInterconnect_io_masters_0_r_bits_data),
    .io_masters_0_r_bits_last(ctrlInterconnect_io_masters_0_r_bits_last),
    .io_masters_0_r_bits_id(ctrlInterconnect_io_masters_0_r_bits_id),
    .io_slaves_0_aw_ready(ctrlInterconnect_io_slaves_0_aw_ready),
    .io_slaves_0_aw_valid(ctrlInterconnect_io_slaves_0_aw_valid),
    .io_slaves_0_aw_bits_addr(ctrlInterconnect_io_slaves_0_aw_bits_addr),
    .io_slaves_0_aw_bits_len(ctrlInterconnect_io_slaves_0_aw_bits_len),
    .io_slaves_0_aw_bits_id(ctrlInterconnect_io_slaves_0_aw_bits_id),
    .io_slaves_0_w_ready(ctrlInterconnect_io_slaves_0_w_ready),
    .io_slaves_0_w_valid(ctrlInterconnect_io_slaves_0_w_valid),
    .io_slaves_0_w_bits_data(ctrlInterconnect_io_slaves_0_w_bits_data),
    .io_slaves_0_b_ready(ctrlInterconnect_io_slaves_0_b_ready),
    .io_slaves_0_b_valid(ctrlInterconnect_io_slaves_0_b_valid),
    .io_slaves_0_b_bits_id(ctrlInterconnect_io_slaves_0_b_bits_id),
    .io_slaves_0_ar_ready(ctrlInterconnect_io_slaves_0_ar_ready),
    .io_slaves_0_ar_valid(ctrlInterconnect_io_slaves_0_ar_valid),
    .io_slaves_0_ar_bits_addr(ctrlInterconnect_io_slaves_0_ar_bits_addr),
    .io_slaves_0_ar_bits_len(ctrlInterconnect_io_slaves_0_ar_bits_len),
    .io_slaves_0_ar_bits_id(ctrlInterconnect_io_slaves_0_ar_bits_id),
    .io_slaves_0_r_ready(ctrlInterconnect_io_slaves_0_r_ready),
    .io_slaves_0_r_valid(ctrlInterconnect_io_slaves_0_r_valid),
    .io_slaves_0_r_bits_data(ctrlInterconnect_io_slaves_0_r_bits_data),
    .io_slaves_0_r_bits_id(ctrlInterconnect_io_slaves_0_r_bits_id),
    .io_slaves_1_aw_ready(ctrlInterconnect_io_slaves_1_aw_ready),
    .io_slaves_1_aw_valid(ctrlInterconnect_io_slaves_1_aw_valid),
    .io_slaves_1_aw_bits_addr(ctrlInterconnect_io_slaves_1_aw_bits_addr),
    .io_slaves_1_aw_bits_len(ctrlInterconnect_io_slaves_1_aw_bits_len),
    .io_slaves_1_aw_bits_id(ctrlInterconnect_io_slaves_1_aw_bits_id),
    .io_slaves_1_w_ready(ctrlInterconnect_io_slaves_1_w_ready),
    .io_slaves_1_w_valid(ctrlInterconnect_io_slaves_1_w_valid),
    .io_slaves_1_w_bits_data(ctrlInterconnect_io_slaves_1_w_bits_data),
    .io_slaves_1_b_ready(ctrlInterconnect_io_slaves_1_b_ready),
    .io_slaves_1_b_valid(ctrlInterconnect_io_slaves_1_b_valid),
    .io_slaves_1_b_bits_id(ctrlInterconnect_io_slaves_1_b_bits_id),
    .io_slaves_1_ar_ready(ctrlInterconnect_io_slaves_1_ar_ready),
    .io_slaves_1_ar_valid(ctrlInterconnect_io_slaves_1_ar_valid),
    .io_slaves_1_ar_bits_addr(ctrlInterconnect_io_slaves_1_ar_bits_addr),
    .io_slaves_1_ar_bits_len(ctrlInterconnect_io_slaves_1_ar_bits_len),
    .io_slaves_1_ar_bits_id(ctrlInterconnect_io_slaves_1_ar_bits_id),
    .io_slaves_1_r_ready(ctrlInterconnect_io_slaves_1_r_ready),
    .io_slaves_1_r_valid(ctrlInterconnect_io_slaves_1_r_valid),
    .io_slaves_1_r_bits_data(ctrlInterconnect_io_slaves_1_r_bits_data),
    .io_slaves_1_r_bits_id(ctrlInterconnect_io_slaves_1_r_bits_id),
    .io_slaves_2_aw_ready(ctrlInterconnect_io_slaves_2_aw_ready),
    .io_slaves_2_aw_valid(ctrlInterconnect_io_slaves_2_aw_valid),
    .io_slaves_2_aw_bits_addr(ctrlInterconnect_io_slaves_2_aw_bits_addr),
    .io_slaves_2_aw_bits_len(ctrlInterconnect_io_slaves_2_aw_bits_len),
    .io_slaves_2_aw_bits_id(ctrlInterconnect_io_slaves_2_aw_bits_id),
    .io_slaves_2_w_ready(ctrlInterconnect_io_slaves_2_w_ready),
    .io_slaves_2_w_valid(ctrlInterconnect_io_slaves_2_w_valid),
    .io_slaves_2_w_bits_data(ctrlInterconnect_io_slaves_2_w_bits_data),
    .io_slaves_2_b_ready(ctrlInterconnect_io_slaves_2_b_ready),
    .io_slaves_2_b_valid(ctrlInterconnect_io_slaves_2_b_valid),
    .io_slaves_2_b_bits_id(ctrlInterconnect_io_slaves_2_b_bits_id),
    .io_slaves_2_ar_ready(ctrlInterconnect_io_slaves_2_ar_ready),
    .io_slaves_2_ar_valid(ctrlInterconnect_io_slaves_2_ar_valid),
    .io_slaves_2_ar_bits_addr(ctrlInterconnect_io_slaves_2_ar_bits_addr),
    .io_slaves_2_ar_bits_len(ctrlInterconnect_io_slaves_2_ar_bits_len),
    .io_slaves_2_ar_bits_id(ctrlInterconnect_io_slaves_2_ar_bits_id),
    .io_slaves_2_r_ready(ctrlInterconnect_io_slaves_2_r_ready),
    .io_slaves_2_r_valid(ctrlInterconnect_io_slaves_2_r_valid),
    .io_slaves_2_r_bits_data(ctrlInterconnect_io_slaves_2_r_bits_data),
    .io_slaves_2_r_bits_id(ctrlInterconnect_io_slaves_2_r_bits_id),
    .io_slaves_3_aw_ready(ctrlInterconnect_io_slaves_3_aw_ready),
    .io_slaves_3_aw_valid(ctrlInterconnect_io_slaves_3_aw_valid),
    .io_slaves_3_aw_bits_addr(ctrlInterconnect_io_slaves_3_aw_bits_addr),
    .io_slaves_3_aw_bits_len(ctrlInterconnect_io_slaves_3_aw_bits_len),
    .io_slaves_3_aw_bits_id(ctrlInterconnect_io_slaves_3_aw_bits_id),
    .io_slaves_3_w_ready(ctrlInterconnect_io_slaves_3_w_ready),
    .io_slaves_3_w_valid(ctrlInterconnect_io_slaves_3_w_valid),
    .io_slaves_3_w_bits_data(ctrlInterconnect_io_slaves_3_w_bits_data),
    .io_slaves_3_b_ready(ctrlInterconnect_io_slaves_3_b_ready),
    .io_slaves_3_b_valid(ctrlInterconnect_io_slaves_3_b_valid),
    .io_slaves_3_b_bits_id(ctrlInterconnect_io_slaves_3_b_bits_id),
    .io_slaves_3_ar_ready(ctrlInterconnect_io_slaves_3_ar_ready),
    .io_slaves_3_ar_valid(ctrlInterconnect_io_slaves_3_ar_valid),
    .io_slaves_3_ar_bits_addr(ctrlInterconnect_io_slaves_3_ar_bits_addr),
    .io_slaves_3_ar_bits_len(ctrlInterconnect_io_slaves_3_ar_bits_len),
    .io_slaves_3_ar_bits_id(ctrlInterconnect_io_slaves_3_ar_bits_id),
    .io_slaves_3_r_ready(ctrlInterconnect_io_slaves_3_r_ready),
    .io_slaves_3_r_valid(ctrlInterconnect_io_slaves_3_r_valid),
    .io_slaves_3_r_bits_data(ctrlInterconnect_io_slaves_3_r_bits_data),
    .io_slaves_3_r_bits_id(ctrlInterconnect_io_slaves_3_r_bits_id)
  );
  assign ctrl_aw_ready = ctrlInterconnect_io_masters_0_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_w_ready = ctrlInterconnect_io_masters_0_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_b_valid = ctrlInterconnect_io_masters_0_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_b_bits_resp = ctrlInterconnect_io_masters_0_b_bits_resp; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_b_bits_id = ctrlInterconnect_io_masters_0_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_b_bits_user = 1'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_ar_ready = ctrlInterconnect_io_masters_0_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_valid = ctrlInterconnect_io_masters_0_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_bits_resp = ctrlInterconnect_io_masters_0_r_bits_resp; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_bits_data = ctrlInterconnect_io_masters_0_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_bits_last = ctrlInterconnect_io_masters_0_r_bits_last; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_bits_id = ctrlInterconnect_io_masters_0_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrl_r_bits_user = 1'h0; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign SimulationMaster_0_clock = clock;
  assign SimulationMaster_0_reset = reset;
  assign SimulationMaster_0_io_ctrl_aw_valid = ctrlInterconnect_io_slaves_3_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_aw_bits_addr = ctrlInterconnect_io_slaves_3_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_aw_bits_len = ctrlInterconnect_io_slaves_3_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_aw_bits_id = ctrlInterconnect_io_slaves_3_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_w_valid = ctrlInterconnect_io_slaves_3_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_w_bits_data = ctrlInterconnect_io_slaves_3_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_b_ready = ctrlInterconnect_io_slaves_3_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_ar_valid = ctrlInterconnect_io_slaves_3_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_ar_bits_addr = ctrlInterconnect_io_slaves_3_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_ar_bits_len = ctrlInterconnect_io_slaves_3_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_ar_bits_id = ctrlInterconnect_io_slaves_3_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign SimulationMaster_0_io_ctrl_r_ready = ctrlInterconnect_io_slaves_3_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_clock = clock;
  assign ClockBridgeModule_0_reset = reset;
  assign ClockBridgeModule_0_io_ctrl_aw_valid = ctrlInterconnect_io_slaves_1_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_aw_bits_addr = ctrlInterconnect_io_slaves_1_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_aw_bits_len = ctrlInterconnect_io_slaves_1_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_aw_bits_id = ctrlInterconnect_io_slaves_1_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_w_valid = ctrlInterconnect_io_slaves_1_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_w_bits_data = ctrlInterconnect_io_slaves_1_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_b_ready = ctrlInterconnect_io_slaves_1_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_ar_valid = ctrlInterconnect_io_slaves_1_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_ar_bits_addr = ctrlInterconnect_io_slaves_1_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_ar_bits_len = ctrlInterconnect_io_slaves_1_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_ar_bits_id = ctrlInterconnect_io_slaves_1_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_io_ctrl_r_ready = ctrlInterconnect_io_slaves_1_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ClockBridgeModule_0_hPort_clocks_ready = sim_channelPorts_GCD__RationalClockBridge_clocks_0_sink_ready; // @[midas/src/main/scala/midas/widgets/ClockBridge.scala 31:30]
  assign PeekPokeBridgeModule_0_clock = clock;
  assign PeekPokeBridgeModule_0_reset = reset;
  assign PeekPokeBridgeModule_0_io_ctrl_aw_valid = ctrlInterconnect_io_slaves_0_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_aw_bits_addr = ctrlInterconnect_io_slaves_0_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_aw_bits_len = ctrlInterconnect_io_slaves_0_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_aw_bits_id = ctrlInterconnect_io_slaves_0_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_w_valid = ctrlInterconnect_io_slaves_0_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_w_bits_data = ctrlInterconnect_io_slaves_0_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_b_ready = ctrlInterconnect_io_slaves_0_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_ar_valid = ctrlInterconnect_io_slaves_0_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_ar_bits_addr = ctrlInterconnect_io_slaves_0_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_ar_bits_len = ctrlInterconnect_io_slaves_0_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_ar_bits_id = ctrlInterconnect_io_slaves_0_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_io_ctrl_r_ready = ctrlInterconnect_io_slaves_0_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign PeekPokeBridgeModule_0_hPort_io_z_valid = sim_channelPorts_GCD__peekPokeBridge_io_z_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign PeekPokeBridgeModule_0_hPort_io_z_bits = sim_channelPorts_GCD__peekPokeBridge_io_z_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign PeekPokeBridgeModule_0_hPort_io_v_valid = sim_channelPorts_GCD__peekPokeBridge_io_v_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign PeekPokeBridgeModule_0_hPort_io_v_bits = sim_channelPorts_GCD__peekPokeBridge_io_v_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign PeekPokeBridgeModule_0_hPort_io_a_ready = sim_channelPorts_GCD__peekPokeBridge_io_a_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign PeekPokeBridgeModule_0_hPort_io_b_ready = sim_channelPorts_GCD__peekPokeBridge_io_b_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign PeekPokeBridgeModule_0_hPort_io_e_ready = sim_channelPorts_GCD__peekPokeBridge_io_e_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign PeekPokeBridgeModule_0_hPort_reset_ready = sim_channelPorts_GCD__peekPokeBridge_reset_sink_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign AssertBridgeModule_0_clock = clock;
  assign AssertBridgeModule_0_reset = reset;
  assign AssertBridgeModule_0_io_ctrl_aw_valid = ctrlInterconnect_io_slaves_2_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_aw_bits_addr = ctrlInterconnect_io_slaves_2_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_aw_bits_len = ctrlInterconnect_io_slaves_2_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_aw_bits_id = ctrlInterconnect_io_slaves_2_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_w_valid = ctrlInterconnect_io_slaves_2_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_w_bits_data = ctrlInterconnect_io_slaves_2_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_b_ready = ctrlInterconnect_io_slaves_2_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_ar_valid = ctrlInterconnect_io_slaves_2_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_ar_bits_addr = ctrlInterconnect_io_slaves_2_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_ar_bits_len = ctrlInterconnect_io_slaves_2_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_ar_bits_id = ctrlInterconnect_io_slaves_2_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_io_ctrl_r_ready = ctrlInterconnect_io_slaves_2_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_globalResetCondition =
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 440:13]
  assign AssertBridgeModule_0_hPort_hBits_midasAsserts_RationalClockBridge_clocks_0_asserts =
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 440:13]
  assign AssertBridgeModule_0_hPort_toHost_hValid =
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid &
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 473:61]
  assign sim_clock = clock;
  assign sim_reset = reset;
  assign sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready =
    AssertBridgeModule_0_hPort_toHost_hReady &
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready =
    AssertBridgeModule_0_hPort_toHost_hReady &
    sim_channelPorts_GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[rocket-chip/src/main/scala/util/Misc.scala 26:53]
  assign sim_channelPorts_GCD__peekPokeBridge_io_a_sink_valid = PeekPokeBridgeModule_0_hPort_io_a_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_a_sink_bits = PeekPokeBridgeModule_0_hPort_io_a_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_b_sink_valid = PeekPokeBridgeModule_0_hPort_io_b_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_b_sink_bits = PeekPokeBridgeModule_0_hPort_io_b_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_e_sink_valid = PeekPokeBridgeModule_0_hPort_io_e_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_e_sink_bits = PeekPokeBridgeModule_0_hPort_io_e_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_reset_sink_valid = PeekPokeBridgeModule_0_hPort_reset_valid; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_reset_sink_bits = PeekPokeBridgeModule_0_hPort_reset_bits; // @[midas/src/main/scala/midas/core/FPGATop.scala 498:64]
  assign sim_channelPorts_GCD__peekPokeBridge_io_z_source_ready = PeekPokeBridgeModule_0_hPort_io_z_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign sim_channelPorts_GCD__peekPokeBridge_io_v_source_ready = PeekPokeBridgeModule_0_hPort_io_v_ready; // @[midas/src/main/scala/midas/core/FPGATop.scala 496:17]
  assign ctrlInterconnect_clock = clock;
  assign ctrlInterconnect_reset = reset;
  assign ctrlInterconnect_io_masters_0_aw_valid = ctrl_aw_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_aw_bits_addr = ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_aw_bits_len = ctrl_aw_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_aw_bits_id = ctrl_aw_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_w_valid = ctrl_w_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_w_bits_data = ctrl_w_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_w_bits_last = ctrl_w_bits_last; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_b_ready = ctrl_b_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_ar_valid = ctrl_ar_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_ar_bits_addr = ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_ar_bits_len = ctrl_ar_bits_len; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_ar_bits_id = ctrl_ar_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_masters_0_r_ready = ctrl_r_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 337:36]
  assign ctrlInterconnect_io_slaves_0_aw_ready = PeekPokeBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_w_ready = PeekPokeBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_b_valid = PeekPokeBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_b_bits_id = PeekPokeBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_ar_ready = PeekPokeBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_r_valid = PeekPokeBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_r_bits_data = PeekPokeBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_0_r_bits_id = PeekPokeBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_aw_ready = ClockBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_w_ready = ClockBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_b_valid = ClockBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_b_bits_id = ClockBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_ar_ready = ClockBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_r_valid = ClockBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_r_bits_data = ClockBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_1_r_bits_id = ClockBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_aw_ready = AssertBridgeModule_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_w_ready = AssertBridgeModule_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_b_valid = AssertBridgeModule_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_b_bits_id = AssertBridgeModule_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_ar_ready = AssertBridgeModule_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_r_valid = AssertBridgeModule_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_r_bits_data = AssertBridgeModule_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_2_r_bits_id = AssertBridgeModule_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_aw_ready = SimulationMaster_0_io_ctrl_aw_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_w_ready = SimulationMaster_0_io_ctrl_w_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_b_valid = SimulationMaster_0_io_ctrl_b_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_b_bits_id = SimulationMaster_0_io_ctrl_b_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_ar_ready = SimulationMaster_0_io_ctrl_ar_ready; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_r_valid = SimulationMaster_0_io_ctrl_r_valid; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_r_bits_data = SimulationMaster_0_io_ctrl_r_bits_data; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
  assign ctrlInterconnect_io_slaves_3_r_bits_id = SimulationMaster_0_io_ctrl_r_bits_id; // @[midas/src/main/scala/midas/widgets/Widget.scala 339:24]
endmodule
module F1Shim(
  input          clock,
  input          reset,
  output         io_master_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [24:0]  io_master_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [7:0]   io_master_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [2:0]   io_master_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [1:0]   io_master_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [2:0]   io_master_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_aw_bits_region, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [11:0]  io_master_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_aw_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [31:0]  io_master_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [11:0]  io_master_w_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_w_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output [1:0]   io_master_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output [11:0]  io_master_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_b_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [24:0]  io_master_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [7:0]   io_master_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [2:0]   io_master_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [1:0]   io_master_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [2:0]   io_master_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [3:0]   io_master_ar_bits_region, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input  [11:0]  io_master_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_ar_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  input          io_master_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output [1:0]   io_master_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output [31:0]  io_master_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_r_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output [11:0]  io_master_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_master_r_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 44:23]
  output         io_pcis_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [63:0]  io_pcis_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [7:0]   io_pcis_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [2:0]   io_pcis_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [1:0]   io_pcis_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [2:0]   io_pcis_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_aw_bits_region, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [15:0]  io_pcis_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_aw_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [511:0] io_pcis_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [15:0]  io_pcis_w_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [63:0]  io_pcis_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_w_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output [1:0]   io_pcis_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output [15:0]  io_pcis_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_b_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [63:0]  io_pcis_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [7:0]   io_pcis_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [2:0]   io_pcis_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [1:0]   io_pcis_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [2:0]   io_pcis_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [3:0]   io_pcis_ar_bits_region, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input  [15:0]  io_pcis_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_ar_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_pcis_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output [1:0]   io_pcis_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output [511:0] io_pcis_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_r_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output [15:0]  io_pcis_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  output         io_pcis_r_bits_user, // @[midas/src/main/scala/midas/platform/F1Shim.scala 45:23]
  input          io_slave_0_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_0_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_0_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_0_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_0_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_0_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_0_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_0_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_0_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_0_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [63:0]  io_slave_0_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_0_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_0_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_0_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_0_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_0_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_0_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_0_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_0_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_0_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_0_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_0_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_0_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_0_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_0_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_0_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_0_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [63:0]  io_slave_0_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_0_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_0_r_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_1_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_1_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_1_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_1_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_1_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_1_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_1_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_1_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [63:0]  io_slave_1_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_1_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_1_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_1_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_1_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_1_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_1_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_1_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_1_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_1_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_1_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_1_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_1_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_1_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [63:0]  io_slave_1_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_1_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_1_r_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_2_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_2_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_2_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_2_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_2_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_2_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_2_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_2_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [63:0]  io_slave_2_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_2_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_2_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_2_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_2_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_2_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_2_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_2_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_2_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_2_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_2_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_2_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_2_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_2_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [63:0]  io_slave_2_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_2_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_2_r_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_aw_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_aw_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_3_aw_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_3_aw_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_3_aw_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_3_aw_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_3_aw_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_aw_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_3_aw_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_3_aw_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_3_aw_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_w_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_w_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [63:0]  io_slave_3_w_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_3_w_bits_strb, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_w_bits_last, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_b_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_b_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_3_b_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_3_b_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_ar_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_ar_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [15:0]  io_slave_3_ar_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [33:0]  io_slave_3_ar_bits_addr, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [7:0]   io_slave_3_ar_bits_len, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_3_ar_bits_size, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [1:0]   io_slave_3_ar_bits_burst, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_ar_bits_lock, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_3_ar_bits_cache, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [2:0]   io_slave_3_ar_bits_prot, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output [3:0]   io_slave_3_ar_bits_qos, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  output         io_slave_3_r_ready, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_r_valid, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [15:0]  io_slave_3_r_bits_id, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [63:0]  io_slave_3_r_bits_data, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input  [1:0]   io_slave_3_r_bits_resp, // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
  input          io_slave_3_r_bits_last // @[midas/src/main/scala/midas/platform/F1Shim.scala 46:23]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
`endif // RANDOMIZE_REG_INIT
  wire  top_clock; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_reset; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_aw_ready; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_aw_valid; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [24:0] top_ctrl_aw_bits_addr; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [7:0] top_ctrl_aw_bits_len; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [2:0] top_ctrl_aw_bits_size; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [1:0] top_ctrl_aw_bits_burst; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_aw_bits_lock; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_aw_bits_cache; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [2:0] top_ctrl_aw_bits_prot; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_aw_bits_qos; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_aw_bits_region; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [11:0] top_ctrl_aw_bits_id; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_aw_bits_user; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_w_ready; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_w_valid; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [31:0] top_ctrl_w_bits_data; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_w_bits_last; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [11:0] top_ctrl_w_bits_id; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_w_bits_strb; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_w_bits_user; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_b_ready; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_b_valid; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [1:0] top_ctrl_b_bits_resp; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [11:0] top_ctrl_b_bits_id; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_b_bits_user; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_ar_ready; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_ar_valid; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [24:0] top_ctrl_ar_bits_addr; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [7:0] top_ctrl_ar_bits_len; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [2:0] top_ctrl_ar_bits_size; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [1:0] top_ctrl_ar_bits_burst; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_ar_bits_lock; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_ar_bits_cache; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [2:0] top_ctrl_ar_bits_prot; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_ar_bits_qos; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [3:0] top_ctrl_ar_bits_region; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [11:0] top_ctrl_ar_bits_id; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_ar_bits_user; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_r_ready; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_r_valid; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [1:0] top_ctrl_r_bits_resp; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [31:0] top_ctrl_r_bits_data; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_r_bits_last; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire [11:0] top_ctrl_r_bits_id; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  top_ctrl_r_bits_user; // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
  wire  _T = io_master_aw_ready & io_master_aw_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  reg [11:0] wCounterValue; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [11:0] _wrap_value_T_1 = wCounterValue + 12'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:24]
  wire  _T_1 = io_master_ar_ready & io_master_ar_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 57:35]
  reg [11:0] rCounterValue; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [11:0] _wrap_value_T_3 = rCounterValue + 12'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:24]
  FPGATop top ( // @[midas/src/main/scala/midas/platform/PlatformShim.scala 23:23]
    .clock(top_clock),
    .reset(top_reset),
    .ctrl_aw_ready(top_ctrl_aw_ready),
    .ctrl_aw_valid(top_ctrl_aw_valid),
    .ctrl_aw_bits_addr(top_ctrl_aw_bits_addr),
    .ctrl_aw_bits_len(top_ctrl_aw_bits_len),
    .ctrl_aw_bits_size(top_ctrl_aw_bits_size),
    .ctrl_aw_bits_burst(top_ctrl_aw_bits_burst),
    .ctrl_aw_bits_lock(top_ctrl_aw_bits_lock),
    .ctrl_aw_bits_cache(top_ctrl_aw_bits_cache),
    .ctrl_aw_bits_prot(top_ctrl_aw_bits_prot),
    .ctrl_aw_bits_qos(top_ctrl_aw_bits_qos),
    .ctrl_aw_bits_region(top_ctrl_aw_bits_region),
    .ctrl_aw_bits_id(top_ctrl_aw_bits_id),
    .ctrl_aw_bits_user(top_ctrl_aw_bits_user),
    .ctrl_w_ready(top_ctrl_w_ready),
    .ctrl_w_valid(top_ctrl_w_valid),
    .ctrl_w_bits_data(top_ctrl_w_bits_data),
    .ctrl_w_bits_last(top_ctrl_w_bits_last),
    .ctrl_w_bits_id(top_ctrl_w_bits_id),
    .ctrl_w_bits_strb(top_ctrl_w_bits_strb),
    .ctrl_w_bits_user(top_ctrl_w_bits_user),
    .ctrl_b_ready(top_ctrl_b_ready),
    .ctrl_b_valid(top_ctrl_b_valid),
    .ctrl_b_bits_resp(top_ctrl_b_bits_resp),
    .ctrl_b_bits_id(top_ctrl_b_bits_id),
    .ctrl_b_bits_user(top_ctrl_b_bits_user),
    .ctrl_ar_ready(top_ctrl_ar_ready),
    .ctrl_ar_valid(top_ctrl_ar_valid),
    .ctrl_ar_bits_addr(top_ctrl_ar_bits_addr),
    .ctrl_ar_bits_len(top_ctrl_ar_bits_len),
    .ctrl_ar_bits_size(top_ctrl_ar_bits_size),
    .ctrl_ar_bits_burst(top_ctrl_ar_bits_burst),
    .ctrl_ar_bits_lock(top_ctrl_ar_bits_lock),
    .ctrl_ar_bits_cache(top_ctrl_ar_bits_cache),
    .ctrl_ar_bits_prot(top_ctrl_ar_bits_prot),
    .ctrl_ar_bits_qos(top_ctrl_ar_bits_qos),
    .ctrl_ar_bits_region(top_ctrl_ar_bits_region),
    .ctrl_ar_bits_id(top_ctrl_ar_bits_id),
    .ctrl_ar_bits_user(top_ctrl_ar_bits_user),
    .ctrl_r_ready(top_ctrl_r_ready),
    .ctrl_r_valid(top_ctrl_r_valid),
    .ctrl_r_bits_resp(top_ctrl_r_bits_resp),
    .ctrl_r_bits_data(top_ctrl_r_bits_data),
    .ctrl_r_bits_last(top_ctrl_r_bits_last),
    .ctrl_r_bits_id(top_ctrl_r_bits_id),
    .ctrl_r_bits_user(top_ctrl_r_bits_user)
  );
  assign io_master_aw_ready = top_ctrl_aw_ready; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_w_ready = top_ctrl_w_ready; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_b_valid = top_ctrl_b_valid; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_b_bits_resp = top_ctrl_b_bits_resp; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_b_bits_id = top_ctrl_b_bits_id; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_b_bits_user = top_ctrl_b_bits_user; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_ar_ready = top_ctrl_ar_ready; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_valid = top_ctrl_r_valid; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_bits_resp = top_ctrl_r_bits_resp; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_bits_data = top_ctrl_r_bits_data; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_bits_last = top_ctrl_r_bits_last; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_bits_id = top_ctrl_r_bits_id; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_master_r_bits_user = top_ctrl_r_bits_user; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign io_pcis_aw_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 59:26]
  assign io_pcis_w_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 61:26]
  assign io_pcis_b_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 64:26]
  assign io_pcis_b_bits_resp = 2'h0;
  assign io_pcis_b_bits_id = 16'h0;
  assign io_pcis_b_bits_user = 1'h0;
  assign io_pcis_ar_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 60:26]
  assign io_pcis_r_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 62:26]
  assign io_pcis_r_bits_resp = 2'h0;
  assign io_pcis_r_bits_data = 512'h0;
  assign io_pcis_r_bits_last = 1'h0;
  assign io_pcis_r_bits_id = 16'h0;
  assign io_pcis_r_bits_user = 1'h0;
  assign io_slave_0_aw_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 95:22]
  assign io_slave_0_aw_bits_id = 16'h0;
  assign io_slave_0_aw_bits_addr = 34'h0;
  assign io_slave_0_aw_bits_len = 8'h0;
  assign io_slave_0_aw_bits_size = 3'h0;
  assign io_slave_0_aw_bits_burst = 2'h0;
  assign io_slave_0_aw_bits_lock = 1'h0;
  assign io_slave_0_aw_bits_cache = 4'h0;
  assign io_slave_0_aw_bits_prot = 3'h0;
  assign io_slave_0_aw_bits_qos = 4'h0;
  assign io_slave_0_w_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 99:22]
  assign io_slave_0_w_bits_data = 64'h0;
  assign io_slave_0_w_bits_strb = 8'h0;
  assign io_slave_0_w_bits_last = 1'h0;
  assign io_slave_0_b_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 102:22]
  assign io_slave_0_ar_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 97:22]
  assign io_slave_0_ar_bits_id = 16'h0;
  assign io_slave_0_ar_bits_addr = 34'h0;
  assign io_slave_0_ar_bits_len = 8'h0;
  assign io_slave_0_ar_bits_size = 3'h0;
  assign io_slave_0_ar_bits_burst = 2'h0;
  assign io_slave_0_ar_bits_lock = 1'h0;
  assign io_slave_0_ar_bits_cache = 4'h0;
  assign io_slave_0_ar_bits_prot = 3'h0;
  assign io_slave_0_ar_bits_qos = 4'h0;
  assign io_slave_0_r_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 101:22]
  assign io_slave_1_aw_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 95:22]
  assign io_slave_1_aw_bits_id = 16'h0;
  assign io_slave_1_aw_bits_addr = 34'h0;
  assign io_slave_1_aw_bits_len = 8'h0;
  assign io_slave_1_aw_bits_size = 3'h0;
  assign io_slave_1_aw_bits_burst = 2'h0;
  assign io_slave_1_aw_bits_lock = 1'h0;
  assign io_slave_1_aw_bits_cache = 4'h0;
  assign io_slave_1_aw_bits_prot = 3'h0;
  assign io_slave_1_aw_bits_qos = 4'h0;
  assign io_slave_1_w_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 99:22]
  assign io_slave_1_w_bits_data = 64'h0;
  assign io_slave_1_w_bits_strb = 8'h0;
  assign io_slave_1_w_bits_last = 1'h0;
  assign io_slave_1_b_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 102:22]
  assign io_slave_1_ar_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 97:22]
  assign io_slave_1_ar_bits_id = 16'h0;
  assign io_slave_1_ar_bits_addr = 34'h0;
  assign io_slave_1_ar_bits_len = 8'h0;
  assign io_slave_1_ar_bits_size = 3'h0;
  assign io_slave_1_ar_bits_burst = 2'h0;
  assign io_slave_1_ar_bits_lock = 1'h0;
  assign io_slave_1_ar_bits_cache = 4'h0;
  assign io_slave_1_ar_bits_prot = 3'h0;
  assign io_slave_1_ar_bits_qos = 4'h0;
  assign io_slave_1_r_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 101:22]
  assign io_slave_2_aw_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 95:22]
  assign io_slave_2_aw_bits_id = 16'h0;
  assign io_slave_2_aw_bits_addr = 34'h0;
  assign io_slave_2_aw_bits_len = 8'h0;
  assign io_slave_2_aw_bits_size = 3'h0;
  assign io_slave_2_aw_bits_burst = 2'h0;
  assign io_slave_2_aw_bits_lock = 1'h0;
  assign io_slave_2_aw_bits_cache = 4'h0;
  assign io_slave_2_aw_bits_prot = 3'h0;
  assign io_slave_2_aw_bits_qos = 4'h0;
  assign io_slave_2_w_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 99:22]
  assign io_slave_2_w_bits_data = 64'h0;
  assign io_slave_2_w_bits_strb = 8'h0;
  assign io_slave_2_w_bits_last = 1'h0;
  assign io_slave_2_b_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 102:22]
  assign io_slave_2_ar_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 97:22]
  assign io_slave_2_ar_bits_id = 16'h0;
  assign io_slave_2_ar_bits_addr = 34'h0;
  assign io_slave_2_ar_bits_len = 8'h0;
  assign io_slave_2_ar_bits_size = 3'h0;
  assign io_slave_2_ar_bits_burst = 2'h0;
  assign io_slave_2_ar_bits_lock = 1'h0;
  assign io_slave_2_ar_bits_cache = 4'h0;
  assign io_slave_2_ar_bits_prot = 3'h0;
  assign io_slave_2_ar_bits_qos = 4'h0;
  assign io_slave_2_r_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 101:22]
  assign io_slave_3_aw_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 95:22]
  assign io_slave_3_aw_bits_id = 16'h0;
  assign io_slave_3_aw_bits_addr = 34'h0;
  assign io_slave_3_aw_bits_len = 8'h0;
  assign io_slave_3_aw_bits_size = 3'h0;
  assign io_slave_3_aw_bits_burst = 2'h0;
  assign io_slave_3_aw_bits_lock = 1'h0;
  assign io_slave_3_aw_bits_cache = 4'h0;
  assign io_slave_3_aw_bits_prot = 3'h0;
  assign io_slave_3_aw_bits_qos = 4'h0;
  assign io_slave_3_w_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 99:22]
  assign io_slave_3_w_bits_data = 64'h0;
  assign io_slave_3_w_bits_strb = 8'h0;
  assign io_slave_3_w_bits_last = 1'h0;
  assign io_slave_3_b_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 102:22]
  assign io_slave_3_ar_valid = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 97:22]
  assign io_slave_3_ar_bits_id = 16'h0;
  assign io_slave_3_ar_bits_addr = 34'h0;
  assign io_slave_3_ar_bits_len = 8'h0;
  assign io_slave_3_ar_bits_size = 3'h0;
  assign io_slave_3_ar_bits_burst = 2'h0;
  assign io_slave_3_ar_bits_lock = 1'h0;
  assign io_slave_3_ar_bits_cache = 4'h0;
  assign io_slave_3_ar_bits_prot = 3'h0;
  assign io_slave_3_ar_bits_qos = 4'h0;
  assign io_slave_3_r_ready = 1'h0; // @[midas/src/main/scala/midas/platform/F1Shim.scala 101:22]
  assign top_clock = clock;
  assign top_reset = reset;
  assign top_ctrl_aw_valid = io_master_aw_valid; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_addr = io_master_aw_bits_addr; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_len = io_master_aw_bits_len; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_size = io_master_aw_bits_size; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_burst = io_master_aw_bits_burst; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_lock = io_master_aw_bits_lock; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_cache = io_master_aw_bits_cache; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_prot = io_master_aw_bits_prot; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_qos = io_master_aw_bits_qos; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_region = io_master_aw_bits_region; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_aw_bits_id = wCounterValue; // @[midas/src/main/scala/midas/platform/F1Shim.scala 108:32]
  assign top_ctrl_aw_bits_user = io_master_aw_bits_user; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_valid = io_master_w_valid; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_bits_data = io_master_w_bits_data; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_bits_last = io_master_w_bits_last; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_bits_id = io_master_w_bits_id; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_bits_strb = io_master_w_bits_strb; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_w_bits_user = io_master_w_bits_user; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_b_ready = io_master_b_ready; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_valid = io_master_ar_valid; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_addr = io_master_ar_bits_addr; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_len = io_master_ar_bits_len; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_size = io_master_ar_bits_size; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_burst = io_master_ar_bits_burst; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_lock = io_master_ar_bits_lock; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_cache = io_master_ar_bits_cache; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_prot = io_master_ar_bits_prot; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_qos = io_master_ar_bits_qos; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_region = io_master_ar_bits_region; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_ar_bits_id = rCounterValue; // @[midas/src/main/scala/midas/platform/F1Shim.scala 111:32]
  assign top_ctrl_ar_bits_user = io_master_ar_bits_user; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  assign top_ctrl_r_ready = io_master_r_ready; // @[midas/src/main/scala/midas/platform/F1Shim.scala 54:21]
  always @(posedge clock) begin
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      wCounterValue <= 12'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (_T) begin // @[src/main/scala/chisel3/util/Counter.scala 118:16]
      wCounterValue <= _wrap_value_T_1; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
    if (reset) begin // @[src/main/scala/chisel3/util/Counter.scala 61:40]
      rCounterValue <= 12'h0; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
    end else if (_T_1) begin // @[src/main/scala/chisel3/util/Counter.scala 118:16]
      rCounterValue <= _wrap_value_T_3; // @[src/main/scala/chisel3/util/Counter.scala 77:15]
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  wCounterValue = _RAND_0[11:0];
  _RAND_1 = {1{`RANDOM}};
  rCounterValue = _RAND_1[11:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module FAMETop(
  input         hostClock,
  input         hostReset,
  output        GCD__RationalClockBridge_clocks_0_sink_ready,
  input         GCD__RationalClockBridge_clocks_0_sink_bits,
  output        GCD__peekPokeBridge_reset_sink_ready,
  input         GCD__peekPokeBridge_reset_sink_valid,
  input         GCD__peekPokeBridge_reset_sink_bits,
  output        GCD__peekPokeBridge_io_e_sink_ready,
  input         GCD__peekPokeBridge_io_e_sink_valid,
  output        GCD__peekPokeBridge_io_b_sink_ready,
  input         GCD__peekPokeBridge_io_b_sink_valid,
  output        GCD__peekPokeBridge_io_a_sink_ready,
  input         GCD__peekPokeBridge_io_a_sink_valid,
  output        GCD__dut_inner2_io_z_sink_ready,
  input         GCD__dut_inner2_io_z_sink_valid,
  input  [15:0] GCD__dut_inner2_io_z_sink_bits,
  output        GCD__dut_inner2_io_v_sink_ready,
  input         GCD__dut_inner2_io_v_sink_valid,
  input         GCD__dut_inner2_io_v_sink_bits,
  output        GCD__dut_inner1_io_z_sink_ready,
  input         GCD__dut_inner1_io_z_sink_valid,
  input  [15:0] GCD__dut_inner1_io_z_sink_bits,
  output        GCD__dut_inner1_io_v_sink_ready,
  input         GCD__dut_inner1_io_v_sink_valid,
  input         GCD__dut_inner1_io_v_sink_bits,
  output        GCD_dut_inner1_reset_sink_ready,
  input         GCD_dut_inner1_reset_sink_valid,
  input         GCD_dut_inner1_reset_sink_bits,
  output        GCD_dut_inner2_reset_sink_ready,
  input         GCD_dut_inner2_reset_sink_valid,
  input         GCD_dut_inner2_reset_sink_bits,
  output        GCD_dut_inner1_io_e_sink_ready,
  input         GCD_dut_inner1_io_e_sink_valid,
  input         GCD_dut_inner1_io_e_sink_bits,
  output        GCD_dut_inner2_io_e_sink_ready,
  input         GCD_dut_inner2_io_e_sink_valid,
  input         GCD_dut_inner2_io_e_sink_bits,
  output        GCD_dut_inner1_io_b_sink_ready,
  input         GCD_dut_inner1_io_b_sink_valid,
  input  [15:0] GCD_dut_inner1_io_b_sink_bits,
  output        GCD_dut_inner2_io_a_sink_ready,
  input         GCD_dut_inner2_io_a_sink_valid,
  input  [15:0] GCD_dut_inner2_io_a_sink_bits,
  output        GCD_dut_inner1_io_a_sink_ready,
  input         GCD_dut_inner1_io_a_sink_valid,
  input  [15:0] GCD_dut_inner1_io_a_sink_bits,
  output        GCD_dut_inner2_io_b_sink_ready,
  input         GCD_dut_inner2_io_b_sink_valid,
  input  [15:0] GCD_dut_inner2_io_b_sink_bits,
  input         GCD__peekPokeBridge_io_v_source_ready,
  output        GCD__peekPokeBridge_io_v_source_valid,
  output        GCD__peekPokeBridge_io_v_source_bits,
  input         GCD__peekPokeBridge_io_z_source_ready,
  output        GCD__peekPokeBridge_io_z_source_valid,
  output [15:0] GCD__peekPokeBridge_io_z_source_bits,
  input         GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready,
  output        GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid,
  output        GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits,
  input         GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready,
  output        GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid,
  input         GCD_dut_inner2_io_z_source_ready,
  output        GCD_dut_inner2_io_z_source_valid,
  output [15:0] GCD_dut_inner2_io_z_source_bits,
  input         GCD_dut_inner2_io_v_source_ready,
  output        GCD_dut_inner2_io_v_source_valid,
  output        GCD_dut_inner2_io_v_source_bits,
  input         GCD_dut_inner1_io_z_source_ready,
  output        GCD_dut_inner1_io_z_source_valid,
  output [15:0] GCD_dut_inner1_io_z_source_bits,
  input         GCD_dut_inner1_io_v_source_ready,
  output        GCD_dut_inner1_io_v_source_valid,
  output        GCD_dut_inner1_io_v_source_bits
);
  wire  GCD___hostClock;
  wire  GCD___hostReset;
  wire  GCD___RationalClockBridge_clocks_0_sink_ready;
  wire  GCD___RationalClockBridge_clocks_0_sink_bits;
  wire  GCD___dut_inner1_io_z_sink_ready;
  wire  GCD___dut_inner1_io_z_sink_valid;
  wire [15:0] GCD___dut_inner1_io_z_sink_bits;
  wire  GCD___peekPokeBridge_reset_sink_ready;
  wire  GCD___peekPokeBridge_reset_sink_valid;
  wire  GCD___peekPokeBridge_reset_sink_bits;
  wire  GCD___dut_inner2_io_v_sink_ready;
  wire  GCD___dut_inner2_io_v_sink_valid;
  wire  GCD___dut_inner2_io_v_sink_bits;
  wire  GCD___dut_inner1_io_v_sink_ready;
  wire  GCD___dut_inner1_io_v_sink_valid;
  wire  GCD___dut_inner1_io_v_sink_bits;
  wire  GCD___peekPokeBridge_io_b_sink_ready;
  wire  GCD___peekPokeBridge_io_b_sink_valid;
  wire  GCD___peekPokeBridge_io_e_sink_ready;
  wire  GCD___peekPokeBridge_io_e_sink_valid;
  wire  GCD___dut_inner2_io_z_sink_ready;
  wire  GCD___dut_inner2_io_z_sink_valid;
  wire [15:0] GCD___dut_inner2_io_z_sink_bits;
  wire  GCD___peekPokeBridge_io_a_sink_ready;
  wire  GCD___peekPokeBridge_io_a_sink_valid;
  wire  GCD___peekPokeBridge_io_v_source_ready;
  wire  GCD___peekPokeBridge_io_v_source_valid;
  wire  GCD___peekPokeBridge_io_v_source_bits;
  wire  GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready;
  wire  GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid;
  wire  GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits;
  wire  GCD___peekPokeBridge_io_z_source_ready;
  wire  GCD___peekPokeBridge_io_z_source_valid;
  wire [15:0] GCD___peekPokeBridge_io_z_source_bits;
  wire  GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready;
  wire  GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid;
  wire  GCD_dut_inner1__hostClock; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__hostReset; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_b_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_b_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire [15:0] GCD_dut_inner1__io_b_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_e_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_e_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_e_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__reset_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__reset_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__reset_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_a_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_a_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire [15:0] GCD_dut_inner1__io_a_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_z_source_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_z_source_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire [15:0] GCD_dut_inner1__io_z_source_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_v_source_ready; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_v_source_valid; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner1__io_v_source_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  wire  GCD_dut_inner2__hostClock; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__hostReset; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_b_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_b_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire [15:0] GCD_dut_inner2__io_b_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_e_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_e_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_e_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__reset_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__reset_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__reset_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_a_sink_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_a_sink_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire [15:0] GCD_dut_inner2__io_a_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_z_source_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_z_source_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire [15:0] GCD_dut_inner2__io_z_source_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_v_source_ready; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_v_source_valid; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  wire  GCD_dut_inner2__io_v_source_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  GCD GCD__ (
    .hostClock(GCD___hostClock),
    .hostReset(GCD___hostReset),
    .RationalClockBridge_clocks_0_sink_ready(GCD___RationalClockBridge_clocks_0_sink_ready),
    .RationalClockBridge_clocks_0_sink_bits(GCD___RationalClockBridge_clocks_0_sink_bits),
    .dut_inner1_io_z_sink_ready(GCD___dut_inner1_io_z_sink_ready),
    .dut_inner1_io_z_sink_valid(GCD___dut_inner1_io_z_sink_valid),
    .dut_inner1_io_z_sink_bits(GCD___dut_inner1_io_z_sink_bits),
    .peekPokeBridge_reset_sink_ready(GCD___peekPokeBridge_reset_sink_ready),
    .peekPokeBridge_reset_sink_valid(GCD___peekPokeBridge_reset_sink_valid),
    .peekPokeBridge_reset_sink_bits(GCD___peekPokeBridge_reset_sink_bits),
    .dut_inner2_io_v_sink_ready(GCD___dut_inner2_io_v_sink_ready),
    .dut_inner2_io_v_sink_valid(GCD___dut_inner2_io_v_sink_valid),
    .dut_inner2_io_v_sink_bits(GCD___dut_inner2_io_v_sink_bits),
    .dut_inner1_io_v_sink_ready(GCD___dut_inner1_io_v_sink_ready),
    .dut_inner1_io_v_sink_valid(GCD___dut_inner1_io_v_sink_valid),
    .dut_inner1_io_v_sink_bits(GCD___dut_inner1_io_v_sink_bits),
    .peekPokeBridge_io_b_sink_ready(GCD___peekPokeBridge_io_b_sink_ready),
    .peekPokeBridge_io_b_sink_valid(GCD___peekPokeBridge_io_b_sink_valid),
    .peekPokeBridge_io_e_sink_ready(GCD___peekPokeBridge_io_e_sink_ready),
    .peekPokeBridge_io_e_sink_valid(GCD___peekPokeBridge_io_e_sink_valid),
    .dut_inner2_io_z_sink_ready(GCD___dut_inner2_io_z_sink_ready),
    .dut_inner2_io_z_sink_valid(GCD___dut_inner2_io_z_sink_valid),
    .dut_inner2_io_z_sink_bits(GCD___dut_inner2_io_z_sink_bits),
    .peekPokeBridge_io_a_sink_ready(GCD___peekPokeBridge_io_a_sink_ready),
    .peekPokeBridge_io_a_sink_valid(GCD___peekPokeBridge_io_a_sink_valid),
    .peekPokeBridge_io_v_source_ready(GCD___peekPokeBridge_io_v_source_ready),
    .peekPokeBridge_io_v_source_valid(GCD___peekPokeBridge_io_v_source_valid),
    .peekPokeBridge_io_v_source_bits(GCD___peekPokeBridge_io_v_source_bits),
    .midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready(
      GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready),
    .midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid(
      GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid),
    .midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits(
      GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits),
    .peekPokeBridge_io_z_source_ready(GCD___peekPokeBridge_io_z_source_ready),
    .peekPokeBridge_io_z_source_valid(GCD___peekPokeBridge_io_z_source_valid),
    .peekPokeBridge_io_z_source_bits(GCD___peekPokeBridge_io_z_source_bits),
    .midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready(
      GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready),
    .midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid(
      GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid)
  );
  GCDInner GCD_dut_inner1_ ( // @[src/main/scala/midasexamples/GCD.scala 36:22]
    .hostClock(GCD_dut_inner1__hostClock),
    .hostReset(GCD_dut_inner1__hostReset),
    .io_b_sink_ready(GCD_dut_inner1__io_b_sink_ready),
    .io_b_sink_valid(GCD_dut_inner1__io_b_sink_valid),
    .io_b_sink_bits(GCD_dut_inner1__io_b_sink_bits),
    .io_e_sink_ready(GCD_dut_inner1__io_e_sink_ready),
    .io_e_sink_valid(GCD_dut_inner1__io_e_sink_valid),
    .io_e_sink_bits(GCD_dut_inner1__io_e_sink_bits),
    .reset_sink_ready(GCD_dut_inner1__reset_sink_ready),
    .reset_sink_valid(GCD_dut_inner1__reset_sink_valid),
    .reset_sink_bits(GCD_dut_inner1__reset_sink_bits),
    .io_a_sink_ready(GCD_dut_inner1__io_a_sink_ready),
    .io_a_sink_valid(GCD_dut_inner1__io_a_sink_valid),
    .io_a_sink_bits(GCD_dut_inner1__io_a_sink_bits),
    .io_z_source_ready(GCD_dut_inner1__io_z_source_ready),
    .io_z_source_valid(GCD_dut_inner1__io_z_source_valid),
    .io_z_source_bits(GCD_dut_inner1__io_z_source_bits),
    .io_v_source_ready(GCD_dut_inner1__io_v_source_ready),
    .io_v_source_valid(GCD_dut_inner1__io_v_source_valid),
    .io_v_source_bits(GCD_dut_inner1__io_v_source_bits)
  );
  GCDInner GCD_dut_inner2_ ( // @[src/main/scala/midasexamples/GCD.scala 38:22]
    .hostClock(GCD_dut_inner2__hostClock),
    .hostReset(GCD_dut_inner2__hostReset),
    .io_b_sink_ready(GCD_dut_inner2__io_b_sink_ready),
    .io_b_sink_valid(GCD_dut_inner2__io_b_sink_valid),
    .io_b_sink_bits(GCD_dut_inner2__io_b_sink_bits),
    .io_e_sink_ready(GCD_dut_inner2__io_e_sink_ready),
    .io_e_sink_valid(GCD_dut_inner2__io_e_sink_valid),
    .io_e_sink_bits(GCD_dut_inner2__io_e_sink_bits),
    .reset_sink_ready(GCD_dut_inner2__reset_sink_ready),
    .reset_sink_valid(GCD_dut_inner2__reset_sink_valid),
    .reset_sink_bits(GCD_dut_inner2__reset_sink_bits),
    .io_a_sink_ready(GCD_dut_inner2__io_a_sink_ready),
    .io_a_sink_valid(GCD_dut_inner2__io_a_sink_valid),
    .io_a_sink_bits(GCD_dut_inner2__io_a_sink_bits),
    .io_z_source_ready(GCD_dut_inner2__io_z_source_ready),
    .io_z_source_valid(GCD_dut_inner2__io_z_source_valid),
    .io_z_source_bits(GCD_dut_inner2__io_z_source_bits),
    .io_v_source_ready(GCD_dut_inner2__io_v_source_ready),
    .io_v_source_valid(GCD_dut_inner2__io_v_source_valid),
    .io_v_source_bits(GCD_dut_inner2__io_v_source_bits)
  );
  assign GCD__RationalClockBridge_clocks_0_sink_ready = GCD___RationalClockBridge_clocks_0_sink_ready;
  assign GCD__peekPokeBridge_reset_sink_ready = GCD___peekPokeBridge_reset_sink_ready;
  assign GCD__peekPokeBridge_io_e_sink_ready = GCD___peekPokeBridge_io_e_sink_ready;
  assign GCD__peekPokeBridge_io_b_sink_ready = GCD___peekPokeBridge_io_b_sink_ready;
  assign GCD__peekPokeBridge_io_a_sink_ready = GCD___peekPokeBridge_io_a_sink_ready;
  assign GCD__dut_inner2_io_z_sink_ready = GCD___dut_inner2_io_z_sink_ready;
  assign GCD__dut_inner2_io_v_sink_ready = GCD___dut_inner2_io_v_sink_ready;
  assign GCD__dut_inner1_io_z_sink_ready = GCD___dut_inner1_io_z_sink_ready;
  assign GCD__dut_inner1_io_v_sink_ready = GCD___dut_inner1_io_v_sink_ready;
  assign GCD_dut_inner1_reset_sink_ready = GCD_dut_inner1__reset_sink_ready;
  assign GCD_dut_inner2_reset_sink_ready = GCD_dut_inner2__reset_sink_ready;
  assign GCD_dut_inner1_io_e_sink_ready = GCD_dut_inner1__io_e_sink_ready;
  assign GCD_dut_inner2_io_e_sink_ready = GCD_dut_inner2__io_e_sink_ready;
  assign GCD_dut_inner1_io_b_sink_ready = GCD_dut_inner1__io_b_sink_ready;
  assign GCD_dut_inner2_io_a_sink_ready = GCD_dut_inner2__io_a_sink_ready;
  assign GCD_dut_inner1_io_a_sink_ready = GCD_dut_inner1__io_a_sink_ready;
  assign GCD_dut_inner2_io_b_sink_ready = GCD_dut_inner2__io_b_sink_ready;
  assign GCD__peekPokeBridge_io_v_source_valid = GCD___peekPokeBridge_io_v_source_valid;
  assign GCD__peekPokeBridge_io_v_source_bits = GCD___peekPokeBridge_io_v_source_bits;
  assign GCD__peekPokeBridge_io_z_source_valid = GCD___peekPokeBridge_io_z_source_valid;
  assign GCD__peekPokeBridge_io_z_source_bits = GCD___peekPokeBridge_io_z_source_bits;
  assign GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid =
    GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid;
  assign GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits =
    GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits;
  assign GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid =
    GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid;
  assign GCD_dut_inner2_io_z_source_valid = GCD_dut_inner2__io_z_source_valid;
  assign GCD_dut_inner2_io_z_source_bits = GCD_dut_inner2__io_z_source_bits;
  assign GCD_dut_inner2_io_v_source_valid = GCD_dut_inner2__io_v_source_valid;
  assign GCD_dut_inner2_io_v_source_bits = GCD_dut_inner2__io_v_source_bits;
  assign GCD_dut_inner1_io_z_source_valid = GCD_dut_inner1__io_z_source_valid;
  assign GCD_dut_inner1_io_z_source_bits = GCD_dut_inner1__io_z_source_bits;
  assign GCD_dut_inner1_io_v_source_valid = GCD_dut_inner1__io_v_source_valid;
  assign GCD_dut_inner1_io_v_source_bits = GCD_dut_inner1__io_v_source_bits;
  assign GCD___hostClock = hostClock;
  assign GCD___hostReset = hostReset;
  assign GCD___RationalClockBridge_clocks_0_sink_bits = GCD__RationalClockBridge_clocks_0_sink_bits;
  assign GCD___dut_inner1_io_z_sink_valid = GCD__dut_inner1_io_z_sink_valid;
  assign GCD___dut_inner1_io_z_sink_bits = GCD__dut_inner1_io_z_sink_bits;
  assign GCD___peekPokeBridge_reset_sink_valid = GCD__peekPokeBridge_reset_sink_valid;
  assign GCD___peekPokeBridge_reset_sink_bits = GCD__peekPokeBridge_reset_sink_bits;
  assign GCD___dut_inner2_io_v_sink_valid = GCD__dut_inner2_io_v_sink_valid;
  assign GCD___dut_inner2_io_v_sink_bits = GCD__dut_inner2_io_v_sink_bits;
  assign GCD___dut_inner1_io_v_sink_valid = GCD__dut_inner1_io_v_sink_valid;
  assign GCD___dut_inner1_io_v_sink_bits = GCD__dut_inner1_io_v_sink_bits;
  assign GCD___peekPokeBridge_io_b_sink_valid = GCD__peekPokeBridge_io_b_sink_valid;
  assign GCD___peekPokeBridge_io_e_sink_valid = GCD__peekPokeBridge_io_e_sink_valid;
  assign GCD___dut_inner2_io_z_sink_valid = GCD__dut_inner2_io_z_sink_valid;
  assign GCD___dut_inner2_io_z_sink_bits = GCD__dut_inner2_io_z_sink_bits;
  assign GCD___peekPokeBridge_io_a_sink_valid = GCD__peekPokeBridge_io_a_sink_valid;
  assign GCD___peekPokeBridge_io_v_source_ready = GCD__peekPokeBridge_io_v_source_ready;
  assign GCD___midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready =
    GCD__midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready;
  assign GCD___peekPokeBridge_io_z_source_ready = GCD__peekPokeBridge_io_z_source_ready;
  assign GCD___midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready =
    GCD__midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready;
  assign GCD_dut_inner1__hostClock = hostClock;
  assign GCD_dut_inner1__hostReset = hostReset;
  assign GCD_dut_inner1__io_b_sink_valid = GCD_dut_inner1_io_b_sink_valid;
  assign GCD_dut_inner1__io_b_sink_bits = GCD_dut_inner1_io_b_sink_bits;
  assign GCD_dut_inner1__io_e_sink_valid = GCD_dut_inner1_io_e_sink_valid;
  assign GCD_dut_inner1__io_e_sink_bits = GCD_dut_inner1_io_e_sink_bits;
  assign GCD_dut_inner1__reset_sink_valid = GCD_dut_inner1_reset_sink_valid;
  assign GCD_dut_inner1__reset_sink_bits = GCD_dut_inner1_reset_sink_bits;
  assign GCD_dut_inner1__io_a_sink_valid = GCD_dut_inner1_io_a_sink_valid;
  assign GCD_dut_inner1__io_a_sink_bits = GCD_dut_inner1_io_a_sink_bits;
  assign GCD_dut_inner1__io_z_source_ready = GCD_dut_inner1_io_z_source_ready;
  assign GCD_dut_inner1__io_v_source_ready = GCD_dut_inner1_io_v_source_ready;
  assign GCD_dut_inner2__hostClock = hostClock;
  assign GCD_dut_inner2__hostReset = hostReset;
  assign GCD_dut_inner2__io_b_sink_valid = GCD_dut_inner2_io_b_sink_valid;
  assign GCD_dut_inner2__io_b_sink_bits = GCD_dut_inner2_io_b_sink_bits;
  assign GCD_dut_inner2__io_e_sink_valid = GCD_dut_inner2_io_e_sink_valid;
  assign GCD_dut_inner2__io_e_sink_bits = GCD_dut_inner2_io_e_sink_bits;
  assign GCD_dut_inner2__reset_sink_valid = GCD_dut_inner2_reset_sink_valid;
  assign GCD_dut_inner2__reset_sink_bits = GCD_dut_inner2_reset_sink_bits;
  assign GCD_dut_inner2__io_a_sink_valid = GCD_dut_inner2_io_a_sink_valid;
  assign GCD_dut_inner2__io_a_sink_bits = GCD_dut_inner2_io_a_sink_bits;
  assign GCD_dut_inner2__io_z_source_ready = GCD_dut_inner2_io_z_source_ready;
  assign GCD_dut_inner2__io_v_source_ready = GCD_dut_inner2_io_v_source_ready;
endmodule
module GCD(
  input         hostClock,
  input         hostReset,
  output        RationalClockBridge_clocks_0_sink_ready,
  input         RationalClockBridge_clocks_0_sink_bits,
  output        dut_inner1_io_z_sink_ready,
  input         dut_inner1_io_z_sink_valid,
  input  [15:0] dut_inner1_io_z_sink_bits,
  output        peekPokeBridge_reset_sink_ready,
  input         peekPokeBridge_reset_sink_valid,
  input         peekPokeBridge_reset_sink_bits,
  output        dut_inner2_io_v_sink_ready,
  input         dut_inner2_io_v_sink_valid,
  input         dut_inner2_io_v_sink_bits,
  output        dut_inner1_io_v_sink_ready,
  input         dut_inner1_io_v_sink_valid,
  input         dut_inner1_io_v_sink_bits,
  output        peekPokeBridge_io_b_sink_ready,
  input         peekPokeBridge_io_b_sink_valid,
  output        peekPokeBridge_io_e_sink_ready,
  input         peekPokeBridge_io_e_sink_valid,
  output        dut_inner2_io_z_sink_ready,
  input         dut_inner2_io_z_sink_valid,
  input  [15:0] dut_inner2_io_z_sink_bits,
  output        peekPokeBridge_io_a_sink_ready,
  input         peekPokeBridge_io_a_sink_valid,
  input         peekPokeBridge_io_v_source_ready,
  output        peekPokeBridge_io_v_source_valid,
  output        peekPokeBridge_io_v_source_bits,
  input         midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready,
  output        midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid,
  output        midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits,
  input         peekPokeBridge_io_z_source_ready,
  output        peekPokeBridge_io_z_source_valid,
  output [15:0] peekPokeBridge_io_z_source_bits,
  input         midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready,
  output        midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
`endif // RANDOMIZE_REG_INIT
  wire  RationalClockBridge_clocks_0_buffer_I;
  wire  RationalClockBridge_clocks_0_buffer_CE;
  wire  RationalClockBridge_clocks_0_buffer_O;
  wire  dut__clock; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire  dut__reset; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire [15:0] dut__io_z; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire  dut__io_v; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire  dut__midasAsserts; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire [15:0] dut__inner2_io_z; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire  dut__inner2_io_v; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire [15:0] dut__inner1_io_z; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  wire  dut__inner1_io_v; // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
  reg  RationalClockBridge_clocks_0_enabled;
  reg  dut_inner1_io_z_fired_0;
  reg  peekPokeBridge_reset_fired_0;
  reg  dut_inner2_io_v_fired_0;
  reg  dut_inner1_io_v_fired_0;
  reg  peekPokeBridge_io_b_fired_0;
  reg  peekPokeBridge_io_e_fired_0;
  reg  dut_inner2_io_z_fired_0;
  reg  peekPokeBridge_io_a_fired_0;
  reg  peekPokeBridge_io_v_fired_0;
  reg  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0;
  reg  peekPokeBridge_io_z_fired_0;
  reg  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0;
  wire  targetCycleFinishing = (peekPokeBridge_io_v_fired_0 | peekPokeBridge_io_v_source_ready &
    peekPokeBridge_io_v_source_valid) & (midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 |
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid) & (peekPokeBridge_io_z_fired_0 |
    peekPokeBridge_io_z_source_ready & peekPokeBridge_io_z_source_valid) & (
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 |
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid) & dut_inner1_io_z_sink_valid &
    peekPokeBridge_reset_sink_valid & dut_inner2_io_v_sink_valid & dut_inner1_io_v_sink_valid &
    peekPokeBridge_io_b_sink_valid & peekPokeBridge_io_e_sink_valid & dut_inner2_io_z_sink_valid &
    peekPokeBridge_io_a_sink_valid;
  wire  _GEN_49 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : dut_inner1_io_z_fired_0 |
    dut_inner1_io_z_sink_ready & dut_inner1_io_z_sink_valid;
  wire  _GEN_52 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : peekPokeBridge_reset_fired_0 |
    peekPokeBridge_reset_sink_ready & peekPokeBridge_reset_sink_valid;
  wire  _GEN_55 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : dut_inner2_io_v_fired_0 |
    dut_inner2_io_v_sink_ready & dut_inner2_io_v_sink_valid;
  wire  _GEN_58 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : dut_inner1_io_v_fired_0 |
    dut_inner1_io_v_sink_ready & dut_inner1_io_v_sink_valid;
  wire  _GEN_61 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : peekPokeBridge_io_b_fired_0 |
    peekPokeBridge_io_b_sink_ready & peekPokeBridge_io_b_sink_valid;
  wire  _GEN_64 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : peekPokeBridge_io_e_fired_0 |
    peekPokeBridge_io_e_sink_ready & peekPokeBridge_io_e_sink_valid;
  wire  _GEN_67 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : dut_inner2_io_z_fired_0 |
    dut_inner2_io_z_sink_ready & dut_inner2_io_z_sink_valid;
  wire  _GEN_70 = targetCycleFinishing ? ~RationalClockBridge_clocks_0_sink_bits : peekPokeBridge_io_a_fired_0 |
    peekPokeBridge_io_a_sink_ready & peekPokeBridge_io_a_sink_valid;
  BUFGCE RationalClockBridge_clocks_0_buffer (
    .I(RationalClockBridge_clocks_0_buffer_I),
    .CE(RationalClockBridge_clocks_0_buffer_CE),
    .O(RationalClockBridge_clocks_0_buffer_O)
  );
  GCDDUT dut_ ( // @[firesim-lib/src/main/scala/testutils/PeekPokeHarness.scala 18:21]
    .clock(dut__clock),
    .reset(dut__reset),
    .io_z(dut__io_z),
    .io_v(dut__io_v),
    .midasAsserts(dut__midasAsserts),
    .inner2_io_z(dut__inner2_io_z),
    .inner2_io_v(dut__inner2_io_v),
    .inner1_io_z(dut__inner1_io_z),
    .inner1_io_v(dut__inner1_io_v)
  );
  assign RationalClockBridge_clocks_0_sink_ready = (peekPokeBridge_io_v_fired_0 | peekPokeBridge_io_v_source_ready &
    peekPokeBridge_io_v_source_valid) & (midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 |
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid) & (peekPokeBridge_io_z_fired_0 |
    peekPokeBridge_io_z_source_ready & peekPokeBridge_io_z_source_valid) & (
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 |
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid) & dut_inner1_io_z_sink_valid &
    peekPokeBridge_reset_sink_valid & dut_inner2_io_v_sink_valid & dut_inner1_io_v_sink_valid &
    peekPokeBridge_io_b_sink_valid & peekPokeBridge_io_e_sink_valid & dut_inner2_io_z_sink_valid &
    peekPokeBridge_io_a_sink_valid;
  assign dut_inner1_io_z_sink_ready = targetCycleFinishing & ~dut_inner1_io_z_fired_0;
  assign peekPokeBridge_reset_sink_ready = targetCycleFinishing & ~peekPokeBridge_reset_fired_0;
  assign dut_inner2_io_v_sink_ready = targetCycleFinishing & ~dut_inner2_io_v_fired_0;
  assign dut_inner1_io_v_sink_ready = targetCycleFinishing & ~dut_inner1_io_v_fired_0;
  assign peekPokeBridge_io_b_sink_ready = targetCycleFinishing & ~peekPokeBridge_io_b_fired_0;
  assign peekPokeBridge_io_e_sink_ready = targetCycleFinishing & ~peekPokeBridge_io_e_fired_0;
  assign dut_inner2_io_z_sink_ready = targetCycleFinishing & ~dut_inner2_io_z_fired_0;
  assign peekPokeBridge_io_a_sink_ready = targetCycleFinishing & ~peekPokeBridge_io_a_fired_0;
  assign peekPokeBridge_io_v_source_valid = ~peekPokeBridge_io_v_fired_0;
  assign peekPokeBridge_io_v_source_bits = dut__io_v; // @[firesim-lib/src/main/scala/bridges/PeekPokeBridge.scala 83:58]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid = peekPokeBridge_reset_sink_valid & ~
    midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0;
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_source_bits = dut__midasAsserts;
  assign peekPokeBridge_io_z_source_valid = ~peekPokeBridge_io_z_fired_0;
  assign peekPokeBridge_io_z_source_bits = dut__io_z; // @[firesim-lib/src/main/scala/bridges/PeekPokeBridge.scala 83:58]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid = ~
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0;
  assign RationalClockBridge_clocks_0_buffer_I = hostClock;
  assign RationalClockBridge_clocks_0_buffer_CE = RationalClockBridge_clocks_0_enabled & targetCycleFinishing & ~
    hostReset;
  assign dut__clock = RationalClockBridge_clocks_0_buffer_O;
  assign dut__reset = peekPokeBridge_reset_sink_bits; // @[firesim-lib/src/main/scala/bridges/PeekPokeBridge.scala 80:32 83:58]
  assign dut__inner2_io_z = dut_inner2_io_z_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  assign dut__inner2_io_v = dut_inner2_io_v_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 38:22]
  assign dut__inner1_io_z = dut_inner1_io_z_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  assign dut__inner1_io_v = dut_inner1_io_v_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 36:22]
  always @(posedge hostClock) begin
    if (hostReset) begin
      RationalClockBridge_clocks_0_enabled <= 1'h0;
    end else if (targetCycleFinishing) begin
      RationalClockBridge_clocks_0_enabled <= RationalClockBridge_clocks_0_sink_bits;
    end
    dut_inner1_io_z_fired_0 <= hostReset | _GEN_49;
    peekPokeBridge_reset_fired_0 <= hostReset | _GEN_52;
    dut_inner2_io_v_fired_0 <= hostReset | _GEN_55;
    dut_inner1_io_v_fired_0 <= hostReset | _GEN_58;
    peekPokeBridge_io_b_fired_0 <= hostReset | _GEN_61;
    peekPokeBridge_io_e_fired_0 <= hostReset | _GEN_64;
    dut_inner2_io_z_fired_0 <= hostReset | _GEN_67;
    peekPokeBridge_io_a_fired_0 <= hostReset | _GEN_70;
    if (hostReset) begin
      peekPokeBridge_io_v_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      peekPokeBridge_io_v_fired_0 <= ~RationalClockBridge_clocks_0_enabled;
    end else begin
      peekPokeBridge_io_v_fired_0 <= peekPokeBridge_io_v_fired_0 | peekPokeBridge_io_v_source_ready &
        peekPokeBridge_io_v_source_valid;
    end
    if (hostReset) begin
      midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 <= ~RationalClockBridge_clocks_0_enabled;
    end else begin
      midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 <=
        midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 |
        midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready &
        midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid;
    end
    if (hostReset) begin
      peekPokeBridge_io_z_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      peekPokeBridge_io_z_fired_0 <= ~RationalClockBridge_clocks_0_enabled;
    end else begin
      peekPokeBridge_io_z_fired_0 <= peekPokeBridge_io_z_fired_0 | peekPokeBridge_io_z_source_ready &
        peekPokeBridge_io_z_source_valid;
    end
    if (hostReset) begin
      midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 <= ~RationalClockBridge_clocks_0_enabled;
    end else begin
      midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 <=
        midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 |
        midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready &
        midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid;
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  RationalClockBridge_clocks_0_enabled = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  dut_inner1_io_z_fired_0 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  peekPokeBridge_reset_fired_0 = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  dut_inner2_io_v_fired_0 = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  dut_inner1_io_v_fired_0 = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  peekPokeBridge_io_b_fired_0 = _RAND_5[0:0];
  _RAND_6 = {1{`RANDOM}};
  peekPokeBridge_io_e_fired_0 = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  dut_inner2_io_z_fired_0 = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  peekPokeBridge_io_a_fired_0 = _RAND_8[0:0];
  _RAND_9 = {1{`RANDOM}};
  peekPokeBridge_io_v_fired_0 = _RAND_9[0:0];
  _RAND_10 = {1{`RANDOM}};
  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 = _RAND_10[0:0];
  _RAND_11 = {1{`RANDOM}};
  peekPokeBridge_io_z_fired_0 = _RAND_11[0:0];
  _RAND_12 = {1{`RANDOM}};
  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 = _RAND_12[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module GCD_threaded( // @[@ [Added during FAME5Transform]]
  input   hostClock,
  input   hostReset,
  input   RationalClockBridge_clocks_0_sink_valid,
  input   RationalClockBridge_clocks_0_sink_bits,
  input   dut_inner1_io_z_sink_valid,
  input   peekPokeBridge_reset_sink_valid,
  input   dut_inner2_io_v_sink_valid,
  input   dut_inner1_io_v_sink_valid,
  input   peekPokeBridge_io_b_sink_valid,
  input   peekPokeBridge_io_e_sink_valid,
  input   dut_inner2_io_z_sink_valid,
  input   peekPokeBridge_io_a_sink_valid,
  input   peekPokeBridge_io_v_source_ready,
  output  peekPokeBridge_io_v_source_valid,
  input   midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready,
  output  midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid,
  input   peekPokeBridge_io_z_source_ready,
  output  peekPokeBridge_io_z_source_valid,
  input   midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready,
  output  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_5;
`endif // RANDOMIZE_REG_INIT
  wire  RationalClockBridge_clocks_0_buffer_I;
  wire  RationalClockBridge_clocks_0_buffer_CE;
  wire  RationalClockBridge_clocks_0_buffer_O;
  reg  RationalClockBridge_clocks_0_enabled [0:0]; // @[@ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_read_data; // @[@ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  RationalClockBridge_clocks_0_enabled_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  peekPokeBridge_io_v_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_v_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  peekPokeBridge_io_z_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  peekPokeBridge_io_z_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  threadIdx; // @[@ [Added during FAME5Transform]]
  wire  targetCycleFinishing = (peekPokeBridge_io_v_fired_0_read_data | peekPokeBridge_io_v_source_ready &
    peekPokeBridge_io_v_source_valid) & (midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_data |
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid) & (peekPokeBridge_io_z_fired_0_read_data |
    peekPokeBridge_io_z_source_ready & peekPokeBridge_io_z_source_valid) & (
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_data |
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid) & dut_inner1_io_z_sink_valid &
    peekPokeBridge_reset_sink_valid & dut_inner2_io_v_sink_valid & dut_inner1_io_v_sink_valid &
    peekPokeBridge_io_b_sink_valid & peekPokeBridge_io_e_sink_valid & dut_inner2_io_z_sink_valid &
    peekPokeBridge_io_a_sink_valid & RationalClockBridge_clocks_0_sink_valid;
  wire [1:0] _GEN_118 = ~threadIdx ? 2'h0 : threadIdx + 1'h1; // @[@ [Added during FAME5Transform]]
  BUFGCE RationalClockBridge_clocks_0_buffer (
    .I(RationalClockBridge_clocks_0_buffer_I),
    .CE(RationalClockBridge_clocks_0_buffer_CE),
    .O(RationalClockBridge_clocks_0_buffer_O)
  );
  assign RationalClockBridge_clocks_0_enabled_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_read_data =
    RationalClockBridge_clocks_0_enabled[RationalClockBridge_clocks_0_enabled_read_addr]; // @[@ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_write_data = hostReset ? 1'h0 : targetCycleFinishing ?
    RationalClockBridge_clocks_0_sink_bits : RationalClockBridge_clocks_0_enabled_read_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign RationalClockBridge_clocks_0_enabled_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_read_data = peekPokeBridge_io_v_fired_0[peekPokeBridge_io_v_fired_0_read_addr]; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_write_data = hostReset ? 1'h0 : targetCycleFinishing ? ~
    RationalClockBridge_clocks_0_enabled_read_data : peekPokeBridge_io_v_fired_0_read_data |
    peekPokeBridge_io_v_source_ready & peekPokeBridge_io_v_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_data =
    midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0[midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_addr]
    ; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_data = hostReset ? 1'h0 : targetCycleFinishing
     ? ~RationalClockBridge_clocks_0_enabled_read_data :
    midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_data |
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_read_data = peekPokeBridge_io_z_fired_0[peekPokeBridge_io_z_fired_0_read_addr]; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_write_data = hostReset ? 1'h0 : targetCycleFinishing ? ~
    RationalClockBridge_clocks_0_enabled_read_data : peekPokeBridge_io_z_fired_0_read_data |
    peekPokeBridge_io_z_source_ready & peekPokeBridge_io_z_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign peekPokeBridge_io_z_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_data =
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0[midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_addr]
    ; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_data = hostReset ? 1'h0 :
    targetCycleFinishing ? ~RationalClockBridge_clocks_0_enabled_read_data :
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_data |
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_ready &
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign peekPokeBridge_io_v_source_valid = ~peekPokeBridge_io_v_fired_0_read_data;
  assign midasAsserts_RationalClockBridge_clocks_0_asserts_source_valid = peekPokeBridge_reset_sink_valid & ~
    midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_read_data;
  assign peekPokeBridge_io_z_source_valid = ~peekPokeBridge_io_z_fired_0_read_data;
  assign midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_source_valid = ~
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_read_data;
  assign RationalClockBridge_clocks_0_buffer_I = hostClock;
  assign RationalClockBridge_clocks_0_buffer_CE = RationalClockBridge_clocks_0_enabled_read_data & targetCycleFinishing
     & ~hostReset;
  always @(posedge hostClock) begin
    if (RationalClockBridge_clocks_0_enabled_write_en & RationalClockBridge_clocks_0_enabled_write_mask) begin
      RationalClockBridge_clocks_0_enabled[RationalClockBridge_clocks_0_enabled_write_addr] <=
        RationalClockBridge_clocks_0_enabled_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (peekPokeBridge_io_v_fired_0_write_en & peekPokeBridge_io_v_fired_0_write_mask) begin
      peekPokeBridge_io_v_fired_0[peekPokeBridge_io_v_fired_0_write_addr] <= peekPokeBridge_io_v_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_en &
      midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_mask) begin

        midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0[midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_addr]
         <= midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (peekPokeBridge_io_z_fired_0_write_en & peekPokeBridge_io_z_fired_0_write_mask) begin
      peekPokeBridge_io_z_fired_0[peekPokeBridge_io_z_fired_0_write_addr] <= peekPokeBridge_io_z_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_en &
      midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_mask) begin

        midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0[midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_addr]
         <= midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    threadIdx <= _GEN_118[0]; // @[@ [Added during FAME5Transform]]
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    RationalClockBridge_clocks_0_enabled[initvar] = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    peekPokeBridge_io_v_fired_0[initvar] = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    midasAsserts_RationalClockBridge_clocks_0_asserts_fired_0[initvar] = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    peekPokeBridge_io_z_fired_0[initvar] = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    midasAsserts_RationalClockBridge_clocks_0_globalResetCondition_fired_0[initvar] = _RAND_4[0:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  threadIdx = _RAND_5[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module GCDInner(
  input         hostClock,
  input         hostReset,
  output        io_b_sink_ready,
  input         io_b_sink_valid,
  input  [15:0] io_b_sink_bits,
  output        io_e_sink_ready,
  input         io_e_sink_valid,
  input         io_e_sink_bits,
  output        reset_sink_ready,
  input         reset_sink_valid,
  input         reset_sink_bits,
  output        io_a_sink_ready,
  input         io_a_sink_valid,
  input  [15:0] io_a_sink_bits,
  input         io_z_source_ready,
  output        io_z_source_valid,
  output [15:0] io_z_source_bits,
  input         io_v_source_ready,
  output        io_v_source_valid,
  output        io_v_source_bits
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
`endif // RANDOMIZE_REG_INIT
  wire  clock_buffer_I;
  wire  clock_buffer_CE;
  wire  clock_buffer_O;
  reg  clock_enabled;
  reg  io_b_fired_0;
  reg  io_e_fired_0;
  reg  reset_fired_0;
  reg  io_a_fired_0;
  reg  io_z_fired_0;
  reg  io_v_fired_0;
  reg [15:0] x; // @[src/main/scala/midasexamples/GCD.scala 21:15]
  reg [15:0] y; // @[src/main/scala/midasexamples/GCD.scala 22:15]
  wire [15:0] _x_T_1 = x - y; // @[src/main/scala/midasexamples/GCD.scala 23:24]
  wire [15:0] _y_T_1 = y - x; // @[src/main/scala/midasexamples/GCD.scala 24:25]
  wire  targetCycleFinishing = (io_z_fired_0 | io_z_source_ready & io_z_source_valid) & (io_v_fired_0 |
    io_v_source_ready & io_v_source_valid) & io_b_sink_valid & io_e_sink_valid & reset_sink_valid & io_a_sink_valid;
  BUFGCE clock_buffer (
    .I(clock_buffer_I),
    .CE(clock_buffer_CE),
    .O(clock_buffer_O)
  );
  assign io_b_sink_ready = targetCycleFinishing & ~io_b_fired_0;
  assign io_e_sink_ready = targetCycleFinishing & ~io_e_fired_0;
  assign reset_sink_ready = targetCycleFinishing & ~reset_fired_0;
  assign io_a_sink_ready = targetCycleFinishing & ~io_a_fired_0;
  assign io_z_source_valid = ~io_z_fired_0;
  assign io_z_source_bits = x; // @[src/main/scala/midasexamples/GCD.scala 26:8]
  assign io_v_source_valid = ~io_v_fired_0;
  assign io_v_source_bits = y == 16'h0; // @[src/main/scala/midasexamples/GCD.scala 27:13]
  assign clock_buffer_I = hostClock;
  assign clock_buffer_CE = clock_enabled & targetCycleFinishing & ~hostReset;
  always @(posedge hostClock) begin
    if (hostReset) begin
      clock_enabled <= 1'h0;
    end else begin
      clock_enabled <= targetCycleFinishing | clock_enabled;
    end
    if (hostReset) begin
      io_b_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      io_b_fired_0 <= 1'h0;
    end else begin
      io_b_fired_0 <= io_b_fired_0 | io_b_sink_ready & io_b_sink_valid;
    end
    if (hostReset) begin
      io_e_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      io_e_fired_0 <= 1'h0;
    end else begin
      io_e_fired_0 <= io_e_fired_0 | io_e_sink_ready & io_e_sink_valid;
    end
    if (hostReset) begin
      reset_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      reset_fired_0 <= 1'h0;
    end else begin
      reset_fired_0 <= reset_fired_0 | reset_sink_ready & reset_sink_valid;
    end
    if (hostReset) begin
      io_a_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      io_a_fired_0 <= 1'h0;
    end else begin
      io_a_fired_0 <= io_a_fired_0 | io_a_sink_ready & io_a_sink_valid;
    end
    if (hostReset) begin
      io_z_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      io_z_fired_0 <= 1'h0;
    end else begin
      io_z_fired_0 <= io_z_fired_0 | io_z_source_ready & io_z_source_valid;
    end
    if (hostReset) begin
      io_v_fired_0 <= 1'h0;
    end else if (targetCycleFinishing) begin
      io_v_fired_0 <= 1'h0;
    end else begin
      io_v_fired_0 <= io_v_fired_0 | io_v_source_ready & io_v_source_valid;
    end
  end
  always @(posedge clock_buffer_O) begin
    if (io_e_sink_bits) begin // @[src/main/scala/midasexamples/GCD.scala 25:14]
      x <= io_a_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 25:18]
    end else if (x > y) begin // @[src/main/scala/midasexamples/GCD.scala 23:15]
      x <= _x_T_1; // @[src/main/scala/midasexamples/GCD.scala 23:19]
    end
    if (io_e_sink_bits) begin // @[src/main/scala/midasexamples/GCD.scala 25:14]
      y <= io_b_sink_bits; // @[src/main/scala/midasexamples/GCD.scala 25:29]
    end else if (x <= y) begin // @[src/main/scala/midasexamples/GCD.scala 24:16]
      y <= _y_T_1; // @[src/main/scala/midasexamples/GCD.scala 24:20]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset_sink_bits) begin
          $fwrite(32'h80000002,"X: %d, Y:%d\n",x,y); // @[src/main/scala/midasexamples/GCD.scala 30:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  clock_enabled = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  io_b_fired_0 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  io_e_fired_0 = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  reset_fired_0 = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  io_a_fired_0 = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  io_z_fired_0 = _RAND_5[0:0];
  _RAND_6 = {1{`RANDOM}};
  io_v_fired_0 = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  x = _RAND_7[15:0];
  _RAND_8 = {1{`RANDOM}};
  y = _RAND_8[15:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module GCDInner_threaded( // @[@ [Added during FAME5Transform]]
  input         hostClock,
  input         hostReset,
  input         io_b_sink_valid,
  input  [15:0] io_b_sink_bits,
  input         io_e_sink_valid,
  input         io_e_sink_bits,
  input         reset_sink_valid,
  input         reset_sink_bits,
  input         io_a_sink_valid,
  input  [15:0] io_a_sink_bits,
  input         io_z_source_ready,
  output        io_z_source_valid,
  input         io_v_source_ready,
  output        io_v_source_valid
);
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_5;
`endif // RANDOMIZE_REG_INIT
  wire  clock_buffer_I;
  wire  clock_buffer_CE;
  wire  clock_buffer_O;
  reg  clock_enabled [0:0]; // @[@ [Added during FAME5Transform]]
  wire  clock_enabled_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  clock_enabled_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  clock_enabled_read_data; // @[@ [Added during FAME5Transform]]
  wire  clock_enabled_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  clock_enabled_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  clock_enabled_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  clock_enabled_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  io_z_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  io_z_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_z_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_z_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  io_z_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_z_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_z_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_z_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg  io_v_fired_0 [0:0]; // @[@ [Added during FAME5Transform]]
  wire  io_v_fired_0_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_v_fired_0_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_v_fired_0_read_data; // @[@ [Added during FAME5Transform]]
  wire  io_v_fired_0_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_v_fired_0_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_v_fired_0_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  wire  io_v_fired_0_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  reg [15:0] x [0:0]; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  wire  x_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:{15,15}]
  wire  x_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:{15,15}]
  wire [15:0] x_read_data; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  wire [15:0] x_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15 25:{14,18}]
  wire  x_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:{15,15}]
  wire  x_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:{15,15}]
  wire  x_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15 25:{14,18}]
  reg [15:0] y [0:0]; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  wire  y_read_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:{15,15}]
  wire  y_read_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:{15,15}]
  wire [15:0] y_read_data; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  wire [15:0] y_write_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15 25:{14,29}]
  wire  y_write_addr; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:{15,15}]
  wire  y_write_mask; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:{15,15}]
  wire  y_write_en; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15 25:{14,29}]
  reg  threadIdx; // @[@ [Added during FAME5Transform]]
  wire [15:0] _x_T_1 = x_read_data - y_read_data; // @[src/main/scala/midasexamples/GCD.scala 23:24]
  wire [15:0] _GEN_0 = x_read_data > y_read_data ? _x_T_1 : x_read_data; // @[src/main/scala/midasexamples/GCD.scala 21:15 23:{15,19}]
  wire [15:0] _y_T_1 = y_read_data - x_read_data; // @[src/main/scala/midasexamples/GCD.scala 24:25]
  wire [15:0] _GEN_1 = x_read_data <= y_read_data ? _y_T_1 : y_read_data; // @[src/main/scala/midasexamples/GCD.scala 22:15 24:{16,20}]
  wire  targetCycleFinishing = (io_z_fired_0_read_data | io_z_source_ready & io_z_source_valid) & (
    io_v_fired_0_read_data | io_v_source_ready & io_v_source_valid) & io_b_sink_valid & io_e_sink_valid &
    reset_sink_valid & io_a_sink_valid;
  wire [1:0] _GEN_36 = ~threadIdx ? 2'h0 : threadIdx + 1'h1; // @[@ [Added during FAME5Transform]]
  BUFGCE clock_buffer (
    .I(clock_buffer_I),
    .CE(clock_buffer_CE),
    .O(clock_buffer_O)
  );
  assign clock_enabled_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign clock_enabled_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign clock_enabled_read_data = clock_enabled[clock_enabled_read_addr]; // @[@ [Added during FAME5Transform]]
  assign clock_enabled_write_data = hostReset ? 1'h0 : targetCycleFinishing | clock_enabled_read_data; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign clock_enabled_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign clock_enabled_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign clock_enabled_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign io_z_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign io_z_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign io_z_fired_0_read_data = io_z_fired_0[io_z_fired_0_read_addr]; // @[@ [Added during FAME5Transform]]
  assign io_z_fired_0_write_data = hostReset ? 1'h0 : targetCycleFinishing ? 1'h0 : io_z_fired_0_read_data |
    io_z_source_ready & io_z_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign io_z_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign io_z_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign io_z_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign io_v_fired_0_read_en = 1'h1; // @[@ [Added during FAME5Transform]]
  assign io_v_fired_0_read_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign io_v_fired_0_read_data = io_v_fired_0[io_v_fired_0_read_addr]; // @[@ [Added during FAME5Transform]]
  assign io_v_fired_0_write_data = hostReset ? 1'h0 : targetCycleFinishing ? 1'h0 : io_v_fired_0_read_data |
    io_v_source_ready & io_v_source_valid; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign io_v_fired_0_write_addr = threadIdx; // @[@ [Added during FAME5Transform]]
  assign io_v_fired_0_write_mask = 1'h1; // @[@ [Added during FAME5Transform]]
  assign io_v_fired_0_write_en = 1'h1; // @[@ [Added during FAME5Transform] @ [Added during FAME5Transform] @ [Added during FAME5Transform]]
  assign x_read_en = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  assign x_read_addr = threadIdx; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  assign x_read_data = x[x_read_addr]; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  assign x_write_data = io_e_sink_bits ? io_a_sink_bits : _GEN_0; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 25:{14,18}]
  assign x_write_addr = threadIdx; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  assign x_write_mask = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
  assign x_write_en = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 25:{14,18}]
  assign y_read_en = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  assign y_read_addr = threadIdx; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  assign y_read_data = y[y_read_addr]; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  assign y_write_data = io_e_sink_bits ? io_b_sink_bits : _GEN_1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 25:{14,29}]
  assign y_write_addr = threadIdx; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  assign y_write_mask = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
  assign y_write_en = 1'h1; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 25:{14,29}]
  assign io_z_source_valid = ~io_z_fired_0_read_data;
  assign io_v_source_valid = ~io_v_fired_0_read_data;
  assign clock_buffer_I = hostClock;
  assign clock_buffer_CE = clock_enabled_read_data & targetCycleFinishing & ~hostReset;
  always @(posedge hostClock) begin
    if (clock_enabled_write_en & clock_enabled_write_mask) begin
      clock_enabled[clock_enabled_write_addr] <= clock_enabled_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (io_z_fired_0_write_en & io_z_fired_0_write_mask) begin
      io_z_fired_0[io_z_fired_0_write_addr] <= io_z_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    if (io_v_fired_0_write_en & io_v_fired_0_write_mask) begin
      io_v_fired_0[io_v_fired_0_write_addr] <= io_v_fired_0_write_data; // @[@ [Added during FAME5Transform]]
    end
    threadIdx <= _GEN_36[0]; // @[@ [Added during FAME5Transform]]
  end
  always @(posedge clock_buffer_O) begin
    if (x_write_en & x_write_mask) begin
      x[x_write_addr] <= x_write_data; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 21:15]
    end
    if (y_write_en & y_write_mask) begin
      y[y_write_addr] <= y_write_data; // @[@ [Added during FAME5Transform] src/main/scala/midasexamples/GCD.scala 22:15]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset_sink_bits) begin
          $fwrite(32'h80000002,"X: %d, Y:%d\n",x_read_data,y_read_data); // @[src/main/scala/midasexamples/GCD.scala 30:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    clock_enabled[initvar] = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    io_z_fired_0[initvar] = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    io_v_fired_0[initvar] = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    x[initvar] = _RAND_3[15:0];
  _RAND_4 = {1{`RANDOM}};
  for (initvar = 0; initvar < 1; initvar = initvar+1)
    y[initvar] = _RAND_4[15:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_5 = {1{`RANDOM}};
  threadIdx = _RAND_5[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module GCDDUT(
  input         clock,
  input         reset,
  output [15:0] io_z, // @[src/main/scala/midasexamples/GCD.scala 35:18]
  output        io_v, // @[src/main/scala/midasexamples/GCD.scala 35:18]
  output        midasAsserts,
  input  [15:0] inner2_io_z, // @[src/main/scala/midasexamples/GCD.scala 38:22]
  input         inner2_io_v, // @[src/main/scala/midasexamples/GCD.scala 38:22]
  input  [15:0] inner1_io_z, // @[src/main/scala/midasexamples/GCD.scala 36:22]
  input         inner1_io_v // @[src/main/scala/midasexamples/GCD.scala 36:22]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_REG_INIT
  reg  select; // @[src/main/scala/midasexamples/GCD.scala 41:23]
  reg  done1; // @[src/main/scala/midasexamples/GCD.scala 44:24]
  reg [15:0] result1; // @[src/main/scala/midasexamples/GCD.scala 45:20]
  wire  _GEN_0 = inner1_io_v | done1; // @[src/main/scala/midasexamples/GCD.scala 49:27 50:13 44:24]
  reg  done2; // @[src/main/scala/midasexamples/GCD.scala 54:24]
  reg [15:0] result2; // @[src/main/scala/midasexamples/GCD.scala 55:20]
  wire  _GEN_4 = inner2_io_v | done2; // @[src/main/scala/midasexamples/GCD.scala 59:27 60:13 54:24]
  assign io_z = select ? result1 : result2; // @[src/main/scala/midasexamples/GCD.scala 72:14]
  assign io_v = done1 & done2; // @[src/main/scala/midasexamples/GCD.scala 73:17]
  assign midasAsserts = ~reset & ~(~done1 | ~done2 | result1 == result2); // @[src/main/scala/midasexamples/GCD.scala 75:9]
  always @(posedge clock) begin
    if (reset) begin // @[src/main/scala/midasexamples/GCD.scala 41:23]
      select <= 1'h0; // @[src/main/scala/midasexamples/GCD.scala 41:23]
    end else begin
      select <= ~select; // @[src/main/scala/midasexamples/GCD.scala 42:10]
    end
    if (reset) begin // @[src/main/scala/midasexamples/GCD.scala 44:24]
      done1 <= 1'h0; // @[src/main/scala/midasexamples/GCD.scala 44:24]
    end else if (io_v) begin // @[src/main/scala/midasexamples/GCD.scala 47:14]
      done1 <= 1'h0; // @[src/main/scala/midasexamples/GCD.scala 48:11]
    end else begin
      done1 <= _GEN_0;
    end
    if (!(io_v)) begin // @[src/main/scala/midasexamples/GCD.scala 47:14]
      if (inner1_io_v) begin // @[src/main/scala/midasexamples/GCD.scala 49:27]
        result1 <= inner1_io_z; // @[src/main/scala/midasexamples/GCD.scala 51:13]
      end
    end
    if (reset) begin // @[src/main/scala/midasexamples/GCD.scala 54:24]
      done2 <= 1'h0; // @[src/main/scala/midasexamples/GCD.scala 54:24]
    end else if (io_v) begin // @[src/main/scala/midasexamples/GCD.scala 57:14]
      done2 <= 1'h0; // @[src/main/scala/midasexamples/GCD.scala 58:11]
    end else begin
      done2 <= _GEN_4;
    end
    if (!(io_v)) begin // @[src/main/scala/midasexamples/GCD.scala 57:14]
      if (inner2_io_v) begin // @[src/main/scala/midasexamples/GCD.scala 59:27]
        result2 <= inner2_io_z; // @[src/main/scala/midasexamples/GCD.scala 61:13]
      end
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  select = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  done1 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  result1 = _RAND_2[15:0];
  _RAND_3 = {1{`RANDOM}};
  done2 = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  result2 = _RAND_4[15:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
`ifndef ABSTRACTCLOCKGATE
`define ABSTRACTCLOCKGATE
module AbstractClockGate(
  input      I,
  input      CE,
  output reg O
);
  /* verilator lint_off COMBDLY */
  reg enable;
  always @(posedge I)
    enable <= CE;
  assign O = (I & enable);
  /* verilator lint_on COMBDLY */
endmodule
`endif
