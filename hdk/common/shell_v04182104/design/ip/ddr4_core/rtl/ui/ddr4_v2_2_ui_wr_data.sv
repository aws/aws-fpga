//*****************************************************************************
// (c) Copyright 2013 - 2014 Xilinx, Inc. All rights reserved.
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
//*****************************************************************************
//   ____  ____
//  /   /\/   /
// /___/  \  /    Vendor                : Xilinx
// \   \   \/     Version               : 1.1
//  \   \         Application           : MIG
//  /   /         Filename              : ddr4_v2_2_10_ui_wr_data.sv
// /___/   /\     Date Last Modified    : $Date$
// \   \  /  \    Date Created          : Thu Apr 18 2013
//  \___\/\___\
//
//Device            : UltraScale
//Design Name       : DDR3 SDRAM & DDR4 SDRAM
//Purpose           :
//Reference         :
//Revision History  :
//*****************************************************************************

// User interface write data buffer.  Consists of four counters,
// a pointer RAM and the write data storage RAM.
//
// All RAMs are implemented with distributed RAM.
//
// Whe ordering is set to STRICT or NORM, data moves through
// the write data buffer in strictly FIFO order.  In RELAXED
// mode, data may be retired from the write data RAM in any
// order relative to the input order.  This implementation
// supports all ordering modes.
//
// The pointer RAM stores a list of pointers to the write data storage RAM.
// This is a list of vacant entries.  As data is written into the RAM, a
// pointer is pulled from the pointer RAM and used to index the write
// operation.  In a semi autonomously manner, pointers are also pulled, in
// the same order, and provided to the command port as the data_buf_addr.
//
// When the MC reads data from the write data buffer, it uses the
// data_buf_addr provided with the command to extract the data from the
// write data buffer.  It also writes this pointer into the end
// of the pointer RAM.
//
// The occupancy counter keeps track of how many entries are valid
// in the write data storage RAM.  app_wdf_rdy and app_rdy will be
// de-asserted when there is no more storage in the write data buffer.
//
// Three sequentially incrementing counters/indexes are used to maintain
// and use the contents of the pointer RAM.
//
// The write buffer write data address index generates the pointer
// used to extract the write data address from the pointer RAM.  It
// is incremented with each buffer write.  The counter is actually one
// ahead of the current write address so that the actual data buffer
// write address can be registered to give a full state to propagate to
// the write data distributed RAMs.
//
// The data_buf_addr counter is used to extract the data_buf_addr for
// the command port.  It is incremented as each command is written
// into the MC.
//
// The read data index points to the end of the list of free
// buffers.  When the MC fetches data from the write data buffer, it
// provides the buffer address.  The buffer address is used to fetch
// the data, but is also written into the pointer at the location indicated
// by the read data index.
//
// Enter and exiting a buffer full condition generates corner cases.  Upon
// entering a full condition, incrementing the write buffer write data
// address index must be inhibited.  When exiting the full condition,
// the just arrived pointer must propagate through the pointer RAM, then
// indexed by the current value of the write buffer write data
// address counter, the value is registered in the write buffer write
// data address register, then the counter can be advanced.
//
// The pointer RAM must be initialized with valid data after reset.  This is
// accomplished by stepping through each pointer RAM entry and writing
// the locations address into the pointer RAM.  For the FIFO modes, this means
// that buffer address will always proceed in a sequential order.  In the
// RELAXED mode, the original write traversal will be in sequential
// order, but once the MC begins to retire out of order, the entries in
// the pointer RAM will become randomized.  The ui_rd_data module provides
// the control information for the initialization process.

`timescale 1 ps / 1 ps

module ddr4_v2_2_10_ui_wr_data #
  (
   parameter TCQ = 100,
   parameter APP_DATA_WIDTH       = 256,
   parameter APP_MASK_WIDTH       = 32,
   parameter ECC                  = "OFF",
   parameter EARLY_WR_DATA        = "OFF",
   parameter nCK_PER_CLK          = 2 ,
   parameter ECC_TEST             = "OFF"
  )
  (/*AUTOARG*/
  // Outputs
  app_wdf_rdy, wr_req_16, wr_data_buf_addr, wr_data, wr_data_mask,
  raw_not_ecc,
  // Inputs
  rst, clk, app_wdf_data, app_wdf_mask, app_raw_not_ecc, app_wdf_wren,
  app_wdf_end, wr_data_offset, wr_data_addr, wr_data_en, wr_accepted,
  ram_init_done_r, ram_init_addr
  );

  input rst;
  input clk;

  input [APP_DATA_WIDTH-1:0] app_wdf_data;
  input [APP_MASK_WIDTH-1:0] app_wdf_mask;
  input [2*nCK_PER_CLK-1:0] app_raw_not_ecc;
  input app_wdf_wren;
  input app_wdf_end;

  reg [APP_DATA_WIDTH-1:0] app_wdf_data_r1;
  reg [APP_MASK_WIDTH-1:0] app_wdf_mask_r1;
  reg [2*nCK_PER_CLK-1:0] app_raw_not_ecc_r1 = 4'b0;
  reg app_wdf_wren_r1;
  reg app_wdf_end_r1;
  (* KEEP = "true" *) reg app_wdf_rdy_r;

  localparam WR_BUF_WIDTH = 
               APP_DATA_WIDTH + APP_MASK_WIDTH + (ECC_TEST == "OFF" ? 0 : 2*nCK_PER_CLK);
  localparam FULL_RAM_CNT = (WR_BUF_WIDTH/6);
  localparam REMAINDER = WR_BUF_WIDTH % 6;
  localparam RAM_CNT = FULL_RAM_CNT + ((REMAINDER == 0 ) ? 0 : 1);
  localparam RAM_WIDTH = (RAM_CNT*6);

  //Adding few copies of the app_wdf_rdy_r signal in order to meet
  //timing. This is signal has a very high fanout. So grouped into
  //few functional groups and alloted one copy per group.
  (* keep = "true" *) reg app_wdf_rdy_r_copy1;
  (* keep = "true" *) reg app_wdf_rdy_r_copy2;
  (* keep = "true" *) reg app_wdf_rdy_r_copy3;
  (* keep = "true" *) reg app_wdf_rdy_r_copy4;
  (* keep = "true" *) reg app_wdf_rdy_r_copy5;
  (* keep = "true" *) reg app_wdf_rdy_r_copy6;
  (* keep = "true" *) reg app_wdf_rdy_r_copy7;

  wire [APP_DATA_WIDTH-1:0] app_wdf_data_ns1 =
         ~app_wdf_rdy_r_copy2 ? app_wdf_data_r1 : app_wdf_data;
  wire [APP_MASK_WIDTH-1:0] app_wdf_mask_ns1 =
         ~app_wdf_rdy_r_copy5 ? app_wdf_mask_r1 : app_wdf_mask;

  generate
    if (ECC_TEST != "OFF") begin : ecc_on
      always @(app_raw_not_ecc) app_raw_not_ecc_r1 = app_raw_not_ecc;
    end
  endgenerate

// Be explicit about the latch enable on these registers.
  always @(posedge clk) begin
    app_wdf_data_r1 <= #TCQ app_wdf_data_ns1;
    app_wdf_mask_r1 <= #TCQ app_wdf_mask_ns1;
  end

  always @(posedge clk) begin
    if (rst) begin
      app_wdf_wren_r1 <= #TCQ 1'b0;
      app_wdf_end_r1 <= #TCQ 1'b0;
    end else begin
      if (app_wdf_rdy_r_copy6)
        app_wdf_wren_r1 <= #TCQ app_wdf_wren;
      if (app_wdf_rdy_r_copy7)
        app_wdf_end_r1 <= #TCQ app_wdf_end;
    end
  end

// The signals wr_data_addr and wr_data_offset come at different
// times depending on ECC and the value of CWL.  The data portion
// always needs to look a the raw wires, the control portion needs
// to look at a delayed version when ECC is on and CWL != 8. The
// currently supported write data delays do not require this
// functionality, but preserve for future use.
// Update:  This function is now controlled with the parameter EARLY_WR_DATA.
//          It will be used with ECC enabled or for low CWL
  input wr_data_offset;
  input [3:0] wr_data_addr;
  reg wr_data_offset_r;
  reg [3:0] wr_data_addr_r;
  generate
    if (EARLY_WR_DATA == "OFF") begin : pass_wr_addr
      always @(wr_data_offset) wr_data_offset_r = wr_data_offset;
      always @(wr_data_addr) wr_data_addr_r = wr_data_addr;
    end
    else begin : delay_wr_addr
      always @(posedge clk) wr_data_offset_r <= #TCQ wr_data_offset;
      always @(posedge clk) wr_data_addr_r <= #TCQ wr_data_addr;
    end
  endgenerate

// rd_data_cnt is the pointer RAM index for data read from the write data
// buffer.  Ie, its the data on its way out to the DRAM.
  input wr_data_en;
  wire new_rd_data = wr_data_en && ~wr_data_offset_r;
  reg [3:0] rd_data_indx_r;
(* keep = "true" *)  reg rd_data_upd_indx_r;
(* keep = "true" *)  reg rd_data_upd_indx_cpy_r;
  generate
    always @(posedge clk)
      if (rst) 
        rd_data_indx_r <= #TCQ 'b0;
      else if (new_rd_data)
        rd_data_indx_r <= #TCQ rd_data_indx_r + 5'h1;
    always @(posedge clk) 
      if (rst) begin
        rd_data_upd_indx_r <= #TCQ 'b0;
        rd_data_upd_indx_cpy_r <= #TCQ 'b0;
      end else begin
        rd_data_upd_indx_r <= #TCQ new_rd_data;
        rd_data_upd_indx_cpy_r <= #TCQ new_rd_data;
      end
  endgenerate

// data_buf_addr_cnt generates the pointer for the pointer RAM on behalf
// of data buf address that comes with the wr_data_en.
// The data buf address is written into the memory
// controller along with the command and address.
  input wr_accepted;
  reg [3:0] data_buf_addr_cnt_r;
  generate

      reg [3:0] data_buf_addr_cnt_ns;
      always @(/*AS*/data_buf_addr_cnt_r or rst or wr_accepted) begin
        data_buf_addr_cnt_ns = data_buf_addr_cnt_r;
        if (rst) data_buf_addr_cnt_ns = 4'b0;
        else if (wr_accepted) data_buf_addr_cnt_ns =
                                data_buf_addr_cnt_r + 4'h1;
      end
      always @(posedge clk) data_buf_addr_cnt_r <= #TCQ data_buf_addr_cnt_ns;

  endgenerate

// Control writing data into the write data buffer.
wire wdf_rdy_ns;
wire wdf_rdy_ns_cpy;
  always @(posedge clk) begin
    if (rst) begin
      app_wdf_rdy_r_copy1 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy2 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy3 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy4 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy5 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy6 <= #TCQ 1'b0;
      app_wdf_rdy_r_copy7 <= #TCQ 1'b0;
    end else begin
      app_wdf_rdy_r_copy1 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy2 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy3 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy4 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy5 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy6 <= #TCQ wdf_rdy_ns_cpy;
      app_wdf_rdy_r_copy7 <= #TCQ wdf_rdy_ns_cpy;
    end
  end
  wire wr_data_end = app_wdf_end_r1 && app_wdf_rdy_r_copy1 && app_wdf_wren_r1;
  wire [3:0] wr_data_pntr;
  wire [4:0] wb_wr_data_addr;
  wire [4:0] wb_wr_data_addr_w;
  reg [3:0] wr_data_indx_r;
  generate

      wire wr_data_addr_le = (wr_data_end && wdf_rdy_ns_cpy) ||
                             (rd_data_upd_indx_r && ~app_wdf_rdy_r_copy4);

// For pointer RAM.  Initialize to one since this is one ahead of
// what's being registered in wb_wr_data_addr.  Assumes pointer RAM
// has been initialized such that address equals contents.
      always @(posedge clk) begin
        if (rst) 
          wr_data_indx_r <= #TCQ 4'h1;
        else if (wr_data_addr_le)
          wr_data_indx_r <= #TCQ wr_data_indx_r + 4'h1;
      end

// Take pointer from pointer RAM and set into the write data address.
// Needs to be split into zeroth bit and everything else because synthesis
// tools don't always allow assigning bit vectors seperately.  Bit zero of the
// address is computed via an entirely different algorithm.
      reg [4:1] wb_wr_data_addr_ns;
      reg [4:1] wb_wr_data_addr_r;
      always @(/*AS*/rst or wb_wr_data_addr_r or wr_data_addr_le
               or wr_data_pntr) begin
        wb_wr_data_addr_ns = wb_wr_data_addr_r;
        if (rst) wb_wr_data_addr_ns = 4'h0;
        else if (wr_data_addr_le) wb_wr_data_addr_ns = wr_data_pntr;
      end
      always @(posedge clk) wb_wr_data_addr_r <= #TCQ wb_wr_data_addr_ns;

// If we see the first getting accepted, then
// second half is unconditionally accepted.
      reg wb_wr_data_addr0_r;
      wire wb_wr_data_addr0_ns = ((app_wdf_rdy_r_copy3 && app_wdf_wren_r1 && ~app_wdf_end_r1) ||
                                  (wb_wr_data_addr0_r && ~app_wdf_wren_r1));

      always @(posedge clk) begin
        if (rst) 
          wb_wr_data_addr0_r <= #TCQ 'b0;
        else
          wb_wr_data_addr0_r <= #TCQ wb_wr_data_addr0_ns;
      end

      assign wb_wr_data_addr = {wb_wr_data_addr_r, wb_wr_data_addr0_r};
      assign wb_wr_data_addr_w = {wb_wr_data_addr_ns, wb_wr_data_addr0_ns};

  endgenerate

// Keep track of how many entries in the queue hold data.
  input [3:0] ram_init_done_r;
  output wire app_wdf_rdy;
  generate
      
      reg [15:0] occ_cnt;
      always @(posedge clk) begin
      	if (rst)
	   occ_cnt <= #TCQ 16'h0000;
	else case ({wr_data_end, rd_data_upd_indx_r})
	      2'b01 : occ_cnt <= #TCQ {1'b0,occ_cnt[15:1]};
	      2'b10 : occ_cnt <= #TCQ {occ_cnt[14:0],1'b1};
             endcase // case ({wr_data_end, rd_data_upd_indx_r})
      end
      assign wdf_rdy_ns = !(~ram_init_done_r[0] || 
                           (occ_cnt[14] && wr_data_end && ~rd_data_upd_indx_cpy_r) || 
                           (occ_cnt[15] && ~rd_data_upd_indx_cpy_r));

      assign wdf_rdy_ns_cpy = !(~ram_init_done_r[3] || 
                               (occ_cnt[14] && wr_data_end && ~rd_data_upd_indx_r) || 
                               (occ_cnt[15] && ~rd_data_upd_indx_r));

      always @(posedge clk) 
        if (rst)
          app_wdf_rdy_r <= #TCQ 1'b0;
        else
          app_wdf_rdy_r <= #TCQ wdf_rdy_ns_cpy;

      assign app_wdf_rdy = app_wdf_rdy_r;

`ifdef MC_SVA
  wr_data_buffer_full: cover property (@(posedge clk)
         (~rst && ~app_wdf_rdy_r));
`endif
  endgenerate

// Keep track of how many write requests are in the memory controller.  We
// must limit this to 16 because we only have that many data_buf_addrs to
// hand out.  Since the memory controller queue and the write data buffer
// queue are distinct, the number of valid entries can be different.
// Throttle request acceptance once there are sixteen write requests in
// the memory controller.  Note that there is still a requirement
// for a write reqeusts corresponding write data to be written into the
// write data queue with two states of the request.
  output wire wr_req_16;
  generate
      reg [4:0] wr_req_cnt_ns;
      reg [4:0] wr_req_cnt_r;
      always @(/*AS*/rd_data_upd_indx_r or rst or wr_accepted
               or wr_req_cnt_r) begin
        wr_req_cnt_ns = wr_req_cnt_r;
        if (rst) wr_req_cnt_ns = 5'b0;
        else case ({wr_accepted, rd_data_upd_indx_r})
               2'b01 : wr_req_cnt_ns = wr_req_cnt_r - 5'b1;
               2'b10 : wr_req_cnt_ns = wr_req_cnt_r + 5'b1;
             endcase // case ({wr_accepted, rd_data_upd_indx_r})
      end
      always @(posedge clk) wr_req_cnt_r <= #TCQ wr_req_cnt_ns;
      assign wr_req_16 = (wr_req_cnt_ns == 5'h10);

`ifdef MC_SVA
  wr_req_mc_full: cover property (@(posedge clk) (~rst && wr_req_16));
  wr_req_mc_full_inc_dec_15: cover property (@(posedge clk)
       (~rst && wr_accepted && rd_data_upd_indx_r && (wr_req_cnt_r == 5'hf)));
  wr_req_underflow: assert property (@(posedge clk)
         (rst || !((wr_req_cnt_r == 5'b0) && (wr_req_cnt_ns == 5'h1f))));
  wr_req_overflow: assert property (@(posedge clk)
         (rst || !((wr_req_cnt_r == 5'h10) && (wr_req_cnt_ns == 5'h11))));
`endif
  endgenerate



// Instantiate pointer RAM.  Made up of RAM32M in single write, two read
// port mode, 2 bit wide mode.
  input [3:0] ram_init_addr;
  output wire [3:0] wr_data_buf_addr;
  localparam PNTR_RAM_CNT = 2;
  generate
      wire pointer_we = new_rd_data || ~ram_init_done_r[1];
      wire [3:0] pointer_wr_data = ram_init_done_r[2]
                                    ? wr_data_addr_r
                                    : ram_init_addr;
      wire [3:0] pointer_wr_addr = ram_init_done_r[2]
                                    ? rd_data_indx_r
                                    : ram_init_addr;
      genvar i;
      for (i=0; i<PNTR_RAM_CNT; i=i+1) begin : rams
        RAM32M
          #(.INIT_A(64'h0000000000000000),
            .INIT_B(64'h0000000000000000),
            .INIT_C(64'h0000000000000000),
            .INIT_D(64'h0000000000000000)
          ) RAM32M0 (
            .DOA(),
            .DOB(wr_data_buf_addr[i*2+:2]),
            .DOC(wr_data_pntr[i*2+:2]),
            .DOD(),
            .DIA(2'b0),
            .DIB(pointer_wr_data[i*2+:2]),
            .DIC(pointer_wr_data[i*2+:2]),
            .DID(2'b0),
            .ADDRA(5'b0),
            .ADDRB({1'b0, data_buf_addr_cnt_r}),
            .ADDRC({1'b0, wr_data_indx_r}),
            .ADDRD({1'b0, pointer_wr_addr}),
            .WE(pointer_we),
            .WCLK(clk)
           );
      end // block : rams
  endgenerate


// Instantiate write data buffer.  Depending on width of DQ bus and
// DRAM CK to fabric ratio, number of RAM32Ms is variable.  RAM32Ms are
// used in single write, single read, 6 bit wide mode.
  wire [RAM_WIDTH-1:0] wr_buf_out_data_w;
  reg [RAM_WIDTH-1:0] wr_buf_out_data;
  generate
      wire [RAM_WIDTH-1:0] wr_buf_in_data;
      if (REMAINDER == 0)
        if (ECC_TEST == "OFF")
          assign wr_buf_in_data = {app_wdf_mask_ns1, app_wdf_data_ns1};
        else
          assign wr_buf_in_data = 
                   {app_raw_not_ecc_r1, app_wdf_mask_ns1, app_wdf_data_ns1};
      else
        if (ECC_TEST == "OFF")
          assign wr_buf_in_data =
               {{6-REMAINDER{1'b0}}, app_wdf_mask_ns1, app_wdf_data_ns1};
        else 
          assign wr_buf_in_data = {{6-REMAINDER{1'b0}}, app_raw_not_ecc_r1,//app_raw_not_ecc_r1 is not ff 
                                   app_wdf_mask_ns1, app_wdf_data_ns1};

      wire [4:0] rd_addr_w;

      assign rd_addr_w = {wr_data_addr, wr_data_offset};

      always @(posedge clk) wr_buf_out_data <= #TCQ  wr_buf_out_data_w; // spyglass disable UndrivenNet-ML
      genvar ii;
      for (ii=0; ii<RAM_CNT; ii=ii+1) begin : wr_buffer_ram
        RAM32M
          #(.INIT_A(64'h0000000000000000),
            .INIT_B(64'h0000000000000000),
            .INIT_C(64'h0000000000000000),
            .INIT_D(64'h0000000000000000)
          ) RAM32M0 (
            .DOA(wr_buf_out_data_w[((ii*6)+4)+:2]),
            .DOB(wr_buf_out_data_w[((ii*6)+2)+:2]),
            .DOC(wr_buf_out_data_w[((ii*6)+0)+:2]),
            .DOD(),
            .DIA(wr_buf_in_data[((ii*6)+4)+:2]),
            .DIB(wr_buf_in_data[((ii*6)+2)+:2]),
            .DIC(wr_buf_in_data[((ii*6)+0)+:2]),
            .DID(2'b0),
            .ADDRA(rd_addr_w),
            .ADDRB(rd_addr_w),
            .ADDRC(rd_addr_w),
            .ADDRD(wb_wr_data_addr_w),
            .WE(wdf_rdy_ns),
            .WCLK(clk)
           );
      end // block: wr_buffer_ram
  endgenerate

  output [APP_DATA_WIDTH-1:0] wr_data;
  output [APP_MASK_WIDTH-1:0] wr_data_mask;
  assign {wr_data_mask, wr_data} = wr_buf_out_data[WR_BUF_WIDTH-1:0];
  output [2*nCK_PER_CLK-1:0] raw_not_ecc;
  generate
    if (ECC_TEST == "OFF") assign raw_not_ecc = {2*nCK_PER_CLK{1'b0}};
    else assign raw_not_ecc = wr_buf_out_data[WR_BUF_WIDTH-1-:4];
  endgenerate

endmodule // ddr4_v2_2_10_ui_wr_data


