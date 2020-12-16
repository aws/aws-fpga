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
//  /   /         Filename              : ddr4_v2_2_10_ui_rd_data.sv
// /___/   /\     Date Last Modified    : $Date$
// \   \  /  \    Date Created          :Thu Apr 18 2013
//  \___\/\___\
//
//Device            : UltraScale
//Design Name       : DDR3 SDRAM & DDR4 SDRAM
//Purpose           :
//Reference         :
//Revision History  :
//*****************************************************************************

// User interface read buffer.  Re orders read data returned from the
// memory controller back to the request order.
//
// Consists of a large buffer for the data, a status RAM and two counters.
//
// The large buffer is implemented with distributed RAM in 4 bit wide,
// 1 read, 1 write mode.  The status RAM is implemented with a distributed
// RAM configured as 2 bits wide 1 read/write, 1 read mode.
//
// As read requests are received from the application, the data_buf_addr
// counter supplies the data_buf_addr sent into the memory controller.
// With each read request, the counter is incremented, eventually rolling
// over.  This mechanism labels each read request with an incrementing number.
//
// When the memory controller returns read data, it echos the original
// data_buf_addr with the read data.
//
// The status RAM is indexed with the same address as the data buffer
// RAM.  Each word of the data buffer RAM has an associated status bit
// and "end" bit.  Requests of size 1 return a data burst on two consecutive
// states.  Requests of size zero return with a single assertion of rd_data_en.
//
// Upon returning data, the status and end bits are updated for each
// corresponding location in the status RAM indexed by the data_buf_addr
// echoed on the rd_data_addr field.
//
// The other side of the status and data RAMs is indexed by the rd_buf_indx.
// The rd_buf_indx constantly monitors the status bit it is currently
// pointing to.  When the status becomes set to the proper state (more on
// this later) read data is returned to the application, and the rd_buf_indx
// is incremented.
//
// At rst the rd_buf_indx is initialized to zero.  Data will not have been
// returned from the memory controller yet, so there is nothing to return
// to the application. Evenutally, read requests will be made, and the
// memory controller will return the corresponding data.  The memory
// controller may not return this data in the request order.  In which
// case, the status bit at location zero, will not indicate
// the data for request zero is ready.  Eventually, the memory controller
// will return data for request zero.  The data is forwarded on to the
// application, and rd_buf_indx is incremented to point to the next status
// bits and data in the buffers.  The status bit will be examined, and if
// data is valid, this data will be returned as well.  This process
// continues until the status bit indexed by rd_buf_indx indicates data
// is not ready.  This may be because the rd_data_buf
// is empty, or that some data was returned out of order.   Since rd_buf_indx
// always increments sequentially, data is always returned to the application
// in request order.
//
// Some further discussion of the status bit is in order.  The rd_data_buf
// is a circular buffer.  The status bit is a single bit.  Distributed RAM
// supports only a single write port.  The write port is consumed by
// memory controller read data updates.  If a simple '1' were used to
// indicate the status, when rd_data_indx rolled over it would immediately
// encounter a one for a request that may not be ready.
//
// This problem is solved by causing read data returns to flip the
// status bit, and adding hi order bit beyond the size required to
// index the rd_data_buf.  Data is considered ready when the status bit
// and this hi order bit are equal.
//
// The status RAM needs to be initialized to zero after reset.  This is
// accomplished by cycling through all rd_buf_indx valus and writing a
// zero to the status bits directly following deassertion of reset.  This
// mechanism is used for similar purposes
// for the wr_data_buf.
//
// When ORDERING == "STRICT", read data reordering is unnecessary.  For thi
// case, most of the logic in the block is not generated.

`timescale 1 ps / 1 ps

// User interface read data.

module ddr4_v2_2_10_ui_rd_data #
  (
   parameter TCQ = 100,
   parameter APP_DATA_WIDTH       = 256,
   parameter DATA_BUF_ADDR_WIDTH  = 5,
   parameter ECC                  = "OFF",
   parameter nCK_PER_CLK          = 2 ,
   parameter ORDERING             = "NORM"
  )
  (/*AUTOARG*/
  // Inputs
  input                                rst,
  input                                clk, 
  input                                rd_data_en, 
  input [DATA_BUF_ADDR_WIDTH-1:0]      rd_data_addr,
  input                                rd_data_offset,
  input                                rd_data_end,
  input [APP_DATA_WIDTH-1:0]           rd_data,
  input [2*nCK_PER_CLK-1:0]            ecc_multiple,
  input                                rd_accepted,
  
  // Outputs
  output wire [3:0]                    ram_init_done_r,
  output wire [3:0]                    ram_init_addr,
  output reg                           app_rd_data_valid,
  output reg                           app_rd_data_end,
  output [APP_DATA_WIDTH-1:0]          app_rd_data,
  output wire [2*nCK_PER_CLK-1:0]      app_ecc_multiple_err,
  output wire                          rd_buf_full,
  output wire [DATA_BUF_ADDR_WIDTH-1:0] rd_data_buf_addr_r
  );


// REGISTER DECLARATIONS
// rd_buf_indx points to the status and data storage rams for
// reading data out to the app.
reg [5:0]         rd_buf_indx_r [0:19];
(* keep = "true" *)  reg [7:0]         ram_init_done_r_lcl;
  reg [2*nCK_PER_CLK-1:0]              app_ecc_multiple_err_r = 'b0;

// WIRE DECLARATIONS
  wire                                 single_data;
  wire                                 rd_data_rdy_cpy;
  wire                                 bypass_cpy;

// LOCAL PARAMETERS

// TASKS AND FUNCTION DECLARATIONS
  function match6_1;
    input [5:0] addr;
  case (addr)
    6'b000000 : match6_1 = 1'b1;
    6'b001001 : match6_1 = 1'b1;
    6'b010010 : match6_1 = 1'b1;
    6'b011011 : match6_1 = 1'b1;
    6'b100100 : match6_1 = 1'b1;
    6'b101101 : match6_1 = 1'b1;
    6'b110110 : match6_1 = 1'b1;
    6'b111111 : match6_1 = 1'b1;
    default : match6_1 = 1'b0;
  endcase
  endfunction   

  function match4_1;
    input [3:0] addr;
  case (addr)
    4'b0000 : match4_1 = 1'b1;
    4'b0101 : match4_1 = 1'b1;
    4'b1010 : match4_1 = 1'b1;
    4'b1111 : match4_1 = 1'b1;
    default : match4_1 = 1'b0;
  endcase
  endfunction   

// Output assignments
  assign ram_init_done_r[0] = ram_init_done_r_lcl[0];
  assign ram_init_done_r[1] = ram_init_done_r_lcl[1];
  assign ram_init_done_r[2] = ram_init_done_r_lcl[2];
  assign ram_init_done_r[3] = ram_init_done_r_lcl[3];
  assign app_ecc_multiple_err = app_ecc_multiple_err_r;
  assign ram_init_addr = rd_buf_indx_r[2][3:0];

// Loop through all status write addresses once after rst. Initializes
// the status and pointer RAMs.
  generate
  genvar j;
      wire upd_rd_buf_indx = (ram_init_done_r_lcl[4] ? 
                              ((ORDERING == "NORM") && (bypass_cpy || rd_data_rdy_cpy)) : 1'b1);

      always @(posedge clk)
        if (rst)
          ram_init_done_r_lcl <= #TCQ 8'h00;
        else if (rd_buf_indx_r[0][4:0] == 5'h1f)
          ram_init_done_r_lcl <= #TCQ 8'hFF;
   
      for (j=0; j<20; j=j+1) begin : rd_buf_index_cpy
        always @(posedge clk) begin
          if (rst) rd_buf_indx_r[j] <= #TCQ 'b0;
          else if (upd_rd_buf_indx) rd_buf_indx_r[j] <= #TCQ
            rd_buf_indx_r[j] + 6'h1 + (DATA_BUF_ADDR_WIDTH == 5 ? 0 : 
                                       (single_data && ~rd_buf_indx_r[j][0]));
        end
      end
  endgenerate

// Compute dimensions of read data buffer.  Depending on width of
// DQ bus and DRAM CK
// to fabric ratio, number of RAM32Ms is variable.  RAM32Ms are used in
// single write, single read, 6 bit wide mode.
  localparam RD_BUF_WIDTH = APP_DATA_WIDTH + (ECC == "OFF" ? 0 : 2*nCK_PER_CLK);
  localparam FULL_RAM_CNT = (RD_BUF_WIDTH/6);
  localparam REMAINDER = RD_BUF_WIDTH % 6;
  localparam RAM_CNT = FULL_RAM_CNT + ((REMAINDER == 0 ) ? 0 : 1);
  localparam RAM_WIDTH = (RAM_CNT*6);

// STRICT MODE
  generate
    if (ORDERING == "STRICT") begin : strict_mode
      assign single_data = 1'b0;
      assign rd_buf_full = 1'b0;
      reg [DATA_BUF_ADDR_WIDTH-1:0] rd_data_buf_addr_r_lcl;
      reg [APP_DATA_WIDTH-1:0] rd_data_r;
      wire [DATA_BUF_ADDR_WIDTH-1:0] rd_data_buf_addr_ns =
                   rst
                    ? 0
                    : rd_data_buf_addr_r_lcl + rd_accepted;
      always @(posedge clk) rd_data_buf_addr_r_lcl <=
                                #TCQ rd_data_buf_addr_ns;
      assign rd_data_buf_addr_r = rd_data_buf_addr_ns;
// app_* signals required to be registered.      
      if (ECC == "OFF") begin : ecc_off
        assign app_rd_data = rd_data;
        always @(/*AS*/rd_data_en) app_rd_data_valid = rd_data_en;
        always @(/*AS*/rd_data_end) app_rd_data_end = rd_data_end;
      end
      else begin : ecc_on  
        assign app_rd_data = rd_data_r;
        always @(posedge clk) rd_data_r <= #TCQ rd_data;
        always @(posedge clk) app_rd_data_valid <= #TCQ rd_data_en;
        always @(posedge clk) app_rd_data_end <= #TCQ rd_data_end;
        always @(posedge clk) app_ecc_multiple_err_r <= #TCQ ecc_multiple;
      end
    end

// NON-STRICT MODE
// In configurations where read data is returned in a single fabric cycle
// the offset is always zero and we can use the bit to get a deeper
// FIFO. The RAMB32 has 5 address bits, so when the DATA_BUF_ADDR_WIDTH
// is set to use them all, discard the offset. Otherwise, include the
// offset.
    else begin : not_strict_mode
      genvar k;
      reg [5:0]  rd_buf_indx_sts_r [0:3];
      (* keep = "true" *) reg        rd_buf_we_r1;
      (* keep = "true" *) reg [3:0]  ram_init_done_r_lcl_sts;
      reg [3:0]  upd_rd_buf_indx_sts;
      wire [1:0] rd_status[0:6];
      wire [3:0] address_match_sts_0;
      wire [3:0] address_match_sts_1;
      wire [3:0] bypass_sts;
      wire [3:0] app_rd_data_end_sts;
      wire [3:0] single_data_sts;
      wire [3:0] rd_buf_we_sts;
      wire [4:0] rd_buf_wr_addr_sts [0:3];
      wire [3:0] rd_data_rdy_sts;
      wire [4:0] rd_buf_wr_addr = (DATA_BUF_ADDR_WIDTH == 5) ? rd_data_addr[4:0] :
                                                               {rd_data_addr[3:0], rd_data_offset};

      for (k = 0; k < 4; k = k +1) begin : status_ram_signals
      
        assign address_match_sts_0[k] = match6_1({rd_buf_wr_addr_sts[k][2:0],rd_buf_indx_sts_r[k][2:0]});
        assign address_match_sts_1[k] = match4_1({rd_buf_wr_addr_sts[k][4:3],rd_buf_indx_sts_r[k][4:3]});
        assign bypass_sts[k] = rd_data_en && address_match_sts_0[k] && address_match_sts_1[k];
        assign app_rd_data_end_sts[k] = bypass_sts[k] ? rd_data_end : rd_status[k][1];
        assign single_data_sts[k] = ram_init_done_r_lcl_sts[k] && app_rd_data_end_sts[k];
        assign rd_buf_we_sts[k] = ~ram_init_done_r_lcl_sts[k] || rd_data_en;
        assign rd_buf_wr_addr_sts[k] = (DATA_BUF_ADDR_WIDTH == 5) ? rd_data_addr :
                                                                    {rd_data_addr, rd_data_offset};
        assign rd_data_rdy_sts[k] = (rd_status[k][0] == rd_buf_indx_sts_r[k][5]);

        always @(*) begin
          casez ({ram_init_done_r_lcl_sts[k],address_match_sts_0[k],address_match_sts_1[k],
                  rd_data_en, rd_data_rdy_sts[k]})
            5'b0???? : upd_rd_buf_indx_sts[k] = 1'b1;
            5'b1???1 : upd_rd_buf_indx_sts[k] = 1'b1;
            5'b11110 : upd_rd_buf_indx_sts[k] = 1'b1;
            default : upd_rd_buf_indx_sts[k] = 1'b0;
          endcase 
        end

        always @(posedge clk)
          if (rst)
            ram_init_done_r_lcl_sts[k] <= #TCQ 1'b0;
          else if (rd_buf_indx_sts_r[k][4:0] == 5'h1f)
            ram_init_done_r_lcl_sts[k] <= #TCQ 1'b1;

        always @(posedge clk) begin
          if (rst) rd_buf_indx_sts_r[k] <= #TCQ 'b0;
          else if (upd_rd_buf_indx_sts[k]) rd_buf_indx_sts_r[k] <= #TCQ
            rd_buf_indx_sts_r[k] + 6'h1 + (DATA_BUF_ADDR_WIDTH == 5 ? 0 : 
                                           (single_data_sts[k] && ~rd_buf_indx_sts_r[k][0]));
        end
      
      end

// Instantiate status RAM.  One bit for status and one for "end".
// Turns out read to write back status is a timing path.  Update
// the status in the ram on the state following the read.  Bypass
// the write data into the status read path.
// Not guaranteed to write second status bit. If it is written, always
// copy in the first status bit.
      begin : status_ram_0
        reg [4:0] status_ram_wr_addr_r;
        reg [1:0] status_ram_wr_data_r;
        reg wr_status_r1;
        wire [1:0] wr_status;
        wire [4:0] status_ram_wr_addr_ns = ram_init_done_r_lcl_sts[0]
                                           ? rd_buf_wr_addr_sts[0]
                                           : rd_buf_indx_sts_r[0][4:0];
        wire [1:0] status_ram_wr_data_ns = ram_init_done_r_lcl_sts[0] ?
                                           {rd_data_end, ~(rd_data_offset
                                                          ? wr_status_r1
                                                          : wr_status[0])}
                                           : 2'b0;
        always @(posedge clk) 
          status_ram_wr_addr_r <= #TCQ status_ram_wr_addr_ns;
        always @(posedge clk) wr_status_r1 <= #TCQ wr_status[0];
        always @(posedge clk) 
          status_ram_wr_data_r <= #TCQ status_ram_wr_data_ns;
        always @(posedge clk) rd_buf_we_r1 <= #TCQ rd_buf_we_sts[0];

        RAM32M
          #(.INIT_A(64'h0000000000000000),
            .INIT_B(64'h0000000000000000),
            .INIT_C(64'h0000000000000000),
            .INIT_D(64'h0000000000000000)
           ) RAM32M0 (
            .DOA(rd_status[0]),
            .DOB(),
            .DOC(wr_status),
            .DOD(),
            .DIA(status_ram_wr_data_r),
            .DIB(2'b0),
            .DIC(status_ram_wr_data_r),
            .DID(status_ram_wr_data_r),
            .ADDRA(rd_buf_indx_sts_r[0][4:0]),
            .ADDRB(5'h0),
            .ADDRC(status_ram_wr_addr_ns),
            .ADDRD(status_ram_wr_addr_r),
            .WE(rd_buf_we_r1),
            .WCLK(clk)
           );

// Copies of the status RAM to meet timing
        genvar l;
        (* keep = "true" *) reg [4:0] status_ram_wr_addr_cpy_r [0:2];
        (* keep = "true" *) reg [1:0] status_ram_wr_data_cpy_r [0:2];
        (* keep = "true" *) reg [2:0] wr_status_r;
        wire [1:0] wr_status_cpy [0:2];
        (* keep = "true" *) wire [4:0] status_ram_wr_addr_cpy [0:2];
        (* keep = "true" *) wire [1:0] status_ram_wr_data_cpy [0:2];
        (* keep = "true" *) reg [2:0] rd_buf_we_r;
        
        for (l = 0; l < 3; l = l+1) begin : copies_of_sts_ram

          assign status_ram_wr_addr_cpy[l] = ram_init_done_r_lcl_sts[l+1] ?
                                             rd_buf_wr_addr_sts[l+1] :
                                             rd_buf_indx_sts_r[l+1][4:0];

          assign status_ram_wr_data_cpy[l] = ram_init_done_r_lcl_sts[l+1] ?
                                             {rd_data_end, ~(rd_data_offset ?
                                                            wr_status_r[l] :
                                                            wr_status_cpy[l][0])} :
                                             2'b0; 

          always @(posedge clk) wr_status_r[l] <= #TCQ wr_status_cpy[l][0];
          always @(posedge clk) 
            status_ram_wr_addr_cpy_r[l] <= #TCQ status_ram_wr_addr_cpy[l];
          always @(posedge clk) 
            status_ram_wr_data_cpy_r[l] <= #TCQ status_ram_wr_data_cpy[l];
          always @(posedge clk) rd_buf_we_r[l] <= #TCQ rd_buf_we_sts[l+1];

          RAM32M
            #(.INIT_A(64'h0000000000000000),
              .INIT_B(64'h0000000000000000),
              .INIT_C(64'h0000000000000000),
              .INIT_D(64'h0000000000000000)
             ) RAM32M1 (
              .DOA(rd_status[l+1]),
              .DOB(rd_status[l+4]),
              .DOC(wr_status_cpy[l]),
              .DOD(),
              .DIA(status_ram_wr_data_cpy_r[l]),
              .DIB(status_ram_wr_data_cpy_r[l]),
              .DIC(status_ram_wr_data_cpy_r[l]),
              .DID(2'b0),
              .ADDRA(rd_buf_indx_sts_r[l+1][4:0]),
              .ADDRB(rd_buf_indx_sts_r[l+1][4:0]),
              .ADDRC(status_ram_wr_addr_cpy[l]),
              .ADDRD(status_ram_wr_addr_cpy_r[l]),
              .WE(rd_buf_we_r[l]),
              .WCLK(clk)
             );

        end
      end // block: status_ram

      wire [RAM_WIDTH-1:0] rd_buf_out_data;
      begin : rd_buf
        wire [RAM_WIDTH-1:0] rd_buf_in_data;
        if (REMAINDER == 0)
          if (ECC == "OFF")
            assign rd_buf_in_data = rd_data;
          else
            assign rd_buf_in_data = {ecc_multiple, rd_data};
        else
          if (ECC == "OFF")
            assign rd_buf_in_data = {{6-REMAINDER{1'b0}}, rd_data};
          else
            assign rd_buf_in_data = {{6-REMAINDER{1'b0}}, ecc_multiple, rd_data};

        reg [5:0] rd_buf_indx_cpy_r [0:RAM_CNT-1];
        reg [RAM_CNT-1:0] upd_rd_buf_indx_cpy;
        (* keep = "true" *) reg [RAM_CNT-1:0] init_done_r;
        wire [RAM_CNT-1:0] address_match_buf0;
        wire [RAM_CNT-1:0] address_match_buf1;
        wire [RAM_CNT-1:0] address_match_dout0;
        wire [RAM_CNT-1:0] address_match_dout1;
        wire [RAM_CNT-1:0] bypass_buf;
        wire [RAM_CNT-1:0] app_rd_data_end_buf;
        (* keep = "true" *) reg [RAM_CNT-1:0] single_data_buf;
        wire [RAM_CNT-1:0] rd_data_rdy_buf;
        (* keep = "true" *) wire [RAM_CNT-1:0] rd_buf_we;
        reg [RAM_WIDTH-1:0] app_rd_data_ns;  // spyglass disable W498

        genvar i;
        for (i=0; i<RAM_CNT; i=i+1) begin : rd_buffer_ram

          // Dedicated copy for driving distributed RAM.
          assign address_match_buf0[i] = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_cpy_r[i][2:0]});
          assign address_match_buf1[i] = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_cpy_r[i][4:3]});
          assign address_match_dout0[i] = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_cpy_r[i][2:0]});
          assign address_match_dout1[i] = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_cpy_r[i][4:3]});
          assign bypass_buf[i] = rd_data_en && address_match_buf0[i] && address_match_buf1[i];
          assign app_rd_data_end_buf[i] = bypass_buf[i] ? rd_data_end : rd_status[i%6+1][1];  // spyglass disable UndrivenNet-ML
          assign rd_data_rdy_buf[i] = (rd_status[i%6+1][0] == rd_buf_indx_cpy_r[i][5]);
          assign rd_buf_we[i] = ~init_done_r[i] || rd_data_en;
            always @(posedge clk)
              if (rst)
                single_data_buf[i] <= #TCQ 1'b0;
              else if (init_done_r[i]) 
                single_data_buf[i] <= #TCQ app_rd_data_end_buf[i] && ~(DATA_BUF_ADDR_WIDTH == 5) &&
                                           ~rd_buf_indx_cpy_r[i][0];
          
          always @(posedge clk)
            if (rst)
              init_done_r[i] <= #TCQ 1'b0;
            else if (rd_buf_indx_cpy_r[i][4:0] == 5'h1f)
              init_done_r[i] <= #TCQ 1'b1;
   
          always @(*) begin
            casez ({init_done_r[i],address_match_buf0[i],address_match_buf1[i],
                    rd_data_en, rd_data_rdy_buf[i]})
              5'b0???? : upd_rd_buf_indx_cpy[i] = 1'b1;
              5'b1???1 : upd_rd_buf_indx_cpy[i] = 1'b1;
              5'b11110 : upd_rd_buf_indx_cpy[i] = 1'b1;
              default : upd_rd_buf_indx_cpy[i] = 1'b0;
            endcase 
          end

          always @(posedge clk) begin
            if (rst) 
              rd_buf_indx_cpy_r[i] <= #TCQ 'b0;
            else if (upd_rd_buf_indx_cpy[i]) 
              rd_buf_indx_cpy_r[i] <= #TCQ rd_buf_indx_cpy_r[i] + 6'h1;
          end

          RAM32M
            #(.INIT_A(64'h0000000000000000),
              .INIT_B(64'h0000000000000000),
              .INIT_C(64'h0000000000000000),
              .INIT_D(64'h0000000000000000)
          ) RAM32M0 (
              .DOA(rd_buf_out_data[((i*6)+4)+:2]),
              .DOB(rd_buf_out_data[((i*6)+2)+:2]),
              .DOC(rd_buf_out_data[((i*6)+0)+:2]),
              .DOD(),
              .DIA(rd_buf_in_data[((i*6)+4)+:2]),
              .DIB(rd_buf_in_data[((i*6)+2)+:2]),
              .DIC(rd_buf_in_data[((i*6)+0)+:2]),
              .DID(2'b0),
              .ADDRA(rd_buf_indx_cpy_r[i][4:0] + single_data_buf[i]),
              .ADDRB(rd_buf_indx_cpy_r[i][4:0] + single_data_buf[i]),
              .ADDRC(rd_buf_indx_cpy_r[i][4:0] + single_data_buf[i]),
              .ADDRD(rd_buf_wr_addr),
              .WE(rd_buf_we[i]),
              .WCLK(clk)
             );

          always @(posedge clk)
            if (rd_data_en & address_match_dout0[i] & address_match_dout1[i])  
              app_rd_data_ns[i*6+:6] <= #TCQ rd_buf_in_data[i*6+:6]; 
            else
              app_rd_data_ns[i*6+:6] <= #TCQ rd_buf_out_data[i*6+:6]; // spyglass disable UndrivenNet-ML

        end // block: rd_buffer_ram

        assign app_rd_data = app_rd_data_ns[APP_DATA_WIDTH-1:0]; 

      end

      wire address_match_cpy2_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[9][2:0]});
      wire address_match_cpy2_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[9][4:3]});
      assign bypass_cpy = rd_data_en && address_match_cpy2_0 && address_match_cpy2_1;
      assign rd_data_rdy_cpy = (rd_status[0][0] == rd_buf_indx_r[9][5]);

      wire address_match_cpy_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[1][2:0]});  
      wire address_match_cpy_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[1][4:3]});  
      wire address_match_cpy6_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[14][2:0]});
      wire address_match_cpy6_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[14][4:3]});
      wire address_match_cpy11_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[5][2:0]});
      wire address_match_cpy11_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[5][4:3]});

      wire bypass = rd_data_en && address_match_cpy_0 && address_match_cpy_1;

      wire rd_data_rdy = (rd_status[0][0] == rd_buf_indx_r[5][5]);
      wire bypass_cpy2 = rd_data_en && address_match_cpy11_0 && address_match_cpy11_1;

      always @(posedge clk) begin
        if (rst)
          app_rd_data_valid <= #TCQ 1'b0;
        else if (ram_init_done_r_lcl[5])
          app_rd_data_valid <= #TCQ (bypass_cpy2 || rd_data_rdy);
      end

      always @(posedge clk) begin
        if (rst)
          app_rd_data_end <= #TCQ 1'b0;
        else begin
          if (rd_data_en & address_match_cpy6_0 & address_match_cpy6_1)
            app_rd_data_end <= #TCQ rd_data_end;
          else
            app_rd_data_end <= #TCQ rd_status[0][1];
        end
      end

      wire address_match_cpy13_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[7][2:0]});
      wire address_match_cpy13_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[7][4:3]});
      wire app_rd_data_end_cpy0 = bypass ? rd_data_end : rd_status[0][1];
      assign single_data = ram_init_done_r_lcl[6] && app_rd_data_end_cpy0;

      if (ECC != "OFF") begin : assign_app_ecc_multiple
        wire [2*nCK_PER_CLK-1:0] app_ecc_multiple_err_ns =
                                   bypass
                                   ? ecc_multiple
                                   : rd_buf_out_data[APP_DATA_WIDTH+:8];
        always @(posedge clk) app_ecc_multiple_err_r <= 
                                #TCQ app_ecc_multiple_err_ns;
      end

      //Added to fix timing. The signal app_rd_data_valid has 
      //a very high fanout. So making a dedicated copy for usage
      //with the occ_cnt counter.
      (* keep = "true" *) reg app_rd_data_valid_cpy_r;
      wire address_match_cpy12_0 = match6_1({rd_buf_wr_addr[2:0],rd_buf_indx_r[19][2:0]});
      wire address_match_cpy12_1 = match4_1({rd_buf_wr_addr[4:3],rd_buf_indx_r[19][4:3]});
      wire bypass_cpy1 = rd_data_en && address_match_cpy12_0 && address_match_cpy12_1;      
      wire rd_data_rdy_cpy2 = (rd_status[0][0] == rd_buf_indx_r[19][5]);
 
      always @(posedge clk) begin
        if (rst)
          app_rd_data_valid_cpy_r <= #TCQ 1'b0;
        else if (ram_init_done_r_lcl[7])
          app_rd_data_valid_cpy_r <= #TCQ (bypass_cpy1 || rd_data_rdy_cpy2);
      end

      // Keep track of how many entries in the queue hold data.
      // changed to use registered version of the signals in
      // ordered to fix timing
      wire free_rd_buf = app_rd_data_valid_cpy_r && app_rd_data_end; 
                                                                    
      reg [DATA_BUF_ADDR_WIDTH:0] occ_cnt_r;
      wire [DATA_BUF_ADDR_WIDTH:0] occ_minus_one = occ_cnt_r - 1;
      wire [DATA_BUF_ADDR_WIDTH:0] occ_plus_one = occ_cnt_r + 1;
      begin : occupied_counter
        always @(posedge clk) begin 
          if (rst) occ_cnt_r <= #TCQ 'b0;
          else case ({rd_accepted, free_rd_buf})
                 2'b01 : occ_cnt_r <= #TCQ occ_minus_one;
                 2'b10 : occ_cnt_r <= #TCQ occ_plus_one;
          endcase // case ({wr_data_end, new_rd_data})
        end
        //assign rd_buf_full = occ_cnt_r[DATA_BUF_ADDR_WIDTH];
        assign rd_buf_full = (((occ_cnt_r[DATA_BUF_ADDR_WIDTH-1:0] == {DATA_BUF_ADDR_WIDTH{1'b1}}) && rd_accepted) ||
	                      occ_cnt_r[DATA_BUF_ADDR_WIDTH])
	                     ? 1 : 0;


`ifdef MC_SVA
  rd_data_buffer_full: cover property (@(posedge clk) (~rst && rd_buf_full));
  rd_data_buffer_inc_dec_15: cover property (@(posedge clk)
         (~rst && rd_accepted && free_rd_buf && (occ_cnt_r == 'hf)));
  rd_data_underflow: assert property (@(posedge clk)
         (rst || !((occ_cnt_r == 'b0) && (occ_cnt_r == 'h1f))));
  rd_data_overflow: assert property (@(posedge clk)
         (rst || !((occ_cnt_r == 'h10) && (occ_cnt_r == 'h11))));
`endif
      end // block: occupied_counter


// Generate the data_buf_address written into the memory controller
// for reads.  Increment with each accepted read, and rollover at 0xf.
      reg [DATA_BUF_ADDR_WIDTH-1:0] rd_data_buf_addr_r_lcl;
      assign rd_data_buf_addr_r = rd_data_buf_addr_r_lcl;
      begin : data_buf_addr
        always @(posedge clk) begin 
          if (rst) rd_data_buf_addr_r_lcl <= #TCQ 'b0;
          else if (rd_accepted) rd_data_buf_addr_r_lcl <= #TCQ
                                rd_data_buf_addr_r_lcl + 1;
        end
      end // block: data_buf_addr
    end // block: not_strict_mode
  endgenerate

endmodule // ddr4_v2_2_10_ui_rd_data

// Local Variables:
// verilog-library-directories:(".")
// End:

