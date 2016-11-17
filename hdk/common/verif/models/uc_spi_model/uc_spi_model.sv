`timescale 1ns/100ps

//-----------------------------------------------------------------------------------------------------------
// Note the way SPI works is you shift out data (Most significant bit first), and at the same time you
// are shifting in data.  A cycle is some number of bytes.  This is the master so:
//
//    - Shift out from Master to Slave (MOSI - "master out, slave in")
//    - Shift in from Slave to Master (MISO - "master in, slave out") 
//
//Protocol:
// All transactions are 8 bytes:
//
//    - byte 0 - CMD
//    - byte1-3 - Address
//    - byte4-7 - Data
//
// CMD:
//    - 0x01 - Write
//    - 0x02 - Read
//    - 0x03 - Read Status
//    - 0x04 - Read Data
//
// Status is:
//    bit[0] - Busy
//
//
// To do an access you would:
//       Issue Read/Write CMD with address/data (for read, data is ignored)
//       Issue Read Status until you see the busy bit clear
//       If Read, then issue Read Data command (would get the real read data)
//
// Note although address is 3bytes, only 2 bytes are significant (our address space is 64KB).
//-----------------------------------------------------------------------------------------------------------


module uc_spi_model #(parameter SPI_CLK_PERIOD=2) (
   input rst_n,

   output logic spi_clk,
   output logic spi_sel_n,
   output logic spi_mosi,

   input spi_miso
   );

logic free_spi_clk;

logic[63:0] spi_out;

logic[63:0] spi_in;

initial free_spi_clk = 1;

//Create SPI clock
always #(SPI_CLK_PERIOD/2) free_spi_clk = ~free_spi_clk;

assign spi_clk = (~spi_sel_n)? free_spi_clk: 1'b0;

//Reset SPI Select
always @(negedge rst_n)
begin
   spi_sel_n <= 1;
end

//On every negedge of SPI clock shift data out
always @(negedge rst_n or negedge spi_clk)
   if (!rst_n)
      spi_out <= 0;
   else
      spi_out <= spi_out << 1;

assign spi_mosi = spi_out[63];

//On every posedge sample data in
always @(negedge rst_n or posedge spi_clk)
   if (!rst_n)
      spi_in <= 0;
   else
      spi_in <= {spi_in, spi_miso};

//--------------------------------------------
// Task to issue a generic command
//    A test would use this task.
//--------------------------------------------
task spi_gen (input[7:0] cmd, input[23:0] addr = 24'h000000, input[31:0] write_data = 32'h0000_0000, output[31:0] read_data);
begin
   $display("[%t] : SPI Command 0x%02x issued with address 0x%06x and write data 0x%08x", $realtime, cmd, addr, write_data);
   @(posedge free_spi_clk);
   spi_out <= {cmd, addr, write_data};
   @(negedge free_spi_clk);
   spi_sel_n <= 0;

   repeat(64)
      @(posedge free_spi_clk);
   @(negedge free_spi_clk);
   spi_sel_n <= 1;

   read_data[31:0] = spi_in[31:0];

   $display("[%t] : SPI Command 0x%02x returned data 0x%08x", $realtime, cmd, read_data[31:0]);
end
endtask

//--------------------------------------------
// Task to issue a write
//    A test would use this task.
//--------------------------------------------
task spi_write (input[23:0] addr, input[31:0] write_data, input[7:0] cmd=8'h01);
logic[7:0] pol_cmd;
begin
   $display("[%t] : SPI Write to address 0x%06x with data 0x%08x", $realtime, addr, write_data);
   @(posedge free_spi_clk);
   spi_out <= {cmd, addr, write_data};
   @(negedge free_spi_clk);
   spi_sel_n <= 0;

   repeat(64)
      @(posedge free_spi_clk);
   @(negedge free_spi_clk);
   spi_sel_n <= 1;

   pol_cmd = (cmd==8'h01)? 8'h03: 8'h09;
   spi_poll(pol_cmd);
end
endtask

//-----------------------------------------------------------------------
// Task to issue a read command (data is not transferred until later)   
//    Generally a test would not use this.
//-----------------------------------------------------------------------
task spi_rd_cmd (input[23:0] addr, input[7:0] cmd=8'h02);
begin
   @(posedge free_spi_clk);
   spi_out <= {cmd, addr, 32'h0};
   @(negedge free_spi_clk);
   spi_sel_n <= 0;

   repeat(64)
      @(posedge free_spi_clk);
   @(negedge free_spi_clk);
   spi_sel_n <= 1;

end
endtask

//----------------------------------------------------------
// Task to pol the Status, or read the data
//    Generally a test would not use this.
//----------------------------------------------------------
task spi_rd_pol(input[7:0] cmd);
begin
   @(posedge free_spi_clk);
   spi_out[63:56] <= cmd;
   spi_out[55:0] <= 0;
   @(negedge free_spi_clk);
   spi_sel_n <= 0;
         
   repeat(64)
      @(posedge free_spi_clk);
   @(negedge free_spi_clk);
   spi_sel_n <= 1;
end
endtask

//---------------------------------------------------
// Poll for "done" (i.e. not busy).  Has timeout
//    Generally test will not use this
//---------------------------------------------------
task spi_poll (input[7:0] cmd);
int count;
begin
   count = 0;
   repeat(2)
      @(posedge free_spi_clk);
   spi_rd_pol(cmd);
   while (spi_in[0])
   begin
      repeat(2)
         @(posedge free_spi_clk);
      spi_rd_pol(cmd);
      count = count + 1;
      if (count==100)
      begin
         $display("[%t] : *** ERROR *** SPI poll timeout", $realtime);
         repeat(5)
            @(posedge free_spi_clk);
         $finish;
      end
   end
end
endtask
         

//------------------------------------------------------------------------------
// Execute SPI read.  This is what a test would use
//------------------------------------------------------------------------------
task spi_read (input[23:0] addr, input[31:0] exp_data = 32'h0, input compare = 0, input[7:0] cmd=8'h02, output [31:0] read_data);
logic[31:0] count;
logic[7:0] poll_cmd;
begin
   $display("[%t] : SPI Reading from address 0x%06x", $realtime, addr);
   spi_rd_cmd (addr, cmd);
   poll_cmd = (cmd==8'h02)? 8'h03: 8'h09;
   spi_poll(poll_cmd);
   poll_cmd = (cmd==8'h02)? 8'h04: 8'h0a;
   spi_rd_pol(poll_cmd);

   read_data[31:0] = spi_in[31:0];
   
   $display("[%t] : SPI Read data 0x%08x", $realtime, spi_in[31:0]);
   if (compare && (spi_in[31:0] !== exp_data))
   begin
      $display("[%t] : *** ERROR *** SPI read miscompare. Expected 0x%08x, Actual 0x%08x", $realtime, exp_data, spi_in[31:0]);
      repeat(5)
         @(posedge free_spi_clk);
      $finish;
   end
end
endtask


endmodule

      

