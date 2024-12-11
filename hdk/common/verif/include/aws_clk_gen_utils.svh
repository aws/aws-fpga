
// START SDA OFFSETS

//
// MMCM Regs address used by AWS_CLK_GEN
//
`define AWS_CLKGEN_BASE_B     64'h50000
`define AWS_CLKGEN_BASE_C     64'h51000
`define AWS_CLKGEN_BASE_A     64'h52000
`define AWS_CLKGEN_BASE_HBM   64'h54000
`define AWS_CLKGEN_BASE_REG   64'h58000

//
// AWS_CLK_GEN Specific Regs
//
`define AWS_CLKGEN_ID_REG      (`AWS_CLKGEN_BASE_REG + 64'h0)
`define AWS_CLKGEN_VER_REG     (`AWS_CLKGEN_BASE_REG + 64'h4)
`define AWS_CLKGEN_BLD_REG     (`AWS_CLKGEN_BASE_REG + 64'h8)
`define AWS_CLKGEN_GRST_REG    (`AWS_CLKGEN_BASE_REG + 64'h10)
`define AWS_CLKGEN_SYSRST_REG  (`AWS_CLKGEN_BASE_REG + 64'h14)
`define AWS_CLKGEN_LOCK_REG    (`AWS_CLKGEN_BASE_REG + 64'h20)

`define AWS_CLKGEN_LOCK   32'h151

`define MMCM_STATUS     64'h04
`define MMCM_MAIN_CFG   64'h200 // Main clock multiplier/dividers
`define MMCM_CLK0_CFG   (`MMCM_MAIN_CFG + 64'h08) // clk0 dividers
`define MMCM_CLK1_CFG   (`MMCM_MAIN_CFG + 64'h14) // clk1 divider
`define MMCM_CLK2_CFG   (`MMCM_MAIN_CFG + 64'h20) // clk2 divider
`define MMCM_LOAD_CFG   (`MMCM_MAIN_CFG + 64'h5C) // LOAD/SEN register

// END SDA OFFSETS

// START OCL OFFSETS

//
// CL_CLK_FREQ measurement regs
//
`define CLK_FREQ_OFFSET   (64'h600)
`define CTL_REG           (`CLK_FREQ_OFFSET + 64'h00)
`define REF_FREQ_CTR      (`CLK_FREQ_OFFSET + 64'h04)
`define FREQ_CTR_0        (`CLK_FREQ_OFFSET + 64'h10)
`define FREQ_CTR_1        (`CLK_FREQ_OFFSET + 64'h14)
`define FREQ_CTR_2        (`CLK_FREQ_OFFSET + 64'h18)
`define FREQ_CTR_3        (`CLK_FREQ_OFFSET + 64'h1C)
`define FREQ_CTR_4        (`CLK_FREQ_OFFSET + 64'h20)
`define FREQ_CTR_5        (`CLK_FREQ_OFFSET + 64'h24)
`define FREQ_CTR_6        (`CLK_FREQ_OFFSET + 64'h28)
`define FREQ_CTR_7        (`CLK_FREQ_OFFSET + 64'h2C)
`define FREQ_CTR_8        (`CLK_FREQ_OFFSET + 64'h30)
`define FREQ_CTR_9        (`CLK_FREQ_OFFSET + 64'h34)

// END OCL OFFSETS

//
// Frequency Table with multiplier and divider values for MMCM, sorted as per increasing frequency order.
//
`define AWS_CLKGEN_TABLE_ROWS 27
`define AWS_CLKGEN_TABLE_COLS 6

int FREQ_TABLE [`AWS_CLKGEN_TABLE_ROWS][`AWS_CLKGEN_TABLE_COLS] = '{
    /*idx=0 */ '{/*freq*/ 87,  /*sharedMult*/ 87,   /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=1 */ '{/*freq*/ 97,  /*sharedMult*/ 97,   /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=2 */ '{/*freq*/ 109, /*sharedMult*/ 109,  /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=3 */ '{/*freq*/ 125, /*sharedMult*/ 125,  /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=4 */ '{/*freq*/ 136, /*sharedMult*/ 136,  /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=5 */ '{/*freq*/ 156, /*sharedMult*/ 156,  /*sharedDiv*/ 10, /*sharedMultFrac*/ 000, /*div0*/ 10, /*div0Frac*/ 000},
    /*idx=6 */ '{/*freq*/ 166, /*sharedMult*/ 166,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=7 */ '{/*freq*/ 171, /*sharedMult*/ 171,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=8 */ '{/*freq*/ 177, /*sharedMult*/ 177,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=9 */ '{/*freq*/ 182, /*sharedMult*/ 182,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=10*/ '{/*freq*/ 187, /*sharedMult*/ 187,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=11*/ '{/*freq*/ 196, /*sharedMult*/ 196,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=12*/ '{/*freq*/ 218, /*sharedMult*/ 218,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=13*/ '{/*freq*/ 227, /*sharedMult*/ 227,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=14*/ '{/*freq*/ 250, /*sharedMult*/ 250,  /*sharedDiv*/ 20, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=15*/ '{/*freq*/ 265, /*sharedMult*/ 26,   /*sharedDiv*/ 02, /*sharedMultFrac*/ 500, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=16*/ '{/*freq*/ 273, /*sharedMult*/ 27,   /*sharedDiv*/ 02, /*sharedMultFrac*/ 250, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=17*/ '{/*freq*/ 291, /*sharedMult*/ 29,   /*sharedDiv*/ 02, /*sharedMultFrac*/ 000, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=18*/ '{/*freq*/ 318, /*sharedMult*/ 31,   /*sharedDiv*/ 02, /*sharedMultFrac*/ 750, /*div0*/ 05, /*div0Frac*/ 000},
    /*idx=19*/ '{/*freq*/ 333, /*sharedMult*/ 33,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 250, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=20*/ '{/*freq*/ 343, /*sharedMult*/ 34,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 250, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=21*/ '{/*freq*/ 364, /*sharedMult*/ 36,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 750, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=22*/ '{/*freq*/ 375, /*sharedMult*/ 37,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 500, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=23*/ '{/*freq*/ 437, /*sharedMult*/ 43,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 625, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=24*/ '{/*freq*/ 450, /*sharedMult*/ 45,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 000, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=25*/ '{/*freq*/ 458, /*sharedMult*/ 45,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 750, /*div0*/ 02, /*div0Frac*/ 500},
    /*idx=26*/ '{/*freq*/ 500, /*sharedMult*/ 50,   /*sharedDiv*/ 04, /*sharedMultFrac*/ 000, /*div0*/ 02, /*div0Frac*/ 500}
};

typedef struct {
   string       name;
   int          frequency; // MHz
   logic [63:0] addr;
} clk;

task aws_clkgen_asrt_rst();
   // Task to assert all resets from AWS_CLK_GEN IP
   logic [31:0] read_data;

   $display("__INFO__: Writing SDA interface at Base addr = 0x%0x\n", `AWS_CLKGEN_BASE_REG);
   tb.poke_sda(.addr(`AWS_CLKGEN_SYSRST_REG ), .data(32'hFFFF_FFFF)); // SYS_RST_REG
   tb.poke_sda(.addr(`AWS_CLKGEN_BASE_REG + 64'h18 ), .data(32'd1)); // DIS_RST_MAIN_REG

endtask // aws_clkgen_asrt_rst

task aws_clkgen_dsrt_rst();
   //
   // Task to de-assert all resets from AWS_CLK_GEN IP
   //
   logic [31:0] read_data;

   $display("__INFO__: Writing SDA interface at Base addr = 0x%0x\n", `AWS_CLKGEN_BASE_REG);
   tb.poke_sda(.addr(`AWS_CLKGEN_GRST_REG), .data(32'd0)); // G_RST_REG
   tb.poke_sda(.addr(`AWS_CLKGEN_SYSRST_REG ), .data(32'd0)); // SYS_RST_REG
   tb.poke_sda(.addr(`AWS_CLKGEN_BASE_REG + 64'h18 ), .data(32'd0)); // DIS_RST_MAIN_REG

   // wait for MMCMs to lock
   do begin
      tb.wait_clock(100);
      tb.peek_sda(.addr(`AWS_CLKGEN_LOCK_REG), .data(read_data));
      $display("__INFO__: Reading SDA interface at addr = 0x%0x | read_data = 0x%0x\n", (`AWS_CLKGEN_LOCK_REG), read_data);
   end while (read_data != `AWS_CLKGEN_LOCK);

endtask // aws_clkgen_dsrt_rst

`define SAMPLE_COUNT 100
task measure_cl_clk_freq(clk clks [10:0]);
   // Configure CL_CLK_FREQ block to measure clock frequencies of AWS_CLK_GEN clocks
   logic [11:0] offset;
   logic [31:0] read_data;
   logic [31:0] clk_speed;
   // localparam REF_CNT_MAX = 10000 from cl_clk_freq.sv divided by 100

   // Clear all the counters
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h8000_0000));
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h0000_0000));
   // Start Measurement
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h0000_0001));

   do begin
      tb.wait_clock(5);
      tb.peek_ocl(.addr(`CTL_REG), .data(read_data));
   end while (read_data[0] != 1'b0); // Wait until bit[0] is clear

   for (int i = 0; i < 11; i++) begin
      tb.peek_ocl(.addr(clks[i].addr), .data(read_data));
      clk_speed = read_data / `SAMPLE_COUNT;
      $display("__INFO__: Clk %12s Reg %2d at OCL addr = 0x%0x | read_data = 0x%03x | %4d MHz\n", clks[i].name, i, clks[i].addr, read_data, clk_speed);
   end
endtask // measure_cl_clk_freq

`define FREQ_RANGE 1 // MHz band to compare around the expected value
task compare_cl_clk_freq(clk clks [10:0]);
   // Configure CL_CLK_FREQ block to measure clock frequencies of AWS_CLK_GEN clocks
   logic [11:0] offset;
   logic [31:0] read_data;
   logic [31:0] clk_speed;
   // localparam REF_CNT_MAX = 10000 from cl_clk_freq.sv divided by 100

   // Clear all the counters
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h8000_0000));
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h0000_0000));
   // Start Measurement
   tb.poke_ocl(.addr(`CTL_REG), .data(32'h0000_0001));

   do begin
      tb.wait_clock(5);
      tb.peek_ocl(.addr(`CTL_REG), .data(read_data));
   end while (read_data[0] != 1'b0); // Wait until bit[0] is clear

   for (int i = 0; i < 11; i++) begin
      tb.peek_ocl(.addr(clks[i].addr), .data(read_data));
      clk_speed = read_data / `SAMPLE_COUNT;
      if (clk_speed > clks[i].frequency + `FREQ_RANGE || clk_speed < clks[i].frequency - `FREQ_RANGE) begin
         error_count++;
         $error("__ERROR__: Clk %12s Reg %2d at OCL addr = 0x%0x | read_data = 0x%03x | %4d MHz | Execpted clk speed = %4d MHz\n",
                                                      clks[i].name, i, clks[i].addr, read_data, clk_speed, clks[i].frequency);
      end
      $display("__INFO__: Clk %12s Reg %2d at OCL addr = 0x%0x | read_data = 0x%03x | %4d MHz\n", clks[i].name, i, clks[i].addr, read_data, clk_speed);
   end
endtask // compare_cl_clk_freq

task aws_clkgen_set_freq(logic [63:0] mmcm_base, int req_freq, bit reset);
    automatic int freq_sel  = 0;
    automatic int mult      = 1;
    automatic int mult_frac = 0;
    automatic int div       = 1;
    automatic int div0      = 1;
    automatic int div0_frac = 0;
    const int div1 = 15;
    const int div2 = 15;
    int idx_choice;

    // If requested frequency is lower than min supported then error out
    if (!reset && (req_freq < FREQ_TABLE[0][0])) begin
        error_count++;
        $error("__ERROR__: Requested frequency (%d MHz) is lower than min supported (%d MHz)", req_freq, FREQ_TABLE[0][0]);
    end

   if (!reset) begin
      // get index of closest match to the target freq from the FREQ_TABLE
      for (int ii = 0; ii < `AWS_CLKGEN_TABLE_ROWS; ii++) begin
         idx_choice = ii;
         if (FREQ_TABLE[ii][0] > req_freq) begin
               idx_choice = (ii == 0) ? 0 : ii-1;
               break;
         end
      end

      freq_sel  = FREQ_TABLE[idx_choice][0];
      mult      = FREQ_TABLE[idx_choice][1];
      div       = FREQ_TABLE[idx_choice][2];
      mult_frac = FREQ_TABLE[idx_choice][3];
      div0      = FREQ_TABLE[idx_choice][4];
      div0_frac = FREQ_TABLE[idx_choice][5];
   end

   $display("__DEBUG__: MMCM = 0x%08x | Requested Freq = %d MHz | MMCM Freq = %d MHz\n", mmcm_base, req_freq, freq_sel);
   // Program MMCM
   aws_clkgen_set_mmcm(.mmcm_base(mmcm_base),
                       .mult(mult),
                       .mult_frac(mult_frac),
                       .div(div),
                       .div0(div0),
                       .div0_frac(div0_frac),
                       .div1(div1),
                       .div2(div2),
                       .reset(reset));
endtask // aws_clkgen_set_freq

task aws_clkgen_set_mmcm(logic [63:0] mmcm_base, int mult, int mult_frac, int div, int div0, int div0_frac, int div1, int div2, bit reset);
   logic [31:0] wdata;
   int tmp_mult;
   int tmp_div;

   if (!reset) begin
      // Set main clock divider and multiplier values. Ensure non-zero values.
      tmp_mult = (mult == 0) ? 1 : mult;
      tmp_div  = (div  == 0) ? 1 : div;
      wdata    = ((tmp_div << 0) & 32'hFF) | ((tmp_mult << 8) & 32'hFF00) | ((mult_frac << 16) & 32'h0FFF_0000);
      tb.poke_sda(.addr(mmcm_base + `MMCM_MAIN_CFG), .data(wdata));

      // Set clk0 divider values. Ensure non-zero values.
      tmp_div  = (div0  == 0) ? 1 : div0;
      wdata    = ((tmp_div << 0) & 32'hFF) | ((div0_frac << 8) & 32'h000F_FF00);
      tb.poke_sda(.addr(mmcm_base + `MMCM_CLK0_CFG), .data(wdata));

      // Set clk1 divider values
      tmp_div  = (div1  == 0) ? 1 : div1;
      wdata    = ((tmp_div << 0) & 32'hFF);
      tb.poke_sda(.addr(mmcm_base + `MMCM_CLK1_CFG), .data(wdata));

      // Set clk2 divider values
      tmp_div  = (div2  == 0) ? 1 : div2;
      wdata    = ((tmp_div << 0) & 32'hFF);
      tb.poke_sda(.addr(mmcm_base + `MMCM_CLK2_CFG), .data(wdata));
   end

   check_clkgen_status_locked(.mmcm_base(mmcm_base));

   // Load clock configurations
   wdata = reset ? 32'h1 : 32'h3;
   tb.poke_sda(.addr(mmcm_base + `MMCM_LOAD_CFG), .data(wdata));

   check_clkgen_status_locked(.mmcm_base(mmcm_base));
endtask // aws_clkgen_set_mmcm

`define LOCKED 1
`define MAX_CLKGEN_LOOP_RETRIES 1000
`define LOOP_WAIT_NS 100
// Wait until mmcm_base + `MMCM_STATUS bit[0] is 1 for locked, 0 for unlocked
task check_clkgen_status_locked(logic [63:0] mmcm_base);
   // Check Status Register is currently locked.
   automatic int loop_count = 0;
   logic [63:0] read_data;
   do begin
      tb.nsec_delay(`LOOP_WAIT_NS);
      tb.peek_sda(.addr(mmcm_base + `MMCM_STATUS), .data(read_data));
      loop_count++;
   end while ((read_data[0] != `LOCKED) && (loop_count < `MAX_CLKGEN_LOOP_RETRIES));

   if (loop_count >= `MAX_CLKGEN_LOOP_RETRIES) begin
      error_count++;
      $display("__ERROR__: Timeout: MMCM is not locked after %d ns. MMCM address = 0x%08x\n",
                              loop_count * `LOOP_WAIT_NS, mmcm_base + `MMCM_STATUS);
   end
endtask // check_clkgen_status_reaches_state

task aws_clkgen_reset(bit reset);
   automatic int loop_count = 0;
   logic [31:0] read_data;
   // Clear global reset reg
   tb.poke_sda(.addr(`AWS_CLKGEN_GRST_REG), .data(32'd0));

   // Wait for MMCM lock if de-asserting resets
   if (!reset) begin
      do begin
         tb.nsec_delay(`LOOP_WAIT_NS);
         tb.peek_sda(.addr(`AWS_CLKGEN_LOCK_REG), .data(read_data));
         loop_count++;
      end while ((read_data != `AWS_CLKGEN_LOCK) && (loop_count < `MAX_CLKGEN_LOOP_RETRIES));

      if (loop_count >= `MAX_CLKGEN_LOOP_RETRIES) begin
         error_count++;
         $display("__ERROR__: Timeout: Failed to achieve MMCM lock after %d iterations. @addr = 0x%08x | lock_status = 0x%08x | lock_expected = 0x%08x ",
                     loop_count * `LOOP_WAIT_NS, `AWS_CLKGEN_LOCK_REG, read_data, `AWS_CLKGEN_LOCK);
      end
   end

   // assert/de-assert SYS_RST REG
   tb.poke_sda(.addr(`AWS_CLKGEN_SYSRST_REG), .data(reset ? 32'hFFFFFFFF : 32'h0));
endtask

task aws_clkgen_dynamic_freq(int freq_clk_a, int freq_clk_b, int freq_clk_c, int freq_clk_hbm, bit reset);
      aws_clkgen_reset(.reset(1));

      aws_clkgen_set_freq(.mmcm_base(`AWS_CLKGEN_BASE_A), .req_freq(freq_clk_a), .reset(reset));
      aws_clkgen_set_freq(.mmcm_base(`AWS_CLKGEN_BASE_B), .req_freq(freq_clk_b), .reset(reset));
      aws_clkgen_set_freq(.mmcm_base(`AWS_CLKGEN_BASE_C), .req_freq(freq_clk_c), .reset(reset));
      aws_clkgen_set_freq(.mmcm_base(`AWS_CLKGEN_BASE_HBM), .req_freq(freq_clk_hbm), .reset(reset));

      aws_clkgen_reset(.reset(0));
endtask
