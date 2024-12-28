// ============================================================================
// Amazon FPGA Hardware Development Kit
//
// Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
// ============================================================================


   //---------------------------------------------------------------------------
   // DIMM Interface from CL
   //---------------------------------------------------------------------------
   wire              CLK_DIMM_DP;
   wire              CLK_DIMM_DN;
   wire              M_ACT_N;
   wire [17:0]       M_MA;
   wire [1:0]        M_BA;
   wire [1:0]        M_BG;
   wire [1:0]        M_CKE;
   wire [1:0]        M_ODT;
   wire [1:0]        M_CS_N;
   wire [1:0]        M_CLK_DN;
   wire [1:0]        M_CLK_DP;
   wire              M_PAR;
   wire [63:0]       M_DQ;
   wire [7:0]        M_ECC;
   wire [17:0]       M_DQS_DP;
   wire [17:0]       M_DQS_DN;
   wire              RST_DIMM_N;
   wire              PCIE_EP_PERSTN;
   wire              PCIE_EP_REF_CLK_P;
   wire              PCIE_EP_REF_CLK_N;
   wire  [7:0]       PCIE_EP_TXP;
   wire  [7:0]       PCIE_EP_TXN;
   wire  [7:0]       PCIE_EP_RXP;
   wire  [7:0]       PCIE_EP_RXN;
   wire              PCIE_RP_PERSTN;
   wire              PCIE_RP_REF_CLK_P;
   wire              PCIE_RP_REF_CLK_N;
   wire  [7:0]       PCIE_RP_TXP;
   wire  [7:0]       PCIE_RP_TXN;
   wire  [7:0]       PCIE_RP_RXP;
   wire  [7:0]       PCIE_RP_RXN;

`ifndef NO_DDR

   int               fp[17:0];
   string            ddr_name[17:0];

   //---------------------------------------------------------------------------
   // DDR Clocks source clock to the CL_DDR4 controller.
   // CL_DDR4 generates the actual DDR clocks (M_CLK_DP, M_CLK_DN) based on
   // this source clock
   //---------------------------------------------------------------------------
   logic             ddr_clk;
   initial begin
      ddr_clk = 0;
      forever #5ns ddr_clk = ~ddr_clk;
   end
   assign CLK_DIMM_DP =  ddr_clk;
   assign CLK_DIMM_DN = ~ddr_clk;

`define EOF -1

   //===========================================================================
   // Memory Model instantiation
   //===========================================================================
   ddr4_rdimm_wrapper #(
      .MC_DQ_WIDTH         (72),
      .MC_DQS_BITS         (18),
      .MC_DM_WIDTH         (18),
      .MC_CKE_NUM          (2),
      .MC_ODT_WIDTH        (2),
      .MC_ABITS            (18),
      .MC_BANK_WIDTH       (2),
      .MC_BANK_GROUP       (2),
      .MC_CS_NUM           (2),
      .MC_RANKS_NUM        (2),
      .NUM_PHYSICAL_PARTS  (18),
      .CALIB_EN            ("NO"),
      .tCK                 (938),
      .tPDM                (),
      .MIN_TOTAL_R2R_DELAY (),
      .MAX_TOTAL_R2R_DELAY (),
      .TOTAL_FBT_DELAY     (),
      .MEM_PART_WIDTH      ("x4"),
      .MC_CA_MIRROR        ("ON"),
   // .SDRAM               ("DDR4"),
`ifdef SAMSUNG
      .DDR_SIM_MODEL       ("SAMSUNG"),
`else
      .DDR_SIM_MODEL       ("MICRON"),
`endif
      .DM_DBI              ("NONE"),
      .MC_REG_CTRL         ("ON"),
      .DIMM_MODEL          ("RDIMM"),
      .RDIMM_SLOTS         (1)
      		)
   u_ddr4_rdimm  (
      .ddr4_act_n          (M_ACT_N),
      .ddr4_addr           (M_MA),
      .ddr4_ba             (M_BA),
      .ddr4_bg             (M_BG),
      .ddr4_par            (M_PAR),
      .ddr4_cke            (M_CKE),
      .ddr4_odt            (M_ODT),
      .ddr4_cs_n           (M_CS_N),
      .ddr4_ck_t           (M_CLK_DP),
      .ddr4_ck_c           (M_CLK_DN),
      .ddr4_reset_n        (RST_DIMM_N),
      .ddr4_dm_dbi_n       (),
      .ddr4_dq             ({M_ECC,M_DQ}),
      .ddr4_dqs_t          (M_DQS_DP),
      .ddr4_dqs_c          (M_DQS_DN),
      .ddr4_alert_n        (),
      .initDone            (),
      .scl                 (),
      .sa0                 (),
      .sa1                 (),
      .sa2                 (),
      .sda                 (),
      .bfunc               (),
      .vddspd              ());

`define ddr4_rdimm_inst(N)\
   u_ddr4_rdimm.rcd_enabled.NOT_LRDIMM.u_ddr4_dimm.rank_instances[0].\
   even_ranks.u_ddr4_rank.Micron_model.instance_of_sdram_devices[N].\
   micron_mem_model.u_ddr4_model

`ifndef QUESTA_SIM
`ifndef IES_SIM
   //------------------------------------------------------
   // Turn off warnings from DDR models
   //------------------------------------------------------
   initial begin
      `ddr4_rdimm_inst( 0).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 1).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 2).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 3).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 4).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 5).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 6).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 7).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 8).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst( 9).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(10).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(11).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(12).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(13).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(14).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(15).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(16).set_memory_warnings(0, 0);
      `ddr4_rdimm_inst(17).set_memory_warnings(0, 0);
   end // initial begin
`endif//IES_SIM
`endif//QUESTA_SIM

  task write_cfg_info_to_file(int ddr_fp);
     $display("File pointer is %d", ddr_fp);
     $fdisplay(ddr_fp, "config 4 16");
  endtask

  task write_bdr_ld_data_to_file(logic [63:0] axi_addr, logic [511:0] data);
     logic [16:0]  row_a, row_b;
     logic [1:0]   bank_a, bank_b;
     logic [9:0]   col_a, col_b;
     logic [1:0]   bank_group_a, bank_group_b;
     logic [63:0]  data_fp[17:0];
     logic [511:0] data_t;

     row_a = axi_addr[33:17];
     col_a = {axi_addr[16:11], axi_addr[8], axi_addr[5:3]};
     bank_a = {axi_addr[10:9]};
     bank_group_a = {axi_addr[7:6]};

     row_b = {row_a[16:14], ~row_a[13], row_a[12], ~row_a[11], row_a[10], ~row_a[9:3], row_a[2:0]};
     col_b = {~col_a[9:3], col_a[2:0]};
     bank_b = ~bank_a;
     bank_group_b = ~bank_group_a;

     for (int i=0; i<8; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0]; //3-0

           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];//7-4

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)

        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end

     //ECC
     $fdisplay(fp[14], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, 'h0);
     $fdisplay(fp[15], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, 'h0);

     //ECC
     $fdisplay(fp[14], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, 'h0);
     $fdisplay(fp[15], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, 'h0);

     for (int i=16; i<18; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)
        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end // for (int i=16; i<18; i=i+2)

     for (int i=8; i<13; i=i+2) begin
        data_t = data;
        //Each device is 32-bits wide. 64-bit data is loaded as below.
        for (int j=0; j<8; j++) begin
           data_fp[i][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 4;
           data_fp[i+1][(j*4+3) -: 4] = data_t[3:0];

           data_t = data >> 8;
           data = data_t;
        end // for (int j=0; j<8; j++)
        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_a, bank_a, row_a, col_a, data_fp[i+1][31:0]);

        $fdisplay(fp[i],   "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i]  [31:0]);
        $fdisplay(fp[i+1], "%0h %0h %0h %0h %h", bank_group_b, bank_b, row_b, col_b, data_fp[i+1][31:0]);
     end // for (int i=8; i<13; i=i+2)

  endtask // write_bdr_ld_data_to_file

  task write_bdr_ld_raw_data_to_file(int ddr_file, logic [16:0] row_a, logic [1:0]  bank_a, logic [9:0]  col_a, logic [1:0] bank_group_a, logic [31:0] data);
     $fdisplay(ddr_file, "%0d %0d %0d %0d %h", bank_group_a, bank_a, row_a, col_a, data);
  endtask // write_bdr_ld_raw_data_to_file

  task ddr_bdr_ld(string file_name);
     logic [63:0]  addr;
     logic [511:0] data;
     int           axi_fp;
     int           eof_s;
     int           status;
     // Line buffer
     reg [12*100:1] line;
     int           c;

     axi_fp = $fopen(file_name, "r");

     for (int i=0; i<18; i++) begin
        ddr_name[i] = $sformatf("ddr4_ddr_%0d.mem", i);
        $display("ddr_name is %0s \n", ddr_name[i]);
        fp[i] = $fopen(ddr_name[i], "w");
        if (!fp[i]) begin
           $display("Could not open file %s", ddr_name[i]);
        end
     end
     //Config information for memory.
     for (int i=0; i<18; i++) begin
        write_cfg_info_to_file(fp[i]);
     end
     // Check the first character
     c = $fgetc(axi_fp);
     while (c != `EOF) begin
        status = $ungetc(c, axi_fp);
        //status = $fscanf(axi_fp,"%0h %0h", addr, data);
        status = $fgets(line, axi_fp);
        status = $sscanf(line, "%x %x", addr, data);
        $display("eof_s is %d status is %d \n", eof_s, status);
        $display("addr is %h data is %h \n", addr, data);
        write_bdr_ld_data_to_file(.axi_addr(addr), .data(data));
        c = $fgetc(axi_fp);
     end
     for (int i=0; i<18; i++) begin
        $fclose(fp[i]);
     end
     device_bdr_ld();
  endtask // ddr_bdr_ld

  task device_bdr_ld();
     for (int i=0; i<18; i++) begin
        ddr_name[i] = $sformatf("ddr4_ddr_%0d.mem", i);
        $display("ddr_name is %s \n", ddr_name[i]);
     end
`ifndef DDR_ABSENT
     `ddr4_rdimm_inst( 0).initialize_memory_with_file(ddr_name[0]);
     `ddr4_rdimm_inst( 1).initialize_memory_with_file(ddr_name[1]);
     `ddr4_rdimm_inst( 2).initialize_memory_with_file(ddr_name[2]);
     `ddr4_rdimm_inst( 3).initialize_memory_with_file(ddr_name[3]);
     `ddr4_rdimm_inst( 4).initialize_memory_with_file(ddr_name[4]);
     `ddr4_rdimm_inst( 5).initialize_memory_with_file(ddr_name[5]);
     `ddr4_rdimm_inst( 6).initialize_memory_with_file(ddr_name[6]);
     `ddr4_rdimm_inst( 7).initialize_memory_with_file(ddr_name[7]);
     `ddr4_rdimm_inst( 8).initialize_memory_with_file(ddr_name[16]);
     `ddr4_rdimm_inst( 9).initialize_memory_with_file(ddr_name[17]);
     `ddr4_rdimm_inst(10).initialize_memory_with_file(ddr_name[8]);
     `ddr4_rdimm_inst(11).initialize_memory_with_file(ddr_name[9]);
     `ddr4_rdimm_inst(12).initialize_memory_with_file(ddr_name[10]);
     `ddr4_rdimm_inst(13).initialize_memory_with_file(ddr_name[11]);
     `ddr4_rdimm_inst(14).initialize_memory_with_file(ddr_name[12]);
     `ddr4_rdimm_inst(15).initialize_memory_with_file(ddr_name[13]);
     `ddr4_rdimm_inst(16).initialize_memory_with_file(ddr_name[14]);
     `ddr4_rdimm_inst(17).initialize_memory_with_file(ddr_name[15]);
`endif//DDR_ABSENT
  endtask // device_bdr_ld

`endif//NO_DDR
