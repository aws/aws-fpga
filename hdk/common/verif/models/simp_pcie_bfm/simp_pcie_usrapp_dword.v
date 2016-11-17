module simp_pcie_usrapp #(C_DATA_WIDTH = 256,
                          KEEP_WIDTH = C_DATA_WIDTH/32,
                          ATTR_AXISTEN_IF_RQ_PARITY_CHECK   = 0,
                          ATTR_AXISTEN_IF_CC_PARITY_CHECK   = 0
                          ) 

(
 input                         clk,
 input                         rst,
 input                         user_lnk_up,

 output reg                    s_axis_rq_tlast,
 output reg [C_DATA_WIDTH-1:0] s_axis_rq_tdata,
`ifdef PCIE_X16
 output reg [136:0]            s_axis_rq_tuser,
`else
 output reg [59:0]             s_axis_rq_tuser,
`endif
 output reg [KEEP_WIDTH-1:0]   s_axis_rq_tkeep,
 input                         s_axis_rq_tready,
 output reg                    s_axis_rq_tvalid,

 output reg [C_DATA_WIDTH-1:0] s_axis_cc_tdata,
`ifdef PCIE_X16
 output reg [80:0]             s_axis_cc_tuser,
`else
 output reg [32:0]             s_axis_cc_tuser,
`endif
 output reg                    s_axis_cc_tlast,
 output reg [KEEP_WIDTH-1:0]   s_axis_cc_tkeep,
 output reg                    s_axis_cc_tvalid,
 input                         s_axis_cc_tready,

 input [C_DATA_WIDTH-1:0]      m_axis_cq_tdata,
 input                         m_axis_cq_tlast,
 input                         m_axis_cq_tvalid,
`ifdef PCIE_X16
 input [182:0]                 m_axis_cq_tuser,
`else
 input [84:0]                  m_axis_cq_tuser,
`endif
 input [KEEP_WIDTH-1:0]        m_axis_cq_tkeep,
 output reg                    m_axis_cq_tready,

 input [C_DATA_WIDTH-1:0]      m_axis_rc_tdata,
 input                         m_axis_rc_tlast,
 input                         m_axis_rc_tvalid,
`ifdef PCIE_X16
 input [160:0]                 m_axis_rc_tuser,
`else
 input [74:0]                  m_axis_rc_tuser,
`endif
 input [KEEP_WIDTH-1:0]        m_axis_rc_tkeep,
 output reg                    m_axis_rc_tready

 );

   localparam [2:0]  LINK_CAP_MAX_LINK_SPEED_EP = 3'h4;
   localparam        STRB_WIDTH = C_DATA_WIDTH / 8;

   reg [7:0]    DEFAULT_TAG;

   reg [15:0]   RP_BUS_DEV_FNS;
   reg [15:0]   EP_BUS_DEV_FNS;
   reg [15:0]   EP_BUS_DEV_FNS_PF1;
   reg [15:0]   EP_BUS_DEV_FNS_PF2;
   reg [15:0]   EP_BUS_DEV_FNS_PF3;
   reg          debug;

   string  testname;

`ifdef PCIE_X16
   int  MAX_PAYLOAD_SIZE_BYTES = 512;
`else
   int  MAX_PAYLOAD_SIZE_BYTES = 256;
`endif

   wire                     user_lnk_up_n;
   wire [(STRB_WIDTH-1):0]  s_axis_rq_tparity;
   wire [(STRB_WIDTH-1):0]  s_axis_cc_tparity;

   bit  allow_rand_read;

   bit  check_msix;

   assign user_lnk_up_n = ~user_lnk_up;

   generate
      if(ATTR_AXISTEN_IF_RQ_PARITY_CHECK == 1) begin
         genvar a;
         for(a=0; a< STRB_WIDTH; a = a + 1) // Parity needs to be computed for every byte of data
           begin : parity_assign
              assign s_axis_rq_tparity[a] = !(  s_axis_rq_tdata[(8*a)+ 0] ^ s_axis_rq_tdata[(8*a)+ 1]
                                                ^ s_axis_rq_tdata[(8*a)+ 2] ^ s_axis_rq_tdata[(8*a)+ 3]
                                                ^ s_axis_rq_tdata[(8*a)+ 4] ^ s_axis_rq_tdata[(8*a)+ 5]
                                                ^ s_axis_rq_tdata[(8*a)+ 6] ^ s_axis_rq_tdata[(8*a)+ 7]);
              assign s_axis_cc_tparity[a] = !(  s_axis_cc_tdata[(8*a)+ 0] ^ s_axis_cc_tdata[(8*a)+ 1]
                                                ^ s_axis_cc_tdata[(8*a)+ 2] ^ s_axis_cc_tdata[(8*a)+ 3]
                                                ^ s_axis_cc_tdata[(8*a)+ 4] ^ s_axis_cc_tdata[(8*a)+ 5]
                                                ^ s_axis_cc_tdata[(8*a)+ 6] ^ s_axis_cc_tdata[(8*a)+ 7]);
           end // block: parity_assign
      end // if (ATTR_AXISTEN_IF_RQ_PARITY_CHECK == 1)
   endgenerate

   
`include "tests.vh"

   initial begin
      string tname;
     
      if ($test$plusargs("PCIE_BFM_DEBUG"))
         debug = 1;
      else 
         debug = 0;
      
      if ($value$plusargs("UVM_TESTNAME=%s", tname)) begin
        if (tname == "uvm_null_test") begin
          if ($value$plusargs("TESTNAME=%s", testname))
             $display("Running test {%0s}...", testname);
          else begin
             $display("[%t] : No TESTNAME specified!", $realtime);
             $finish(2);
          end
          verilog_run_test(); // This comes from tests.vh
        end
      end
      
   end // initial begin
   

   initial begin
      if ($test$plusargs("NO_MSIX")) begin
         check_msix = 1'b0;
      end else begin
         check_msix = 1'b1;
      end
   end


   initial begin
      RP_BUS_DEV_FNS       = 16'b0000_0000_1010_1000;
      EP_BUS_DEV_FNS       = 16'b0000_0001_1010_0000;
      EP_BUS_DEV_FNS_PF1   = 16'b0000_0001_1010_0001;
      EP_BUS_DEV_FNS_PF2   = 16'b0000_0001_1010_0010;
      EP_BUS_DEV_FNS_PF3   = 16'b0000_0001_1010_0011;
      DEFAULT_TAG = 8'd0;
      
      s_axis_rq_tlast   = 0;
      s_axis_rq_tdata   = 0;
      s_axis_rq_tuser   = 0;
      s_axis_rq_tkeep   = 0;
      s_axis_rq_tvalid  = 0;

      s_axis_cc_tdata   = 0;
      s_axis_cc_tuser   = 0;
      s_axis_cc_tlast   = 0;
      s_axis_cc_tkeep   = 0;
      s_axis_cc_tvalid  = 0;

      m_axis_rc_tready = 1;
      m_axis_cq_tready = 1;

`ifndef NO_XDMA
      allow_rand_read = 1'b1;
`else
      allow_rand_read = 1'b0;
`endif
   end // initial begin
   
   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////
   ////////////////  REQUESTER INTERFACE    /////////////////
   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////

   task TSK_SYSTEM_INITIALIZATION;

      //--------------------------------------------------------------------------
      // Event # 1: Wait for Transaction reset to be de-asserted...
      //--------------------------------------------------------------------------
      wait (rst == 0);
      $display("[%t] : (simp_pcie_usrapp) Transaction Reset Is De-asserted...", $realtime);

      //--------------------------------------------------------------------------
      // Event # 2: Wait for Transaction link to be asserted...
      //--------------------------------------------------------------------------
      tb.RP.cfg_usrapp.TSK_WRITE_CFG_DW(32'h01, 32'h00000007, 4'h1);
      `ifdef PCIE_X16
         tb.RP.cfg_usrapp.TSK_WRITE_CFG_DW(32'h1e, 32'h0000295f, 4'h3);  // Set MPS to 512B, set all error enable bits
      `else
         tb.RP.cfg_usrapp.TSK_WRITE_CFG_DW(32'h32, 32'h0000295f, 4'h3);  // Set MPS to 512B, set all error enable bits
      `endif
      
      $display("[%t] : (simp_pcie_usrapp) Waiting for ltssm_state...", $realtime);
      if (LINK_CAP_MAX_LINK_SPEED_EP>1) begin
`ifdef PCIE_X16
         //AK -- I don't think the timing on this can be guaranteed.
         //wait(tb.RP.pcie_4_0_rport.pcie_4_0_int_inst.cfg_ltssm_state == 6'h0B);
         wait(tb.RP.pcie_4_0_rport.pcie_4_0_int_inst.cfg_ltssm_state == 6'h10);
`else
         wait(tb.RP.pcie3_uscale_rp_top_i.pcie3_uscale_core_top_inst.cfg_ltssm_state == 6'h0B);
         wait(tb.RP.pcie3_uscale_rp_top_i.pcie3_uscale_core_top_inst.cfg_ltssm_state == 6'h10);
`endif
      end

      $display("[%t] : (simp_pcie_usrapp) Waiting for link_up...", $realtime);
`ifdef PCIE_X16
      wait (tb.RP.pcie_4_0_rport.user_lnk_up == 1);
`else
      wait (tb.RP.pcie3_uscale_rp_top_i.user_lnk_up == 1);
`endif
      TSK_TX_CLK_EAT(100);

      $display("[%t] : (simp_pcie_usrapp) Transaction Link Is Up...", $realtime);

      //Removed TSK_SYSTEM_CONFIGURATION_CHECK;

   endtask // TSK_SYSTEM_INITIALIZATION
   
   task TSK_TYPE0_CFG_READ;
      input [11:0]      reg_addr_;    // Register Number
      output [31:0]     rdata;
      input [15:0]      comp_id;
      
       reg [(C_DATA_WIDTH-1):0]        tdata;
`ifdef PCIE_X16
       reg [160:0]        tuser;
`else
       reg [74:0]         tuser;
`endif
       
      if (debug) $display("[%t] : (simp_pcie_usrapp) RQ_CFG_READ - Addr:0x%03x, Comp_ID:0x%04x", $realtime, reg_addr_, comp_id);

      //-----------------------------------------------------------------------\\
      if (user_lnk_up_n) begin
         $display("[%t] : (simp_pcie_usrapp) interface is MIA", $realtime);
         $finish(1);
      end
      //-----------------------------------------------------------------------\\
      
      @(posedge clk);
      //---------------------------- CFG TYPE-0 Read Transaction : -------------\\
      s_axis_rq_tvalid <= 1'b1;
      s_axis_rq_tlast  <= 1'b1;
`ifdef PCIE_X16
      s_axis_rq_tkeep  <= 16'h000F;         // 2DW Descriptor
`else
      s_axis_rq_tkeep  <= 8'h0F;            // 2DW Descriptor
`endif
      
      s_axis_rq_tdata  <= {
`ifdef PCIE_X16
                           256'b0,          // 8DW unused
`endif
                           128'b0,          // 4DW unused             //256
                           1'b0,            // Force ECRC             //128
                           3'b000,          // Attributes {ID Based Ordering, Relaxed Ordering, No Snoop}
                           3'b000,          // Traffic Class
                           1'b1,            // RID Enable to use the Client supplied Bus/Device/Func No
                           comp_id,         // Completer ID
                           8'd0,            // Tag
                           RP_BUS_DEV_FNS,  // Requester ID  //96
                           1'b0,            // Poisoned Req
                           4'b1000,         // Req Type for TYPE0 CFG READ Req
                           11'b00000000001, // DWORD Count
                           32'b0,           // Address *unused*       // 64
                           16'b0,           // Address *unused*       // 32
                           4'b0,            // Address *unused*
                           reg_addr_[11:2], // Extended + Base Register Number
                           2'b00};          // AT -> 00 : Untranslated Address
      s_axis_rq_tuser  <= {
                           (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
`ifdef PCIE_X16
                           6'h0,
                           6'b001010,       // Seq Number
                           41'h0,
                           4'b0000,         // Byte Lane number in case of Address Aligned mode
                           4'h0,
                           4'b0000,         // Last BE of the Read Data
                           4'h0,
                           4'b1111          // First BE of the Read Data
`else
                           4'b1010,         // Seq Number
                           8'h00,           // TPH Steering Tag
                           1'b0,            // TPH indirect Tag Enable
                           2'b0,            // TPH Type
                           1'b0,            // TPH Present
                           1'b0,            // Discontinue
                           3'b000,          // Byte Lane number in case of Address Aligned mode
                           4'b0000,         // Last BE of the Read Data
                           4'b1111          // First BE of the Read Data
`endif
                          };

      //-----------------------------------------------------------------------\\
       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Cfg Read Desc", $realtime);

      wait_for_rq_tready();
      s_axis_rq_tvalid <= 1'b0;
      s_axis_rq_tlast <= 1'b0;

`ifdef DW_ALIGNED
      // Wait for rc
       if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Cfg Read Completion Desc and Data", $realtime);
      wait_for_rc(tdata, tuser);
      if (tdata[45:43] !== 3'b000) begin
         $display("[%t] : *** FATAL *** Detected completion status 3'b%03b", $realtime, tdata[45:43]);
         #100 $finish;
      end else begin
         rdata[31:0] = tdata[127:96];
      end

`else
      // Wait for rc
       if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Cfg Read Completion Desc", $realtime);
      wait_for_rc(tdata, tuser);
      if (tdata[45:43] !== 3'b000) begin
         $display("[%t] : *** FATAL *** Detected completion status 3'b%03b", $realtime, tdata[45:43]);
         #100 $finish;
      end else begin
         // Wait for rc
         if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Cfg Read Data", $realtime);
         wait_for_rc(tdata, tuser);
         rdata[31:0] = tdata[31:0];
      end

`endif

       if (debug) $display("[%t] : (simp_pcie_usrapp) Complete Cfg Read Data", $realtime);

       $display("[%t] : (simp_pcie_usrapp) RQ_CFG_READ - Addr:0x%08x, Data:0x%08x, Comp_ID:0x%04x", $realtime, reg_addr_, rdata, comp_id);
      
       repeat(10)
         @(posedge clk);
      
   endtask // TSK_TYPE0_CFG_READ
      
   
    task TSK_TYPE0_CFG_WRITE;
       input [11:0]      reg_addr_;    // Register Number
       input [31:0]      reg_data_;    // Data
       input [15:0]      comp_id;
       
       reg [(C_DATA_WIDTH-1):0]        tdata;
`ifdef PCIE_X16
       reg [160:0]        tuser;
`else
       reg [74:0]         tuser;
`endif

       $display("[%t] : (simp_pcie_usrapp) RQ_CFG_WRITE - Addr:0x%03x, Data:0x%08x, Comp_ID:0x%04x", $realtime, reg_addr_, reg_data_, comp_id);
       
       //-----------------------------------------------------------------------\\
       if (user_lnk_up_n) begin
          $display("[%t] : (simp_pcie_usrapp) interface is MIA", $realtime);
          $finish(1);
       end
       //-----------------------------------------------------------------------\\

       @(posedge clk);
       //--------- TYPE-0 CFG Write Transaction :                     -----------\\
       s_axis_rq_tvalid <= 'b1;
`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       s_axis_rq_tlast  <= 1'b1;
 `else
       s_axis_rq_tlast  <= 1'b0;
 `endif
`else
       s_axis_rq_tlast  <= 1'b0;
`endif

`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       s_axis_rq_tkeep  <= 16'h001F;
 `else
       s_axis_rq_tkeep  <= 16'hFFFF;
 `endif
`else
       s_axis_rq_tkeep  <= 8'hFF;       // 2DW Descriptor
`endif       

       s_axis_rq_tdata  <= {
`ifdef PCIE_X16
                            256'b0,          // 8DW unused
 `ifdef DW_ALIGNED
                            96'h0,
                            reg_data_[31:0],
 `else
                            128'h0,
 `endif
`else
                            128'h0,
`endif
                            1'b0,            // Force ECRC             //128
                            3'b000,          // Attributes {ID Based Ordering, Relaxed Ordering, No Snoop}
                            3'b000,          // Traffic Class
                            1'b1,            // RID Enable to use the Client supplied Bus/Device/Func No
                            comp_id,         // Completer ID
                            8'd0,            // Tag
                            RP_BUS_DEV_FNS,  // Requester ID           //96
                            1'b0,            // Poisoned Req
                            4'b1010,         // Req Type for TYPE0 CFG Write Req
                            11'b00000000001, // DWORD Count
                            32'b0,           // Address *unused*       //64
                            16'b0,           // Address *unused*       //32
                            4'b0,            // Address *unused*
                            reg_addr_[11:2], // Extended + Base Register Number
                            2'b00};          // AT -> 00 : Untranslated Address
       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
`ifdef PCIE_X16
                            6'h0,
                            6'b001010,       // Seq Number
                            41'h0,
                            4'b0000,         // Byte Lane number in case of Address Aligned mode
                            4'h0,
                            4'b0000,         // Last BE of the Read Data
                            4'h0,
                            4'b1111          // First BE of the Read Data
`else
                            4'b1010,         // Seq Number
                            8'h00,           // TPH Steering Tag
                            1'b0,            // TPH indirect Tag Enable
                            2'b0,            // TPH Type
                            1'b0,            // TPH Present
                            1'b0,            // Discontinue
                            3'b000,          // Byte Lane number in case of Address Aligned mode (always 0 for Config packets)
                            4'b0000,         // Last BE of the Write Data
                            4'b1111          // First BE of the Write Data
`endif
};

       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Cfg Write Desc", $realtime);

       wait_for_rq_tready();
`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       s_axis_rq_tvalid  <= 1'b0;
       s_axis_rq_tlast  <= 1'b0;
 `else
       s_axis_rq_tlast  <= 1'b1;
 `endif
`else
       s_axis_rq_tlast  <= 1'b1;
`endif

`ifdef PCIE_X16
 `ifndef DW_ALIGNED
       s_axis_rq_tkeep  <= 16'h0001;
 `endif
`else
       s_axis_rq_tkeep  <= 8'h01;
`endif

`ifdef PCIE_X16
 `ifndef DW_ALIGNED
       s_axis_rq_tdata  <= {
                            256'h0,
                            224'd0,
                            reg_data_[31:0]
                           };
 `endif
`else
       s_axis_rq_tdata  <= {
                            224'd0,
                            reg_data_[31:0]
                           };
`endif


`ifdef PCIE_X16
 `ifndef DW_ALIGNED
       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
                            6'h0,
                            6'b001010,       // Seq Number
                            41'h0,
                            4'b0000,         // Byte Lane number in case of Address Aligned mode
                            4'h0,
                            4'b0000,         // Last BE of the Read Data
                            4'h0,
                            4'b1111          // First BE of the Read Data
                           };
 `endif
`else
       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
                            4'b1010,         // Seq Number
                            8'h00,           // TPH Steering Tag
                            1'b0,            // TPH indirect Tag Enable
                            2'b0,            // TPH Type
                            1'b0,            // TPH Present
                            1'b0,            // Discontinue
                            3'b000,          // Byte Lane number in case of Address Aligned mode (always 0 for Config packets)
                            4'b0000,         // Last BE of the Write Data
                            4'b1111          // First BE of the Write Data
};
`endif

       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Cfg Write Data", $realtime);

`ifdef PCIE_X16
 `ifndef DW_ALIGNED
       wait_for_rq_tready();
       s_axis_rq_tvalid <= 1'b0;
       s_axis_rq_tlast <= 1'b0;
 `endif
`else
       wait_for_rq_tready();
       s_axis_rq_tvalid <= 1'b0;
       s_axis_rq_tlast <= 1'b0;
`endif

       // Wait for completion descriptor
       if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Cfg Write Completion Desc", $realtime);
       wait_for_rc(tdata, tuser);
       if (tdata[45:43] !== 3'b000) begin
          $display("[%t] : *** FATAL *** Detected completion status 3'b%03b", $realtime, tdata[45:43]);
          #100 $finish;
       end

       if (debug) $display("[%t] : (simp_pcie_usrapp) Complete Cfg Write", $realtime);

       repeat(10)
         @(posedge clk);
       
    endtask // TSK_TYPE0_CFG_WRITE
   
    task TSK_MEM_WRITE_64;
       input [63:0]      addr;    // Register Number
       input [31:0]      data;    // Data

       TSK_MEM_WRITE_64_PF(.addr(addr), .data(data), .comp_id(EP_BUS_DEV_FNS));
    endtask

    task TSK_MEM_WRITE_64_PF;
       input [63:0]      addr;    // Register Number
       input [31:0]      data;    // Data
       input [15:0]      comp_id;
       
       reg [(C_DATA_WIDTH-1):0]        tdata;
`ifdef PCIE_X16
       reg [160:0]        tuser;
`else
       reg [74:0]         tuser;
`endif
       reg [(C_DATA_WIDTH-1):0]        data_shift ;
       int                shift_amount;
`ifdef PCIE_X16
       reg [16+16-1:0]    tkeep_shift;
`else
       reg [7+8-1:0]      tkeep_shift;
`endif       

       $display("[%t] : (simp_pcie_usrapp) RQ_MEM_WRITE - Addr:0x%016x, Data:0x%08x", $realtime, addr, data);
       
       //-----------------------------------------------------------------------\\
       if (user_lnk_up_n) begin
          $display("[%t] : (simp_pcie_usrapp) interface is MIA", $realtime);
          $finish(1);
       end
       //-----------------------------------------------------------------------\\

       @(posedge clk);
       //--------- TYPE-0 MEM Write Transaction :                     -----------\\
       s_axis_rq_tvalid <= 'b1;
`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       // Assert last if DW count is 12 or less
       s_axis_rq_tlast  <= 1'b1;
 `else
       s_axis_rq_tlast  <= 1'b0;
 `endif
`else
       s_axis_rq_tlast  <= 1'b0;
`endif

`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       s_axis_rq_tkeep  <= 16'h001F;
 `else
       s_axis_rq_tkeep  <= 16'hFFFF;
 `endif
`else
       s_axis_rq_tkeep  <= 8'hFF;
`endif

       s_axis_rq_tdata  <= {
`ifdef PCIE_X16
 `ifdef DW_ALIGNED
                            256'b0,
                            96'b0,
                            data[31:0],
 `else
                            256'b0,
                            128'h0,
 `endif
`else
                            128'h0,
`endif
                            1'b0,            // Force ECRC             //128
                            3'b000,          // Attributes {ID Based Ordering, Relaxed Ordering, No Snoop}
                            3'b000,          // Traffic Class
                            1'b1,            // RID Enable to use the Client supplied Bus/Device/Func No
                            comp_id,         // Completer ID
                            8'd0,            // Tag
                            RP_BUS_DEV_FNS,  // Requester ID           //96
                            1'b0,            // Poisoned Req
                            4'b0001,         // Req Type for TYPE0 MEM Write Req
                            11'b00000000001, // DWORD Count
                            addr[63:2], // Extended + Base Register Number //64
                            2'b00};          // AT -> 00 : Untranslated Address

       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
`ifdef PCIE_X16
                            6'h0,
                            6'b001010,       // Seq Number
                            41'h0,
 `ifdef DW_ALIGNED
                            4'h0,
 `else
                            addr[5:2],       // Byte Lane number in case of Address Aligned mode
 `endif
                            4'h0,
                            4'b0000,         // Last BE of the Read Data
                            4'h0,
                            4'b1111          // First BE of the Read Data
`else
                            4'b1010,         // Seq Number
                            8'h00,           // TPH Steering Tag
                            1'b0,            // TPH indirect Tag Enable
                            2'b0,            // TPH Type
                            1'b0,            // TPH Present
                            1'b0,            // Discontinue
                            addr[4:2],  // Byte Lane number in case of Address Aligned mode (always 0 for Config packets)
                            4'b0000,         // Last BE of the Write Data
                            4'b1111          // First BE of the Write Data
`endif
};
       
       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Mem Write Desc", $realtime);

       wait_for_rq_tready();

`ifdef PCIE_X16
 `ifdef DW_ALIGNED
       s_axis_rq_tvalid  <= 1'b0;
       s_axis_rq_tlast  <= 1'b0;
 `else
       data_shift[(C_DATA_WIDTH-1):0] = {
                            256'd0, 
                            224'd0, 
                            data[31:0]};
       shift_amount = 32 * addr[5:2];

       data_shift[(C_DATA_WIDTH-1):0] = (data_shift[(C_DATA_WIDTH-1):0]) << shift_amount;

       if (debug) $display("[%t] : (simp_pcie_usrapp) Data Shift shift_amount=%0d bits, ", $realtime, shift_amount);
       
       s_axis_rq_tdata  <= data_shift[(C_DATA_WIDTH-1):0];
       s_axis_rq_tlast  <= 1'b1;
       tkeep_shift[16+16-1:0] = {16'd1, {16{1'b1}}};
       tkeep_shift[16+16-1:0] = tkeep_shift[16+16-1:0] << (addr[5:2]);
       s_axis_rq_tkeep  <=  tkeep_shift[16+16-1-:16];
 `endif
`else
       data_shift[(C_DATA_WIDTH-1):0] = {
                            224'd0, 
                            data[31:0]};
       shift_amount = 32 * addr[4:2];

       data_shift[(C_DATA_WIDTH-1):0] = (data_shift[(C_DATA_WIDTH-1):0]) << shift_amount;

       if (debug) $display("[%t] : (simp_pcie_usrapp) Data Shift shift_amount=%0d bits, ", $realtime, shift_amount);
       
       s_axis_rq_tdata  <= data_shift[(C_DATA_WIDTH-1):0];
       s_axis_rq_tlast  <= 1'b1;
       tkeep_shift[7+8-1:0] = {8'd1, {7{1'b1}}};
       tkeep_shift[7+8-1:0] = tkeep_shift[7+8-1:0] << (addr[4:2]);
       s_axis_rq_tkeep  <=  tkeep_shift[7+8-1-:8];
`endif

`ifdef PCIE_X16
 `ifndef DW_ALIGNED
       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
                            6'h0,
                            6'b001010,       // Seq Number
                            41'h0,
                            addr[5:2],       // Byte Lane number in case of Address Aligned mode
                            4'h0,
                            4'b0000,         // Last BE of the Read Data
                            4'h0,
                            4'b1111          // First BE of the Read Data
                           };

       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Mem Write Data", $realtime);

       wait_for_rq_tready();
       s_axis_rq_tvalid <= 1'b0;
       s_axis_rq_tlast <= 1'b0;
       @(posedge clk);
 `endif
`else
       s_axis_rq_tuser  <= {
                            (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
                            4'b1010,         // Seq Number
                            8'h00,           // TPH Steering Tag
                            1'b0,            // TPH indirect Tag Enable
                            2'b0,            // TPH Type
                            1'b0,            // TPH Present
                            1'b0,            // Discontinue
                            addr[4:2],//3'b000,          // Byte Lane number in case of Address Aligned mode (always 0 for Config packets)
                            4'b0000,         // Last BE of the Write Data
                            4'b1111          // First BE of the Write Data
                           };

       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Mem Write Data", $realtime);

       wait_for_rq_tready();
       s_axis_rq_tvalid <= 1'b0;
       s_axis_rq_tlast <= 1'b0;
       @(posedge clk);
`endif

       if (debug) $display("[%t] : (simp_pcie_usrapp) Complete Mem Write", $realtime);

       repeat(10)
         @(posedge clk);
       
    endtask // TSK_MEM_WRITE_64
   
   
   task TSK_MEM_READ_64;
      input [63:0]      addr;
      output [31:0]     rdata;

      TSK_MEM_READ_64_PF(.addr(addr), .rdata(rdata), .comp_id(EP_BUS_DEV_FNS));
   endtask

   task TSK_MEM_READ_64_PF;
      input [63:0]      addr;
      output [31:0]     rdata;
      input [15:0]      comp_id;
      
       reg [(C_DATA_WIDTH-1):0]        tdata;
`ifdef PCIE_X16
       reg [160:0]        tuser;
`else
       reg [74:0]         tuser;
`endif       

      if (debug) $display("[%t] : (simp_pcie_usrapp) RQ_MEM_READ - Addr:0x%16x", $realtime, addr);

      //-----------------------------------------------------------------------\\
      if (user_lnk_up_n) begin
         $display("[%t] : (simp_pcie_usrapp) interface is MIA", $realtime);
         $finish(1);
      end
      //-----------------------------------------------------------------------\\
      
      @(posedge clk);
      //---------------------------- MEM TYPE-0 Read Transaction : -------------\\
      s_axis_rq_tvalid <= 1'b1;
      s_axis_rq_tlast  <= 1'b1;
`ifdef PCIE_X16
      s_axis_rq_tkeep  <= 16'h000F;
`else
      s_axis_rq_tkeep  <= 8'h0F;            // 2DW Descriptor
`endif
      s_axis_rq_tdata  <= {
`ifdef PCIE_X16
                           256'h0,
`endif
                           128'b0,          // 4DW unused             //256
                           1'b0,            // Force ECRC             //128
                           3'b000,          // Attributes {ID Based Ordering, Relaxed Ordering, No Snoop}
                           3'b000,          // Traffic Class
                           1'b1,            // RID Enable to use the Client supplied Bus/Device/Func No
                           comp_id,         // Completer ID
                           8'd0,            // Tag
                           RP_BUS_DEV_FNS,  // Requester ID  //96
                           1'b0,            // Poisoned Req
                           4'b0000,         // Req Type for TYPE0 MEM READ Req
                           11'b00000000001, // DWORD Count
                           addr[63:2], // Extended + Base Register Number
                           2'b00};          // AT -> 00 : Untranslated Address
      s_axis_rq_tuser  <= {
                           (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_rq_tparity : {STRB_WIDTH{1'b0}}), // Parity
`ifdef PCIE_X16
                           6'h0,
                           6'b001010,       // Seq Number
                           41'h0,
                           4'b0000,         // Byte Lane number in case of Address Aligned mode
                           4'h0,
                           4'b0000,         // Last BE of the Read Data
                           4'h0,
                           4'b1111          // First BE of the Read Data
`else
                           4'b1010,         // Seq Number
                           8'h00,           // TPH Steering Tag
                           1'b0,            // TPH indirect Tag Enable
                           2'b0,            // TPH Type
                           1'b0,            // TPH Present
                           1'b0,            // Discontinue
                           3'b000,          // Byte Lane number in case of Address Aligned mode
                           4'b0000,         // Last BE of the Read Data
                           4'b1111          // First BE of the Read Data
`endif
};
      
      //-----------------------------------------------------------------------\\
       if (debug) $display("[%t] : (simp_pcie_usrapp) Sending Mem Read Desc", $realtime);

      wait_for_rq_tready();
      s_axis_rq_tvalid <= 1'b0;
      s_axis_rq_tlast <= 1'b0;

`ifdef DW_ALIGNED
      // Wait for rc
       if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Mem Read Completion Desc and Data", $realtime);
      wait_for_rc(tdata, tuser);
      if (tdata[45:43] !== 3'b000) begin
         $display("[%t] : *** FATAL *** Detected completion status 3'b%03b", $realtime, tdata[45:43]);
         #100 $finish;
      end else begin
         rdata[31:0] = tdata[127:96];
      end
      
`else // !`ifdef DW_ALIGNED
      // Wait for rc
       if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Mem Read Completion Desc", $realtime);
      wait_for_rc(tdata, tuser);
      if (tdata[45:43] !== 3'b000) begin
         $display("[%t] : *** FATAL *** Detected completion status 3'b%03b", $realtime, tdata[45:43]);
         #100 $finish;
      end else begin
         // Wait for rc
         if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for Mem Read Data", $realtime);
         wait_for_rc(tdata, tuser);
         rdata[31:0] = tdata[31:0];
      end

`endif // !`ifdef DW_ALIGNED
      
       if (debug) $display("[%t] : (simp_pcie_usrapp) Complete Mem Read Data", $realtime);

       $display("[%t] : (simp_pcie_usrapp) RQ_MEM_READ - Addr:0x%16x, Data:0x%08x", $realtime, addr, rdata);
      
       repeat(10)
         @(posedge clk);
      
   endtask // TSK_MEM_READ_64
   
   task automatic wait_for_rq_tready();
      reg done;
      done = s_axis_rq_tready;
      if (done == 1) begin
         @(posedge clk);
      end else begin
         while (done == 0) begin
            @(posedge clk);
            done = s_axis_rq_tready;
         end
      end
   endtask // wait_for_rq_tready

`ifdef PCIE_X16
   task automatic wait_for_rc(output [(C_DATA_WIDTH-1):0] tdata, output [160:0] tuser);
`else
   task automatic wait_for_rc(output [(C_DATA_WIDTH-1):0] tdata, output [74:0] tuser);
`endif
      reg done;
      done = m_axis_rc_tvalid;
      if (done == 1) begin
         @(posedge clk);
      end else begin
         while (done == 0) begin
            @(posedge clk);
            done = m_axis_rc_tvalid;
         end
      end
      tdata = m_axis_rc_tdata;
      tuser = m_axis_rc_tuser;
   endtask // wait_for_rc

   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////
   ////////////////  COMPLETER INTERFACE    /////////////////
   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////
   mailbox req_mbx;
   mailbox comp_mbx;

   mailbox pf0_msix_mbx;
   mailbox pf1_msix_mbx;
   mailbox pf2_msix_mbx;
   mailbox pf3_msix_mbx;

   reg [127:0] req_q [$];
   reg [128+64+13+13-1:0] comp_q [$];

   /****************************************************************************
    * Memory (associative array)
    ****************************************************************************/
   typedef bit [31:0]  mem_entry;
   typedef bit [61:0]  mem_index;
   mem_entry  mem_array[mem_index];
   
   /****************************************************************************
    * MSI-X Address and Data
    ****************************************************************************/
   reg [3:0]   msix_intr;

   reg [63:0]  pf0_msix_addr[47:0];
   reg [63:0]  pf1_msix_addr;
   reg [63:0]  pf2_msix_addr;
   reg [63:0]  pf3_msix_addr;

   reg [31:0]  pf0_msix_data[47:0];
   reg [31:0]  pf1_msix_data;
   reg [31:0]  pf2_msix_data;
   reg [31:0]  pf3_msix_data;

   bit         pf0_msix_mask[47:0];
   bit         pf1_msix_mask;
   bit         pf2_msix_mask;
   bit         pf3_msix_mask;

   initial begin
      reg [(C_DATA_WIDTH-1):0] cq_tdata;
`ifdef PCIE_X16
      reg [182:0]  cq_tuser;
`else
      reg [84:0]  cq_tuser;
`endif
      reg [KEEP_WIDTH-1:0] cq_tkeep;
      reg cq_tlast;

      req_mbx = new();
      comp_mbx = new();

      pf0_msix_mbx = new();
      pf1_msix_mbx = new();
      pf2_msix_mbx = new();
      pf3_msix_mbx = new();

      foreach (pf0_msix_mask[i]) begin
         pf0_msix_mask[i] = 1'b1;
      end
      pf1_msix_mask = 1'b1;
      pf2_msix_mask = 1'b1;
      pf3_msix_mask = 1'b1;

      msix_intr = 4'h0;

      fork
         perform_cq_rd_req();
         send_cq_rd_comp();
      join_none
      
      // A forever loop to monitor descriptors
      @(posedge clk);
      forever begin
         if (rst)
         begin
            while (rst)
               @(posedge clk);
         end
         wait_for_cq(cq_tdata, cq_tuser, cq_tkeep, cq_tlast);
         // Can support MEM RD or WR Requests only
         assert(cq_tdata[78:75] === 4'b0000 || cq_tdata[78:75] === 4'b0001);
         if (cq_tdata[78:75] == 4'b0001) begin
            perform_cq_wr(cq_tdata, cq_tuser, cq_tkeep, cq_tlast);
         end else if (cq_tdata[78:75] == 4'b0000) begin
            perform_cq_rd(cq_tdata, cq_tuser, cq_tkeep, cq_tlast);
         end else begin
            $display("[%t] : *** FATAL *** Detected unsupported request type 0x%1x", $realtime, cq_tdata[78:75]);
            #100 $finish;
         end

      end
      
   end // initial begin


   task enable_rand_read();
      // Accesses will still be reported with WARNING messages
      $display("[%t] : Enabling reads from uninitialized memory", $realtime);
      allow_rand_read = 1'b1;
   endtask

   task disable_rand_read();
      // Accesses will be reported with ERROR messages
      $display("[%t] : Disabling reads from uninitialized memory", $realtime);
      allow_rand_read = 1'b0;
   endtask

`ifdef PCIE_X16
   task automatic wait_for_cq(output [(C_DATA_WIDTH-1):0] cq_tdata, output [182:0] cq_tuser, output [KEEP_WIDTH-1:0] cq_tkeep, output cq_tlast);
`else
   task automatic wait_for_cq(output [(C_DATA_WIDTH-1):0] cq_tdata, output [84:0] cq_tuser, output [KEEP_WIDTH-1:0] cq_tkeep, output cq_tlast);
`endif
      reg done;
      done = m_axis_cq_tvalid;
      while (done == 0) begin
         @(posedge clk);
         done = m_axis_cq_tvalid;
      end
      cq_tdata = m_axis_cq_tdata;
      cq_tuser = m_axis_cq_tuser;
      cq_tkeep = m_axis_cq_tkeep;
      cq_tlast = m_axis_cq_tlast;
      assert_cq_tready(0);
      @(posedge clk);
   endtask // wait_for_cq

   task assert_cq_tready (input int delay_in = -1);
      int delay;

      if (delay_in == -1) begin
         delay = $random(12345) % 3;
         delay = delay < 0 ? -delay : delay;
      end
      else
        delay = delay_in;
      
      m_axis_cq_tready <= 1'b0;
      repeat(delay)
        @(posedge clk);
      m_axis_cq_tready <= 1'b1;
      
   endtask // assert_cq_tready
   

   task set_msix_config(input logic [15:0] comp_id, logic [63:0] addr, [31:0] data, bit mask, logic [7:0] vector_num = 8'h0);
      case (comp_id)
        EP_BUS_DEV_FNS:
          begin
             pf0_msix_addr[vector_num] = addr;
             pf0_msix_data[vector_num] = data;
             pf0_msix_mask[vector_num] = mask;
          end
        EP_BUS_DEV_FNS_PF1:
          begin
             pf1_msix_addr = addr;
             pf1_msix_data = data;
             pf1_msix_mask = mask;
          end
        EP_BUS_DEV_FNS_PF2:
          begin
             pf2_msix_addr = addr;
             pf2_msix_data = data;
             pf2_msix_mask = mask;
          end
        EP_BUS_DEV_FNS_PF3:
          begin
             pf3_msix_addr = addr;
             pf3_msix_data = data;
             pf3_msix_mask = mask;
          end
        default:
          begin
             $display("[%t] : *** FATAL *** Attempted to set unsupported MSI-X configuration (Comp ID 0x%04x)", $realtime, comp_id);
             #100 $finish;
          end
      endcase
   endtask


   task wait_for_msix_intr(input logic [15:0] comp_id, logic [7:0] vector_num = 8'h00, bit clear = 1'b0, int timeout = 2000);
      int dummy;

      if (debug) $display("[%t] : (simp_pcie_usrapp) Waiting for MSI-X interrupt (Comp ID 0x%04x)", $realtime, comp_id);

      fork
         begin
            case (comp_id)
              EP_BUS_DEV_FNS:
                begin
                   pf0_msix_mbx.get(dummy);
                   if (dummy !== vector_num) begin
                      $display("[%t] : *** FATAL *** Received unexpected MSI-X interrupt (Comp ID 0x%04x, Vector %2d)", $realtime, comp_id, dummy);
                      #100 $finish;
                   end
                   if (clear) msix_intr[0] = 1'b0;
                end
              EP_BUS_DEV_FNS_PF1:
                begin
                   pf1_msix_mbx.get(dummy);
                   if (clear) msix_intr[1] = 1'b0;
                end
              EP_BUS_DEV_FNS_PF2:
                begin
                   pf2_msix_mbx.get(dummy);
                   if (clear) msix_intr[2] = 1'b0;
                end
              EP_BUS_DEV_FNS_PF3:
                begin
                   pf3_msix_mbx.get(dummy);
                   if (clear) msix_intr[3] = 1'b0;
                end
              default:
                begin
                   $display("[%t] : *** FATAL *** Attempted to wait for MSI-X interrupt from unsupported Comp ID 0x%04x", $realtime, comp_id);
                   #100 $finish;
                end
            endcase
         end
         begin
            TSK_TX_CLK_EAT(timeout);
            $display("[%t] : *** ERROR *** Timeout waiting for MSI-X interrupt (Comp ID 0x%04x)", $realtime, comp_id);
            $finish;
         end
      join_any
      disable fork;

   endtask


`ifdef PCIE_X16
   task perform_cq_wr(input [(C_DATA_WIDTH-1):0] cq_tdata, input [182:0] cq_tuser, input [KEEP_WIDTH-1:0] cq_tkeep, input cq_tlast);
`else
   task perform_cq_wr(input [(C_DATA_WIDTH-1):0] cq_tdata, input [84:0] cq_tuser, input [KEEP_WIDTH-1:0] cq_tkeep, input cq_tlast);
`endif
      reg [63:0] addr;
      reg [10:0] dw_cnt;
      reg        last_slice;
      reg        first_slice;
      
      reg [(C_DATA_WIDTH-1):0] slc_cq_tdata;
`ifdef PCIE_X16
      reg [182:0]  slc_cq_tuser;
`else
      reg [84:0]  slc_cq_tuser;
`endif
      reg [KEEP_WIDTH-1:0] slc_cq_tkeep;
      reg slc_cq_tlast;

      reg [63:0] slc_start_addr;
      int        rem_dw_cnt;
      int        slc_dw_cnt;
      int        slc_start_dw_idx;
      int        slc_idx;
      
      reg [31:0] mem_data;
      reg [61:0] mem_dw_idx;
      reg [63:0] mem_byte_addr;

      reg [3:0]  msix_intr_addr_match;
      int        msix_vector;

      msix_intr_addr_match = 4'h0;
      msix_vector = 0;

      addr[63:0] = {cq_tdata[63:2], 2'b00};
      dw_cnt[10:0] = cq_tdata[64 +: 11];

      $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_WRITE - Addr:0x%16x, DW_CNT:%0d", $realtime, addr, dw_cnt);

      if (check_msix == 1'b1) begin
         // Check for MSI-X interrupt write
         foreach (pf0_msix_addr[i]) begin
            if ((addr == pf0_msix_addr[i]) && (pf0_msix_mask[i] == 1'b0)) begin
               msix_intr_addr_match[0] = 1'b1;
               msix_vector = i;
            end
         end
         if ((addr == pf1_msix_addr) && (pf1_msix_mask == 1'b0)) begin
            msix_intr_addr_match[1] = 1'b1;
         end else if ((addr == pf2_msix_addr) && (pf2_msix_mask == 1'b0)) begin
            msix_intr_addr_match[2] = 1'b1;
         end else if ((addr == pf3_msix_addr) && (pf3_msix_mask == 1'b0)) begin
            msix_intr_addr_match[3] = 1'b1;
         end
      end

      last_slice = 0;
      first_slice = 1;
      
      slc_start_addr[63:0] = addr[63:0];
      rem_dw_cnt = 0;
      rem_dw_cnt = {21'd0, dw_cnt};

      slc_idx = 0;
      while (last_slice == 0) begin
// `ifdef PCIE_X16
//  `ifdef DW_ALIGNED
//          slc_cq_tdata = cq_tdata;
//          slc_cq_tuser = cq_tuser;
//          slc_cq_tkeep = cq_tkeep;
//          slc_cq_tlast = cq_tlast;
//  `else
//          wait_for_cq(slc_cq_tdata, slc_cq_tuser, slc_cq_tkeep, slc_cq_tlast);
//  `endif
// `else
//          wait_for_cq(slc_cq_tdata, slc_cq_tuser, slc_cq_tkeep, slc_cq_tlast);
// `endif
//          last_slice = slc_cq_tlast;
// 
//          if (last_slice) begin
// `ifdef PCIE_X16
//  `ifdef DW_ALIGNED
//             slc_start_dw_idx = 4;
//  `else
//             slc_start_dw_idx = 0;
//  `endif
// `else
//             slc_start_dw_idx = 0;
// `endif
//             slc_dw_cnt = rem_dw_cnt; // slc_cq_tkeep;
//          end
//          else begin
//             slc_start_dw_idx = 0;
// `ifdef PCIE_X16
//  `ifdef DW_ALIGNED
//             slc_start_dw_idx = 4;
//  `else
//             slc_start_dw_idx = slc_start_addr[5:2];
//  `endif
//             slc_dw_cnt = 16 - slc_start_dw_idx;
// `else
//             slc_start_dw_idx = slc_start_addr[4:2];
//             slc_dw_cnt = 8 - slc_start_dw_idx;
// `endif
//          end

         if (first_slice) begin
            first_slice = 0;
`ifdef PCIE_X16
 `ifdef DW_ALIGNED
            slc_start_dw_idx = 4;
            slc_cq_tdata = cq_tdata;
            slc_cq_tuser = cq_tuser;
            slc_cq_tkeep = cq_tkeep;
            slc_cq_tlast = cq_tlast;
 `else
            slc_start_dw_idx = slc_start_addr[5:2];
            wait_for_cq(slc_cq_tdata, slc_cq_tuser, slc_cq_tkeep, slc_cq_tlast);
 `endif
`else
            slc_start_dw_idx = slc_start_addr[4:2];
            wait_for_cq(slc_cq_tdata, slc_cq_tuser, slc_cq_tkeep, slc_cq_tlast);
`endif

            if (check_msix == 1'b1) begin
               // Check for MSI-X interrupt data
               if (msix_intr_addr_match[0] == 1'b1) begin
                  if (slc_cq_tdata[(slc_start_dw_idx*32) +: 32] == pf0_msix_data[msix_vector]) begin
                     msix_intr[0] = 1'b1;
                     pf0_msix_mbx.put(msix_vector);
                     $display("[%t] : (simp_pcie_usrapp) MSI-X Interrupt Write Detected for function 0, vector %2d", $realtime, msix_vector);
                  end
                  msix_intr_addr_match[0] = 1'b0;
               end else if (msix_intr_addr_match[1] == 1'b1) begin
                  if (slc_cq_tdata[(slc_start_dw_idx*32) +: 32] == pf1_msix_data) begin
                     msix_intr[1] = 1'b1;
                     pf1_msix_mbx.put(1);
                     $display("[%t] : (simp_pcie_usrapp) MSI-X Interrupt Write Detected for function 1", $realtime);
                  end
                  msix_intr_addr_match[1] = 1'b0;
               end else if (msix_intr_addr_match[2] == 1'b1) begin
                  if (slc_cq_tdata[(slc_start_dw_idx*32) +: 32] == pf2_msix_data) begin
                     msix_intr[2] = 1'b1;
                     pf2_msix_mbx.put(1);
                     $display("[%t] : (simp_pcie_usrapp) MSI-X Interrupt Write Detected for function 2", $realtime);
                  end
                  msix_intr_addr_match[2] = 1'b0;
               end else if (msix_intr_addr_match[3] == 1'b1) begin
                  if (slc_cq_tdata[(slc_start_dw_idx*32) +: 32] == pf3_msix_data) begin
                     msix_intr[3] = 1'b1;
                     pf3_msix_mbx.put(1);
                     $display("[%t] : (simp_pcie_usrapp) MSI-X Interrupt Write Detected for function 3", $realtime);
                  end
                  msix_intr_addr_match[3] = 1'b0;
               end
            end

         end
         else begin
            slc_start_dw_idx = 0;
            wait_for_cq(slc_cq_tdata, slc_cq_tuser, slc_cq_tkeep, slc_cq_tlast);
         end
         last_slice = slc_cq_tlast;
         
`ifdef PCIE_X16
         slc_dw_cnt = last_slice ? rem_dw_cnt : (16 - slc_start_dw_idx);
`else
         slc_dw_cnt = last_slice ? rem_dw_cnt : (8 - slc_start_dw_idx);
`endif

         if (debug) $display("[%t] : (simp_pcie_usrapp) CQ_MEM_WRITE [slc %02d] - slc_start_dw_idx = %0d, slc_dw_cnt = %0d, loop_end = %0d\n", $realtime, slc_idx, slc_start_dw_idx, slc_dw_cnt, (slc_start_dw_idx + slc_dw_cnt));
         
         for (int dw_idx = slc_start_dw_idx; dw_idx < (slc_start_dw_idx + slc_dw_cnt); dw_idx++) begin
            mem_data[31:0] = slc_cq_tdata[(dw_idx*32) +: 32];
            mem_dw_idx[61:0] = slc_start_addr[63:2] + dw_idx - slc_start_dw_idx;
            mem_byte_addr[63:0] = {mem_dw_idx[61:0], 2'd0};
            if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_WRITE [slc %02d] [dw %1d] - Addr:0x%16x, DATA:0x%08x", $realtime, slc_idx, (dw_idx-slc_start_dw_idx), mem_byte_addr[63:0], mem_data[31:0]);
            mem_array[mem_dw_idx] = mem_data;
            
         end

         rem_dw_cnt -= slc_dw_cnt;
         slc_start_addr += (slc_dw_cnt*4);
         slc_idx++;
      end // while (last_slice == 0)
      
   endtask // perform_cq_wr
   
`ifdef PCIE_X16
   task perform_cq_rd(input [(C_DATA_WIDTH-1):0] cq_tdata, input [182:0] cq_tuser, input [KEEP_WIDTH-1:0] cq_tkeep, input cq_tlast);
`else
   task perform_cq_rd(input [(C_DATA_WIDTH-1):0] cq_tdata, input [84:0] cq_tuser, input [KEEP_WIDTH-1:0] cq_tkeep, input cq_tlast);
`endif
      reg [63:0] addr;
      reg [10:0] dw_cnt;
      reg [127:0] cq_tdata_to_send;
      
      addr[63:0] = {cq_tdata[63:2], 2'b00};
      dw_cnt[10:0] = cq_tdata[64 +: 11];

      $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ - Addr:0x%16x, DW_CNT:%0d", $realtime, addr, dw_cnt);
      
      // Send to req_q
      cq_tdata_to_send[127:0] = cq_tdata[127:0];

      req_q.push_back(cq_tdata_to_send);
      req_mbx.put(1);
   endtask // perform_cq_rd
   

   task perform_cq_rd_req();
      // This tasks gets the request and generates completion packets
      // Each completion packet is equal to MAX_PAYLOAD_SIZE_BYTES

      reg [127:0] cq_rd_desc;
      reg [11:0]  dw_cnt;
      reg [63:0]  start_addr;
      reg [63:0]  end_addr;
      reg [63:0]  prev_mps_boundary_addr;
      reg [63:0]  next_mps_boundary_addr;
      reg [63:0]  comp_avail_byte_cnt;
      reg [63:0]  rem_byte_cnt;
      reg [63:0]  comp_byte_cnt;
      reg [63:0]  comp_start_addr;
      reg [128+64+13+13-1:0] comp_to_send;
      int                 comp_idx;
      reg                 last_comp;
      int                 dummy;
      
      forever begin
         req_mbx.get(dummy);
         
         cq_rd_desc = req_q.pop_front();
         
         start_addr = {cq_rd_desc[63:2], 2'b00};
         dw_cnt[10:0] = cq_rd_desc[74:64]; //cq_rd_desc[64 +: 11];

         
         rem_byte_cnt = {51'd0, dw_cnt[10:0], 2'd0};
         
         end_addr[63:0] = start_addr[63:0] + rem_byte_cnt[63:0] - 64'd1;
         last_comp = 0;
         comp_idx = 0;
         
         if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ_REQ - StartAddr:0x%016x, EndAddr:0x%016x, DW_CNT:%4d, ByteCnt=%4d", $realtime, start_addr, end_addr, dw_cnt[10:0], rem_byte_cnt);

         while (last_comp == 0) begin
            prev_mps_boundary_addr = start_addr - (start_addr % MAX_PAYLOAD_SIZE_BYTES);
            next_mps_boundary_addr = prev_mps_boundary_addr + MAX_PAYLOAD_SIZE_BYTES;
            if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ_REQ [Comp %02d] - PrevBoundAddr:0x%016x, NextBoundAddr:0x%016x", $realtime, comp_idx, prev_mps_boundary_addr, next_mps_boundary_addr);

            if (end_addr >= next_mps_boundary_addr)
              // This means end address is next comp
              comp_byte_cnt = next_mps_boundary_addr - start_addr;
            else
              // This means the end address is in the same completion
              comp_byte_cnt = end_addr - start_addr + 64'd1;

            comp_start_addr = start_addr;

            start_addr += comp_byte_cnt;

            rem_byte_cnt -= comp_byte_cnt;

            if (rem_byte_cnt > 0) begin
               last_comp = 0;
               assert(end_addr > start_addr);
            end
            else begin
               last_comp = 1;
               assert(rem_byte_cnt == 0);
               assert(end_addr == start_addr - 1);
            end

            comp_to_send = {cq_rd_desc[127:0], comp_start_addr[63:0], comp_byte_cnt[12:0], rem_byte_cnt[12:0]};
            if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ_REQ [Comp %02d] - StartAddr:0x%016x, ByteCnt :%4d, RemByteCnt :%4d, last_comp=%1d", $realtime, comp_idx, comp_start_addr, comp_byte_cnt, rem_byte_cnt, last_comp);

            comp_q.push_back(comp_to_send);
            
            comp_mbx.put(1);

            comp_idx++;
            
         end // while (last_comp == 0)
      end // forever begin
   endtask // perform_cq_rd_req
   
   task send_cq_rd_comp();
      // This task gets the completion from the mailbox.
      // It constructs the completion descriptor and data slices and sends
      reg [128+64+13+13-1:0] rd_comp;
      int                 dummy;

      reg [127:0] cq_rd_desc;
      reg [11:0]  dw_cnt;
      reg [63:0]  start_addr;
      reg [63:0]  end_addr;
      reg [63:0]  comp_avail_byte_cnt;
      reg [63:0]  rem_byte_cnt;
      reg [63:0]  comp_byte_cnt;
      reg [63:0]  comp_start_addr;
      reg [128+64+13-1:0] comp_to_send;
      int                 comp_idx;
      reg                 last_comp;
      reg [12:0]          byte_cnt_for_desc;
      reg        last_slice;

      reg [KEEP_WIDTH-1:0] slc_cc_tkeep;
      
      reg [(C_DATA_WIDTH-1):0] slc_cc_tdata;
      reg [63:0] slc_start_addr;
      int        rem_dw_cnt;
      int        slc_dw_cnt, slc_avail_dw_cnt;
      int        slc_start_dw_idx;
      int        slc_idx;
      
      reg [31:0] mem_data;
      reg [61:0] mem_dw_idx;
      reg [63:0] mem_byte_addr;
      bit [31:0] rand_data;

      bit        interleave_tags;
      int        queue_size;
      int        queue_index;
      int        rand_index;
      int        loop_count;

      comp_idx = 0;

      if ($test$plusargs("INTERLEAVE_READ_TAGS")) begin
         interleave_tags = 1'b1;
      end else begin
         interleave_tags = 1'b0;
      end

      forever begin
         comp_mbx.get(dummy);

         if (interleave_tags == 1'b1) begin
            loop_count = 0;
            do begin
               queue_size = comp_q.size();
               loop_count++;
               if (queue_size == 1) begin
                  // Wait for a while to allow multiple entries in queue
                  TSK_TX_CLK_EAT(100);
               end
            end while ((queue_size == 1) && (loop_count < 10));

            if (queue_size == 1) begin
               queue_index = 0;
            end else begin
               // Pick random entry from queue
               rand_index = $urandom_range(queue_size-1,0);
               // Find earliest entry in queue with matching address
               queue_index = rand_index;
               for (int i=0; i<rand_index; i++) begin
                  // Only look for address match in bits [63:12], lower bits can be different within 4k chunk
                  if (comp_q[i][89:38] == comp_q[rand_index][89:38]) begin
                     queue_index = i;
                     break;
                  end
               end
            end
            rd_comp = comp_q[queue_index];
            // Remove entry from queue
            comp_q.delete(queue_index);
         end else begin
            rd_comp = comp_q.pop_front();
         end

         comp_byte_cnt[63:0] = 0;
         rem_byte_cnt[63:0] = 0;
         {cq_rd_desc[127:0], comp_start_addr[63:0], comp_byte_cnt[12:0], rem_byte_cnt[12:0]} = rd_comp;
         $display ("[%t] : (simp_pcie_usrapp) CC_MEM_RD_COMPL [TAG 0x%02x] - Addr:0x%016x, Current DW_CNT :%4d, Remaining DW :%4d", $realtime, cq_rd_desc[103:96], comp_start_addr, comp_byte_cnt[12:2], rem_byte_cnt[12:2]);

         byte_cnt_for_desc[12:0] = comp_byte_cnt[12:0] + rem_byte_cnt[12:0];
         
         @(posedge clk);

`ifdef PCIE_X16
 `ifdef DW_ALIGNED

         // Send descriptor slice first with up to 12 DW

         slc_start_addr[63:0] = comp_start_addr[63:0];
         rem_dw_cnt = comp_byte_cnt[12:2];
         slc_idx = 0;
         last_slice = 0;
         while (last_slice == 0) begin

            slc_cc_tkeep = 0;
            slc_cc_tdata[(C_DATA_WIDTH-1):0] = 0;

            if (slc_idx == 0) begin
               slc_cc_tdata[95:0]  = {
                                        1'b0,                    // Force ECRC        //96
                                        cq_rd_desc[126:124],     // Attributes
                                        cq_rd_desc[123:121],     // TC
                                        1'b1,                    // RID Enable to use the Client supplied Bus/Device/Func No
                                        RP_BUS_DEV_FNS,          // Completer ID
                                        cq_rd_desc[103:96],      // TAG
                                        cq_rd_desc[95:80],       // Requester ID       //64
                                        1'b0,                    // Unused
                                        1'b0,                    // Poisoned
                                        3'd0,                    // Completion Status
                                        comp_byte_cnt[12:2],     // DW Count in Current Completion
                                        2'd0,                    // Unused              //32
                                        1'b0,                    // Locked Read Completion
                                        byte_cnt_for_desc[12:0], // Remaining Byte Count (Including the bytes in the current completion)
                                        6'd0,                    // Unused
                                        cq_rd_desc[1:0],         // AT
                                        1'b0,                    // Unused
                                        comp_start_addr[6:0]     // Start Address LSBs
                                        };
               slc_cc_tkeep[2:0] = 3'h7;
            end

            slc_start_dw_idx = slc_idx ? 4'h0 : 4'h3;
            slc_avail_dw_cnt = 16 - slc_start_dw_idx;
            if (rem_dw_cnt > slc_avail_dw_cnt) begin
               slc_dw_cnt = 16 - slc_start_dw_idx;
               last_slice = 0;
            end
            else begin
               slc_dw_cnt = rem_dw_cnt;
               last_slice = 1;
            end
            
            for (int dw_idx = slc_start_dw_idx; dw_idx < (slc_start_dw_idx + slc_dw_cnt); dw_idx++) begin
               mem_dw_idx[61:0] = slc_start_addr[63:2] + dw_idx - slc_start_dw_idx;
               mem_byte_addr[63:0] = {mem_dw_idx[61:0], 2'd0};
               if (!mem_array.exists(mem_dw_idx)) begin
                  rand_data = $urandom();
                  mem_array[mem_dw_idx] = rand_data;
                  if (allow_rand_read == 1'b1) begin
                     $display("[%t] : (simp_pcie_usrapp) *** WARNING *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end else begin
                     $display("[%t] : (simp_pcie_usrapp) *** ERROR *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end
               end

               mem_data[31:0] = mem_array[mem_dw_idx];
               slc_cc_tdata[(dw_idx*32) +: 32] = mem_data[31:0];

               for (int bit_idx = 0; bit_idx < KEEP_WIDTH; bit_idx++)
                 if (bit_idx <= dw_idx)
                   slc_cc_tkeep[dw_idx] = 1'b1;
               
               if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ [slc %02d] [dw %1d] - Addr:0x%016x, DATA:0x%08x", $realtime, slc_idx, (dw_idx-slc_start_dw_idx), mem_byte_addr[63:0], mem_data[31:0]);
            end
            
            rem_dw_cnt -= slc_dw_cnt;
            slc_start_addr += (slc_dw_cnt*4);
            slc_idx++;

            s_axis_cc_tvalid <= 'b1;
            s_axis_cc_tlast  <= last_slice;
            s_axis_cc_tkeep  <= slc_cc_tkeep;
            s_axis_cc_tdata  <= slc_cc_tdata;
            s_axis_cc_tuser  <= {
                                 (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_cc_tparity : {STRB_WIDTH{1'b0}}), // Parity
                                 17'h0
                                };

            if (debug) $display("[%t] : (simp_pcie_usrapp) Sending CC Mem Read Data Slice", $realtime);

            wait_for_cc_tready();

         end // while (last_slice == 0)

         s_axis_cc_tvalid <= 1'b0;
         s_axis_cc_tlast  <= 1'b0;
         @(posedge clk);
 `else
         // Send descriptor slice
         s_axis_cc_tvalid <= 'b1;
         s_axis_cc_tlast  <= 1'b0;
         s_axis_cc_tkeep  <= 16'h0007;    // 3DW Descriptor

         s_axis_cc_tdata  <= {
                              256'd0,
                              160'd0,                  // unused            //256
                              1'b0,                    // Force ECRC        //96
                              cq_rd_desc[126:124],     // Attributes
                              cq_rd_desc[123:121],     // TC
                              1'b1,                    // RID Enable to use the Client supplied Bus/Device/Func No
                              RP_BUS_DEV_FNS,          // Completer ID
                              cq_rd_desc[103:96],      // TAG
                              cq_rd_desc[95:80],       // Requester ID       //64
                              1'b0,                    // Unused
                              1'b0,                    // Poisoned
                              3'd0,                    // Completion Status
                              comp_byte_cnt[12:2],     // DW Count in Current Completion
                              2'd0,                    // Unused              //32
                              1'b0,                    // Locked Read Completion
                              byte_cnt_for_desc[12:0], // Remaining Byte Count (Including the bytes in the current completion)
                              6'd0,                    // Unused
                              cq_rd_desc[1:0],         // AT
                              1'b0,                    // Unused
                              comp_start_addr[6:0]     // Start Address LSBs
                             };

         s_axis_cc_tuser  <= {
                              (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_cc_tparity : {STRB_WIDTH{1'b0}}), // Parity
                              17'h0
                             };


         if (debug) $display("[%t] : (simp_pcie_usrapp) Sending CC Mem Read Desc", $realtime);

         wait_for_cc_tready();

         // Send data slices
         slc_start_addr[63:0] = comp_start_addr[63:0];
         rem_dw_cnt = comp_byte_cnt[12:2];
         slc_idx = 0;
         last_slice = 0;
         while (last_slice == 0) begin

            slc_cc_tkeep = 0;
            slc_cc_tdata[(C_DATA_WIDTH-1):0] = 0;
            
            slc_start_dw_idx = slc_start_addr[5:2];
            slc_avail_dw_cnt = 16 - slc_start_dw_idx;
            if (rem_dw_cnt > slc_avail_dw_cnt) begin
               slc_dw_cnt = 16 - slc_start_dw_idx;
               last_slice = 0;
            end
            else begin
               slc_dw_cnt = rem_dw_cnt;
               last_slice = 1;
            end
            
            for (int dw_idx = slc_start_dw_idx; dw_idx < (slc_start_dw_idx + slc_dw_cnt); dw_idx++) begin
               mem_dw_idx[61:0] = slc_start_addr[63:2] + dw_idx - slc_start_dw_idx;
               mem_byte_addr[63:0] = {mem_dw_idx[61:0], 2'd0};
               if (!mem_array.exists(mem_dw_idx)) begin
                  rand_data = $urandom();
                  mem_array[mem_dw_idx] = rand_data;
                  if (allow_rand_read == 1'b1) begin
                     $display("[%t] : (simp_pcie_usrapp) *** WARNING *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end else begin
                     $display("[%t] : (simp_pcie_usrapp) *** ERROR *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end
               end

               mem_data[31:0] = mem_array[mem_dw_idx];
               slc_cc_tdata[(dw_idx*32) +: 32] = mem_data[31:0];

               for (int bit_idx = 0; bit_idx < KEEP_WIDTH; bit_idx++)
                 if (bit_idx <= dw_idx)
                   slc_cc_tkeep[dw_idx] = 1'b1;
               
               if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ [slc %02d] [dw %1d] - Addr:0x%016x, DATA:0x%08x", $realtime, slc_idx, (dw_idx-slc_start_dw_idx), mem_byte_addr[63:0], mem_data[31:0]);
            end
            
            rem_dw_cnt -= slc_dw_cnt;
            slc_start_addr += (slc_dw_cnt*4);
            slc_idx++;

            s_axis_cc_tvalid <= 'b1;
            s_axis_cc_tlast  <= last_slice;
            s_axis_cc_tkeep  <= last_slice ? slc_cc_tkeep : 16'hFFFF;
            s_axis_cc_tdata  <= slc_cc_tdata;
            s_axis_cc_tuser  <= {
                                 (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_cc_tparity : {STRB_WIDTH{1'b0}}), // Parity
                                 17'h0
                                };

            if (debug) $display("[%t] : (simp_pcie_usrapp) Sending CC Mem Read Data Slice", $realtime);

            wait_for_cc_tready();

         end // while (last_slice == 0)

         s_axis_cc_tvalid <= 1'b0;
         s_axis_cc_tlast  <= 1'b0;
         @(posedge clk);
 `endif
`else
         // Send descriptor slice
         s_axis_cc_tvalid <= 'b1;
         s_axis_cc_tlast  <= 1'b0;
         s_axis_cc_tkeep  <= 8'h07;       // 3DW Descriptor

         s_axis_cc_tdata  <= {
                              160'd0,                  // unused            //256
                              1'b0,                    // Force ECRC        //96
                              cq_rd_desc[126:124],     // Attributes
                              cq_rd_desc[123:121],     // TC
                              1'b1,                    // RID Enable to use the Client supplied Bus/Device/Func No
                              RP_BUS_DEV_FNS,          // Completer ID
                              cq_rd_desc[103:96],      // TAG
                              cq_rd_desc[95:80],       // Requester ID       //64
                              1'b0,                    // Unused
                              1'b0,                    // Poisoned
                              3'd0,                    // Completion Status
                              comp_byte_cnt[12:2],     // DW Count in Current Completion
                              2'd0,                    // Unused              //32
                              1'b0,                    // Locked Read Completion
                              byte_cnt_for_desc[12:0], // Remaining Byte Count (Including the bytes in the current completion)
                              6'd0,                    // Unused
                              cq_rd_desc[1:0],         // AT
                              1'b0,                    // Unused
                              comp_start_addr[6:0]     // Start Address LSBs
                             };

         s_axis_cc_tuser  <= {
                              (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_cc_tparity : {STRB_WIDTH{1'b0}}), // Parity
                              1'b0              // Discontinue
                             };



         if (debug) $display("[%t] : (simp_pcie_usrapp) Sending CC Mem Read Desc", $realtime);

         wait_for_cc_tready();

         // Send data slices
         slc_start_addr[63:0] = comp_start_addr[63:0];
         rem_dw_cnt = comp_byte_cnt[12:2];
         slc_idx = 0;
         last_slice = 0;
         while (last_slice == 0) begin

            slc_cc_tkeep = 0;
            slc_cc_tdata[(C_DATA_WIDTH-1):0] = 0;
            
            slc_start_dw_idx = slc_start_addr[4:2];
            slc_avail_dw_cnt = 8 - slc_start_dw_idx;
            if (rem_dw_cnt > slc_avail_dw_cnt) begin
               slc_dw_cnt = 8 - slc_start_dw_idx;
               last_slice = 0;
            end
            else begin
               slc_dw_cnt = rem_dw_cnt;
               last_slice = 1;
            end
            
            for (int dw_idx = slc_start_dw_idx; dw_idx < (slc_start_dw_idx + slc_dw_cnt); dw_idx++) begin
               mem_dw_idx[61:0] = slc_start_addr[63:2] + dw_idx - slc_start_dw_idx;
               mem_byte_addr[63:0] = {mem_dw_idx[61:0], 2'd0};
               if (!mem_array.exists(mem_dw_idx)) begin
                  rand_data = $urandom();
                  mem_array[mem_dw_idx] = rand_data;
                  if (allow_rand_read == 1'b1) begin
                     $display("[%t] : (simp_pcie_usrapp) *** WARNING *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end else begin
                     $display("[%t] : (simp_pcie_usrapp) *** ERROR *** Reading random data from uninitialized memory address 0x%016x", $realtime, mem_byte_addr);
                  end
               end

               mem_data[31:0] = mem_array[mem_dw_idx];
               slc_cc_tdata[(dw_idx*32) +: 32] = mem_data[31:0];

               for (int bit_idx = 0; bit_idx < KEEP_WIDTH; bit_idx++)
                 if (bit_idx <= dw_idx)
                   slc_cc_tkeep[dw_idx] = 1'b1;
               
               if (debug) $display ("[%t] : (simp_pcie_usrapp) CQ_MEM_READ [slc %02d] [dw %1d] - Addr:0x%016x, DATA:0x%08x", $realtime, slc_idx, (dw_idx-slc_start_dw_idx), mem_byte_addr[63:0], mem_data[31:0]);
            end
            
            rem_dw_cnt -= slc_dw_cnt;
            slc_start_addr += (slc_dw_cnt*4);
            slc_idx++;

            s_axis_cc_tvalid <= 'b1;
            s_axis_cc_tlast  <= last_slice;
            s_axis_cc_tkeep  <= last_slice ? slc_cc_tkeep : 8'hFF;
            s_axis_cc_tdata  <= slc_cc_tdata;
            s_axis_cc_tuser  <= {
                                 (ATTR_AXISTEN_IF_RQ_PARITY_CHECK ?  s_axis_cc_tparity : {STRB_WIDTH{1'b0}}), // Parity
                                 1'b0              // Discontinue
                                };

            if (debug) $display("[%t] : (simp_pcie_usrapp) Sending CC Mem Read Data Slice", $realtime);

            wait_for_cc_tready();

         end // while (last_slice == 0)

         s_axis_cc_tvalid <= 1'b0;
         s_axis_cc_tlast  <= 1'b0;
         @(posedge clk);
`endif

         if (debug) $display("[%t] : (simp_pcie_usrapp) Done with Mem Read Completion", $realtime);
         comp_idx++;
         
      end // forever begin
      
   endtask // send_cq_rd_comp
   
   task automatic wait_for_cc_tready();
      reg done;
      done = s_axis_cc_tready;
      if (done == 1) begin
         @(posedge clk);
      end else begin
         while (done == 0) begin
            @(posedge clk);
            done = s_axis_cc_tready;
         end
      end
   endtask // wait_for_cc_tready

   
   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////
   ////////  DUMMY TASKS FOR SUPPORTING OLD CODE    /////////
   //////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////
   // Dummy tasks to avoid elaboration errors

   task automatic TSK_TX_CLK_EAT;
      input    [31:0]            clock_count;
      repeat(clock_count)
        @(posedge clk);
   endtask // TSK_TX_CLK_EAT

   task S_MEMORY_WRITE_64 (input[63:0] addr, input[31:0] data);
      TSK_MEM_WRITE_64(addr, data);
   endtask // S_MEMORY_WRITE_64

   task S_MEMORY_READ_64_RET (input[63:0] addr, output[31:0] rdata);
      TSK_MEM_READ_64(addr, rdata);
   endtask // S_MEMORY_READ_64_RET

   
endmodule // simp_pcie_usrapp

 
 
   
