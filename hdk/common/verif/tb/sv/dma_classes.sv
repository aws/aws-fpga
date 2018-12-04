// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

// This has DMA helper classes
//--------------------------------------

//TODO:
// - Add support for freeing, reusing pages
// - Add flow control  (Desc, and wb ring)


//************************************************************************************
//------------------------------------------------------------------------------------
// Access class, this provides access to the DUT and testing infrastructure.  We
// use a class so that can move easily bewteen testbenches without changing the tests.
// The access given here are:
//
//    - BAR4 peek/poke
//    - Host memory write/read
//
//------------------------------------------------------------------------------------
//************************************************************************************

`ifdef SH_BFM_TB
   import tb_type_defines_pkg::*;
`endif

class mem_access_t;
   logic rnw;
   logic [63:0] addr;
   logic [31:0] data [$];
   logic        wc;

   function new();
   endfunction // new

endclass // mem_access_t

class access_t;

   bit wc;                 //Enable write combining
   mailbox poke_mb;
   bit[63:0] bar;
   bit[63:0] ocl_bar;
   semaphore access_lock;  //Semaphore to make sure read/write are exclusive.  This is required for BFMs that cannot handle multiple
                           // outstanding cycles simultaneously

   function new (input bit wc=0, input[63:0] bar=0, input[63:0] ocl_bar=0);

      this.wc = wc;
      this.poke_mb = new(1);
      this.bar = bar;
      this.ocl_bar = ocl_bar;
      access_lock = new(1);

   endfunction


   virtual task peek_verify (input[63:0] addr, output logic[31:0] data, input [31:0] exp_data, input [31:0] mask=32'hffff_ffff, output logic error, input exit_on_error = 0, input int max_iters = 10);
      int iter = 0;
      while (iter < max_iters) begin
         peek(.addr(addr), .data(data));

         if ((data & mask) != exp_data) begin
            if (iter == (max_iters-1)) begin
               $display($time,,,"***ERROR*** : peek_verify - Addr = 0x%016x, Expected Data = 0x%08x, Actual Data = 0x%08x, Mask = 0x%08x", addr, exp_data, data, mask);
               error = 1;
               if (exit_on_error) begin
                  $display($time,,,"***FATAL*** : peek_verify - Exiting on Error");
                  $finish;
               end // if (exit_on_error)
            end // if (iter >= max_iters)
            else begin
               error = 0;
            end // else: !if(iter >= max_iters)

         end // if ((data & mask) != exp_data)
         else
           return;

         iter++;
      end // while (iter < max_iters)
   endtask // peek_verify


   task start_mem_access_threads();
      fork : FORK_MEM_ACCESS_THREADS
         mem_write_thread();
      join_none
   endtask // start_mem_access_threads

   //Poke
   task poke (input[63:0] addr, input[31:0] data[$], input bit wc=this.wc);
      mem_access_t wr_txn;
      wr_txn = new();
      wr_txn.rnw = 0;
      wr_txn.addr = addr;
      wr_txn.data = data;
      wr_txn.wc = wc;

      poke_mb.put(wr_txn);
   endtask // poke

   virtual task poke_dw (input [63:0] addr, input [31:0] data);
      logic [31:0] data_q [$];
      data_q.push_back(data);

      this.poke (.addr(addr), .data(data_q), .wc(0));
   endtask // poke_dw

   //Allocate a page.  Note in sh_bfm tb don't need to do any allocation because is assoc array
   virtual function alloc_mem (input[63:0] addr);

      //tb.map_host_memory(.addr(addr));

   endfunction

   //Read task
   extern virtual task peek (input[63:0] addr, output logic[31:0] data);

   //Mem Write processing thread
   extern task mem_write_thread ();

   //Write DW to the host from the buffer
   extern virtual function write_host_dw (input[63:0] addr, input[31:0] data);

   //Read DW from the host into buffer
   extern virtual function[31:0] read_host_dw (input[63:0] addr);

   //Write byte to the host from the buffer
   extern virtual function write_host_byte (input[63:0] addr, input[7:0] data);

   //Read byte from the host into buffer
   extern virtual function[7:0] read_host_byte (input[63:0] addr);

   //Write to OCL
   extern virtual task poke_ocl(input[15:0] addr, input[31:0] data);

   //Read from OCL
   extern virtual task peek_ocl(input[15:0] addr, output[31:0] data);

endclass


   //Peek
   task access_t::peek (input[63:0] addr, output logic[31:0] data);

      tb.peek(.addr(addr), .data(data));

   endtask


   //mem_write_thread
   task access_t::mem_write_thread();
      mem_access_t wr_txn;

      forever begin
         poke_mb.get(wr_txn);
         if (!wr_txn.wc) begin
            for (int i=0; i<wr_txn.data.size(); i++)
              tb.poke(.addr(wr_txn.addr + i*4), .data(wr_txn.data[i]));
         end
         else begin
            tb.poke_pcis_wc(.addr(wr_txn.addr), .data(wr_txn.data));
         end
      end

   endtask // mem_write_thread

   //write_host_dw
   function access_t::write_host_dw (input[63:0] addr, input[31:0] data);

      for (int i=0; i<4; i++)
      begin
         tb.hm_put_byte(.addr(addr+i), .d(data[i*8+:8]));
      end
   endfunction

   //read_host_dw
   function[31:0] access_t::read_host_dw (input[63:0] addr);
      logic[31:0] tmp_data;

      for (int i=0; i<4; i++)
         tmp_data[i*8+:8] = tb.hm_get_byte(.addr(addr + i));

      read_host_dw = tmp_data;
   endfunction

   //write_host_byte
   function access_t::write_host_byte (input[63:0] addr, input[7:0] data);

      tb.hm_put_byte(.addr(addr), .d(data));
   endfunction

   //read_host_byte
   function[7:0] access_t::read_host_byte (input[63:0] addr);
      logic[7:0] tmp_data;

         tmp_data = tb.hm_get_byte(.addr(addr));

      read_host_byte = tmp_data;
   endfunction

   //Write to OCL
   task access_t::poke_ocl(input[15:0] addr, input[31:0] data);
      tb.poke_ocl(.addr(addr), .data(data));
   endtask

   //Read from OCL
   task access_t::peek_ocl(input[15:0] addr, output[31:0] data);
      tb.peek_ocl(.addr(addr), .data(data));
   endtask

//**************************************************************
//--------------------------------------------------------------
// WriteBack descriptor class
//--------------------------------------------------------------
//**************************************************************
class wb_desc_t;
   logic valid;
   logic eop;
   logic[31:0] length;
   logic[63:0] user_bits;

   function new(logic valid=0, logic eop=0, logic[31:0] length=0, logic[63:0] user_bits=0);
      this.valid = valid;
      this.eop = eop;
      this.length = length;
      this.user_bits = user_bits;
   endfunction

endclass



//*************************************************************************************
//-------------------------------------------------------------------------------------
// Buffer class.  has data array, and methods to read/write to/from host memory,
// and compare buffers.
//-------------------------------------------------------------------------------------
//*************************************************************************************


class dma_buf_t extends gen_buf_t;

   logic[63:0] addr;                //this is the base address of the buffer
   access_t access;                 //Access function
   int buf_size;
   bit verbose;

   //Input size of buffer in bytes -- assume address of all f's is "null"
   function new (access_t access, input[63:0] addr = 64'hffffffff_ffffffff, input int buf_size = 4096, input verbose=0);
      super.new();
      this.addr = addr;
      this.access = access;
      this.buf_size = buf_size;
      if (verbose)
         $display($time,,,"dma_buf_t: Allocating buffer addr=0x%x, size=0x%x", this.addr, this.buf_size);
   endfunction


   //Write to memory.
   // Start_offset - byte offset of start
   //  Length - length in bytes
   function write_buf_host(input[63:0] start_offset=0, input[31:0] length=32'hffffffff);

//      bit[31:0] length;

      //If length is 0xffff_ffff, that is special value meaning use the buf_size
      if (length==32'hffffffff)
         length = this.buf_size;

      // $display($time,,,"dma_buf_t:write_host_buf length=%0d", length);

      for (int i=0; i<length; i++)
      begin
         //Write byte to host memory
         access.write_host_byte((this.addr + start_offset + i), this.data[start_offset + i]);
      end

   endfunction

   //Read from memory.  Length is in bytes
   function read_host_buf(input[63:0] start_offset=0, input[31:0] length=32'hffffffff, input bit verbose=0);
      logic [31:0] cur_dw;
//      int length;

      //If length is 0xffff_ffff, that is special value meaning use the buf_size
      if (length==32'hffffffff)
         length = (this.buf_size);

      if (verbose)
        $display($time,,,"dma_buf_t:read_host_buf length=%0d", length);

      for (int i=0; i<length; i++)
      begin
         //Get byte from host memory
         this.data[start_offset + i] = access.read_host_byte(this.addr + start_offset + i);
         if (verbose)
           $display($time,,,"dma_buf_t:read_host_buf addr=0x%016x, data[%0d]=0x%08x", this.addr + start_offset + i, start_offset + i,  this.data[start_offset + i]);
      end

   endfunction


endclass


//*************************************************************************************
//-------------------------------------------------------------------------------------
// DMA class.
//
//    Has the descriptor rings, and methods to post descriptors
//-------------------------------------------------------------------------------------
//*************************************************************************************

class sde_dma_t;


   parameter C2H_DESC_BASE       = 16'h0000;
   parameter H2C_DESC_BASE       = 16'h1000;
   parameter H2C_SPB_BASE        = 16'h2000;
   parameter CSR_BASE            = 16'h3000;

   bit verbose = 0;


   bit inc_page_alloc_mode = 1;           //Allocate buffers in incrementing order
   bit desc_type = 0;                     //0 = Regular, 1 = Compact
   bit[15:0] c2h_desc_size;                   //Descriptor size in bytes
   bit[15:0] h2c_desc_size;                   //Descriptor size in bytes
   bit[7:0] c2h_wb_desc_size;                 //Writeback descriptor size in bytes
   int page_size;                         //Page size in bytes

   int error_count;

   randc bit[15:0] rnd_alloc_page;
   int alloc_num_pages;

   int inc_page_alloc = 0;

   int num_chan = 1;                      //Don't yet support multiple channels

   int wb_poll_interval;                  //Writeback descriptor poll interval in ns

   int num_c2h_pkts;                      //Number of c2h packets received by Host


   logic[31:0] h2c_desc_q[$];             //Store all the descriptors we are creating before we post
   logic[31:0] c2h_desc_q[$];             //Store all the descriptors we are creating before we post

   logic[15:0] c2h_wb_desc_wr_ptr;        //Have a page size ring for writeback descriptors
   //logic[15:0] h2c_wb_desc_wr_ptr;        //Have a page size ring for writeback descriptors

   logic[15:0] c2h_wb_desc_rd_ptr;        //Have a page size ring for writeback descriptors
   //logic[15:0] h2c_wb_desc_rd_ptr;        //Have a page size ring for writeback descriptors

   dma_buf_t c2h_wb_buf;                  //Page for C2H writeback
   //dma_buf_t h2c_wb_buf;                  //Page for H2C writeback

   access_t access;                       //Access functions (peek, poke, host buf access)


   dma_buf_t c2h_post_buf_q[$];           //C2H buffers posted in the descriptors

   gen_buf_t c2h_pkt_rx_q[$];             //C2H received packets. This can be used by scoreboard for checking
   logic[63:0] c2h_pkt_rq_user_q[$];      //C2H received user bits.

   bit [63:0]  cfg_c2h_wb_status_addr;    //C2H WB status base address in host
   bit[63:0] cfg_c2h_wb_desc_cnt_addr;    //C2H WB descriptor credit count address in host
   bit cfg_c2h_wb_desc_cdt_en;            //Enable WB descriptor credit count
   bit cfg_c2h_wb_desc_cnt_en;            //Enable WB completed descriptor count
   bit cfg_c2h_wb_md_ptr_en;              //Enable WB metadata pointer count

   bit[63:0] cfg_c2h_cdt_limit_addr;      //C2H descriptor credit count address in host

   bit[63:0] cfg_c2h_wb_pkt_cnt_addr;     //C2H WB descriptor packet count address in host
   bit cfg_c2h_wb_pkt_cnt_en;             //Enable WB packet credit count

   bit [63:0] cfg_c2h_wb_wr_ptr_addr;     //C2H WB Read Pointer Address in host

   int cfg_desc_wc_min;
   int cfg_desc_wc_max;

   int pc2h_min_length = 1;               //Post C2H descriptor min length in bytes
   int pc2h_max_length = 4096;            //Post C2H descriptor max length in bytes
   int pc2h_min_offset = 0;               //Minimum offset of address
   int pc2h_max_offset = 64;              //Maximum offset of address

   bit [63:0]  cfg_h2c_wb_status_addr;    //H2C WB status base address in host
   bit[63:0] cfg_h2c_cdt_limit_addr;      //H2C credit limit address
   bit cfg_h2c_wb_desc_cdt_en;            //Enable WB descriptor credit count
   bit cfg_h2c_wb_desc_cnt_en;            //Enable WB completed descriptor count
   bit[63:0] cfg_h2c_wb_desc_cnt_addr;    //H2C descriptor credit count address in host

   bit[63:0] cfg_h2c_wb_pkt_cnt_addr;     //H2C WB descriptor packet count address in host
   bit cfg_h2c_wb_pkt_cnt_en;             //Enable WB packet credit count

   logic [63:0] c2h_csr_offset = 64'h400;
   logic [63:0] c2h_csr_base_addr;
   logic [63:0] h2c_csr_offset = 64'hA00;
   logic [63:0] h2c_csr_base_addr;

   int          c2h_wb_rdptr_coalesce_cnt = 20; // Number of write-backs to wait for before updating read pointer

   logic [5:0]  cfg_c2h_wc_cnt = 6'd0;
   logic        cfg_c2h_md_wr_ptr_wc_en = 0;
   logic        cfg_c2h_pkt_cnt_wc_en = 0;
   logic        cfg_c2h_desc_cnt_wc_en = 0;
   logic        cfg_c2h_desc_cdt_wc_en = 0;
   logic [3:0]  cfg_c2h_wc_to_cnt = 4'd0;
   logic [19:0] cfg_c2h_wc_to_rsln = 20'd0;
   logic [5:0]  cfg_h2c_wc_cnt = 6'd0;
   logic        cfg_h2c_pkt_cnt_wc_en = 0;
   logic        cfg_h2c_desc_cnt_wc_en = 0;
   logic        cfg_h2c_desc_cdt_wc_en = 0;
   logic [3:0]  cfg_h2c_wc_to_cnt = 4'd0;
   logic [19:0] cfg_h2c_wc_to_rsln = 20'd0;

   logic [31:0] cfg_c2h_ring_size = 512;
   logic [15:0] cfg_c2h_num_md = 64;
   logic [15:0] cfg_c2h_ring_offset = 0;


   int h2c_total_desc = 0;                   //Total number of descriptors posted H2C
   int c2h_total_desc = 0;                   //Total number of descriptors posted C2H

//   C2H:
//      credit_limit : 64'h00001000_00000000
//      desc_cnt :     64'h00001000_00000004
//      pkt_cnt :      64'h00001000_00000008
//
//   H2C:
//      credit_limit : 64'h00004000_00000000
//      desc_cnt :     64'h00004000_00000004
//      pkt_cnt :      64'h00004000_00000008

   //---------------------------------------------------
   // New function -- desc_size is in bytes
   //---------------------------------------------------
   function new(access_t access, input int page_size = 4096, input desc_type = 0, input int wb_poll_interval = 100,
                input[63:0] cfg_c2h_wb_status_addr=64'h00001000_00000000,
                input cfg_c2h_wb_desc_cdt_en=1,
                input cfg_c2h_wb_desc_cnt_en=0,
                input cfg_c2h_wb_md_ptr_en = 1,
                input cfg_c2h_wb_pkt_cnt_en=0,
                input[63:0] cfg_h2c_wb_status_addr=64'h00004000_00000000,
                input cfg_h2c_wb_desc_cdt_en=1,
                input cfg_h2c_wb_desc_cnt_en=0,
                input cfg_h2c_wb_pkt_cnt_en=0,
                input int cfg_desc_wc_min = 64,
                input int cfg_desc_wc_max = 64,
                input [5:0] cfg_c2h_wc_cnt = 6'd0,
                input cfg_c2h_md_wr_ptr_wc_en = 0,
                input cfg_c2h_pkt_cnt_wc_en = 0,
                input cfg_c2h_desc_cnt_wc_en = 0,
                input cfg_c2h_desc_cdt_wc_en = 0,
                input [3:0] cfg_c2h_wc_to_cnt = 4'd0,
                input [19:0] cfg_c2h_wc_to_rsln = 20'd0,
                input [5:0] cfg_h2c_wc_cnt = 6'd0,
                input cfg_h2c_pkt_cnt_wc_en = 0,
                input cfg_h2c_desc_cnt_wc_en = 0,
                input cfg_h2c_desc_cdt_wc_en = 0,
                input [3:0] cfg_h2c_wc_to_cnt = 4'd0,
                input [19:0] cfg_h2c_wc_to_rsln = 20'd0,
                input [15:0] cfg_c2h_num_md = 256,
                input [15:0] cfg_c2h_ring_offset = 0,
                input verbose = 0
                );

      bit[15:0] cur_page;

      this.desc_type = desc_type;


      this.page_size = page_size;
      this.access = access;

      this.c2h_desc_size = 16;
      this.h2c_desc_size = desc_type ? 16 : 32;
      this.c2h_wb_desc_size = desc_type ? 8 : 16;

      this.alloc_num_pages = 0;

      this.c2h_wb_desc_wr_ptr = 0;

      this.c2h_wb_desc_rd_ptr = 0;

      this.wb_poll_interval = (wb_poll_interval<1)? 1: wb_poll_interval;

      this.cfg_desc_wc_min = cfg_desc_wc_min;
      this.cfg_desc_wc_max = cfg_desc_wc_max;

      this.verbose = verbose;

      num_c2h_pkts = 0;

      this.h2c_csr_base_addr = CSR_BASE + this.h2c_csr_offset;
      this.c2h_csr_base_addr = CSR_BASE + this.c2h_csr_offset;

      this.cfg_c2h_wb_status_addr = cfg_c2h_wb_status_addr;
      this.cfg_c2h_cdt_limit_addr = this.cfg_c2h_wb_status_addr + 4;
      this.cfg_c2h_wb_desc_cnt_addr = this.cfg_c2h_wb_status_addr + 8;
      this.cfg_c2h_wb_desc_cdt_en = cfg_c2h_wb_desc_cdt_en;
      this.cfg_c2h_wb_desc_cnt_en = cfg_c2h_wb_desc_cnt_en;
      this.cfg_c2h_wb_md_ptr_en   = cfg_c2h_wb_md_ptr_en;
      this.cfg_c2h_wb_pkt_cnt_addr = this.cfg_c2h_wb_status_addr + 12;
      this.cfg_c2h_wb_pkt_cnt_en = cfg_c2h_wb_pkt_cnt_en;
      this.cfg_c2h_wb_wr_ptr_addr = this.cfg_c2h_wb_status_addr + 16;

      this.cfg_h2c_wb_status_addr = cfg_h2c_wb_status_addr;
      this.cfg_h2c_cdt_limit_addr = this.cfg_h2c_wb_status_addr + 4;
      this.cfg_h2c_wb_desc_cnt_addr = this.cfg_h2c_wb_status_addr + 8;
      this.cfg_h2c_wb_desc_cdt_en = cfg_h2c_wb_desc_cdt_en;
      this.cfg_h2c_wb_desc_cnt_en = cfg_h2c_wb_desc_cnt_en;
      this.cfg_h2c_wb_pkt_cnt_addr = this.cfg_h2c_wb_status_addr + 12;
      this.cfg_h2c_wb_pkt_cnt_en = cfg_h2c_wb_pkt_cnt_en;

      this.cfg_c2h_wc_cnt          = cfg_c2h_wc_cnt         ;
      this.cfg_c2h_md_wr_ptr_wc_en = cfg_c2h_md_wr_ptr_wc_en;
      this.cfg_c2h_pkt_cnt_wc_en   = cfg_c2h_pkt_cnt_wc_en  ;
      this.cfg_c2h_desc_cnt_wc_en  = cfg_c2h_desc_cnt_wc_en ;
      this.cfg_c2h_desc_cdt_wc_en  = cfg_c2h_desc_cdt_wc_en ;
      this.cfg_c2h_wc_to_cnt       = cfg_c2h_wc_to_cnt      ;
      this.cfg_c2h_wc_to_rsln      = cfg_c2h_wc_to_rsln     ;
      this.cfg_h2c_wc_cnt          = cfg_h2c_wc_cnt         ;
      this.cfg_h2c_pkt_cnt_wc_en   = cfg_h2c_pkt_cnt_wc_en  ;
      this.cfg_h2c_desc_cnt_wc_en  = cfg_h2c_desc_cnt_wc_en ;
      this.cfg_h2c_desc_cdt_wc_en  = cfg_h2c_desc_cdt_wc_en ;
      this.cfg_h2c_wc_to_cnt       = cfg_h2c_wc_to_cnt      ;
      this.cfg_h2c_wc_to_rsln      = cfg_h2c_wc_to_rsln     ;

      this.cfg_c2h_num_md = cfg_c2h_num_md;
      this.cfg_c2h_ring_size = this.cfg_c2h_num_md * this.c2h_wb_desc_size;
      this.cfg_c2h_ring_offset = cfg_c2h_ring_offset;

      // Allocate metadata ring
      c2h_wb_buf = new(.access(access), .addr(alloc_page(.s("C2H_WB_BUF")) + cfg_c2h_ring_offset), .buf_size(cfg_c2h_ring_size), .verbose(this.verbose));

      //Initialize the writeback descriptors to 0
      c2h_wb_buf.init_const(.first_data(0), .length(cfg_c2h_ring_size));
      c2h_wb_buf.write_buf_host();


      //Initialize the Credit limit values in Host memory to 0
      access.write_host_dw(.addr(this.cfg_c2h_cdt_limit_addr), .data(32'h0));
      access.write_host_dw(.addr(this.cfg_c2h_wb_desc_cnt_addr), .data(32'h0));

      access.write_host_dw(.addr(this.cfg_h2c_cdt_limit_addr), .data(32'h0));
      $display($time,,,"NOTE: sde_dma: NEW desc_type=%s, page_size=0x%x,  c2h_wb_buf_addr=0x%x, cfg_c2h_wb_desc_cnt_addr=0x%x, cfg_c2h_wb_desc_cdt_en=0x%0x, cfg_c2h_wb_desc_cnt_en=0x%0x, cfg_c2h_wb_md_ptr_en=0x%0x cfg_c2h_wb_status_addr=0x%x, cfg_c2h_num_md=%0d, cfg_c2h_ring_offset=%0d", (this.desc_type ? "COMPACT" : "REGULAR"), this.page_size, c2h_wb_buf.addr, this.cfg_c2h_wb_desc_cnt_addr, this.cfg_c2h_wb_desc_cdt_en, this.cfg_c2h_wb_desc_cnt_en, this.cfg_c2h_wb_md_ptr_en, this.cfg_c2h_wb_status_addr, cfg_c2h_num_md, cfg_c2h_ring_offset);

   endfunction

   virtual      task configure (input verify = 0);
      // perform all required CSR configuration of the dma engine
      c2h_configure(verify);
      h2c_configure(verify);
   endtask // configure

   virtual      task c2h_configure(input verify=0);
      logic [31:0] rd_data;
      logic [31:0] wr_data;
      bit          error;
      logic [63:0] addr;

      $display($time,,,"sde.c2h_configure");

      // Initialize counters and write-back addresses
      // Enable Descriptor Count and Packet Count Write-Backs
      addr = c2h_csr_base_addr + 16'h300;
      wr_data = {16'd0,
                 2'd0, cfg_c2h_wc_cnt[5:4],
                 cfg_c2h_wc_cnt[3:0],
                 cfg_c2h_md_wr_ptr_wc_en, cfg_c2h_pkt_cnt_wc_en, cfg_c2h_desc_cnt_wc_en, cfg_c2h_desc_cdt_wc_en,
                 cfg_c2h_wb_md_ptr_en, cfg_c2h_wb_desc_cdt_en, cfg_c2h_wb_pkt_cnt_en, cfg_c2h_wb_desc_cnt_en};
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Configure counter Write-Back Address
      addr = c2h_csr_base_addr + 16'h304;
      wr_data = cfg_c2h_wb_status_addr[31:0];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      addr = c2h_csr_base_addr + 16'h308;
      wr_data = cfg_c2h_wb_status_addr[63:32];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Configure Coalesce Timeout Counter
      addr = c2h_csr_base_addr + 16'h30C;
      wr_data = {cfg_c2h_wc_to_cnt, cfg_c2h_wc_to_rsln};
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Clear credit "limit" counter
      addr = c2h_csr_base_addr + 16'h100;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

      // Clear credit "consumed" counter
      addr = c2h_csr_base_addr + 16'h104;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd64), .error(error), .exit_on_error(1));

      // Clear descriptor count counter
      addr = c2h_csr_base_addr + 16'h108;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

      // Clear Packet Counters
      addr = c2h_csr_base_addr + 16'h500;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

      // WB Ring configuration
      // Ring Base Address
      addr = c2h_csr_base_addr + 16'h318;
      wr_data = c2h_wb_buf.addr[31:0];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      addr = c2h_csr_base_addr + 16'h31C;
      wr_data = c2h_wb_buf.addr[63:32];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Ring Size in Bytes
      addr = c2h_csr_base_addr + 16'h320;
      wr_data = c2h_wb_buf.buf_size;
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Initialize Read-pointer
      addr = c2h_csr_base_addr + 16'h324;
      wr_data = 0;
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Clear Write-Pointer
      addr = c2h_csr_base_addr + 16'h328;
      wr_data = 0;
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

   endtask // c2h_configure

   virtual         task h2c_configure(input verify=0);
      logic [31:0] rd_data;
      logic [31:0] wr_data;
      bit          error;
      logic [63:0] addr;

      $display($time,,,"sde.h2c_configure");
      // Initialize counters and write-back addresses
      // Enable Descriptor Count and Packet Count Write-Backs
      addr = h2c_csr_base_addr + 16'h300;
      wr_data = {16'd0,
                 2'd0, cfg_h2c_wc_cnt[5:4],
                 cfg_h2c_wc_cnt[3:0],
                 1'b0, cfg_h2c_pkt_cnt_wc_en, cfg_h2c_desc_cnt_wc_en, cfg_h2c_desc_cdt_wc_en,
                 1'd0, cfg_h2c_wb_desc_cdt_en, cfg_h2c_wb_pkt_cnt_en, cfg_h2c_wb_desc_cnt_en};
      access.poke_dw (.addr(addr), .data(wr_data));
      access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Configure counter Write-Back Address
      addr = h2c_csr_base_addr + 16'h304;
      wr_data = cfg_h2c_wb_status_addr[31:0];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      addr = h2c_csr_base_addr + 16'h308;
      wr_data = cfg_h2c_wb_status_addr[63:32];
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Configure Coalesce Timeout Counter
      addr = h2c_csr_base_addr + 16'h30C;
      wr_data = {cfg_h2c_wc_to_cnt, cfg_h2c_wc_to_rsln};
      access.poke_dw (.addr(addr), .data(wr_data));
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));

      // Clear credit "limit" counter
      addr = h2c_csr_base_addr + 16'h100;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

      // Clear credit "consumed" counter
      addr = h2c_csr_base_addr + 16'h104;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd64), .error(error), .exit_on_error(1));

      // Clear descriptor count counter
      addr = h2c_csr_base_addr + 16'h108;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

      // Clear Packet Counters
      addr = h2c_csr_base_addr + 16'h500;
      access.poke_dw (.addr(addr), .data(32'd0));
      // Read and check if it got cleared
      if (verify)
         access.peek_verify (.addr(addr), .data(rd_data), .exp_data(32'd0), .error(error), .exit_on_error(1));

   endtask // h2c_configure

   //------------------------------------------------------------------------
   //Allocate a page.  Note we do not support freeing and re-using pages.
   // Returns the byte address of the page
   //------------------------------------------------------------------------
   function[63:0] alloc_page (input string s="");
      if (this.alloc_num_pages == 'h10_0000)
      begin
         $display($time,,,"***FATAL*** Only support allocating up to 1M pages");
         $finish;
      end
      else
      begin
         alloc_page = (inc_page_alloc_mode)? (inc_page_alloc++) * this.page_size: std::randomize(rnd_alloc_page) * this.page_size;
         access.alloc_mem(alloc_page);
         if (this.verbose)
            $display($time,,,"sde_dma_t: Allocating page - %s: addr=0x%x (page_size=0x%x)", s, alloc_page, this.page_size);
      end
   endfunction

   //---------------------------
   //Post H2C descriptor
   //---------------------------
   virtual function void post_h2c_desc (input dma_buf_t post_buf, input sop=0, input eop=0, input spb=0, input[63:0] user=0);

      logic[31:0] desc[];

     if (this.h2c_desc_size==16)
      begin
         desc = new[4];
         desc[0] = post_buf.buf_size[31:0];
         desc[1] = post_buf.addr[31:0];
         desc[2] = {spb, eop, post_buf.addr[47:32]};
         desc[3] = 0;
      end
      else
      begin
         desc = new[8];
         desc[0] = post_buf.buf_size[31:0];
         desc[1] = post_buf.addr[31:0];
         desc[2] = post_buf.addr[63:32];
         desc[3] = {spb, eop};
         desc[4] = 0;
         desc[5] = 0;
         desc[6] = user[31:0];
         desc[7] = user[63:32];
      end

      for (int i=0; i<desc.size(); i++)
         h2c_desc_q.push_back(desc[i]);

   endfunction

   //-------------------------------
   //Post a C2H descriptor
   //-------------------------------
   virtual function void post_c2h_desc (input dma_buf_t post_buf, input sop=0, input eop=0, input[63:0] wb_addr=64'hffffffff_ffffffff);

      logic[31:0] desc[];
      logic [31:0] c2h_wb_desc_wr_ptr_next;

      //Auto writeback address
      if (wb_addr==64'hffffffff_ffffffff)
        begin
           c2h_wb_desc_wr_ptr_next = c2h_wb_desc_wr_ptr == (cfg_c2h_num_md-1) ? 0 : (c2h_wb_desc_wr_ptr + 1);
        if (c2h_wb_desc_wr_ptr_next == c2h_wb_desc_rd_ptr)
         begin
            $display($time,,,"***FATAL*** sde_dma_t.post_c2h_desc write_back pointer overflow");
            $finish;
         end
         else
         begin
            wb_addr = c2h_wb_buf.addr + (c2h_wb_desc_wr_ptr * c2h_wb_desc_size);
            if (c2h_wb_desc_wr_ptr == (cfg_c2h_num_md - 1))
               c2h_wb_desc_wr_ptr = 0;
            else
               c2h_wb_desc_wr_ptr += 1;
         end
      end

      if (this.desc_type)
      begin
         desc = new[4];
         desc[0] = post_buf.buf_size[31:0];
         desc[1] = post_buf.addr[31:0];
         desc[2] = post_buf.addr[47:32];
         desc[3] = 32'd0;
      end
      else
      begin
         desc = new[4];
         desc[0] = post_buf.buf_size[31:0];
         desc[1] = post_buf.addr[31:00];
         desc[2] = post_buf.addr[63:32];
         desc[3] = 32'd0;
      end

      for (int i=0; i<desc.size(); i++)
      begin
         this.c2h_desc_q.push_back(desc[i]);
      end

      //Push onto posted buffer queue so can assemble packet when recevie packet
      this.c2h_post_buf_q.push_back(post_buf);


   endfunction

   //----------------------------------------------------
   //H2C "doorbell", is write descriptors to SDE
   //----------------------------------------------------
   virtual task h2c_doorbell;

      int cur_wc_length;

      logic[31:0] cur_wdata_q[$];

      h2c_total_desc += this.h2c_desc_q.size()/(this.h2c_desc_size/4);
      if (this.verbose)
         $display($time,,,"sde_dma_t: H2C_DOORBELL: NumDesc=%0d, TotalDesc=0x%x", this.h2c_desc_q.size()/(this.h2c_desc_size/4), h2c_total_desc);
      //Make sure have some descriptors to poke
      while (this.h2c_desc_q.size()>0)
      begin

         //Clear out the write data
         cur_wdata_q = {};

         
	 //Supported DW lengths for H2C/C2H descriptors = 1DW, 4DW, 8DW
	 this.cfg_desc_wc_max = (this.cfg_desc_wc_max > 8) ? 8 : this.cfg_desc_wc_max;
	 this.cfg_desc_wc_min = (this.cfg_desc_wc_min > 8) ? 8 : this.cfg_desc_wc_min;
	 if ((this.cfg_desc_wc_min == this.cfg_desc_wc_max) && (this.cfg_desc_wc_min == 1 || this.cfg_desc_wc_min == 4 || this.cfg_desc_wc_min == 8))
	   cur_wc_length = this.cfg_desc_wc_min;
	 else
	   std::randomize(cur_wc_length) with {cur_wc_length inside {1, 4, 8};};

         //If amount of data is less than write combine length, use that amount for data length
         if (this.h2c_desc_q.size<cur_wc_length)
            cur_wc_length = this.h2c_desc_q.size;

         //Transfer data from h2c_desc_q to cur_wdata_q;
         for (int i=0; i<cur_wc_length; i++)
            cur_wdata_q.push_back(this.h2c_desc_q.pop_front());

         if (this.verbose)
            $display($time,,,"sde_dma_t:    H2C_DOORBELL: CurDW=%0d, DWLeft=%0d", cur_wdata_q.size(), h2c_desc_q.size());

         access.poke(.addr(H2C_DESC_BASE), .data(cur_wdata_q));
      end
      this.h2c_desc_q = {};
   endtask // h2c_doorbell

   //----------------------------------------------------
   //H2C "doorbell", induce Out of Order Error, Unaligned addr error
   //----------------------------------------------------
   virtual task h2c_doorbell_error(input out_of_order=0, input unalign_addr=0);

      int cur_wc_length;

      logic [31:0] cur_wdata_q[$];
      logic 	   induce_error = 0;
      logic [31:0] addr1, addr2;

      h2c_total_desc += this.h2c_desc_q.size()/(this.h2c_desc_size/4);
      if (this.verbose)
         $display($time,,,"sde_dma_t: H2C_DOORBELL: NumDesc=%0d, TotalDesc=0x%x", this.h2c_desc_q.size()/(this.h2c_desc_size/4), h2c_total_desc);
      //Make sure have some descriptors to poke
      while (this.h2c_desc_q.size()>0)
      begin

         //Clear out the write data
         cur_wdata_q = {};

         //Get a random write combine length -- note this works with no write combine as well (just takes a bit longer)
	 //Supported DW lengths for H2C/C2H descriptors = 1DW, 4DW, 8DW
	 this.cfg_desc_wc_max = (this.cfg_desc_wc_max > 8) ? 8 : this.cfg_desc_wc_max;
	 this.cfg_desc_wc_min = (this.cfg_desc_wc_min > 8) ? 8 : this.cfg_desc_wc_min;
	 if ((this.cfg_desc_wc_min == this.cfg_desc_wc_max) && (this.cfg_desc_wc_min == 1 || this.cfg_desc_wc_min == 4 || this.cfg_desc_wc_min == 8))
	   cur_wc_length = this.cfg_desc_wc_min;
	 else
	   std::randomize(cur_wc_length) with {cur_wc_length inside {1, 4, 8};};

         //If amount of data is less than write combine length, use that amount for data length
         if (this.h2c_desc_q.size<cur_wc_length)
            cur_wc_length = this.h2c_desc_q.size;

         //Transfer data from h2c_desc_q to cur_wdata_q;
         for (int i=0; i<cur_wc_length; i++)
            cur_wdata_q.push_back(this.h2c_desc_q.pop_front());

         if (this.verbose)
            $display($time,,,"sde_dma_t:    H2C_DOORBELL: CurDW=%0d, DWLeft=%0d", cur_wdata_q.size(), h2c_desc_q.size());

	 if (out_of_order) begin
	    if (induce_error == 0) begin //{
	       //addr1 = ($urandom_range(H2C_DESC_BASE + 'h80, H2C_DESC_BASE + 16'hFC0)) & 32'hFFFF_FFC0; //64B aligned address
	       addr1 = H2C_DESC_BASE + 'h80;
	       access.poke(.addr(addr1), .data(cur_wdata_q));
	       induce_error = 1;
	    end else begin //}{
	       //do
	       //	 addr2 = ($urandom_range(H2C_DESC_BASE, H2C_DESC_BASE + 16'hFC0)) & 32'hFFFF_FFC0; //64B aligned address
	       //while (addr2 < addr1);
	       addr2 = H2C_DESC_BASE + 'h40;
	       access.poke(.addr(addr2), .data(cur_wdata_q));
	    end //}
	 end else if (unalign_addr) begin
	    if (induce_error == 0) begin //{
	       access.poke(.addr(H2C_DESC_BASE), .data(cur_wdata_q));
	       induce_error = 1;
	    end else begin //}{
	       //access.poke(.addr(H2C_DESC_BASE + $urandom_range(5,63)), .data(cur_wdata_q));
	       access.poke(.addr(H2C_DESC_BASE + 'h20), .data(cur_wdata_q));
	    end //}
	 end else begin
	    access.poke(.addr(H2C_DESC_BASE), .data(cur_wdata_q));
	 end
      end
      this.h2c_desc_q = {};
   endtask


   //----------------------------------------------------
   //C2H "doorbell", is write descriptors to SDE
   //----------------------------------------------------
   virtual task c2h_doorbell;
      int cur_wc_length;

      logic[31:0] cur_wdata_q[$];

      c2h_total_desc += this.c2h_desc_q.size()/(this.c2h_desc_size/4);
      if (this.verbose)
         $display($time,,,"sde_dma_t: C2H_DOORBELL: NumDesc=%0d, TotalDesc=0x%x", this.c2h_desc_q.size()/(this.c2h_desc_size/4), c2h_total_desc);
      //Make sure have some descriptors to poke
      while (this.c2h_desc_q.size()>0)
      begin
         //Clear out the write data
         cur_wdata_q = {};

         //Get a random write combine length -- note this works with no write combine as well (just takes a bit longer)
         //CHAKRA: cur_wc_length = $urandom_range(this.cfg_desc_wc_max, this.cfg_desc_wc_min);
	 //Supported DW lengths for H2C/C2H descriptors = 1DW, 4DW, 8DW
	 this.cfg_desc_wc_max = (this.cfg_desc_wc_max > 8) ? 8 : this.cfg_desc_wc_max;
	 this.cfg_desc_wc_min = (this.cfg_desc_wc_min > 8) ? 8 : this.cfg_desc_wc_min;
	 if ((this.cfg_desc_wc_min == this.cfg_desc_wc_max) && (this.cfg_desc_wc_min == 1 || this.cfg_desc_wc_min == 4 || this.cfg_desc_wc_min == 8))
	   cur_wc_length = this.cfg_desc_wc_min;
	 else
	   std::randomize(cur_wc_length) with {cur_wc_length inside {1, 4, 8};};

         //If amount of data is less than write combine length, use that amount for data length
         if (this.c2h_desc_q.size<cur_wc_length)
            cur_wc_length = this.c2h_desc_q.size;

         //Transfer data from c2h_desc_q to cur_wdata_q;
         for (int i=0; i<cur_wc_length; i++)
            cur_wdata_q.push_back(this.c2h_desc_q.pop_front());

         if (this.verbose)
            $display($time,,,"sde_dma_t:    C2H_DOORBELL: CurDW=%0d, DWLeft=%0d", cur_wdata_q.size(), c2h_desc_q.size());
         access.poke(.addr(C2H_DESC_BASE), .data(cur_wdata_q));
      end
      this.c2h_desc_q = {};
   endtask // c2h_doorbell

   //----------------------------------------------------------------
   //C2H "doorbell", induce Out of Order Error, Unaligned addr error
   //----------------------------------------------------------------
   virtual task c2h_doorbell_error (input out_of_order=0, input unalign_addr=0);
      int cur_wc_length;

      logic [31:0] cur_wdata_q[$];
      logic 	   induce_error = 0;

      c2h_total_desc += this.c2h_desc_q.size()/(this.c2h_desc_size/4);
      if (this.verbose)
         $display($time,,,"sde_dma_t: C2H_DOORBELL Out Of Order: NumDesc=%0d, TotalDesc=0x%x", this.c2h_desc_q.size()/(this.c2h_desc_size/4), c2h_total_desc);
      //Make sure have some descriptors to poke
      while (this.c2h_desc_q.size()>0)
      begin
         //Clear out the write data
         cur_wdata_q = {};

         //Get a random write combine length -- note this works with no write combine as well (just takes a bit longer)
	 //Supported DW lengths for H2C/C2H descriptors = 1DW, 4DW, 8DW
	 this.cfg_desc_wc_max = (this.cfg_desc_wc_max > 8) ? 8 : this.cfg_desc_wc_max;
	 this.cfg_desc_wc_min = (this.cfg_desc_wc_min > 8) ? 8 : this.cfg_desc_wc_min;
	 if ((this.cfg_desc_wc_min == this.cfg_desc_wc_max) && (this.cfg_desc_wc_min == 1 || this.cfg_desc_wc_min == 4 || this.cfg_desc_wc_min == 8))
	   cur_wc_length = this.cfg_desc_wc_min;
	 else
	   std::randomize(cur_wc_length) with {cur_wc_length inside {1, 4, 8};};

         //If amount of data is less than write combine length, use that amount for data length
         if (this.c2h_desc_q.size<cur_wc_length)
            cur_wc_length = this.c2h_desc_q.size;

         //Transfer data from c2h_desc_q to cur_wdata_q;
         for (int i=0; i<cur_wc_length; i++)
            cur_wdata_q.push_back(this.c2h_desc_q.pop_front());

         if (this.verbose)
            $display($time,,,"sde_dma_t:    C2H_DOORBELL: CurDW=%0d, DWLeft=%0d", cur_wdata_q.size(), c2h_desc_q.size());

	 if (out_of_order) begin
	    if (induce_error == 0) begin //{
	       access.poke(.addr(C2H_DESC_BASE + 'h80), .data(cur_wdata_q));
	       induce_error = 1;
	    end else begin //}{
	       access.poke(.addr(C2H_DESC_BASE + 'h40), .data(cur_wdata_q));
	    end //}
	 end else if (unalign_addr) begin
	    if (induce_error == 0) begin //{
	       access.poke(.addr(C2H_DESC_BASE), .data(cur_wdata_q));
	       induce_error = 1;
	    end else begin //}{
	       access.poke(.addr(C2H_DESC_BASE + 'h20), .data(cur_wdata_q));
	    end //}
	 end else begin
	    access.poke(.addr(C2H_DESC_BASE), .data(cur_wdata_q));
	 end
      end
      this.c2h_desc_q = {};
   endtask


   //-----------------------------------------------------------------------------
   // C2H Writeback descriptor processing
   //
   // - Wait for WB descriptors to be valid
   // - Get the corresponding packet data and assemble into a packet buffer
   // - Clear WB desciptor so can be re-used by H/W
   // - On EOP push onto RX Pkt Q that can be used by scoreboard
   //-----------------------------------------------------------------------------
   virtual task process_c2h_wb_thread();

      gen_buf_t cur_asm_pkt;           //Current packet we are assembling
      dma_buf_t cur_post_buf;          //Current posted buffer

      wb_desc_t cur_wb_desc;           //Current wb descriptor

      bit pkt_inp;                     //Currently assembling a packet

      int num_desc;
      string desc_info_q[$];             //Descriptors

      logic [63:0] addr;
      logic [31:0] wr_data;
      logic [31:0] rd_data;
      logic        error;

      int          rd_ptr_pend_cnt = 0;

      int accum_length;

      int          num_wb_to_read = 0;
      logic [31:0] curr_md_wr_ptr;

      pkt_inp = 0;
      forever
        begin

           #(this.wb_poll_interval * 1ns);

           num_wb_to_read = 0;

           while (num_wb_to_read == 0) begin
              curr_md_wr_ptr = access.read_host_dw(cfg_c2h_wb_wr_ptr_addr);

              num_wb_to_read = curr_md_wr_ptr >= c2h_wb_desc_rd_ptr ? (curr_md_wr_ptr - c2h_wb_desc_rd_ptr) :
                               (cfg_c2h_num_md + curr_md_wr_ptr - c2h_wb_desc_rd_ptr);

              #1ns;
           end

           // $display($time,,,"dma_buf_t.process_c2h_wb_thread curr_md_wr_ptr = %0d, c2h_wb_desc_rd_ptr = %0d, num_wb_to_read = %0d", curr_md_wr_ptr, c2h_wb_desc_rd_ptr, num_wb_to_read);

           //Get the next descriptor fields
           //$display($time,,,"Getting next descriptor. c2h_wb_desc_rd_ptr=0x%0x", c2h_wb_desc_rd_ptr);

           repeat (num_wb_to_read) begin

              cur_wb_desc = get_nxt_wb_desc(.wb_buf(c2h_wb_buf), .wb_ptr(c2h_wb_desc_rd_ptr));

         //$display($time,,,"POLL: valid=0x%x; dw=0x%x", desc_valid, cur_wb_desc[0]);

              //         while(cur_wb_desc.valid)
              //         begin

              assert(cur_wb_desc.valid == 1'b1) else begin
                 $display($time,,,"***ERROR*** dma_buf_t.process_c2h_wb_thread Pkt[%0d] cur_wb_desc.valid=0", num_c2h_pkts);
                 $finish;
              end


              //If packet is not in progress, create a new buffer to assemble packet
              if (!pkt_inp)
                begin
                   cur_asm_pkt = new();
                   pkt_inp = 1;
                   accum_length = 0;
                end

              //Get the next RX buffer that was posted so can extract the packet data
              cur_post_buf = c2h_post_buf_q.pop_front();

              //Populate the buffer from Host Memory
              cur_post_buf.read_host_buf(.length(cur_wb_desc.length));

              //Make sure the WB length is <= buffer length
              if (cur_wb_desc.length>cur_post_buf.buf_size) begin
                 $display($time,,,"***ERROR*** dma_buf_t.process_c2h_wb_thread Pkt[%0d] cur_wb_desc.length=0x%0x is greater than posted length cur_post_buf.buf_size=0x%0x", num_c2h_pkts, cur_wb_desc.length, cur_post_buf.buf_size);
                 $finish;
              end

              //Copy the post buffer data to the assembled packet data
              for (int i=0; i<cur_wb_desc.length; i++)
                cur_asm_pkt.data.push_back(cur_post_buf.data[i]);

              //Update the Descriptor info string for display
             // desc_info_q.push_back(sprintf("DESC: addr=0x%x, buf_length=0x%0x, wb_length=0x%0x, accum_length=0x%0x", cur_post_buf.addr, cur_post_buf.buf_size, cur_wb_desc.length, accum_length));
              accum_length += cur_wb_desc.length;

              //If EOP, then add the packet to the RX_Q
              if (cur_wb_desc.eop)
                begin
                   if (this.verbose)
                     begin
                        $display($time,,,"dma_buf_t.process_c2h_wb_thread Host RX_PKT [%0d] length=0x%0x, start_data=0x%x", num_c2h_pkts, cur_asm_pkt.data.size(), {cur_asm_pkt.data[3], cur_asm_pkt.data[2], cur_asm_pkt.data[1], cur_asm_pkt.data[0]});
                        //foreach (desc_info_q[i])
                        //  $display($time,,,"         %s", desc_info_q[i]);
                     end
                   c2h_pkt_rx_q.push_back(cur_asm_pkt);
                   c2h_pkt_rq_user_q.push_back(cur_wb_desc.user_bits);
                   pkt_inp = 0;
                   desc_info_q = {};
                   num_c2h_pkts++;
                end

              //Clear out the WB desc in memory (clear the valid bit)
              clr_wb_desc(.wb_buf(c2h_wb_buf), .wb_ptr(c2h_wb_desc_rd_ptr));

              //Update Read Pointer
              c2h_wb_desc_rd_ptr = (c2h_wb_desc_rd_ptr == (cfg_c2h_num_md-1))? 0: c2h_wb_desc_rd_ptr + 1;
              rd_ptr_pend_cnt++;

              if (rd_ptr_pend_cnt >= c2h_wb_rdptr_coalesce_cnt) begin
                 //            if (rd_ptr_pend_cnt >= (cfg_c2h_num_md-1)) begin
                 //Update Read Pointer in HW
                 addr = c2h_csr_base_addr + 16'h324;
                 wr_data = c2h_wb_desc_rd_ptr;
                 access.poke_dw (.addr(addr), .data(wr_data));
                 // There is a delay for writes to reach the HW// access.peek_verify (.addr(addr), .data(rd_data), .exp_data(wr_data), .error(error), .exit_on_error(1));
                 rd_ptr_pend_cnt = 0;
                 c2h_wb_rdptr_coalesce_cnt = $urandom_range((cfg_c2h_num_md-1), 1);

              end

              //Read the next Descriptor
              //cur_wb_desc = get_nxt_wb_desc(.wb_buf(c2h_wb_buf), .wb_ptr(c2h_wb_desc_rd_ptr));
              //end

           end // repeat (num_wb_to_read)

        end // forever begin


   endtask



//Get the next WB descriptor
function wb_desc_t get_nxt_wb_desc (dma_buf_t wb_buf, input int wb_ptr);
   wb_desc_t wb_desc;
   logic [29:0] dummy;

   wb_desc = new();
   // $display("Calling read_host_buf with length = %0d", c2h_wb_desc_size);

   wb_buf.read_host_buf(.start_offset(wb_ptr * c2h_wb_desc_size), .length(c2h_wb_desc_size));
   {wb_desc.length[31:0]} =  {  wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 3],
                                wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 2],
                                wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 1],
                                wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 0] };

   {dummy[29:0], wb_desc.eop, wb_desc.valid} =  { wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 7],
                                                              wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 6],
                                                              wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 5],
                                                              wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 4] };

   if (this.desc_type == 0)
   begin

      {wb_desc.user_bits[32:0]} =                        { wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 11],
                                                           wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 10],
                                                           wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 9],
                                                           wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 8] };

      {wb_desc.user_bits[63:32]} =                        { wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 15],
                                                            wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 14],
                                                            wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 13],
                                                            wb_buf.data[(wb_ptr * c2h_wb_desc_size) + 12] };
   end // if (this.desc_type == 0)
   else begin
      wb_desc.user_bits[63:0] = 64'd0;
   end

   get_nxt_wb_desc = wb_desc;

endfunction


//Clear the WB descriptor
function clr_wb_desc(dma_buf_t wb_buf, input int wb_ptr);

   //Clear the WB descriptor
   for (int i=0; i<c2h_wb_desc_size; i++)
   begin
      wb_buf.data[wb_ptr * c2h_wb_desc_size + i] = 0;
   end

   //Update host memory
   wb_buf.write_buf_host(.start_offset(wb_ptr * c2h_wb_desc_size), .length(c2h_wb_desc_size));

endfunction

//---------------------------------------------------------------------
//Task to continually post C2H descriptors
// - Will keep posting descriptors until reach max_num_desc limit (max number of outstanding descriptors)
// - Randomize the length and offset
// - Randomly ring doorbell (currently fixed at 50% chance, FIXME -- Make this parameterizable)
// - If reached the max number of descriptors outstanding always ring doorbell (otherwise will deadlock)
//---------------------------------------------------------------------
task post_c2h_desc_thread(input int max_num_desc=64);

   bit[31:0] c2h_cdt_cons = 0;            //C2H descriptor credit consumed
   bit[31:0] c2h_cdt_limit = 64;          //C2H descriptor credit consumed

   bit[31:0] c2h_cdt_limit_old;
   bit[31:0] pkt_count;
   bit[31:0] desc_count;
   bit[31:0] wb_wr_ptr;


   bit[31:0] credit_diff;

   int tmp_length;
   int tmp_offset;
   dma_buf_t tmp_buf;

   bit[31:0] tmp_rnd;
   bit [31:0] c2h_wb_desc_wr_ptr_next;

   forever
   begin
      credit_diff = c2h_cdt_limit - c2h_cdt_cons;

      c2h_wb_desc_wr_ptr_next = c2h_wb_desc_wr_ptr == (cfg_c2h_num_md-1) ? 0 : (c2h_wb_desc_wr_ptr + 1);

      while ((c2h_cdt_limit==c2h_cdt_cons || ((32'h64 - credit_diff) >= max_num_desc)) ||
             (c2h_wb_desc_wr_ptr_next == c2h_wb_desc_rd_ptr))
      begin
         #(this.wb_poll_interval * 1ns);
         c2h_cdt_limit_old = c2h_cdt_limit;
         c2h_cdt_limit = access.read_host_dw(cfg_c2h_cdt_limit_addr);
         credit_diff = c2h_cdt_limit - c2h_cdt_cons;
         if (c2h_cdt_limit_old != c2h_cdt_limit)
         begin
            pkt_count = access.read_host_dw(cfg_c2h_wb_pkt_cnt_addr);
            desc_count = access.read_host_dw(cfg_c2h_wb_desc_cnt_addr);
            wb_wr_ptr = access.read_host_dw(cfg_c2h_wb_status_addr);
            if (this.verbose)
               $display($time,,,"Poll C2H Status: desc_cons=0x%0x, desc_limit=0x%0x, pkt_count=0x%0x, desc_count=0x%0x, wb_wr_ptr=0x%0x", c2h_cdt_cons, c2h_cdt_limit, pkt_count, desc_count, wb_wr_ptr);
         end
      end

      //Randomize length/offset
      tmp_length = $urandom_range(pc2h_max_length, pc2h_min_length);
      tmp_offset = $urandom_range(pc2h_max_offset, pc2h_min_offset);

      //Adjust length if offset + length > page_size
      if ((tmp_offset + tmp_length) > page_size)
         tmp_length = page_size - tmp_offset;

      //Allocate the buffer
      tmp_buf = new(.access(this.access), .addr(this.alloc_page(.s("POST_C2H_DESC_THREAD")) + tmp_offset), .buf_size(tmp_length), .verbose(this.verbose));

      //Post the Buffer
      this.post_c2h_desc(.post_buf(tmp_buf));

      //Increment the consumed
      c2h_cdt_cons++;
      credit_diff = c2h_cdt_limit - c2h_cdt_cons;

      //50/50 chance of ringing the doorbell
      tmp_rnd = $urandom;

      //Always ring doorbell if posted max_num_desc
      if (tmp_rnd[0] || ((32'h64 - credit_diff) >= max_num_desc))
         this.c2h_doorbell();
   end

endtask

endclass




