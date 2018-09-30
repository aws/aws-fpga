// Amazon FPGA Hardware Development Kit
//
// Copyright 2016-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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



package sde_pkg;

// Descriptor Definitions

///////////////////////////////////////////////////////////////
// C2H Descriptors
///////////////////////////////////////////////////////////////

//------------------------|-----------------------------------|-----------------------------------|
//                        |            REGULAR TYPE           |            COMPACT TYPE           |
//      Field             |-----------|-----------|-----------|-----------|-----------|-----------|
//                        | Bit-Width |  High Bit |  Low Bit  | Bit-Width |  High Bit |  Low Bit  |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Length (Bytes)         |    32     |     31    |     00    |    32     |     31    |     00    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Physical Address       |    64     |     95    |     32    |    48     |     79    |     32    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// RSVD Bits              |    32     |    127    |     96    |    48     |    127    |     80    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Total Bits             |   128     |           |           |   128     |           |           |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|

   // C2H Reg Mode Descriptor Definition (Including RSVD bits)
   typedef struct packed {
      logic [31:0] rsvd;
      logic [63:0] dest_addr;
      logic [31:0] len;
   } c2h_reg_desc_t;

   // C2H Compact Mode Descriptor 
   typedef struct packed {
      logic [47:0] rsvd;
      logic [47:0] dest_addr;
      logic [31:0] len;
   } c2h_comp_desc_t;

   // C2H Compact Mode Descriptor Definition - Used in Descriptor Engine
   typedef struct packed {
      logic [47:0] dest_addr;
      logic [31:0] len;
   } c2h_comp_sav_desc_t;

   // C2H Intermediate Format Descriptor Definition - Used in Data Mover
   typedef struct packed {
      logic [63:0] dest_addr;
      logic [31:0] len;
      logic        desc_type;
   } c2h_if_desc_t;
   
   // C2H Intermediate Format Descriptor Definition - Used in Descritor Engine
   typedef struct packed {
      logic [63:0] dest_addr;
      logic [31:0] len;
   } c2h_reg_sav_desc_t;

   // C2H and H2C Common Format - Used on signals
   typedef struct packed {
      logic [63:0] user;
      logic        spb;
      logic        eop;
      logic [31:0] len;
      logic [63:0] src_addr;
      logic [63:0] dest_addr;
      logic        desc_type;
      logic        h2c;
   } comm_desc_t;

   function comm_desc_t c2h_cnv_desc_reg2comm(c2h_reg_desc_t in_desc);
      comm_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.h2c = 0;
      out_desc.desc_type = 0;
      out_desc.dest_addr = in_desc.dest_addr;
      out_desc.len = in_desc.len;

      c2h_cnv_desc_reg2comm = out_desc;
   endfunction // c2h_cnv_desc_reg2comm

   function comm_desc_t c2h_cnv_desc_comp2comm(c2h_comp_desc_t in_desc);
      comm_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.h2c = 0;
      out_desc.desc_type = 1;
      
      out_desc.dest_addr = in_desc.dest_addr;
      out_desc.len = in_desc.len;

      c2h_cnv_desc_comp2comm = out_desc;
   endfunction // c2h_cnv_desc_reg2comm

//    function c2h_reg_desc_t c2h_cnv_desc_comm2reg(comm_desc_t in_desc);
//       c2h_reg_desc_t out_desc;
//       out_desc = '{default:'0};
// 
//       out_desc.desc_type = in_desc.desc_type;
//       out_desc.dest_addr = in_desc.dest_addr;
//       out_desc.wb_addr = in_desc.wb_addr;
//       out_desc.len = in_desc.len;
// 
//       c2h_cnv_desc_comm2reg = out_desc;
//    endfunction // c2h_cnv_desc_comm2reg
//    
//    function c2h_comp_desc_t c2h_cnv_desc_comm2comp(comm_desc_t in_desc);
//       c2h_comp_desc_t out_desc;
//       out_desc = '{default:'0};
// 
//       out_desc.desc_type = in_desc.desc_type;
//       out_desc.dest_addr = in_desc.dest_addr;
//       out_desc.wb_addr = in_desc.wb_addr;
//       out_desc.len = in_desc.len;
// 
//       c2h_cnv_desc_comm2comp = out_desc;
//    endfunction // c2h_cnv_desc_comm2comp
   
   function c2h_if_desc_t c2h_cnv_desc_comm2if(comm_desc_t in_desc);
      c2h_if_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.desc_type = in_desc.desc_type;
      out_desc.dest_addr = in_desc.dest_addr;
      out_desc.len = in_desc.len;

      c2h_cnv_desc_comm2if = out_desc;
   endfunction // c2h_cnv_desc_reg2comm
   
   
///////////////////////////////////////////////////////////////
// H2C Descriptors
///////////////////////////////////////////////////////////////

//------------------------|-----------------------------------|-----------------------------------|
//                        |            REGULAR TYPE           |            COMPACT TYPE           |
//      Field             |-----------|-----------|-----------|-----------|-----------|-----------|
//                        | Bit-Width |  High Bit |  Low Bit  | Bit-Width |  High Bit |  Low Bit  |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Length (Bytes)         |    32     |     31    |     00    |    32     |     31    |    00     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Physical Address       |    64     |     95    |     32    |    48     |     79    |    32     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// EOP                    |     1     |     96    |     96    |     1     |     80    |    80     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Src (0-Host/1-PktBuf)  |     1     |     97    |     97    |     1     |     81    |    81     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// RSVD Bits              |    94     |    191    |     98    |    NA     |     NA    |    NA     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// User Bits              |    64     |    255    |    192    |    46     |    127    |    82     |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Total Bits             |   256     |           |           |   128     |           |           |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|

   // H2C Reg Mode Descriptor Definition (Including RSVD bits)
   typedef struct packed {
      logic [63:0] user;
      logic [93:0] rsvd;
      logic        spb;
      logic        eop;
      logic [63:0] src_addr;
      logic [31:0] len;
   } h2c_reg_desc_t;

   // H2C Compact Mode Descriptor 
   typedef struct packed {
      logic [45:0] rsvd;
      logic        spb;
      logic        eop;
      logic [47:0] src_addr;
      logic [31:0] len;
   } h2c_comp_desc_t;

   // H2C Intermediate Format Descriptor Definition - Used in Data Mover
   typedef struct packed {
      logic [63:0] user;
      logic        spb;
      logic        eop;
      logic [63:0] src_addr;
      logic [31:0] len;
      logic       desc_type;
   } h2c_if_desc_t;

   // H2C Intermediate Format Descriptor Definition - Used in Descriptor Engine
   typedef struct packed {
      logic [63:0] user;
      logic        spb;
      logic        eop;
      logic [63:0] src_addr;
      logic [31:0] len;
   } h2c_reg_sav_desc_t;

   // H2C Compact Mode Descriptor 
   typedef struct packed {
      logic        spb;
      logic        eop;
      logic [47:0] src_addr;
      logic [31:0] len;
   } h2c_comp_sav_desc_t;

   function comm_desc_t h2c_cnv_desc_reg2comm(h2c_reg_desc_t in_desc);
      comm_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.h2c = 1;
      out_desc.desc_type = 0;
      out_desc.src_addr = in_desc.src_addr;
      out_desc.len = in_desc.len;
      out_desc.eop = in_desc.eop;
      out_desc.spb = in_desc.spb;
      out_desc.user = in_desc.user;

      h2c_cnv_desc_reg2comm = out_desc;
   endfunction // h2c_cnv_desc_reg2comm

   function comm_desc_t h2c_cnv_desc_comp2comm(h2c_comp_desc_t in_desc);
      comm_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.h2c = 1;
      out_desc.desc_type = 1;
      
      out_desc.src_addr = in_desc.src_addr;
      out_desc.len = in_desc.len;
      out_desc.eop = in_desc.eop;
      out_desc.spb = in_desc.spb;

      h2c_cnv_desc_comp2comm = out_desc;
   endfunction // h2c_cnv_desc_reg2comm

   function h2c_if_desc_t h2c_cnv_desc_comm2if(comm_desc_t in_desc);
      h2c_if_desc_t out_desc;
      out_desc = '{default:'0};

      out_desc.desc_type = in_desc.desc_type;
      out_desc.src_addr = in_desc.src_addr;
      out_desc.len = in_desc.len;
      out_desc.eop = in_desc.eop;
      out_desc.spb = in_desc.spb;
      out_desc.user = in_desc.user;

      h2c_cnv_desc_comm2if = out_desc;
   endfunction // h2c_cnv_desc_reg2comm

///////////////////////////////////////////////////////////////
// C2H Write-Back Metadata
///////////////////////////////////////////////////////////////

//------------------------|-----------------------------------|-----------------------------------|
//                        |            REGULAR TYPE           |            COMPACT TYPE           |
//      Field             |-----------|-----------|-----------|-----------|-----------|-----------|
//                        | Bit-Width |  High Bit |  Low Bit  | Bit-Width |  High Bit |  Low Bit  |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Length (Bytes)         |    32     |     31    |     00    |    32     |     31    |     00    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Valid                  |     1     |     32    |     32    |     1     |     32    |     32    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// EOP                    |     1     |     33    |     33    |     1     |     33    |     33    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// RSVD Bits              |    30     |     63    |     34    |    30     |     63    |     34    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// User Bits              |    64     |    127    |     80    |    NA     |     NA    |     NA    |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
// Total Bits             |   128     |           |           |    64     |           |           |
//------------------------|-----------|-----------|-----------|-----------|-----------|-----------|
   
   // C2H Reg Mode Write-Back Metadata Definition (Including RSVD bits)
   typedef struct packed {
      logic [63:0] user;
      logic [29:0] rsvd;
      logic        eop;
      logic        valid;
      logic [31:0] len;
   } c2h_reg_wb_t;

   // C2H Compact Mode Descriptor 
   typedef struct packed {
      logic [29:0] rsvd;
      logic        eop;
      logic        valid;
      logic [31:0] len;
   } c2h_comp_wb_t;

   function c2h_comp_wb_t c2h_conv_wb_reg2comp (c2h_reg_wb_t in_desc);
      c2h_comp_wb_t out_desc;
      out_desc = '{default:'0};

      out_desc.valid = in_desc.valid;
      out_desc.eop = in_desc.eop;
      out_desc.len = in_desc.len;

      c2h_conv_wb_reg2comp = out_desc;
   endfunction // c2h_conv_wb_reg2comp

   //-----------------------------------------------------------------------------------------
   // This function performs round robin arbitration
   //-----------------------------------------------------------------------------------------
   virtual class RR_ARB #(parameter WINNER_WIDTH=2,
                          parameter REQ_WIDTH = 32'h1 << WINNER_WIDTH
                          );
      
      static function logic [WINNER_WIDTH-1:0] do_arb (logic [REQ_WIDTH-1:0] req, 
                                                       logic [WINNER_WIDTH-1:0] curr_winner);

         logic [WINNER_WIDTH-1:0]  start_idx;
         logic [(2*REQ_WIDTH)-1:0] req_req;
         logic [REQ_WIDTH-1:0]     req_shifted;
         logic [WINNER_WIDTH:0]    tmp_winner;
         logic [WINNER_WIDTH-1:0]  winner;

         start_idx = (curr_winner >= (REQ_WIDTH-1)) ? 0 : curr_winner + 1;
         
         req_req = {2{req}};
         req_shifted = req_req >> start_idx;

         tmp_winner = 0;
         for (int i = REQ_WIDTH-1; i > 0; i--) begin
            if (req_shifted[i]) begin
               tmp_winner = start_idx + i;

               if (tmp_winner >= REQ_WIDTH)
                 tmp_winner = tmp_winner - REQ_WIDTH;

            end
         end

         winner = tmp_winner[WINNER_WIDTH-1:0];

         do_arb = winner;
      endfunction // do_arb

   endclass // RR_ARB
   
   
endpackage // sde_pkg
   
   
