`ifndef DMA_DEFINES_SVH
`define DMA_DEFINES_SVH

`include "dma_defines.vh"
`include "pcie_dma_attr_defines.svh"

// Interface Includes at bottom of file (use some structures defined in this file)

`define IF_MI_CONVERSION_M \
    always_comb begin \
        ifc.wadr = wadr;\
        ifc.wen  = wen;\
        ifc.wpar = wpar;\
        ifc.wdat = wdat;\
        ifc.ren  = ren;\
        ifc.radr = radr;\
       rpar = ifc.rpar;\
       rdat = ifc.rdat;\
       rsbe = ifc.rsbe;\
       rdbe = ifc.rdbe;\
    end

`define IF_MI_CONVERSION_S \
    always_comb begin \
        wadr = ifc.wadr;\
        wen  = ifc.wen;\
        wpar = ifc.wpar;\
        wdat = ifc.wdat;\
        ren  = ifc.ren;\
        radr = ifc.radr;\
        ifc.rpar = rpar;\
        ifc.rdat = rdat;\
        ifc.rsbe = rsbe;\
        ifc.rdbe = rdbe;\
    end

typedef struct packed {
   logic                  spl;
    logic [`ADR_WIDTH-1:0] adr;
    logic [`RID_WIDTH-1:0] rid;
    logic [`LEN_WIDTH-1:0] byte_len;   // byte length
    logic [`DID_WIDTH-1:0] did;
        logic [7:0]            fnc;        // function
} rrq_t;

// Descriptor Sideband Info (Context RAM to DSC_CPLI_RAM)
typedef struct packed {
    logic                       wbi;     // Do writeback/interrupt on descriptor completion
    logic                       wbi_chk; // Check status before writeback/interrupt
    logic   [`QID_WIDTH-1:0]    qid;     // Q ID 
    logic   [3:0]               qst;
    logic   [7:0]               fnc;
    logic   [15:0]              cidx;
} dsc_sbi_t;  // 10 + 4 + 8 + 16 = 54

typedef struct packed {
    logic            sop;
    logic            eop;
    logic            wbk;
    logic [4:0]      err;
    logic [3:0]      errc;
    //logic [`DAT_WIDTH/32-1:0] wen; // dword write enable
    logic [`RID_WIDTH-1:0]    rid;
    logic [`DID_WIDTH-1:0]    did;
    logic [5:0]               lba;    // Last beat length adjustment (AXI ST C2H)
    logic [`DAT_WIDTH/8-1:0]  par;
    logic [`DAT_WIDTH-1:0]    dat;
} rcp_t;

typedef struct packed {
   logic                   err;
    logic [`ADR_WIDTH-1:0] adr;
    logic [`RID_WIDTH-1:0] rid;
    logic [`LEN_WIDTH-1:0] byte_len;   // byte length
    logic [5:0]            aln;        // Source alignment
    logic                  eop;
    logic                  eod;
    logic                  eor;
} wrq_t;

typedef struct packed {
    logic    [`DAT_WIDTH/8-1:0]   par;
    logic    [`DAT_WIDTH-1:0]     dat;
} wpl_t;

typedef struct packed {
    logic    [`RID_WIDTH-1:0]  rid;
    logic    [4:0]             err;
} wcp_t;

typedef struct packed {
    logic [31:0]    dat;
} wbrq_t;

typedef struct packed {
    logic [3:0]      be;    
    logic            rd;
    logic            wr;
    logic [31:0]     dat;
    logic [31:0]     adr;
    logic [7:0]      func;
} trq_t;

typedef struct packed {
    logic            vld;
    logic [31:0]         dat;
} tcp_t;

typedef struct packed {
    logic                     run;
    logic                     c2h_wbk_ena;
    logic                     noninc;
    logic [`ADR_WIDTH-1:0]    cdc_wbk_adr;
} creg_t;

typedef struct packed {
    logic    [63:0]        par;         // 136:73 Parity filled later
    logic    [5:0]         seq1;        // 72:67  Sequence Num 1
    logic    [5:0]         seq0;        // 66:61  Sequence Num 0
    logic    [23:0]        tph;         // 60:45  TPH St Tag
                                        // 44:43  TPH Ind Tag
                                        // 42:39  TPH Type
                                        // 38:37  TPH Present
    logic                  disc;        // 36     Discontinue
    logic    [3:0]         eop1_ptr;    // 35:32  EOP 1 Ptr
    logic    [3:0]         eop0_ptr;    // 31:28  EOP 0 Ptr
    logic                  eop1;        // 27     EOP 1
    logic                  eop0;        // 26     EOP 0
    logic    [1:0]         sop1_ptr;    // 25:24  SOP 1 Ptr
    logic    [1:0]         sop0_ptr;    // 23:22  SOP 0 Ptr
    logic                  sop1;        // 21     SOP 1
    logic                  sop0;        // 20     SOP 0
    logic    [3:0]         adr;         // 19:16  Address offset - Address aligned mode only
    logic    [3:0]         lbe1;
    logic    [3:0]         lbe0;
    logic    [3:0]         fbe1;
    logic    [3:0]         fbe0;
} rq_usr_straddle_t;

typedef struct packed {
    logic    [76:0]        rsv;
    logic    [31:0]        par;         // 59:28
    logic    [3:0]        seq;        // 27:24
    logic    [11:0]        tph;        // 23:12
    logic            dis;        // 11
    logic    [2:0]        adr;         // 10:8
    logic    [3:0]         lbe;        // 7:4
    logic    [3:0]         fbe;        // 3:0
} rq_usr_nostraddle_t;

typedef union packed {
    rq_usr_straddle_t       rqu_str;
    rq_usr_nostraddle_t      rqu_nstr;
} rq_usr_t;

typedef struct packed {
    logic   [12:0]  pcie_mrrs;
    logic   [12:0]  pcie_mps;
    logic   [12:0]  axi_mrrs;
    logic   [12:0]  axi_mps;
} cfg_dma_t;

typedef struct packed { 
    logic            ecrc;
    logic     [2:0]        attr;        
    logic    [2:0]        tc;    
    logic            rid_en;
    logic    [15:0]        cpl_id;
    logic    [7:0]        tag;
    logic    [15:0]        req_id;
    logic            poison;
    logic    [3:0]        req;
    logic    [10:0]        len;        
    logic    [63:0]        adr;
} rq_hdr_fields_t;

typedef struct packed { 
    logic    [23:0]        dw3_misc;
    logic    [7:0]        tag;
    logic    [16:0]        dw2_misc;
    logic    [3:0]        req;
    logic    [10:0]        len;        
    logic    [63:0]        adr;
} rq_hdr_compact_t;

typedef struct packed { 
    logic    [31:0]        dw3;
    logic    [31:0]        dw2;
    logic    [31:0]        dw1;
    logic    [31:0]        dw0;
} rq_hdr_dwords_t;

typedef union packed {
    rq_hdr_fields_t        rqh_f;
    rq_hdr_compact_t      rqh_c;
    rq_hdr_dwords_t      rqh_d;
} rq_hdr_t;

typedef struct packed { 
    logic                    tlast;
    logic    [`MULTQ_C2H_TUSER_WIDTH-1:0]    tuser;
    logic    [`DAT_WIDTH/8-1:0]        tkeep;
    logic    [`DAT_WIDTH/8-1:0]        tparity;
    logic    [`DAT_WIDTH-1:0]        tdata;
} dma_s_axis_t;

typedef struct packed {
    logic [`DID_WIDTH-1:0]            waddr;
    logic [`DID_WIDTH-1:0]            raddr;
    logic [`DAT_WIDTH/8-1:0]        wen;
} dat_bram_cmd_t;

typedef struct packed {
    logic [`DAT_WIDTH-1:0]            dat;
    logic [`DAT_WIDTH/8-1:0]        parity; // Even parity
}dat_bram_dat_t;


typedef struct packed {
    
    logic                    tlast;
    logic    [`MULTQ_H2C_TUSER_WIDTH-1:0]    tuser;
    logic    [`DAT_WIDTH/8-1:0]        tkeep;
    logic    [`DAT_WIDTH/8-1:0]        tparity;
    logic    [`DAT_WIDTH-1:0]        tdata;
} dma_m_axis_t;


// Descriptor Completion Memory Interface
typedef struct packed {
    logic    [`DAT_WIDTH-1:0]        rdat;
    logic                    rbe;
}dsc_cpl_bram_out_t;

typedef struct packed {
    logic                wen;
    logic    [`DSC_DID_WIDTH-1:0]    waddr;
    logic    [`DAT_WIDTH-1:0]        wdat;
    logic    [`DSC_RID_WIDTH-1:0]    raddr;
}dsc_cpl_bram_in_t;

// XDMA Descriptor Memory Interface
//typedef struct packed {    
    //logic    [255:0]     rdat;
    //logic                rbe;
//}dsc_bram_out_t;      

typedef struct packed {
    logic                wen;
    logic    [`DSC_DID_WIDTH-1:0]    waddr;
    logic    [255:0]            wdat;
    logic    [`DSC_RID_WIDTH-1:0]    raddr;
}dsc_bram_in_t;


//
typedef struct packed {
    logic    [7:0]            func;
    //logic    [3:0]            be;
} dma_axil_user_t;

// Descriptor Completion
typedef struct packed {
    logic   [63:0]    wadr;
    logic   [63:0]    radr;
    logic   [27:0]    len;
    logic             eop;
    logic             cpl;
    logic             stp;
} dcp_t;

// Descriptor In (user descriptors -> dma)
typedef struct packed {
    logic    [`QID_WIDTH-1:0] qid;    // Q ID 
    logic    [1:0]            chn;    // Channel
    logic    [3:0]            qst;    // Q status
    logic    [2:0]            fmt;    // Format
    logic    [255:0]          dsc;
    logic    [3:0]            vld;
} dma_dsc_in_t;

// Descriptor In Credits (dma credits -> user)
typedef struct packed {
    logic                        vld;
    logic    [8:0]               num;
    logic    [`QID_WIDTH-1:0]    qid;
} dma_dsc_in_crd_t;

// Descriptor Out (dma descriptors -> user)
typedef struct packed {
    logic                       wbi;
    logic                       wbi_chk;
    logic    [15:0]             cidx;
    logic    [`QID_WIDTH-1:0]   qid;    // Q ID
    logic    [1:0]              chn;    // Channel
    logic    [3:0]              qst;    // Q status
    logic    [2:0]              siz;    // Format
    logic                       dir;    // Direction
    logic    [3:0]              vld;
    logic    [255:0]            dsc;
} dma_dsc_block_t;

typedef struct packed {
    logic                       wbi;
    logic                       wbi_chk;
    logic    [15:0]             cidx;
    logic    [`QID_WIDTH-1:0]   qid;    // Q ID
    logic    [1:0]              chn;    // Channel
    logic    [3:0]              qst;    // Q status
    logic    [2:0]              siz;    // Format
    logic                       dir;    // Direction
    logic    [255:0]            dsc;
} dma_dsc_t;

// Descriptor Out Credits (user credits -> dma)
typedef struct packed {
    logic                        vld;
    logic    [8:0]               num;
    logic    [`QID_WIDTH-1:0]    qid;
    logic    [1:0]               chn;
    logic                        clr;
} dma_dsc_out_crd_t;


// Interface Conversion

`define PCIE_CC_TO_DMA_CC_IF(pcie_cc, dma_cc) \
assign pcie_cc.axis_cc_tvalid =       dma_cc.tvalid; \
assign pcie_cc.axis_cc_tdata  = 'h0 | dma_cc.tdata; \
assign pcie_cc.axis_cc_tuser  = 'h0 | dma_cc.tuser; \
assign pcie_cc.axis_cc_tkeep  = 'h0 | dma_cc.tkeep; \
assign pcie_cc.axis_cc_tlast  =       dma_cc.tlast; \
assign dma_cc.tready          = 'h0 | pcie_cc.axis_cc_tready; 

`define PCIE_CQ_TO_DMA_CQ_IF(pcie_cq, dma_cq) \
assign dma_cq.tvalid           =     | pcie_cq.axis_cq_tvalid; \
assign dma_cq.tdata            = 'h0 | pcie_cq.axis_cq_tdata; \
assign dma_cq.tuser            = 'h0 | pcie_cq.axis_cq_tuser; \
assign dma_cq.tkeep            = 'h0 | pcie_cq.axis_cq_tkeep; \
assign dma_cq.tlast            =     | pcie_cq.axis_cq_tlast; \
assign pcie_cq.axis_cq_tready  = 'h0 | dma_cq.tready; 

`define PCIE_RC_TO_DMA_RC_IF(pcie_rc, dma_rc) \
assign dma_rc.tvalid           =     | pcie_rc.axis_rc_tvalid; \
assign dma_rc.tdata            = 'h0 | pcie_rc.axis_rc_tdata; \
assign dma_rc.tuser            = 'h0 | pcie_rc.axis_rc_tuser; \
assign dma_rc.tkeep            = 'h0 | pcie_rc.axis_rc_tkeep; \
assign dma_rc.tlast            =     | pcie_rc.axis_rc_tlast; \
assign pcie_rc.axis_rc_tready  = 'h0 | dma_rc.tready; 

`define PCIE_RQ_TO_DMA_RQ_IF(pcie_rq, dma_rq) \
assign pcie_rq.axis_rq_tvalid =       dma_rq.tvalid; \
assign pcie_rq.axis_rq_tdata  = 'h0 | dma_rq.tdata; \
assign pcie_rq.axis_rq_tuser  = 'h0 | dma_rq.tuser; \
assign pcie_rq.axis_rq_tkeep  = 'h0 | dma_rq.tkeep; \
assign pcie_rq.axis_rq_tlast  =       dma_rq.tlast; \
assign dma_rq.tready          = 'h0 | pcie_rq.axis_rq_tready; 

`include "dma_pcie_axis_cc_if.svh"
`include "dma_pcie_axis_cq_if.svh"
`include "dma_pcie_axis_rc_if.svh"
`include "dma_pcie_axis_rq_if.svh"
//`include "dma_pcie_c2h_axis_if.svh"
`include "dma_pcie_c2h_crdt_if.svh"
`include "dma_pcie_dsc_in_if.svh"
`include "dma_pcie_dsc_out_if.svh"
`include "dma_pcie_fabric_input_if.svh"
`include "dma_pcie_fabric_output_if.svh"
`include "dma_pcie_gic_if.svh"
//`include "dma_pcie_h2c_axis_if.svh"
`include "dma_pcie_h2c_crdt_if.svh"
`include "dma_pcie_mi_16Bx2048_4Bwe_ram_if.svh"
`include "dma_pcie_mi_2Bx2048_ram_if.svh"
`include "dma_pcie_mi_4Bx2048_4Bwe_ram_if.svh"
`include "dma_pcie_mi_64Bx128_32Bwe_ram_if.svh"
`include "dma_pcie_mi_64Bx256_32Bwe_ram_if.svh"
`include "dma_pcie_mi_64Bx512_32Bwe_ram_if.svh"
`include "dma_pcie_mi_64Bx1024_32Bwe_ram_if.svh"
`include "dma_pcie_mi_64Bx2048_32Bwe_ram_if.svh"
`include "dma_pcie_mi_8Bx2048_4Bwe_ram_if.svh"
`include "dma_pcie_mi_dsc_cpld_if.svh"
`include "dma_pcie_mi_dsc_cpli_if.svh"
`include "dma_pcie_misc_input_if.svh"
`include "dma_pcie_misc_output_if.svh"
`endif


