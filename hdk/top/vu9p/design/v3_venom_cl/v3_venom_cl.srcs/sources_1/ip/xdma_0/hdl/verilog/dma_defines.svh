`ifndef DMA_DEFINES_SVH
`define DMA_DEFINES_SVH

`include "dma_defines.vh"


typedef struct packed {
   logic                  spl;
	logic [`ADR_WIDTH-1:0] adr;
	logic [`RID_WIDTH-1:0] rid;
	logic [`LEN_WIDTH-1:0] byte_len;   // byte length
	logic [`DID_WIDTH-1:0] did;
} rrq_t;

typedef struct packed {
	logic			sop;
	logic			eop;
	logic			wbk;
	logic [4:0]		err;
	//logic [`DAT_WIDTH/32-1:0] wen; // dword write enable
	logic [`RID_WIDTH-1:0]	rid;
	logic [`DID_WIDTH-1:0]	did;
	logic [5:0]		lba;	// Last beat length adjustment (AXI ST C2H)
	logic [`DAT_WIDTH/8-1:0] par;
	logic [`DAT_WIDTH-1:0] dat;
} rcp_t;

typedef struct packed {
	logic [`ADR_WIDTH-1:0] adr;
	logic [`RID_WIDTH-1:0] rid;
	logic [`LEN_WIDTH-1:0] byte_len;   // byte length
	logic [5:0]  aln;		// Source alignment
	logic	eop;
	logic	eod;
	logic	eor;
} wrq_t;

typedef struct packed {
	logic	[`DAT_WIDTH/8-1:0]	par;
	logic	[`DAT_WIDTH-1:0] 	dat;
} wpl_t;

typedef struct packed {
	logic	[`RID_WIDTH-1:0]	rid;
	logic	[4:0] 			err;
} wcp_t;

typedef struct packed {
	logic [31:0]	dat;
} wbrq_t;

typedef struct packed {
	logic [3:0]		be;	
	logic			rd;
	logic			wr;
	logic [31:0] 		dat;
	logic [31:0]		adr;
	logic 			multq;
} trq_t;

typedef struct packed {
	logic			vld;
	logic [31:0] 		dat;
} tcp_t;

typedef struct packed {
	logic			run;
	logic			c2h_wbk_ena;
	logic			noninc;
	logic [`ADR_WIDTH-1:0]	cdc_wbk_adr;
} creg_t;

typedef struct packed {
	logic	[63:0]		par; 		// 136:73 Parity filled later
	logic	[5:0] 		seq1;		// 72:67  Sequence Num 1
	logic	[5:0]		seq0;		// 66:61  Sequence Num 0
	logic	[23:0]		tph;		// 60:45  TPH St Tag
						// 44:43  TPH Ind Tag
						// 42:39  TPH Type
						// 38:37  TPH Present
	logic			disc;		// 36     Discontinue
	logic	[3:0]		eop1_ptr;	// 35:32  EOP 1 Ptr
	logic	[3:0]		eop0_ptr;	// 31:28  EOP 0 Ptr
	logic			eop1;		// 27     EOP 1
	logic			eop0;		// 26     EOP 0
	logic	[1:0]		sop1_ptr;	// 25:24  SOP 1 Ptr
	logic	[1:0]		sop0_ptr;	// 23:22  SOP 0 Ptr
	logic			sop1;		// 21     SOP 1
	logic			sop0;		// 20     SOP 0
	logic	[3:0]		adr; 		// 19:16  Address offset - Address aligned mode only
	logic	[3:0] 		lbe1;
	logic	[3:0] 		lbe0;
	logic	[3:0] 		fbe1;
	logic	[3:0] 		fbe0;
} rq_usr_straddle_t;

typedef struct packed {
	logic	[76:0]		rsv;
	logic	[31:0]		par; 		// 59:28
	logic	[3:0]		seq;		// 27:24
	logic	[11:0]		tph;		// 23:12
	logic			dis;		// 11
	logic	[2:0]		adr; 		// 10:8
	logic	[3:0] 		lbe;		// 7:4
	logic	[3:0] 		fbe;		// 3:0
} rq_usr_nostraddle_t;

typedef union packed {
	rq_usr_straddle_t   	rqu_str;
	rq_usr_nostraddle_t  	rqu_nstr;
} rq_usr_t;

typedef struct packed { 
	logic			ecrc;
	logic 	[2:0]		attr;		
	logic	[2:0]		tc;	
	logic			rid_en;
	logic	[15:0]		cpl_id;
	logic	[7:0]		tag;
	logic	[15:0]		req_id;
	logic			poison;
	logic	[3:0]		req;
	logic	[10:0]		len;		
	logic	[63:0]		adr;
} rq_hdr_fields_t;

typedef struct packed { 
	logic	[23:0]		dw3_misc;
	logic	[7:0]		tag;
	logic	[16:0]		dw2_misc;
	logic	[3:0]		req;
	logic	[10:0]		len;		
	logic	[63:0]		adr;
} rq_hdr_compact_t;

typedef struct packed { 
	logic	[31:0]		dw3;
	logic	[31:0]		dw2;
	logic	[31:0]		dw1;
	logic	[31:0]		dw0;
} rq_hdr_dwords_t;

typedef union packed {
	rq_hdr_fields_t		rqh_f;
	rq_hdr_compact_t  	rqh_c;
	rq_hdr_dwords_t  	rqh_d;
} rq_hdr_t;

typedef struct packed { 
	logic					tlast;
	logic	[`MULTQ_C2H_TUSER_WIDTH-1:0]	tuser;
	logic	[`DAT_WIDTH/8-1:0]		tkeep;
	logic	[`DAT_WIDTH/8-1:0]		tparity;
	logic	[`DAT_WIDTH-1:0]		tdata;
} dma_s_axis_t;

typedef struct packed {
        logic [`DID_WIDTH-1:0]          waddr;
        logic [`DID_WIDTH-1:0]          raddr;
        logic [`DAT_WIDTH/8-1:0]        wen;
} dat_bram_cmd_t;

typedef struct packed {
        logic [`DAT_WIDTH-1:0]          dat;
        logic [`DAT_WIDTH/8-1:0]        parity; // Even parity
}dat_bram_dat_t;

typedef struct packed {
        logic                   	wen;
        logic [`DSC_DID_WIDTH-1:0]  	waddr;
        logic [`DAT_WIDTH-1:0]  	wdat;
        logic [`DSC_RID_WIDTH-1:0]  	raddr;
}dsc_bram_wr_t;

typedef struct packed {
	
	logic					tlast;
	logic	[`MULTQ_H2C_TUSER_WIDTH-1:0]	tuser;
	logic	[`DAT_WIDTH/8-1:0]		tkeep;
	logic	[`DAT_WIDTH/8-1:0]		tparity;
	logic	[`DAT_WIDTH-1:0]		tdata;
} dma_m_axis_t;

typedef struct packed {	
        logic [64-1:0]				rdat;
        logic					rbe;
}dsc_bram_rd_t;  	

typedef struct packed {
	logic	[7:0]			func;
	logic	[3:0]			be;
} dma_axil_tuser_t;
`endif
