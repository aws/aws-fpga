`ifndef _USER_ACE_FULL_SEQ_LIB
`define _USER_ACE_FULL_SEQ_LIB

class aceFullUvmUserTransaction extends denaliCdn_axiTransaction;

	`uvm_object_utils(aceFullUvmUserTransaction)

	aceFullUvmUserConfig cfg;

	//Chosen Segment Index
	rand int chosenSegmentIndex;

	function new(string name = "aceFullUvmUserTransaction");
		super.new(name);       
	endfunction : new 

 	function void pre_randomize();
		cdnAxiUvmSequencer seqr;
		super.pre_randomize();                             
	
		if (!$cast(seqr,get_sequencer())) begin
			`uvm_fatal(get_type_name(),"failed $cast(seqr,get_sequencer())");
		end

		if (!$cast(cfg,seqr.pAgent.cfg)) begin
			`uvm_fatal(get_type_name(),"failed $cast(cfg,seqr.pAgent.cfg))");
		end  

		this.SpecVer = (cfg.spec_ver == CDN_AXI_CFG_SPEC_VER_AMBA4 ? DENALI_CDN_AXI_SPECVERSION_AMBA4 :DENALI_CDN_AXI_SPECVERSION_AMBA3);    
		this.SpecSubtype = (cfg.spec_subtype == CDN_AXI_CFG_SPEC_SUBTYPE_ACE ? DENALI_CDN_AXI_SPECSUBTYPE_ACE : DENALI_CDN_AXI_SPECSUBTYPE_BASE);
		this.SpecInterface = (cfg.spec_interface == CDN_AXI_CFG_SPEC_INTERFACE_FULL ?  DENALI_CDN_AXI_SPECINTERFACE_FULL : DENALI_CDN_AXI_SPECINTERFACE_LITE);
		
		if (cfg.pins.rdata.size >= 1024) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_K_BITS;
		end
		else if (cfg.pins.rdata.size >= 512) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_SIXTEEN_WORDS;
		end
		else if (cfg.pins.rdata.size >= 256) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_EIGHT_WORDS;
		end
		else if (cfg.pins.rdata.size >= 128) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_FOUR_WORDS;
		end
		else if (cfg.pins.rdata.size >= 64) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_TWO_WORDS;
		end
		else if (cfg.pins.rdata.size >= 32) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_WORD;
		end
		else if (cfg.pins.rdata.size >= 16) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_HALFWORD;
		end
		else if (cfg.pins.rdata.size >= 8) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_BYTE;
		end
		
		this.CacheLineSize = cfg.cache_line_size;

		this.SpecVer.rand_mode(0);
		this.SpecSubtype.rand_mode(0);
		this.SpecInterface.rand_mode(0);
		this.BurstMaxSize.rand_mode(0);
		this.CacheLineSize.rand_mode(0);

	endfunction    
     
	constraint burstSizeCfgConstraint {                
		BurstSize <= (cfg.pins.rdata.size/8); 
		BurstSize <= (cfg.pins.wdata.size/8);
	}

	constraint burstIdCfgConstraint {      
		IdTag < (1 <<  cfg.pins.awid.size);
		IdTag < (1 << cfg.pins.arid.size);                  
	}

	//NOTE: This constraints is not enough , it doesn't take into considerations length and size to be inside memory segment.
	constraint burstAddresscfgConstraint { 

		solve chosenSegmentIndex before StartAddress;

		chosenSegmentIndex < cfg.memory_segments.size();
		chosenSegmentIndex >= 0;

		foreach (cfg.memory_segments[ii]) {

			if (IsBarrier == DENALI_CDN_AXI_ISBARRIER_NOT_BARRIER && 
					IsDvm == DENALI_CDN_AXI_DVM_NOT_DVM && 
					ii == chosenSegmentIndex) {
					
				StartAddress < cfg.memory_segments[ii].high_address;
				StartAddress >= cfg.memory_segments[ii].low_address;
				Domain == cfg.memory_segments[ii].domain;
			}
		}
	}

endclass


class aceFullUvmUserSeq extends cdnAxiUvmSequence;
	
	// ***************************************************************
	// Use the UVM registration macro for this class.
	// ***************************************************************
	`uvm_object_utils(aceFullUvmUserSeq)  

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new(string name = "aceFullUvmUserSeq");
		super.new(name);        
	endfunction : new

	denaliCdn_axiTransaction trans;

	virtual task pre_body();
		if (starting_phase != null) begin
			starting_phase.raise_objection(this);
		end    
	endtask

	// ***************************************************************
	// Method : post_body
	// Desc.  : Drop the objection raised earlier
	// ***************************************************************
	virtual task post_body();
		if (starting_phase != null) begin
			// Drain time
			#5000;
			starting_phase.drop_objection(this);
		end    
	endtask 

endclass : aceFullUvmUserSeq	
	
	
class userMasterSeq extends aceFullUvmUserSeq;

	// ***************************************************************
	// Use the UVM registration macro for this class.
	// ***************************************************************
	`uvm_object_utils(userMasterSeq)  

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new(string name = "userMasterSeq");
		super.new(name);        
	endfunction : new

	virtual task body();
		for (int i=0; i<100; i++) begin
			`uvm_do_with(trans,{
				trans.Direction inside {DENALI_CDN_AXI_DIRECTION_READ, DENALI_CDN_AXI_DIRECTION_WRITE};
				(trans.ReadSnoop == DENALI_CDN_AXI_READSNOOP_ReadOnce) | (trans.WriteSnoop == DENALI_CDN_AXI_WRITESNOOP_WriteUnique);
      	trans.Length <= 16;
			});
			get_response(trans);
			#1000;
		end

	endtask : body

endclass : userMasterSeq


class userSnoopSeq extends aceFullUvmUserSeq;

	// ***************************************************************
	// Use the UVM registration macro for this class.
	// ***************************************************************
	`uvm_object_utils(userSnoopSeq)  

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new(string name = "userSnoopSeq");
		super.new(name);        
	endfunction : new

	virtual task body();
		for (int i=0; i<100; i++) begin
			`uvm_do_with(trans,{
				trans.Type == DENALI_CDN_AXI_TR_Snoop;
				trans.Domain == DENALI_CDN_AXI_DOMAIN_INNER;
			});
			get_response(trans);	
		end

	endtask : body

endclass : userSnoopSeq

`endif //  `ifndef _USER_ACE_FULL_SEQ_LIB

