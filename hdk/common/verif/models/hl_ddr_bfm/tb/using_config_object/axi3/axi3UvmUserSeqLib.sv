`ifndef _USER_CDN_AXI_SEQ_LIB
`define _USER_CDN_AXI_SEQ_LIB

class myAxiTransaction extends denaliCdn_axiTransaction;

	`uvm_object_utils(myAxiTransaction)

	axi3UvmUserConfig cfg;

	//Chosen Segment Index
	rand int chosenSegmentIndex;

	function new(string name = "myAxiTransaction");
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
		
		if (cfg.pins.rdata.size >= 1024 || cfg.pins.wdata.size >= 1024) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_K_BITS;
		end
		else if (cfg.pins.rdata.size >= 512 || cfg.pins.wdata.size >= 512) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_SIXTEEN_WORDS;
		end
		else if (cfg.pins.rdata.size >= 256 || cfg.pins.wdata.size >= 256) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_EIGHT_WORDS;
		end
		else if (cfg.pins.rdata.size >= 128 || cfg.pins.wdata.size >= 128) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_FOUR_WORDS;
		end
		else if (cfg.pins.rdata.size >= 64 || cfg.pins.wdata.size >= 64) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_TWO_WORDS;
		end
		else if (cfg.pins.rdata.size >= 32 || cfg.pins.wdata.size >= 32) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_WORD;
		end
		else if (cfg.pins.rdata.size >= 16 || cfg.pins.wdata.size >= 16) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_HALFWORD;
		end
		else if (cfg.pins.rdata.size >= 8 || cfg.pins.wdata.size >= 8) begin
			this.BurstMaxSize = DENALI_CDN_AXI_TRANSFERSIZE_BYTE;
		end
		
		this.SpecVer.rand_mode(0);
		this.SpecSubtype.rand_mode(0);
		this.SpecInterface.rand_mode(0);
		this.BurstMaxSize.rand_mode(0);			

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
			if (ii == chosenSegmentIndex) {
				StartAddress < cfg.memory_segments[ii].high_address;
				StartAddress >= cfg.memory_segments[ii].low_address;
			}
		}
	}

endclass


class userSimpleSeq extends cdnAxiUvmSequence;

	// ***************************************************************
	// Use the UVM registration macro for this class.
	// ***************************************************************
	`uvm_object_utils(userSimpleSeq)  

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new(string name = "userSimpleSeq");
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
			starting_phase.drop_objection(this);
		end    
	endtask 

	virtual task body();
		
		#1000;
		
		for (int i=0; i<50; i++) begin
			`uvm_do_with(trans,{
				trans.Type inside {DENALI_CDN_AXI_TR_Read, DENALI_CDN_AXI_TR_Write};
			});
			get_response(trans);     
		end  
	endtask : body

endclass

`endif //  `ifndef _USER_CDN_AXI_SEQ_LIB