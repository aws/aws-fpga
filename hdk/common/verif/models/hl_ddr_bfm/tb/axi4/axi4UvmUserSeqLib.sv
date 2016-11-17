`ifndef _USER_CDN_AXI_SEQ_LIB
`define _USER_CDN_AXI_SEQ_LIB

class myAxiTransaction extends denaliCdn_axiTransaction;

	`uvm_object_utils(myAxiTransaction)

	axi4UvmUserConfig cfg;

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

// ****************************************************************************
// Class : mySlaveResp
// Desc. : This class extends myAxiTransaction class
// ****************************************************************************
class mySlaveResp extends myAxiTransaction;
  `uvm_object_utils(mySlaveResp)

  function new(string name = "mySlaveResp");
    super.new(name);
  endfunction : new   

  constraint wr_resp_dist {
  	Resp dist { DENALI_CDN_AXI_RESPONSE_OKAY   := 50,
                DENALI_CDN_AXI_RESPONSE_SLVERR := 50 
    };        
  }
  
  constraint memory_consistency {
  	 // If data exists in main memory, return it from there and ignore the trnasaction's Data field.
  	 IgnoreConstraints == 1;
  }

endclass : mySlaveResp


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
/*
		for (i=0; i<4; i++) begin
			`uvm_do_with(trans,{
				trans.Type inside {DENALI_CDN_AXI_TR_Write};
                trans.Length == 2;
                trans.StartAddress == 1024;
			});
			get_response(trans);     
            $display("%t, debug - trans: %p", $time(), trans.Data);
		end

		for (i=0; i<4; i++) begin
			`uvm_do_with(trans,{
				trans.Type inside {DENALI_CDN_AXI_TR_Read};
                trans.Length == 2;
                trans.StartAddress == 1024;
			});
			get_response(trans);     
            $display("%t, debug - trans: %p", $time(), trans.Data);
		end
*/
       
				
		for (int i=0; i<1; i++) begin
           `uvm_create(trans);

           trans.StartAddress = i * (64 * 16);
           trans.Type = DENALI_CDN_AXI_TR_Write;
           trans.Direction = DENALI_CDN_AXI_DIRECTION_WRITE;
           trans.Length = 16;
           trans.Size = 7;
           trans.Data = new[64 * 16];
           
           $display("%t - debug Data size: %d", $time(), trans.Data.size());

           
           for(int j=0; j<16; j++)
             for(int k=0; k<trans.Data.size(); k++)
               trans.Data[j*64 + k[7:0]] = k;
           
           `uvm_send(trans);
           
//			`uvm_do_with(trans,{
//				trans.Type inside {DENALI_CDN_AXI_TR_Read, DENALI_CDN_AXI_TR_Write};
//                trans.Size == 1;
//			});
			get_response(trans);     
		end

		// sending "BIG" bursts
		for (int i=0; i<10; i++) begin
			`uvm_do_with(trans, {
//				trans.Type inside {DENALI_CDN_AXI_TR_Read, DENALI_CDN_AXI_TR_Write};
                trans.StartAddress == 64'h0;
				trans.Type inside {DENALI_CDN_AXI_TR_Read};
                trans.Size == 7;
				trans.Length > 16;
			});
			get_response(trans);     
		end

	endtask : body

endclass

class crossing4kBoundaryModifyTransactionSeq extends cdnAxiUvmModifyTransactionSequence;

  // ***************************************************************
  // Use the UVM registration macro for this class.
  // ***************************************************************
  `uvm_object_utils(crossing4kBoundaryModifyTransactionSeq)
  
  rand denaliCdn_axiDirectionT direction;
     
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "crossing4kBoundaryModifyTransactionSeq");
    super.new(name);        
  endfunction : new
  
  myAxiTransaction trans; 
  
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
    denaliCdn_axiTransaction response;

    `uvm_do_with(trans, {
    	trans.Direction == direction;
    })    

    //Wait till transaction is transmitted to DUT
    //   we want the sequence to end only after the transaction transmission is completed.
    //   when sequence ends no modification will take effect
    get_response(response,trans.get_transaction_id());    
        
    `uvm_info(get_type_name(), "Finished Transaction modification", UVM_LOW)
  endtask : body

  // Modify the transaction in BeofreSend callback using TransSet()
  // This is where we decide what are the transaction's attributes (fields) we want to modify 
  // and which items should it effect. 
  virtual function void modifyTransaction(denaliCdn_axiTransaction tr);
    bit status;
    //in this case we can choose to modify only a specific burst this sequence has generated.
    //if there was no condition then the modification would have occurred to any burst being sent.
    //by default only bursts created in this sequence will be affected.
    if (trans != null && tr.UserData ==  trans.UserData)    
    begin
      `uvm_info(get_type_name(), "Starting Transaction modification", UVM_LOW)      
      tr.StartAddress[11:0] = 12'hff0; // close to 4K boundary
      
      // cross 4K boundary
      tr.Kind = DENALI_CDN_AXI_BURSTKIND_INCR;
      tr.Size = DENALI_CDN_AXI_TRANSFERSIZE_FOUR_WORDS;
      tr.Length = 10;
      
      //Update the model transaction with the new values
      //   transSet() is being used to update that fields were changed.
      status = tr.transSet();
          
      `uvm_info(get_type_name(), "Finished Transaction modification", UVM_LOW)
    end
  endfunction

endclass : crossing4kBoundaryModifyTransactionSeq


`endif //  `ifndef _USER_CDN_AXI_SEQ_LIB