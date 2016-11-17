// ***************************************************************
// Class: axi4UvmVirtualSequence
//
// This class defines a base virtual sequence
// ***************************************************************
`ifndef CDN_AXI_UVM_VIRTUAL_SEQUENCE_SV
`define CDN_AXI_UVM_VIRTUAL_SEQUENCE_SV

class axi4UvmVirtualSequence extends uvm_sequence;
  
   // By default, if the response_queue overflows, an error is reported. The
   // response_queue will overflow if more responses are sent to this sequence
   // from the driver than get_response calls are made. Setting value to 1
   // disables these errors, while setting it to 0 enables them.
   bit response_queue_error_report_disbaled = 1;

   `uvm_object_utils_begin(axi4UvmVirtualSequence)
      `uvm_field_int(response_queue_error_report_disbaled, UVM_ALL_ON)
    `uvm_object_utils_end
	
  `uvm_declare_p_sequencer(axi4UvmUserVirtualSequencer)

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "axi4UvmVirtualSequence");
    super.new(name);
    set_response_queue_error_report_disabled(response_queue_error_report_disbaled);
  endfunction : new

  // ***************************************************************
  // Method : pre_body
  // Desc.  : Raise an objection to prevent premature simulation end
  // ***************************************************************
  virtual task pre_body();
    if (starting_phase != null) begin
      starting_phase.raise_objection(this);
      
      // enable Active master tracker
      p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_EnableTracker,1);
      
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
  
endclass : axi4UvmVirtualSequence 

`endif // CDN_AXI_UVM_VIRTUAL_SEQUENCE_SV 

// ****************************************************************************
// Class : perChannalDelaySeq
// Desc. : Eval ID: 4.9
// VIP support dynamic configuration of per channel valid-ready delay
// ****************************************************************************
class perChannalDelaySeq extends axi4UvmVirtualSequence;

	`uvm_object_utils(perChannalDelaySeq)
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "perChannalDelaySeq");
    super.new(name);        
  endfunction : new 
	
	myAxiTransaction masterBurst;
	
	virtual task body();
		
		// disable all AXI channels valid and ready
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteAddrChannel,1); 	// AWVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadAddrChannel,1);  	// ARVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteDataChannel,1);		// WVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,1); 		// RREADY
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,1); 	// BREADY
  
  	p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteAddrChannel,1);		// AWREADY
  	p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadAddrChannel,1);			// ARREADY
  	p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteDataChannel,1);		// WREADY
  	p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,1);			// RVALID
  	p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,1);		// BVALID
  	
		`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr,  { 
			masterBurst.Type == DENALI_CDN_AXI_TR_Write;
			masterBurst.Length == 4;
			masterBurst.TransmitDelay == 0;
		})
						
		`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr,  { 
			masterBurst.Type == DENALI_CDN_AXI_TR_Read;
			masterBurst.Length == 4;
			masterBurst.TransmitDelay == 0;
		})
		
		#5000;
		// enable AWVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteAddrChannel,0);
		
		#5000;
		// enable AWREADY
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteAddrChannel,0);
		
		#5000;
		// enable WVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteDataChannel,0);
		
		#5000;
		// enable WREADY
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteDataChannel,0);
		
		#5000;
		// enable BVALID
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,0);
		
		#5000;
		// enable BREADY
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,0); 
		
		#5000;
		// enable ARVALID
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadAddrChannel,0);
		
		#5000;
		// enable ARREADY
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadAddrChannel,0);
		
		#5000;
		// enable RVALID
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,0);
		
		#5000;
		// enable RREADY
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,0);
		
		#10000;

  endtask
	
endclass : perChannalDelaySeq

// ****************************************************************************
// Class : perTransactionDelaySeq
// Desc. : Eval ID: 4.9
// VIP support dynamic configuration of per transaction valid-ready delay
// ****************************************************************************
class perTransactionDelaySeq extends axi4UvmVirtualSequence;
	
	`uvm_object_utils(perTransactionDelaySeq)
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "perTransactionDelaySeq");
    super.new(name);        
  endfunction : new 
	
	myAxiTransaction masterBurst;
	mySlaveResp slaveResponse;
	
	virtual task body();	

		// xREADY signals initial value after reset
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_AwreadyValueAfterReset,0);
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_WreadyValueAfterReset,0);
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_BreadyValueAfterReset,0);
		p_sequencer.pEnv.activeSlave.regInst.writeReg(DENALI_CDN_AXI_REG_ArreadyValueAfterReset,0);
		p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_RreadyValueAfterReset,0);
		
		for (int i=0; i<5; i++) begin
		
			`uvm_do_on_with(slaveResponse, p_sequencer.slaveSeqr,  {
				slaveResponse.Type == DENALI_CDN_AXI_TR_Write;
				slaveResponse.Length == 4;
				// AWVALID to AWREADY delay
				slaveResponse.AreadyControl == DENALI_CDN_AXI_READYCONTROL_STALL_UNTIL_VALID_AND_DELAY;
				slaveResponse.AddressDelay == 5;			
				// WREADY delay
				slaveResponse.WreadyControl == DENALI_CDN_AXI_READYCONTROL_STALL_UNTIL_VALID_AND_DELAY;
				slaveResponse.TransfersChannelDelay.size() == 4;
				foreach(slaveResponse.TransfersChannelDelay[index]){
		    		slaveResponse.TransfersChannelDelay[index] == 5; // WREADY delay after each WVALID assertion
		    }
				// BVALID delay (from WLAST)
				slaveResponse.ChannelDelay == 5;
			})
							
			`uvm_do_on_with(slaveResponse, p_sequencer.slaveSeqr,  { 
				slaveResponse.Type == DENALI_CDN_AXI_TR_Read;
				slaveResponse.Length == 4;
				// ARVALID to ARREADY delay
				slaveResponse.AreadyControl == DENALI_CDN_AXI_READYCONTROL_STALL_UNTIL_VALID_AND_DELAY;
				slaveResponse.AddressDelay >= 5; // min ARVALID_to_ARREADY delay 
				slaveResponse.AddressDelay <= 10;// max ARVALID_to_ARREADY delay
				
				// TransfersChannelDelay[0] set the delay between ARVALID+ARREADY and first RVALID
				slaveResponse.TransfersChannelDelay.size() == 4;
				foreach(slaveResponse.TransfersChannelDelay[index]){
		    		slaveResponse.TransfersChannelDelay[index] == 5; // RVALID to RVALID delay
		    }
			})
			
			`uvm_create_on(masterBurst, p_sequencer.masterSeqr)
			masterBurst.TransmitDelay_const.constraint_mode(0);
			`uvm_rand_send_with(masterBurst, { 
				masterBurst.Type == DENALI_CDN_AXI_TR_Write;
				masterBurst.Length == 4;
				masterBurst.TransmitDelay == 5; // AwVALID delay	
				// TransfersChannelDelay[0] set the delay between AWVALID+AWREADY and first WVALID
				masterBurst.TransfersChannelDelay.size() == 4;
				foreach(masterBurst.TransfersChannelDelay[index]){
		    		masterBurst.TransfersChannelDelay[index] == 5; // WVALID to WVALID delay
		    }
				// BVALID to BREADY delay
				masterBurst.BreadyControl == DENALI_CDN_AXI_READYCONTROL_STALL_UNTIL_VALID_AND_DELAY;
				masterBurst.BreadyDelay == 5;
	
			})
							
			`uvm_create_on(masterBurst, p_sequencer.masterSeqr)
			masterBurst.TransmitDelay_const.constraint_mode(0);
			`uvm_rand_send_with(masterBurst, { 
				masterBurst.Type == DENALI_CDN_AXI_TR_Read;
				masterBurst.Length == 4;
				masterBurst.TransmitDelay == 5; // ARVALID delay
				// RREADY delay
				masterBurst.RreadyControl == DENALI_CDN_AXI_READYCONTROL_STALL_UNTIL_VALID_AND_DELAY;
				foreach(masterBurst.TransfersChannelDelay[index]){
		    		masterBurst.TransfersChannelDelay[index] == 5; // RREADY delay after each RVALID assertion
		    }
			})
			#100000;
		end
  endtask
	
endclass : perTransactionDelaySeq

// ****************************************************************************
// Class : cross4kBounderySeq
// Desc. : Eval ID: 4.17
// Using transaction class object in user sequence/test generate and issue a illegal transaction for negative testing. 
// This could be post randomization of object change transaction parameters
// ****************************************************************************
class cross4kBoundarySeq extends axi4UvmVirtualSequence;

	`uvm_object_utils(cross4kBoundarySeq)
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "cross4kBoundarySeq");
    super.new(name);        
  endfunction : new 
  	
	crossing4kBoundaryModifyTransactionSeq seq;
	
	virtual task body();
		
		`uvm_do_on_with(seq, p_sequencer.masterSeqr, {
			seq.direction == DENALI_CDN_AXI_DIRECTION_READ;
		})

  endtask
	
endclass : cross4kBoundarySeq

// ****************************************************************************
// Class : IdBasedReorderingSeq
// Desc. : Eval ID: 4.25
// Auto ID management for OOO request per instance 
// Address phase IDs order is 5,4,3,2,1 but read data order is 1,2,3,4,5 and write response order is 5,1,2,3,4
// ****************************************************************************
class IdBasedReorderingSeq extends axi4UvmVirtualSequence;

	`uvm_object_utils(IdBasedReorderingSeq)
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "IdBasedReorderingSeq");
    super.new(name);        
  endfunction : new 
	
	myAxiTransaction masterBurst;
	mySlaveResp slaveResponse;
	
	virtual task body();
		
		p_sequencer.pEnv.activeSlave.cfg.read_ordering_algorithm = CDN_AXI_CFG_READ_ORDERING_ALGORITHM_ROUND_ROBIN;
		p_sequencer.pEnv.activeSlave.cfg.write_resp_ordering_algorithm = CDN_AXI_CFG_WRITE_RESP_ORDERING_ALGORITHM_ROUND_ROBIN;
    p_sequencer.pEnv.activeSlave.reconfigure(p_sequencer.pEnv.activeSlave.cfg); 
    
    p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,1); 
    p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,1); 
    
    for(int ii=0; ii<5; ii++) begin
			`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr, { 
				masterBurst.Type == DENALI_CDN_AXI_TR_Read;
				masterBurst.Length == 4;
				masterBurst.IdTag == 5-ii;
			})
			
			`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr, { 
				masterBurst.Type == DENALI_CDN_AXI_TR_Write;
				masterBurst.Length == 4;
				masterBurst.IdTag == 4-ii;
			})
		end
    
    #100000;
    p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableWriteRespChannel,0); 
    p_sequencer.pEnv.activeMaster.regInst.writeReg(DENALI_CDN_AXI_REG_DisableReadDataChannel,0);
    #100000; 
    
  endtask
	
endclass : IdBasedReorderingSeq

// ****************************************************************************
// Class : blockingNonBlockingSeq
// Desc. : Eval ID: 4.26
// Blocking and Non-blocking request support
// ***************************************************************************
class blockingNonBlockingSeq extends axi4UvmVirtualSequence;

	`uvm_object_utils(blockingNonBlockingSeq)
  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "blockingNonBlockingSeq");
    super.new(name);        
  endfunction : new 
	
	myAxiTransaction masterBurst;
	uvm_sequence_item item;
	
	virtual task body();
		
		`uvm_info(get_type_name(), "sending 100 blocking transactions", UVM_LOW);
		for(int j =0; j<10; ++j) begin
			`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr, {
				masterBurst.Type inside {DENALI_CDN_AXI_TR_Read, DENALI_CDN_AXI_TR_Write};
			})
			get_response(item, masterBurst.get_transaction_id());
		end
		
		`uvm_info(get_type_name(), "sending 100 non-blocking transactions", UVM_LOW);
		for(int j =0; j<10; ++j) begin
			`uvm_do_on_with(masterBurst, p_sequencer.masterSeqr, {
				masterBurst.Type inside {DENALI_CDN_AXI_TR_Read, DENALI_CDN_AXI_TR_Write};
				masterBurst.Length < 10;
			})
		end
		#100000;

  endtask
	
endclass : blockingNonBlockingSeq
