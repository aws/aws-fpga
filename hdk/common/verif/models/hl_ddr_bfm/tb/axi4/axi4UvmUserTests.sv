
`ifndef _USER_CDN_AXI_SVE_TEST
`define _USER_CDN_AXI_SVE_TEST

// ****************************************************************************
// Class : axi4UvmUserSve
// Desc. : This Demo testbench(sve) instantiates the demo env and a virtual sequencer
// ****************************************************************************
class axi4UvmUserSve extends uvm_env;

  axi4UvmUserEnv axiEnv0;
  axi4UvmUserVirtualSequencer vs;
      
  `uvm_component_utils(axi4UvmUserSve)
        
  function new(string name = "axi4UvmUserSve", uvm_component parent);
    super.new(name,parent);
  endfunction // new
   
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);  
    axiEnv0 = axi4UvmUserEnv::type_id::create("axiEnv0", this);
    vs = axi4UvmUserVirtualSequencer::type_id::create("vs", this);    
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
// ww    $cast(vs.slaveSeqr, axiEnv0.activeSlave.sequencer);
    $cast(vs.masterSeqr, axiEnv0.activeMaster.sequencer);
    $cast(vs.pEnv, axiEnv0);
  endfunction 
           
endclass : axi4UvmUserSve

class axi4UvmUserTest extends uvm_test;

	axi4UvmUserSve axiSve0;

	`uvm_component_utils_begin(axi4UvmUserTest)
	`uvm_component_utils_end

	function new(string name = "axi4UvmUserTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		factory.set_type_override_by_type(denaliCdn_axiTransaction::get_type(),myAxiTransaction::get_type());
		axiSve0 = axi4UvmUserSve::type_id::create("axiSve0", this);
		
		uvm_top.set_config_int("*", "recording_detail" , UVM_FULL);  
	endfunction : build_phase
	
	virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uvm_top.print_topology();
  endfunction 

endclass : axi4UvmUserTest

class basicTest extends axi4UvmUserTest;

	`uvm_component_utils_begin(basicTest)
	`uvm_component_utils_end

	function new(string name = "basicTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.axiEnv0.activeMaster.sequencer.run_phase", "default_sequence",userSimpleSeq::type_id::get());
		
	endfunction : build_phase

endclass : basicTest

class perChannalDelayTest extends axi4UvmUserTest;
	
	`uvm_component_utils_begin(perChannalDelayTest)
	`uvm_component_utils_end

	function new(string name = "perChannalDelayTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		 uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.vs.run_phase", "default_sequence",perChannalDelaySeq::type_id::get());
		
	endfunction : build_phase 

endclass : perChannalDelayTest

class perTransactionDelayTest extends axi4UvmUserTest;
	
	`uvm_component_utils_begin(perTransactionDelayTest)
	`uvm_component_utils_end

	function new(string name = "perTransactionDelayTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		 uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.vs.run_phase", "default_sequence",perTransactionDelaySeq::type_id::get());
		
	endfunction : build_phase 

endclass : perTransactionDelayTest

class cross4kBoundaryTest extends axi4UvmUserTest;
	
	`uvm_component_utils_begin(cross4kBoundaryTest)
	`uvm_component_utils_end

	function new(string name = "cross4kBoundaryTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		 uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.vs.run_phase", "default_sequence",cross4kBoundarySeq::type_id::get());
		
	endfunction : build_phase
	
	virtual function void end_of_elaboration_phase(uvm_phase phase);      
      super.end_of_elaboration_phase(phase);     
      // change check to warning
      axiSve0.axiEnv0.passiveMaster.monitor.set_report_severity_id_override(UVM_FATAL,"CDN_AXI_FATAL_ERR_VR_AXI128_READ_CROSS_4K_BOUNDARY",UVM_WARNING);
  endfunction

endclass : cross4kBoundaryTest

class IdBasedReorderingTest extends axi4UvmUserTest;
	
	`uvm_component_utils_begin(IdBasedReorderingTest)
	`uvm_component_utils_end

	function new(string name = "IdBasedReorderingTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		 uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.vs.run_phase", "default_sequence",IdBasedReorderingSeq::type_id::get());
		
	endfunction : build_phase 

endclass : IdBasedReorderingTest

class blockingNonBlockingTest extends axi4UvmUserTest;
	
	`uvm_component_utils_begin(blockingNonBlockingTest)
	`uvm_component_utils_end

	function new(string name = "blockingNonBlockingTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 
		
		//set the starting sequence to system      
		 uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.vs.run_phase", "default_sequence",blockingNonBlockingSeq::type_id::get());
		
	endfunction : build_phase 

endclass : blockingNonBlockingTest


`endif // _USER_CDN_AXI_SVE_TEST
