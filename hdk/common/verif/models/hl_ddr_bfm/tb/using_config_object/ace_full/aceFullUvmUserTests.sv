

`ifndef _MY_ACE_FULL_SVE
`define _MY_ACE_FULL_SVE

// ****************************************************************************
// Class : axiUserSve
// Desc. : This Demo testbench(sve) instantiates the demo env and a virtual sequencer
// ****************************************************************************

class aceFullUvmUserSve extends uvm_env;

  aceFullUvmUserEnv aceFullEnv0;
      
  `uvm_component_utils(aceFullUvmUserSve)
        
  function new(string name = "aceFullUvmUserSve", uvm_component parent);
    super.new(name,parent);
  endfunction // new
   
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    aceFullEnv0 = aceFullUvmUserEnv::type_id::create("aceFullEnv0", this);
		factory.set_type_override_by_type(denaliCdn_axiTransaction::get_type(),aceFullUvmUserTransaction::get_type());
    
  endfunction
         
    
endclass : aceFullUvmUserSve

`endif

class basicTest extends uvm_test;

	aceFullUvmUserSve aceFullSve0;

	`uvm_component_utils_begin(basicTest)
	`uvm_component_utils_end

	function new(string name = "basicTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 

		//set the starting sequences to system      
		uvm_config_db#(uvm_object_wrapper)::set(this, "aceFullSve0.aceFullEnv0.activeMaster.sequencer.run_phase", "default_sequence",userMasterSeq::type_id::get());
		uvm_config_db#(uvm_object_wrapper)::set(this, "aceFullSve0.aceFullEnv0.activeSlave.sequencer.run_phase", "default_sequence",userSnoopSeq::type_id::get());
		
		aceFullSve0 = aceFullUvmUserSve::type_id::create("aceFullSve0", this);

		uvm_top.print_topology();

	endfunction : build_phase

endclass : basicTest


