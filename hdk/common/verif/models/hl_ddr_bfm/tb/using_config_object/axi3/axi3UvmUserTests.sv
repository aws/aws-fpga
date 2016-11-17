
`ifndef _USER_CDN_AXI_SVE_TEST
`define _USER_CDN_AXI_SVE_TEST

// ****************************************************************************
// Class : axi3UvmUserSve
// Desc. : This Demo testbench(sve) instantiates the demo env and a virtual sequencer
// ****************************************************************************
class axi3UvmUserSve extends uvm_env;

  axi3UvmUserEnv axiEnv0;
      
  `uvm_component_utils(axi3UvmUserSve)
        
  function new(string name = "axi3UvmUserSve", uvm_component parent);
    super.new(name,parent);
  endfunction // new
   
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    axiEnv0 = axi3UvmUserEnv::type_id::create("axiEnv0", this);   
    
  endfunction
           
endclass : axi3UvmUserSve


class basicTest extends uvm_test;

	axi3UvmUserSve axiSve0;

	`uvm_component_utils_begin(basicTest)
	`uvm_component_utils_end

	function new(string name = "basicTest",uvm_component parent);
		super.new(name,parent); 
	endfunction : new

	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase); 

		//set the starting sequence to system      
		uvm_config_db#(uvm_object_wrapper)::set(this, "axiSve0.axiEnv0.activeMaster.sequencer.run_phase", "default_sequence",userSimpleSeq::type_id::get());

		factory.set_type_override_by_type(denaliCdn_axiTransaction::get_type(),myAxiTransaction::get_type());

		axiSve0 = axi3UvmUserSve::type_id::create("axiSve0", this);

		uvm_top.print_topology();

	endfunction : build_phase

endclass : basicTest

`endif // _USER_CDN_AXI_SVE_TEST
