
// ****************************************************************************
// Class : axi3UvmUserAgent
// Desc. : This class is used as a basis for the Agents.
//         in cdn_axi vip the mapped address segments are initially empty,
//         this agent type defines the entire 32bit address range as valid. 
// ****************************************************************************
class axi3UvmUserAgent extends cdnAxiUvmAgent;

	`uvm_component_utils_begin(axi3UvmUserAgent)        
	`uvm_component_utils_end

	`cdnAxiDeclareVif(virtual interface cdnAxi3Interface)

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new (string name = "axi3UvmUserAgent", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new      

endclass : axi3UvmUserAgent
