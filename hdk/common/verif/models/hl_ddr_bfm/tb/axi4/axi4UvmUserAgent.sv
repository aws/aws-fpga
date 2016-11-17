
// ****************************************************************************
// Class : axi4UvmUserAgent
// Desc. : This class is used as a basis for the Agents.
//         in cdn_axi VIP the mapped address segments are initially empty,
//         this agent type defines the entire 32bit address range as valid. 
// ****************************************************************************
class axi4UvmUserAgent extends cdnAxiUvmAgent;

	`uvm_component_utils_begin(axi4UvmUserAgent)        
	`uvm_component_utils_end

	`cdnAxiDeclareVif(virtual interface cdnAxi4Interface#(.ID_WIDTH(6), .ADDR_WIDTH(64), .DATA_WIDTH(512)))

	// ***************************************************************
	// Method : new
	// Desc.  : Call the constructor of the parent class.
	// ***************************************************************
	function new (string name = "axi4UvmUserAgent", uvm_component parent = null);
		super.new(name, parent);
	endfunction : new      

endclass : axi4UvmUserAgent
