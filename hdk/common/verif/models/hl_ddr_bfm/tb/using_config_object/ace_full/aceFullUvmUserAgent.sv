
// ****************************************************************************
// Class : axiUserAgent
// Desc. : This class is used as a basis for the Agents.
//         in cdn_axi vip the mapped address segments are initally empty,
//         this agent type defines the entire 32bit address range as valid. 
// ****************************************************************************

class aceFullUvmUserAgent extends cdnAxiUvmAgent;
  
  `uvm_component_utils_begin(aceFullUvmUserAgent)        
  `uvm_component_utils_end
    
 `cdnAxiDeclareVif(virtual interface cdnAceFullInterface#(.DATA_WIDTH(128)))

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new (string name = "aceFullUvmUserAgent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new      

endclass : aceFullUvmUserAgent

class aceFullUvmUserActiveMasterAgent extends aceFullUvmUserAgent;
  
  `uvm_component_utils_begin(aceFullUvmUserActiveMasterAgent)        
  `uvm_component_utils_end
    
`ifdef CDN_AXI_USING_CLOCKING_BLOCK
	`cdnAxiDeclareVif(virtual interface cdnAceFullActiveMasterInterface#(.DATA_WIDTH(128)))
`endif

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new (string name = "aceFullUvmUserActiveMasterAgent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new      

endclass : aceFullUvmUserActiveMasterAgent

class aceFullUvmUserActiveSlaveAgent extends aceFullUvmUserAgent;
  
  `uvm_component_utils_begin(aceFullUvmUserActiveSlaveAgent)        
  `uvm_component_utils_end

`ifdef CDN_AXI_USING_CLOCKING_BLOCK    
	`cdnAxiDeclareVif(virtual interface cdnAceFullActiveSlaveInterface#(.DATA_WIDTH(128)))
`endif

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new (string name = "aceFullUvmUserActiveSlaveAgent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new      

endclass : aceFullUvmUserActiveSlaveAgent

class aceFullUvmUserPassiveSlaveAgent extends aceFullUvmUserAgent;
  
  `uvm_component_utils_begin(aceFullUvmUserPassiveSlaveAgent)        
  `uvm_component_utils_end

`ifdef CDN_AXI_USING_CLOCKING_BLOCK    
	`cdnAxiDeclareVif(virtual interface cdnAceFullPassiveInterface#(.DATA_WIDTH(128)))
`endif

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new (string name = "aceFullUvmUserPassiveSlaveAgent", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new      

endclass : aceFullUvmUserPassiveSlaveAgent
