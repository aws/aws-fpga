
// ****************************************************************************
// Class : aceFullUvmUserConfig
// Desc. : This class can be created by newPureview or manually by customer
// ****************************************************************************

class aceFullUvmUserConfig extends cdnAxiUvmConfig;
    
  `uvm_object_utils_begin(aceFullUvmUserConfig)  
  `uvm_object_utils_end
  
  function new(string name = "aceFullUvmUserConfig");
    super.new(name);
    spec_interface = CDN_AXI_CFG_SPEC_INTERFACE_FULL;
    spec_subtype = CDN_AXI_CFG_SPEC_SUBTYPE_ACE;
    spec_ver = CDN_AXI_CFG_SPEC_VER_AMBA4;    
  endfunction : new       
  
endclass