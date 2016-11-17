
// ****************************************************************************
// Class : axi3UvmUserConfig
// Desc. : This class can be created by newPureview or manually by customer
// ****************************************************************************
class axi3UvmUserConfig extends cdnAxiUvmConfig;
    
  `uvm_object_utils_begin(axi3UvmUserConfig)  
  `uvm_object_utils_end
  
  function new(string name = "axi3UvmUserConfig");
    super.new(name);
    spec_ver = CDN_AXI_CFG_SPEC_VER_AMBA3;
    spec_subtype = CDN_AXI_CFG_SPEC_SUBTYPE_BASE;
    spec_interface = CDN_AXI_CFG_SPEC_INTERFACE_FULL;  
  endfunction : new   
  
endclass