
// ****************************************************************************
// Class : axi4UvmUserEnv
// Desc. : This Demo env instantiates: active slave (mimicking DUT)
//         PassiveSlave (to shadow DUT) and a activeMaster (to drive DUT), 
// **************************************************************************** 
class axi4UvmUserEnv extends uvm_env;

  // ***************************************************************
  // The environment instantiates Master and Slave components
  // ***************************************************************
  axi4UvmUserAgent activeMaster;
  axi4UvmUserAgent activeSlave;
  axi4UvmUserAgent passiveSlave;
  axi4UvmUserAgent passiveMaster;

  `uvm_component_utils_begin(axi4UvmUserEnv)          
  `uvm_component_utils_end

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "axi4UvmUserEnv", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new 

  // ***************************************************************
  // Desc.  : Build all of the components of the environment.  The
  //          environment consists one active slave (mimicking DUT)
  //          one PassiveSlave (to shadow DUT) and one activeMaster 
  //          (to drive DUT),
  // ***************************************************************
  virtual function void build_phase(uvm_phase phase);    
    super.build_phase(phase);

    // Active Master
    activeMaster = axi4UvmUserAgent::type_id::create("activeMaster", this);
    begin
      axi4UvmUserConfig activeMasterCfg = axi4UvmUserConfig::type_id::create("activeMasterCfg",this);
      activeMasterCfg.is_active = UVM_ACTIVE;
      activeMasterCfg.PortType = CDN_AXI_CFG_MASTER;
      activeMasterCfg.reset_signals_sim_start = 1;
      activeMasterCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      activeMasterCfg.addToMemorySegments(32'h0,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);        
      set_config_object("activeMaster","cfg",activeMasterCfg);
    end

    // Active Slave
    activeSlave = axi4UvmUserAgent::type_id::create("activeSlave", this);
    begin
      axi4UvmUserConfig activeSlaveCfg = axi4UvmUserConfig::type_id::create("activeSlaveCfg",this);
      activeSlaveCfg.is_active = UVM_ACTIVE;
      activeSlaveCfg.PortType = CDN_AXI_CFG_SLAVE;
      activeSlaveCfg.reset_signals_sim_start = 1;
      activeSlaveCfg.addToMemorySegments(32'h0,32'h1000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      activeSlaveCfg.addToMemorySegments(32'h2000,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);             
      set_config_object("activeSlave","cfg",activeSlaveCfg);
    end

    // Passive Slave
    passiveSlave = axi4UvmUserAgent::type_id::create("passiveSlave", this);    
    begin
      axi4UvmUserConfig passiveSlaveCfg = axi4UvmUserConfig::type_id::create("passiveSlaveCfg");
      passiveSlaveCfg.is_active = UVM_PASSIVE;
      passiveSlaveCfg.PortType = CDN_AXI_CFG_SLAVE;
      passiveSlaveCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      passiveSlaveCfg.addToMemorySegments(32'h0,32'h1000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      passiveSlaveCfg.addToMemorySegments(32'h2000,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      set_config_object("passiveSlave","cfg",passiveSlaveCfg);
    end
    
    // Passive Master
    passiveMaster = axi4UvmUserAgent::type_id::create("passiveMaster", this);    
    begin
      axi4UvmUserConfig passiveMasterCfg = axi4UvmUserConfig::type_id::create("passiveMasterCfg");
      passiveMasterCfg.is_active = UVM_PASSIVE;
      passiveMasterCfg.PortType = CDN_AXI_CFG_MASTER;
      passiveMasterCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      passiveMasterCfg.addToMemorySegments(32'h0,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);  
      set_config_object("passiveMaster","cfg",passiveMasterCfg);
    end

  endfunction : build_phase
  
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      activeMaster.cfg.write_issuing_capability = 6;
      activeMaster.reconfigure(activeMaster.cfg); 
  endtask
  
endclass : axi4UvmUserEnv
