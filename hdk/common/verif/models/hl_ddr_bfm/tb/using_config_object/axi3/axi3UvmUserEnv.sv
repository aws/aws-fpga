
// ****************************************************************************
// Class : axi3UvmUserEnv
// Desc. : This Demo env instantiates: active slave (mimicking DUT)
//         PassiveSlave (to shadow DUT) and a activeMaster (to drive DUT), 
// **************************************************************************** 
class axi3UvmUserEnv extends uvm_env;

  // ***************************************************************
  // The environment instantiates Master and Slave components
  // ***************************************************************
  axi3UvmUserAgent activeMaster;
  axi3UvmUserAgent activeSlave;
  axi3UvmUserAgent passiveSlave;

  `uvm_component_utils_begin(axi3UvmUserEnv)          
  `uvm_component_utils_end

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "axi3UvmUserEnv", uvm_component parent = null);
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
    activeMaster = axi3UvmUserAgent::type_id::create("activeMaster", this);
    begin
      axi3UvmUserConfig activeMasterCfg = axi3UvmUserConfig::type_id::create("activeMasterCfg",this);
      activeMasterCfg.is_active = UVM_ACTIVE;
      activeMasterCfg.PortType = CDN_AXI_CFG_MASTER;
      activeMasterCfg.reset_signals_sim_start = 1;
      activeMasterCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      activeMasterCfg.addToMemorySegments(32'h0,32'h1000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      activeMasterCfg.addToMemorySegments(32'h2000,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);               
      set_config_object("activeMaster","cfg",activeMasterCfg);
    end

    // Active Slave
    activeSlave = axi3UvmUserAgent::type_id::create("activeSlave", this);
    begin
      axi3UvmUserConfig activeSlaveCfg = axi3UvmUserConfig::type_id::create("activeSlaveCfg",this);
      activeSlaveCfg.is_active = UVM_ACTIVE;
      activeSlaveCfg.PortType = CDN_AXI_CFG_SLAVE;
      activeSlaveCfg.reset_signals_sim_start = 1;
      activeSlaveCfg.addToMemorySegments(32'h0,32'h1000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      activeSlaveCfg.addToMemorySegments(32'h2000,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);             
      set_config_object("activeSlave","cfg",activeSlaveCfg);
    end

    // Passive Slave
    passiveSlave = axi3UvmUserAgent::type_id::create("passiveSlave", this);    
    begin
      axi3UvmUserConfig passiveSlaveCfg = axi3UvmUserConfig::type_id::create("passiveSlaveCfg");
      passiveSlaveCfg.is_active = UVM_PASSIVE;
      passiveSlaveCfg.PortType = CDN_AXI_CFG_SLAVE;
      passiveSlaveCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      passiveSlaveCfg.addToMemorySegments(32'h0,32'h1000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      passiveSlaveCfg.addToMemorySegments(32'h2000,32'h3000,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      set_config_object("passiveSlave","cfg",passiveSlaveCfg);
    end

  endfunction : build_phase
  
  virtual task run_phase(uvm_phase phase);

      super.run_phase(phase);
      begin
        int status;
        activeMaster.cfg.write_issuing_capability = 6;
        activeMaster.cfg.ordering_algorithm = CDN_AXI_CFG_ORDERING_ALGORITHM_FULL_RANDOM;
        activeMaster.reconfigure(activeMaster.cfg);
      end  
  endtask
  
endclass : axi3UvmUserEnv
