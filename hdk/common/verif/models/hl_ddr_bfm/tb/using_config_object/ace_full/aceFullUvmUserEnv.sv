
// ****************************************************************************
// Class : aceFullUvmUserEnv
// Desc. : This Demo env instantiates: active slave (mimicking DUT)
//         PassiveSlave (to shadow DUT) and a activeMaster (to drive DUT), 
// **************************************************************************** 

class aceFullUvmUserEnv extends uvm_env;

  // ***************************************************************
  // The environment instantiates Master and Slave components
  // ***************************************************************
  aceFullUvmUserActiveMasterAgent activeMaster;
  aceFullUvmUserActiveSlaveAgent activeSlave;
  aceFullUvmUserPassiveSlaveAgent passiveSlave;
  	
  `uvm_component_utils_begin(aceFullUvmUserEnv)          
  `uvm_component_utils_end

  // ***************************************************************
  // Method : new
  // Desc.  : Call the constructor of the parent class.
  // ***************************************************************
  function new(string name = "aceFullUvmUserEnv", uvm_component parent = null);
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
    activeMaster = aceFullUvmUserActiveMasterAgent::type_id::create("activeMaster", this);
    begin
      aceFullUvmUserConfig activeMasterCfg = aceFullUvmUserConfig::type_id::create("activeMasterCfg",this);
      activeMasterCfg.is_active = UVM_ACTIVE;
      activeMasterCfg.PortType = CDN_AXI_CFG_MASTER;
      activeMasterCfg.cache_line_size = 64;
      activeMasterCfg.reset_signals_sim_start = 1;
      activeMasterCfg.verbosity = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      activeMasterCfg.addToMemorySegments(64'h0,64'h1fff,CDN_AXI_CFG_DOMAIN_INNER);
      activeMasterCfg.addToMemorySegments(64'h2000,64'h3fff,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
                
      set_config_object("activeMaster","cfg",activeMasterCfg);
    end

    // Active Slave
    activeSlave = aceFullUvmUserActiveSlaveAgent::type_id::create("activeSlave", this);
    begin
      aceFullUvmUserConfig activeSlaveCfg = aceFullUvmUserConfig::type_id::create("activeSlaveCfg",this);
      activeSlaveCfg.is_active = UVM_ACTIVE;
      activeSlaveCfg.PortType = CDN_AXI_CFG_SLAVE;
      activeSlaveCfg.cache_line_size = 64;
      activeSlaveCfg.reset_signals_sim_start = 1;
      activeSlaveCfg.addToMemorySegments(64'h0,64'h1fff,CDN_AXI_CFG_DOMAIN_INNER); 
      activeSlaveCfg.addToMemorySegments(64'h2000,64'h3ffff,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);             
      
      set_config_object("activeSlave","cfg",activeSlaveCfg);
    end


    // Passive Slave
    passiveSlave = aceFullUvmUserPassiveSlaveAgent::type_id::create("passiveSlave", this);    
    begin
      aceFullUvmUserConfig passiveSlaveCfg        = aceFullUvmUserConfig::type_id::create("passiveSlaveCfg");
      passiveSlaveCfg.is_active                   = UVM_PASSIVE;
      passiveSlaveCfg.PortType                    = CDN_AXI_CFG_SLAVE;
      passiveSlaveCfg.cache_line_size             = 64;
      passiveSlaveCfg.verbosity                   = CDN_AXI_CFG_MESSAGEVERBOSITY_LOW;
      passiveSlaveCfg.addToMemorySegments(64'h0,64'h1fff,CDN_AXI_CFG_DOMAIN_INNER);
      passiveSlaveCfg.addToMemorySegments(64'h2000,64'h3ffff,CDN_AXI_CFG_DOMAIN_NON_SHAREABLE);
      
      set_config_object("passiveSlave","cfg",passiveSlaveCfg);
    end


  endfunction : build_phase
  
  virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      begin
        	activeSlave.cfg.snoop_issuing_capability = 3;
        	activeSlave.cfg.update_memory_for_error_snoop_response = 1;
        	activeSlave.reconfigure(activeSlave.cfg);
          
        activeMaster.cfg.write_issuing_capability  = 6;
          activeMaster.reconfigure(activeMaster.cfg);
      end    
  endtask


endclass : aceFullUvmUserEnv
