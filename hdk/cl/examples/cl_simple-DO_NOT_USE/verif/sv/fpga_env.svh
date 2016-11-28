//----------------
// environment env
//----------------
class fpga_env extends uvm_env;

   i2c_agent  m_qspf_i2c_bfm;
   i2c_agent  m_ddr_i2c_bfm;
   i2c_agent  m_hmc_i2c_bfm;

// TODO: Move these into a configuration object
   bit  m_i2c_bfm_is_master = 1'b0;
   bit  m_i2c_bfm_is_active = 1'b1;
   bit  m_i2c_bfm_10bit_addr = 1'b0;

   bit  m_pcie_rq_rc_bfm_is_master = 1'b1;
   bit  m_pcie_rq_rc_bfm_is_active = 1'b1;

   bit  m_pcie_cq_cc_bfm_is_master = 1'b0;
   bit  m_pcie_cq_cc_bfm_is_active = 1'b1;

   virtual i2c_if  m_qspf_i2c_vif;
   virtual i2c_if  m_ddr_i2c_vif;
   virtual i2c_if  m_hmc_i2c_vif;

   `uvm_component_utils(fpga_env)

   function new(string name, uvm_component parent = null);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      i2c_agent_config m_qspf_i2c_bfm_cfg = new("m_qspf_i2c_bfm_cfg");
      i2c_agent_config m_ddr_i2c_bfm_cfg = new("m_ddr_i2c_bfm_cfg");
      i2c_agent_config m_hmc_i2c_bfm_cfg = new("m_hmc_i2c_bfm_cfg");

      super.build_phase(phase);

      m_qspf_i2c_bfm = i2c_agent::type_id::create("m_qspf_i2c_bfm", this);
      m_ddr_i2c_bfm = i2c_agent::type_id::create("m_ddr_i2c_bfm", this);
      m_hmc_i2c_bfm = i2c_agent::type_id::create("m_hmc_i2c_bfm", this);

      m_qspf_i2c_bfm_cfg.configure(
                                   .vif(m_qspf_i2c_vif),
                                   .is_master(m_i2c_bfm_is_master),
                                   .is_active(m_i2c_bfm_is_active),
                                   .address(10'd2),
                                   .ten_bit_addressing(m_i2c_bfm_10bit_addr)
                                  );
      m_qspf_i2c_bfm.configure(m_qspf_i2c_bfm_cfg);

      m_ddr_i2c_bfm_cfg.configure(
                                  .vif(m_ddr_i2c_vif),
                                  .is_master(m_i2c_bfm_is_master),
                                  .is_active(m_i2c_bfm_is_active),
                                  .address(10'h50),
                                  .ten_bit_addressing(m_i2c_bfm_10bit_addr)
                                 );
      m_ddr_i2c_bfm.configure(m_ddr_i2c_bfm_cfg);

      m_hmc_i2c_bfm_cfg.configure(
                                  .vif(m_hmc_i2c_vif),
                                  .is_master(m_i2c_bfm_is_master),
                                  .is_active(m_i2c_bfm_is_active),
                                  .address(10'h50),
                                  .ten_bit_addressing(m_i2c_bfm_10bit_addr)
                                 );
      m_hmc_i2c_bfm.configure(m_hmc_i2c_bfm_cfg);


   endfunction: build_phase

endclass
