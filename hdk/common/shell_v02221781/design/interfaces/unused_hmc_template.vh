//------------------------------------
// Tie-Off HMC Interfaces
//------------------------------------
  assign hmc_iic_scl_o           =  1'b0;
  assign hmc_iic_scl_t           =  1'b0;
  assign hmc_iic_sda_o           =  1'b0;
  assign hmc_iic_sda_t           =  1'b0;

  assign hmc_sh_stat_ack         =  1'b0;
  assign hmc_sh_stat_rdata[31:0] = 32'b0;

  assign hmc_sh_stat_int[7:0]    =  8'b0;

