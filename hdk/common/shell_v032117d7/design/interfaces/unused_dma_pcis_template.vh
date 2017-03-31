  // PCIe Slave (pcis) Interface from SH to CL
  assign cl_sh_dma_pcis_awready      =   1'b0;

  assign cl_sh_dma_pcis_wready       =   1'b0;

  assign cl_sh_dma_pcis_bid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_bresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_bvalid       =   1'b0;

  assign cl_sh_dma_pcis_arready      =   1'b0;

  assign cl_sh_dma_pcis_rid[5:0]     =   6'b0;
  assign cl_sh_dma_pcis_rdata[511:0] = 512'b0;
  assign cl_sh_dma_pcis_rresp[1:0]   =   2'b0;
  assign cl_sh_dma_pcis_rlast        =   1'b0;
  assign cl_sh_dma_pcis_rvalid       =   1'b0;
