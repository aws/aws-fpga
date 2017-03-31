 // PCIe Master (pcim) Interface from CL to SH
  assign cl_sh_pcim_awid             =  16'b0;
  assign cl_sh_pcim_awaddr           =  64'b0;
  assign cl_sh_pcim_awlen            =   8'b0;
  assign cl_sh_pcim_awsize           =   3'h0;
  assign cl_sh_pcim_awuser           =  19'b0;
  assign cl_sh_pcim_awvalid          =   1'b0;

  assign cl_sh_pcim_wdata            = 512'b0;
  assign cl_sh_pcim_wstrb            =  64'b0;
  assign cl_sh_pcim_wlast            =   1'b0;
  assign cl_sh_pcim_wvalid           =   1'b0;

  assign cl_sh_pcim_bready           =   1'b0;

  assign cl_sh_pcim_arid             =  16'b0;
  assign cl_sh_pcim_araddr           =  64'b0;
  assign cl_sh_pcim_arlen            =   8'b0;
  assign cl_sh_pcim_arsize           =   3'h0;
  assign cl_sh_pcim_aruser           =  19'b0;
  assign cl_sh_pcim_arvalid          =   1'b0;

  assign cl_sh_pcim_rready           =   1'b0;

