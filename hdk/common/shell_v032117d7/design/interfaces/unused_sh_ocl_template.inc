  // PCIe Slave (ocl) Interface from SH to CL
  assign ocl_sh_awready             =   1'b0;

  assign ocl_sh_wready              =   1'b0;

  assign ocl_sh_bvalid              =   1'b0;
  assign ocl_sh_bresp[1:0]          =   2'b0;

  assign ocl_sh_arready             =   1'b0;

  assign ocl_sh_rvalid              =   1'b0;
  assign ocl_sh_rdata[31:0]         =  32'b0;
  assign ocl_sh_rresp[1:0]          =   2'b0;

