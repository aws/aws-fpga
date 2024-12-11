`define PSEUDO
`define PS8G8H
`define NODP
`define INIT_MEM_LOW
`ifdef MODEL_TECH
  `include "HBM_questa.vp"
`elsif INCA
  `include "HBM_nc.vp"
`elsif VCS
  `include "HBM_vcs.vp"
`else
  `include "HBM_xsim.sv"
`endif
