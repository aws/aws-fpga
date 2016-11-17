
`ifndef _MY_CDN_AXI_TOP
`define _MY_CDN_AXI_TOP

`include "uvm_macros.svh"
`include "cdnAxiUvmDefines.sv"

package axi4UvmUser;
  
  import uvm_pkg::*;
  import DenaliSvMem::*;
  import DenaliSvCdn_axi::*;
  import cdnAxiUvm::*;    
  
`include "axi4UvmUserConfig.sv"  
`include "axi4UvmUserAgent.sv"
`include "axi4UvmUserSeqLib.sv"
`include "axi4UvmUserEnv.sv"
`include "axi4UvmUserVirtualSequencer.sv"
`include "axi4UvmUserVirtualSeqLib.sv"

endpackage


`endif // _MY_CDN_AXI_TOP
