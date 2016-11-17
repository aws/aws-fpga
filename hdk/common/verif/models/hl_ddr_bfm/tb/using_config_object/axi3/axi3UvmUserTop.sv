
`ifndef _MY_CDN_AXI_TOP
`define _MY_CDN_AXI_TOP

`include "uvm_macros.svh"
`include "cdnAxiUvmDefines.sv"

package axi3UvmUser;
  
  import uvm_pkg::*;
  import DenaliSvMem::*;
  import DenaliSvCdn_axi::*;
  import cdnAxiUvm::*;    
  
`include "axi3UvmUserConfig.sv"  
`include "axi3UvmUserAgent.sv"
`include "axi3UvmUserSeqLib.sv"
`include "axi3UvmUserEnv.sv"

endpackage


`endif // _MY_CDN_AXI_TOP
