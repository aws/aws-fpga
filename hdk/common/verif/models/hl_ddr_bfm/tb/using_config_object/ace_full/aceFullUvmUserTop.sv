
`ifndef _MY_ACE_FULL_TOP
`define _MY_ACE_FULL_TOP

`include "uvm_macros.svh"
`include "cdnAxiUvmDefines.sv"

package aceFullUvmUser;
  
  import uvm_pkg::*;
  import DenaliSvMem::*;
  import DenaliSvCdn_axi::*;
  import cdnAxiUvm::*;    
  
`include "aceFullUvmUserConfig.sv"  
`include "aceFullUvmUserAgent.sv"
`include "aceFullUvmUserSeqLib.sv"
`include "aceFullUvmUserEnv.sv"


endpackage


`endif // _MY_ACE_FULL_TOP
