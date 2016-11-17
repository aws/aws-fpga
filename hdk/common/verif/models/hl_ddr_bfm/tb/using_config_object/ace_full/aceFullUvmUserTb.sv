`timescale 1ps/1ps

`include "uvm_macros.svh"

// Test module
module testbench;

  import uvm_pkg::*;

  // Import the DDVAPI CDN_AXI SV interface and the generic Mem interface
  import DenaliSvCdn_axi::*;
  import DenaliSvMem::*; 

  // Import the VIP UVM base classes
  import cdnAxiUvm::*;  

  // Import the example environment reusable files
  import aceFullUvmUser::*;

  // Includes the Test library
  `include "aceFullUvmUserTests.sv"

  reg aclk;
  reg aresetn;
  
  cdnAceFullInterface#(.DATA_WIDTH(128)) userDutInterface(aclk,aresetn);  
 
  //Toggling the clock
  always #50 aclk = ~aclk;

  //Controlling the reset
  initial
  begin
    aclk = 1'b1;
    aresetn = 1'b1;
    #100;
    aresetn = 1'b0;   
    #5000;
    aresetn = 1'b1;
  end
  

  //setting the virtual interface to the sve and starting uvm.
  initial
  begin
`ifdef CDN_AXI_USING_CLOCKING_BLOCK
    uvm_config_db#(virtual interface cdnAceFullActiveMasterInterface#(.DATA_WIDTH(128)))::set(null,"*activeMaster", "vif", userDutInterface.activeMaster);
    uvm_config_db#(virtual interface cdnAceFullActiveSlaveInterface#(.DATA_WIDTH(128)))::set(null,"*activeSlave", "vif", userDutInterface.activeSlave);
    uvm_config_db#(virtual interface cdnAceFullPassiveInterface#(.DATA_WIDTH(128)))::set(null,"*passiveSlave", "vif", userDutInterface.passiveSlave);
`else    
    uvm_config_db#(virtual interface cdnAceFullInterface#(.DATA_WIDTH(128)))::set(null,"*", "vif", userDutInterface);
`endif
    run_test(); 
  end    

endmodule
