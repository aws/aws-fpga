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
  import axi4UvmUser::*;

  // Includes the Test library
  `include "axi4UvmUserTests.sv"

  reg aclk;
  reg aresetn;
  
  cdnAxi4Interface#(.DATA_WIDTH(128)) userDutInterface (aclk,aresetn);  
 
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
    uvm_config_db#(virtual interface cdnAxi4Interface#(.DATA_WIDTH(128)))::set(null,"*", "vif", userDutInterface);
    run_test(); 
  end    

endmodule
