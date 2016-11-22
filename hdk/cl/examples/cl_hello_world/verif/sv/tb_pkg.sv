/**
 * Package: tb_pkg
 * 
 * @TODO: Add package documentation
 */
`ifndef __tb_pkg__
  `define __tb_pkg__

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import i2c_pkg::*;

  `include "fpga_env.svh"
  `include "uvm_i2c_test.svh"

endpackage: tb_pkg

`endif // __tb_pkg__
