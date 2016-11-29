# Introduction

This example exercises the data movement interfaces from the CL to the Shell. The ./design directory contains all the design source files for cl_simple. The cl_ports.vh file is the port list for a CL and should not be modified. Developers should start with this file for building their CL design. The cl_tst instance in the cl_simple module shows developers how data can be moved into and/or out of PCIe by using the associated AXI interface. There are also cl_tst_scrb instances in the cl_simple module that show developers how data can be moved into and/or out of DDR by using the associated AXI interfaces. The cl_tst module performs Write/Read combinations to the PCIe interface and can verify that the read data matches what was written.  The cl_tst_scrb module includes a cl_tst instance that exercises or clears DDR memory. The cl_simple design does not illustrate how to perform DMA functionality from the instance to the FPGA.

# Simulation

The paths listed in the simulation notes below are all relative to the `aws-fpga/hdk/cl/examples/cl_simple` directory. Two tests are supplied with cl_simple: `test_peek_poke` and `test_ddr`.

To run test_peek_poke, type

```
$ cd verif/scripts
$ make TEST=test_peek_poke
  ...
  [6270000] : Detected   0 errors during this test
  [6270000] : *** TEST PASSED ***
```
  
The results from the test are placed in the `verif/sim/test_peek_poke` directory.

To clean up an existing simulation area (before re-running a test, for example) you can use the clean target. For `test_peek_poke`, the command line is `make clean TEST=test_peek_poke`. Remember to specify the TEST argument to identify which set of existing test results should be removed.

The other test, `test_ddr`, is available uses the code in the ./verif/tests/test_ddr.sv file.  The test writes the registers inside the cl_simple design to issue write and read transactions through the DDR0 interface.

If you want to write a new test, create a file in `verif/tests` with a filename that matches the module name used for the test. Return to `verif/scripts`, and run your test with `make TEST=<module_name>`.

See [Simulating CL Designs](https://github.com/aws/aws-fpga/wiki/Simulating-CL-Designs-%28RTL-Simulation%29)

# Synthesis

[Building CL Designs](https://github.com/aws/aws-fpga/blob/master/hdk/cl/examples/Getting_Started_With_CL_Examples.md#overview-on-process-for-building-a-custom-logic-cl-implementation-for-aws-fpga-instances)

# Validation

