This readme provides information about simulation environment for cl_uram_example example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# URAM EXAMPLE CL Example Simulation

The test can be run from the [verif/scripts](scripts) directory with one of four different simulators:

```
    $ make TEST=test_uram_example (Runs with XSIM by default)
    $ make TEST=test_uram_example IES=1
    $ make TEST=test_uram_example VCS=1
    $ make TEST=test_uram_example QUESTA=1
```

The HW/SW co-simulation test can be run from [verif/scripts](scripts) directory with one of four different simulators:

```
    $ make C_TEST=test_uram_example (Runs with XSIM by default)
    $ make C_TEST=test_uram_example VCS=1
    $ make C_TEST=test_uram_example QUESTA=1
    $ make C_TEST=test_uram_example IES=1
```

Note that the appropriate simulators must be installed.

# Dump Waves 

For information about how to dump waves with XSIM, please refer to [debugging-custom-logic-using-the-aws-hdk](../../../../docs/RTL_Simulating_CL_Designs.md#debugging-custom-logic-using-the-aws-hdk)

# Using IPI to run simulations in cl_uram_example example

Xilinx IPI can also be used to simulate cl_hello_world. For information about how to use IPI to simulate cl_hello_world example, please refer to [IPI_GUI_cl_hello_world_example](../../cl_hello_world_hlx/README.md)

# System Verliog Tests

Global counter test. Test below programs different global counter values.

## test_uram_example.sv

This test verifies that the add, find, del functions for URAM.
Please refer the comments in the test as to how each operation can be tested.
HW/SW co-simulation support is also enabled for this test. 

## test_null.sv 

test_null is not a test. This is a system verilog module needed for HW/SW co-simulation.

# HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_uram_example.c](../software/runtime/test_uram_example.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md). 
