This readme provides information about the simulation environment for the cl_hello_world example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# Hello World CL Example Simulation

The test can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make TEST=test_hello_world (Runs with XSIM by default)
    $ make TEST=test_hello_world IES=1
    $ make TEST=test_hello_world VCS=1
    $ make TEST=test_hello_world QUESTA=1
```

The HW/SW co-simulation test can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make C_TEST=test_hello_world (Runs with XSIM by default)
    $ make C_TEST=test_hello_world VCS=1
    $ make C_TEST=test_hello_world QUESTA=1
    $ make C_TEST=test_hello_world IES=1
```

Note that the appropriate simulators must be installed.

# Dump Waves 

For information about how to dump waves with XSIM, please refer to the section [debugging-custom-logic-using-the-aws-hdk](../../../../docs/RTL_Simulating_CL_Designs.md#debugging-custom-logic-using-the-aws-hdk)

# System Verliog Tests

The system verilog tests can be found at [verif/tests](tests). Below is the information about each test.

## test_gl_cntr.sv

Global counter test. Test programs and checks different global counter values.

## test_hello_world.sv

A basic test that exercises the Hello World Register as well as the Virtual LED Register. It also includes a test that programs global counter in shell model. The test writes a value to the Hello World Register and then reads it back. Additionally, it reads the Virtual LED register.

## test_null.sv 

test_null is not a test. This is a system verilog module needed for HW/SW co-simulation.

# HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_hello_world.c](../software/runtime/test_hello_world.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md). 

# Using IPI to run simulations in cl_hello_world example

Xilinx IPI can also be used to simulate cl_hello_world. For information about how to use IPI to simulate cl_hello_world example, please refer to [IPI_GUI_cl_hello_world_example](../../cl_hello_world_hlx/README.md)
