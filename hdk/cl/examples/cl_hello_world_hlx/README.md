# Hello World Example

## Table of Contents

1. [Overview](#overview)
2. [IPI Flow](#hlx)


<a name="overview"></a>
## Overview

For more information about the hello\_world example, read the following information [Hello World CL Example](./../cl_hello_world/README.md)

<a name="hlx"></a>
## IPI Flow

### Add in the following system variables for clock recipes and IDs for cl\_hello\_world example.

export CLOCK\_A\_RECIPE=0

export CLOCK\_B\_RECIPE=0

export CLOCK\_C\_RECIPE=0

export device\_id=0xF000

export vendor\_id=0x1D0F

export subsystem\_id=0x1D51

export subsystem\_vendor\_id=0xFEDD

### Creating Example Design

Change directories to the cl/examples/cl\_hello\_world\_hlx directory.

Invoke vivado by typing vivado in the console.

In the TCL console type in the following to create the cl\_hello\_world example.  The example will be generated in cl/examples/cl\_hello\_world\_hlx/example\_projects.  The vivado project is examples\_projects/cl\_hello\_world.xpr.

aws::make\_rtl -examples cl\_hello\_world

### Simulation

Click on Simulation->Run Simulation->Run Behavioral Simulation

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

### DPI Simulation with test\_hello\_world.c

Right click on SIMULATION in the Project Manager and select Simulation Settings.

For Verilog options select the ... box and modify TEST\_NAME to test_null to disable sv stimulus.

`TEST_NAME = test_null`

In the TCL console in Vivado project, copy and paste the following command to set the path for the creation of the .so with test\_hello\_world.c script

If using 3rd party simulators, modify the command to match the simulator and the path to dpi.tcl instead of dpi_xsim.tcl (see IP Integrator - Frequently Asked Questions documentation in using 3rd party simulators).

`set_property -name {xsim.compile.tcl.pre} -value $::aws::make_faas::_nsvars::script_dir/../../hlx_examples/build/RTL/cl_hello_world/verif/scripts/dpi_xsim.tcl -objects [get_filesets sim_1]`

Right click on SIMULATION in the Project Manager and select Simulation Settings.

In the Elaboration tab, for xsim.elaborate.xelab.more_options add in the following value.  Settings can be different based upon the simulator.

`-sv_lib dpi`

Certain 3rd party simulators might need the explicit include path to the design directory for provided RTL example designs like cl\_hello\_world and cl\_dram\_dma.  For Verilog options select the ... box and click the + button under Verilog Include Files Search Paths.  Select the path to the cl/cl\_example/design directory.

### Implementing the Design/Tar file

In the Design Runs tab, right click on impl\_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_projects/cl\_hello\_world.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

### CL Example Software

The runtime software must be complied for the AFI to run on F1.

Use the software in cl/examples/cl\_hello\_world

    $ cd cl/cl_hello_world/software/runtime/
    $ make all
    $ sudo ./test_hello_world



