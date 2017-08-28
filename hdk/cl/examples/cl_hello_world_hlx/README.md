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

Note when closing and opening the project in the future, the following command must be run or error could show up in simulation/implementation.

aws::make\_rtl


### Simulation

Click on Simulation->Run Simulation->Run Behavioral Simulation

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

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



