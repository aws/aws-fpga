# cl\_hello\_world\_ref

## Table of Contents

1. [Overview](#overview)
2. [IPI Flow](#hlx)


<a name="overview"></a>
## Overview

The cl\_hello\_world\_ref example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and the use of the Virtual LED and DIP switches. The cl\_hello\_world\_ref example implements two registers in the FPGA AppPF BAR0 memory space connected to the OCL AXI-L interface. The two registers are:

1. Hello World Register (offset 0x500)

2. Virtual LED Register (offset 0x504)

The logic for the original cl\_hello\_world example from github is contained in one RTL module (hello\_world.v).  In hello\_world.v, the top level ports are for AXI4Lite interface, clock/reset and ports for VLED and VDIP which allows for IP packaging of the design and reuse with other flows/AXI4Lite Master interfaces.  Note VIO logic is not included with this example from the original cl\_hello\_world example.

<a name="hlx"></a>
## IPI Flow

### Creating Example Design
Change directories to the cl/examples/cl\_hello\_world\_ref\_hlx directory.

Invoke vivado by typing vivado in the console.

In the TCL console type in the following to create the cl\_hello\_world\_ref\_hlx example.  The example will be generated in cl/examples/cl\_hello\_world\_ref\_hlx/example\_projects.  The vivado project is examples\_projects/cl\_hello\_world\_ref.xpr.

aws::make\_ipi -examples cl\_hello\_world\_ref

Click Refresh Changed Modules on the top of Block Design.

Once the Block diagram is open, review the different IP blocks especially the settings in the AWS IP.

The hello\_world RTL is added to the BD and the instance name is hello\_world\_0. The hello\_world.v source is moved in the Sources tab after validating the design under the cl\_hello\_world\_0\_0 IP source.

### Simulation

The simulation settings are already configured. However, the following step is necessary.

Add signals needed in the simulation.

Type in the following in the TCL console.  Note if Critical Warnings appear click OK and that the following command needs to ran two times.  This is a known issue and will be addressed in later versions of the design.

run -all


### Implementing the Design/Tar file

In the Design Runs tab, right click on impl\_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_project/cl\_hello\_world\_ref.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

### CL Example Software

The runtime software must be complied for the AFI to run on F1.

Use the software in cl/examples/cl\_hello\_world

    $ cd cl/cl_hello_world/software/runtime/
    $ make all
    $ sudo ./test_hello_world
