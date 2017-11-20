# hello\_world IP Integrator Example

## Table of Contents

1. [Overview](#overview)
2. [CL Example](#hlx)


<a name="overview"></a>
## Overview

This IP Integrator design contains the AWS IP configured for BAR1 Interface (AXI4Lite Master Interface) for AXI GPIO to control the VLED and the PCIS Interface (AXI4 Master) to write and read into the AXI BRAM located in the CL.

The VLED is set based upon writing 0xAAAA into the AXI GPIO (0x0) slave register to drive VLED.  The value is read using the Verilog task tb.get\_virtual\_led or fpga-get-virtual-led on F1.

The PCIS Interfaces writes ASCII data into the AXI BRAM memory space and reads back from these address to print out “Hello World!” in simulation or on F1.

Make sure the [HLx Setup Instructions](../../../../hdk/docs/IPI_GUI_Vivado_Setup.md) are followed and executed.

<a name="hlx"></a>
## CL Example


### Creating Example Design

Change directories to the cl/examples/hello\_world\_hlx directory.

Invoke vivado by typing `vivado`, once the GUI has loaded click Tcl Console.

In the TCL console type in the following to create the hello\_world\_hlx example.  The example will be generated in cl/examples/hello\_world\_hlx/example\_projects.  The vivado project is examples\_projects/hello\_world.xpr.

aws::make\_ipi -examples hello\_world

Once the Block diagram is open, review the different IP blocks especially the settings in the AWS IP.

### Simulation

The simulation settings are already configured. From the flow navigator, run simulation.  

Type in the following in the TCL console.  Note if Critical Warnings appear click OK and that the following command needs to ran two times.  This is a known issue and will be addressed in later versions of the design.

run -all

### Implementing the Design/Tar file

In Flow Navigator, select Project Manager, find Design Runs tab, right click on impl\_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_projects/hello_world.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

### CL Example Software

The runtime software must be complied for the AFI to run on F1.

Copy the software directory to any directory and compile with the following commands.

    $ cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/hello_world/software
    $ cd software
    $ make all
    $ sudo ./test_cl
