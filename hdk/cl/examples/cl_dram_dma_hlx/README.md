# CL DRAM DMA Example

## Table of Contents

1. [Overview](#overview)
2. [IPI Flow](#hlx)


<a name="overview"></a>
## Overview

For more information about the cl\_dram\_dma example, read the following information [CL DRAM DMA CL Example](./../cl_dram_dma/README.md)

<a name="hlx"></a>
## HLx Flow for CL Example

### Add in the following system variables for clock recipes and IDs for cl\_dram\_dma example.

export CLOCK\_A\_RECIPE=0

export CLOCK\_B\_RECIPE=0

export CLOCK\_C\_RECIPE=0

export device\_id=0xF001

export vendor\_id=0x1D0F

export subsystem\_id=0x1D51

export subsystem\_vendor\_id=0xFEDC 


### Creating Example Design

Change directories to the cl/examples/cl\_dram\_dma\_hlx directory.

Invoke vivado by typing vivado in the console.

In the TCL console type in the following to create the cl\_dram\_dma example.  The example will be generated in cl/examples/cl\_dram\_dma\_hlx/example_projects.  The vivado project is examples\_projects/cl\_dram\_dma.xpr.

aws::make\_rtl -examples cl\_dram\_dma

### Simulation
Click on Simulation->Run Simulation->Run Behavioral Simulation

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

### Changing Simulation Sources for Tests

cl\_dram\_dma has several simulation sources that can be used for simulation (test\_ddr, test\_dram\_dma, test\_int, test\_peek\_poke, test\_peek\_poke\_pcis\_axsize).  

By default the test\_dram\_dma is used in the project.  To switch tests, right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following name.  Below is an example.

TEST\_NAME=test\_ddr

Click OK, Click Apply, Click OK to back into the Vivado project.

### Implementing the Design/Tar file

In the Design Runs tab, right click on impl\_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_projects/cl\_dram\_dma.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

### CL Example Software

The runtime software must be complied for the AFI to run on F1.  Note the EDMA driver must be installed before running on F1.

Use the software in cl/examples/cl\_dram\_dma

    $ cd cl/cl_dram_dma/software/runtime/
    $ make all
    $ sudo ./test_dram_dma

