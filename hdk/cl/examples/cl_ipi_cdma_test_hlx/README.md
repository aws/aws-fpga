# cl\_ipi\_cdma\_test HLx

## Table of Contents

1. [Overview](#overview)
2. [HLx Flow for CL Example](#hlx)


<a name="overview"></a>
## Overview

The design does the following which simulation and software shows the following behavior.
 
AXIL\_SDA AXI GPIO input connected to DDR4\_A/B/D and SH calibration done signal, processor polls register
 
DMA\_PCIS writes 1K data pattern for DDR4\_SH source buffer

AXIL\_USR sets AXI CDMA for 1K DMA operation from DDR4\_SH to DDR4\_B

AXIL\_USR polls AXI CDMA status register to determine when transfer is complete

DMA\_PCIS reads from destination buffer(DDR4\_B) 1K and compares vs data pattern
 
AXIL\_OCL AXI GPIO output written 16-bits for VLED (16-bit patter of 0xAAAA)

Read from VLED from Verilog task or linux command to read VLED to verify pattern

At this time On-Premise flow is recommended with this environment.

Make sure the [HLx Setup Instructions](../../../docs/AWS_IP_Vivado_Setup.md) are followed and executed.

<a name="hlx"></a>
## HLx Flow for CL Example


### Creating Example Design

Change directories to the cl/examples/cl\_ipi\_cdma\_test\_hlx directory.

Invoke vivado by typing vivado in the console.

In the TCL console type in the following to create the cl\_ipi\_cdma\_test example.  The example will be generated in cl/examples/cl\_ipi\_cdma\_test/example\_projects.  The vivado project is examples\_projects/cl\_ipi\_cdma\_test.xpr.

aws::make\_ipi -examples cl\_ipi\_cdma\_test

Note when closing and opening the project in the future, the following TCL command must be run when the project first opens or an error could show up in simulation/implementation flow.

aws::make\_ipi

Once the Block Diagram is open, review the different IP blocks especially the settings in the AWS IP.

### Simulation

The simulation settings are already configured. However, the following step is necessary.

In the Sources/Hierarchy tab, under sim\_1->IP, disable the 3 IPs for the cl\_ipi\_example design as these IPs are included with the AWS IP.  These IPs are needed when using no DDR4s in the CL for the SH models for DDR4.

Click on Simulation->Run Simulation->Run Behavioral Simulation.

Add signals needed in the simulation.

Type in the following in the TCL console (could take 30 mins to 1 hour based upon machine).

run -all


### Implementing the Design/Tar file

In the Design Runs tab, right click on impl\_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_projects/cl\_ipi\_cdma\_test.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.


### CL Example Software

The runtime software must be complied for the AFI to run on F1.

Copy the software directory to any directory and compile with the following commands.

    $ cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/cl_ipi_cdma_test/software
    $ cd software
    $ make all
    $ sudo ./test_cl

