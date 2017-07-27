# cl_ipi_cdma_test HLx

## Table of Contents

1. [Overview](#overview)
2. [HLx Flow for CL Example](#hlx)


<a name="overview"></a>
## Overview

The design does the following which simulation and software shows the following behavior.
 
AXIL_SDA AXI GPIO input connected to DDR4_A/B/D and SH calibration done signal, processor polls register
 
DMA_PCIS writes 1K data pattern for DDR4_SH source buffer

AXIL_USR sets AXI CDMA for 1K DMA operation from DDR4_SH to DDR4_B

AXIL_USR polls AXI CDMA status register to determine when transfer is complete

DMA_PCIS reads from destination buffer(DDR4_B) 1K and compares vs data pattern
 
AXIL_OCL AXI GPIO output written 16-bits for VLED (16-bit patter of 0xAAAA)

Read from VLED from Verilog task or linux command to read VLED to verify pattern


<a name="hlx"></a>
## HLx Flow for CL Example


### Creating Example Design

Invoke vivado in the cl/examples/cl_ipi_cdma_test_hlx directory.

In the TCL console type in the following to create the cl_ipi_cdma_test example.  The example will be generated in cl/examples/cl_ipi_cdma_test/example_projects.  The vivado project is examples_projects/cl_ipi_cdma_test.xpr.

aws::make_ipi -examples cl_ipi_cdma_test

Once the Block diagram is open, review the different IP blocks especially the settings in the AWS IP.

### Simulation

The simulation settings are already configured. However, the following step is necessary.

In the Sources tab, under sim_1->IP, disable the 3 IPs for the cl_ipi_example design as these IPs are included with the AWS IP.  These IPs are needed when using no DDR4s in the CL for the SH models for DDR4.

Click on Simulation->Run Simulation->Run Behavioral Simulation.

Add signals needed in the simulation.

Type in the following in the TCL console (could take 30 mins to 1 hour based upon machine).

run -all


### Implementing the Design/Tar file

In the Design Runs tab, right click on impl_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.
