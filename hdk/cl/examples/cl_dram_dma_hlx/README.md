# CL DRAM DMA CL Example HLx

## Table of Contents

1. [Overview](#overview)
2. [HLx Flow for CL Example](#hlx)


<a name="overview"></a>
## Overview

For more information about the cl_dram_dma example, read the following information[CL DRAM DMA CL Example](./../cl_dram_dma/README.md)


<a name="hlx"></a>
## HLx Flow for CL Example

### Add in the following system variables for clock recipes and IDs for cl_dram_dma example.

export CLOCK_A_RECIPE=0

export CLOCK_B_RECIPE=0

export CLOCK_C_RECIPE=0

export device_id=0xF001

export vendor_id=0x1D0F

export subsystem_id=0x1D51

export subsystem_vendor_id=0xFEDC 


### Creating Example Design

Invoke vivado in the cl/examples/cl_dram_dma_hlx directory.

In the TCL console type in the following to create the cl_dram_dma example.  The example will be generated in cl/examples/cl_dram_dma_hlx/example_projects.  The vivado project is examples_projects/cl_dram_dma.xpr.

aws::make_rtl -examples cl_dram_dma

### Simulation
Click on Simulation->Run Simulation->Run Behavioral Simulation

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

### Changing Simulation Sources for Tests

cl_dram_dma has several simulation sources that can be used for simulation (test_ddr, test_dram_dma, test_int, test_peek_poke, test_peek_poke_pcis_axsize).  

By default the test_dram_dma is used in the project.  To switch tests, right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following name.  Below is an example.

TEST_NAME=test_ddr

Click OK, Click Apply, Click OK to back into the Vivado project.

### Implementing the Design/Tar file

In the Design Runs tab, right click on impl_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.
