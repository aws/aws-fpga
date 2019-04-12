# Kernel 3DDR Bandwidth OpenCL Example Runtime


## :exclamation:  NOTE: If this is your first time using F1, To go through the full SDAccel application development flow  you should read [Quick Start Guide to Accelerating your C/C++ application on an AWS F1 FPGA Instance with SDAccel](../../../README.md)

## :exclamation:  NOTE: This only works with Xilinx SDx 2017.4 & 2018.2 versions. This example is deprecated from Xilinx Vivado SDx 2018.3+. For an example demonstrating kernel to global memory transfer using 3DDR configuration and Xilinx SDx 2018.3 please refer to [kernel_global_bandwidth](https://github.com/Xilinx/SDAccel_Examples/tree/master/getting_started/kernel_to_gmem/kernel_global_bandwidth) example.
## Table of Contents

1. [Overview](#overview)
2. [Filelist Description](#description)
3. [Execution](#execute)


<a name="overview"></a>
## Overview

This example is a simple OpenCL application to demonstrate kernel to global memory transfer using a 3 DDR configuration.
You Need to be on F1 Instance to be able to execute this application.

<a name="description"></a>
## Filelist Description

```
src directory -- source files for host application and opencl kernel.
Makefile  -- makefile to  build software emulation, hardware emulation and hardware targets of the opencl kernel and executable for host application
description.json -- json file with application description
README.md
```

<a name="execute"></a>
##COMPILATION AND EXECUTION
### Compiling for Application Emulation
As part of the capabilities available to an application developer, SDAccel includes environments to test the correctness of an application at both a software functional level and a hardware emulated level.
These modes, which are named sw_emu and hw_emu, allow the developer to profile and evaluate the performance of a design before compiling for board execution.
It is recommended that all applications are executed in at least the sw_emu mode before being compiled and executed on an FPGA board.
```
source $AWS_FPGA_REPO_DIR/sdaccel_setup.sh
make TARGETS=<sw_emu|hw_emu> DEVICES=$AWS_PLATFORM all 
```
where
```
  sw_emu = software emulation
  hw_emu = hardware emulation
```
*NOTE:* The software emulation flow is a functional correctness check only. It does not estimate the performance of the application in hardware.
The hardware emulation flow is a cycle accurate simulation of the hardware generated for the application. As such, it is expected for this simulation to take a long time.

### Executing Emulated Application 

The makefile for the application can directly execute the application with the following command:
```
make TARGETS=<sw_emu|hw_emu> DEVICES=$AWS_PLATFORM check

```
where
```
  sw_emu = software emulation
  hw_emu = hardware emulation
```
If the application has not been previously compiled, the check makefile rule will compile and execute the application in the emulation mode selected by the user.

### Compiling for Application Execution in the F1 instance FPGA Accelerator Card
The command to compile the application for execution on the FPGA acceleration board is
```
make TARGET=hw DEVICES=$AWS_PLATFORM all
```
The default target for the makefile is to compile for hardware. Therefore, setting the TARGETS option is not required.
*NOTE:* Compilation for application execution in hardware generates custom logic to implement the functionality of the kernels in an application.
It is typical for hardware compile times to range from 30 minutes to a couple of hours.

### Create an Amazon FPGA Image (AFI) of your kernel
After validating the application & kernel with emulation and compiling your code for FPGA you will need to create AFI for your kernel. Please refer to [Create an Amazon FPGA Image](../../../README.md#2-create-an-amazon-fpga-image-afi)
Once your AFI is ready you can proceed to next step of executing the application on F1 instance.

##Execution

Command sequence

```
sudo fpga-clear-local-image -S 0
 >>$sudo sh
sh-4.2# source $AWS_FPGA_REPO_DIR/sdaccel_runtime_setup.sh
sh-4.2# ./kernel_global

```

