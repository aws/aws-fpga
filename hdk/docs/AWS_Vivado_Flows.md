# AWS Vivado Flows

## Table of Content

1. [Overview](#overview)

2. [IP Integrator Project with Example Design](#ipiprojex)

3. [RTL Project with Example Design](#rtlprojex)

4. [IP Integrator Project - User Project](#ipiprojuser)

5. [RTL Project - Existing RTL](#rtlexist)

6. [RTL Project - New RTL Design](#rtlnew)



<a name="overview"></a>
# Overview  

This document covers top level steps (cheat sheet) for using a particular flow
For step by step instructions refer to the Vivado Tutorials/Examples(./AWS_Vivado_Example_Tutorials.md) documentation.

At this time On-Premise flow is recommended with this environment.

Make sure the HLx Setup Instructions are followed and executed.

<a name="ipiprojex"></a>
Create project directory

start vivado

## Execute example
See what examples are possible, type into TCL console.
aws::make_ipi -examples

### Execute example where synth/impl not run.
Type into TCL console based upon example needed.

aws::make_ipi -examples <example requested>

### Implementing the Design/Tar file

In the Design Runs tab, right click on impl_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.


## Reopening project
Type into TCL console any time reopening the project.

aws::make_ipi

<a name="rtlprojex"></a>
Create project directory

start vivado

## Execute example
See what examples are possible, type into TCL console.
aws::make_rtl -examples

### Execute example where synth/impl not run.
Type into TCL console based upon example needed.

aws::make_rtl -examples <example requested>

### Implementing the Design/Tar file

In the Design Runs tab, right click on impl_1 and select Launch Runs… . Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.


## Reopening project
Type into TCL console any time reopening the project.

aws::make_rtl

<a name="rtlnew"></a>
Create project directory
start vivado

## Create Vivado Project
aws::make_rtl

Add RTL sources, sim sources, constraints.

## Reopening project
Type into TCL console any time reopening the project.

aws::make_rtl



