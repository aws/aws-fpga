# Vivado HLx AWS Tutorials and Examples

## Table of Content

1. [Overview](#overview)

2. [IP Integrator Examples Prepackaged](#ipiex)

3. [RTL Examples Prepackaged](#rtlex)

4. [IP Integrator Example Tutorial](#ipitut)

5. [IP Integrator Design Modular Reference Tutorial](#ipimodtut)

6. [Adding Existing RTL Tutorial-cl_hello_world](#rtlexistut_world)

7. [Adding Existing RTL Tutorial-cl_dram_dma](#rtlexistut_dram)

8. [Adding/Existing/Modifying VHDL Tutorial](#rtl_vhdl_existut)

9. [Starting from Scratch RTL Design](#rtlscrtut)



<a name="overview"></a>
# Overview  

This document covers examples provided through the HLx environment and step by step tutorials
with certain flows.

Make sure the HLx Setup Instructions are followed before using any of these examples.


<a name="ipiex"></a>
# IP Integrator Examples Prepackage

## Overview

This section covers using a precanned IP Integrator example designs with Vivado.

Current examples are the following. Select the link below for information on the design and how to create the particular example design.

[cl_hello_world_hlx](../cl/examples/cl_hello_world_hlx/README.md)
[cl_dram_dma_hlx](../cl/examples/cl_dram_dma_hlx/README.md)
[cl_ipi_cdma_test_hlx](../cl/examples/cl_ipi_cdma_test_hlx/README.md)

<a name="rtlex"></a>
# RTL Examples Prepackage

## Overview

This section covers using a precanned RTL example design with Vivado.  The examples are from the cl/examples directory for cl_hello_world and cl_dram_dma.

Current examples are the following. Select the link below for information on the design and how to create the particular example design.

[cl_hello_world_hlx](../cl/examples/cl_hello_world_hlx/README.md)
[cl_dram_dma_hlx](../cl/examples/cl_dram_dma_hlx/README.md)


<a name="rtlexistut_world"></a>
# Adding Example RTL Tutorial-cl_hello_world

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project.  This example uses cl_hello_world from the github examples directory.


## Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl_hello_world_vivado

Change directories into cl_hello_world_vivado/


For the clock recipes and IDs set the following system variables (these match cl_hello_world example).

export CLOCK_A_RECIPE=0

export CLOCK_B_RECIPE=0

export CLOCK_C_RECIPE=0

export device_id=0xF000

export vendor_id=0x0001

export subsystem_id=0x1D51

export subsystem_vendor_id=0xFEDD


Start vivado by typing vivado in the console.

Type in the following to create a generic project.

create_project -name cl_hello_world

To setup the project for RTL mode, type in the following command.

aws::make_rtl

## Adding existing RTL sources (cl_hello_world)
Follow the Import Only instructions to not add the sources to the Vivado project.

Follow The Copy to Project instructions to add the sources to the Vivado project for possible modification of sources.

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the cl/examples/cl_hello_world/design directory. 
Add the cl/examples/common/design directory.

Select Scan and add RTL includes files into project

### Import Only
Deselect Copy sources into project to link to the source files.
### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.

Select Add sources from subdirectories.

## Add simulation sources from example design (cl_hello_world)

Add or create simulation sources.  Select Add Files.
Add the <cl_dir>/verif/tests/test_hello_world.sv

Deselect Scan and add RTL includes files into project

### Import Only
Deselect Copy sources into project to link to the source files.
### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.

Select Add sources from subdirectories.
Select all design sources for simulation.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names.

CL_NAME=cl_hello_world
TEST_NAME=test_hello_world

Click OK, Click Apply, Click OK to back into the Vivado project.

## Running Simulation
Select  Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

## Adding constraints from example design (cl_hello_world)
### Option 1
Constraints can be copied and pasted from opening the original XDCs in a text editor and copying the constraints into the project .xdc files.

For cl_hello_world, copy the following into the cl_pnr_user.xdc in the Source->Constraints->cl_pnr_user.xdc.  Note this is only for cl_hello_world.

set_false_path -from [get_cells CL/vled_q_reg*]

### Option 2
Overriding the .xdc in the vivado project.

cl_synth_user.xdc/cl_pnr_user.xdc can be copied over from the /build/constraints area to the imported area of the vivado project like the following.

<example_design>/build/constraints/ to <project_name>.srcs/constrs_1/imports/subscripts

### Option 3
Deleting the existing .xdc in the vivado project and import constraints or copy constraints into Vivado project. 

Delete cl_synth_user.xdc and cl_pnr_user.xdc in the Source->Constraints tab.

In Flow Navigator select Add Sources and select Add or create constraints.

For cl_synth_user.xdc and cl_pnr_user.xdc select the minus (-) button.  Select Add Files and go to the hdk/cl/examples/<cl_example>/build/constraints directory.  Select cl_pnr_user.xdc and cl_synth_user.xdc.

#### Import Only
Deselect Copy constraints files into project to link to the source files.

#### Copy to Project 
Select Copy constraints files into project to add the source files to local vivado project.

In the Sources/Hierarchy Tab, select cl_pnr_user.xdc and go to Source File Properties.
Under the General Tab, deselect Enabled and select Implementation Box only.
In Properties Tab, select PROCESSING_ORDER to be LATE.

## Implementing the Design/Tar File
Right click on impl_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas_1/build/checkpoints/to_aws/<timestamp>.Developer_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

<a name="rtlexistut_dram"></a>
# Adding Example RTL Tutorial-cl_dram_dma

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project.  This example uses cl_dram_dma from the github examples directory.

Make sure the HLx Setup Instructions are followed before continuing.

## Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl_dram_dma_vivado

Change directories into cl_dram_dma_vivado/

For the clock recipes and IDs set the following system variables (these match cl_dram_dma example).

export CLOCK_A_RECIPE=0

export CLOCK_B_RECIPE=0

export CLOCK_C_RECIPE=0

export device_id=0xF001

export vendor_id=0x1D0F

export subsystem_id=0x1D51

export subsystem_vendor_id=0xFEDC


Start vivado by typing vivado in the console.

Type in the following to create a generic project.

create_project -name cl_dram_dma

To setup the project for RTL mode, type in the following command.

aws::make_rtl

## Adding existing RTL sources (cl_dram_dma)
Follow the Import Only instructions to not add the sources to the Vivado project.
Follow The Copy to Project instructions to add the sources to the Vivado project for possible modification of sources.

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the cl/examples/cl_dram_dma/design directory. 
Add the cl/examples/common/design directory.

Select Scan and add RTL includes files into project

### Import Only
Deselect Copy sources into project to link to the source files.
### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.

Select Add sources from subdirectories.

## Add simulation sources from example design (cl_dram_dma)
cl_dram_dma example has several system verilog tests (test_ddr.sv, test_dram_dma.sv, test_ini.sv, test_peek_poke.sv, test_peek_poke_pcis_axsize.sv).

Add or create simulation sources.  Select Add Files and individually add in the .sv files needed.

Add the <cl_dir>/verif/tests/<tests_to_add>.sv

Deselect Scan and add RTL includes files into project

### Import Only
Deselect Copy sources into project to link to the source files.
### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.

Select Add sources from subdirectories.

Select all design sources for simulation.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names.

CL_NAME=cl_dram_dma

For TEST_NAME choose the name of the .sv used (don’t put .sv at the end of the line).

Below is an example.

TEST_NAME=test_dram_dma

Click OK, Click Apply, Click OK to back into the Vivado project.

## Running Simulation
Select  Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

## Adding constraints from example design (cl_dram_dma)

### Option 1
Constraints can be copied and pasted from opening the original XDCs in a text editor and copying the constraints into the project .xdc files.

### Option 2
Overriding the .xdc in the vivado project.

cl_synth_user.xdc/cl_pnr_user.xdc can be copied over from the /build/constraints area to the imported area of the vivado project like the following.

<example_design>/build/constraints/ to <project_name>.srcs/constrs_1/imports/subscripts

### Option 3
Deleting the existing .xdc in the vivado project and import constraints or copy constraints into Vivado project. 

Delete cl_synth_user.xdc and cl_pnr_user.xdc in the Source->Constraints tab.

In Flow Navigator select Add Sources and select Add or create constraints.

For cl_synth_user.xdc and cl_pnr_user.xdc select the minus (-) button.

Select Add Files and go to the hdk/cl/examples/<cl_example>/build/constraints directory.

Select cl_pnr_user.xdc and cl_synth_user.xdc.

#### Import Only
Deselect Copy constraints files into project to link to the source files.

#### Copy to Project 
Select Copy constraints files into project to add the source files to local vivado project.

In the Sources/Hierarchy Tab, select cl_pnr_user.xdc and go to Source File Properties.
Under the General Tab, deselect Enabled and select Implementation Box only.
In Properties Tab, select PROCESSING_ORDER to be LATE.

## Implementing the Design
Right click on impl_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

<a name="rtlscrtut"></a>

# Starting from Scratch RTL Design

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project.  This example uses cl_dram_dma from the github examples directory.

Make sure the HLx Setup Instructions are followed before continuing.

##Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl_template or the proposed design name.

Change directories into cl_template/

For the clock recipes and IDs set the following system variables which are defaults.
These values can be changed later either in the bash shell or in Vivado based upon the design's needs.

export CLOCK_A_RECIPE=0

export CLOCK_B_RECIPE=0

export CLOCK_C_RECIPE=0

export device_id=0xF000

export vendor_id=0x0001

export subsystem_id=0x1D51

export subsystem_vendor_id=0xFEDD


Start vivado by typing vivado in the console.

Type in the following to create a generic project (change the project name to the proposed design name).

create_project -name cl_template

To setup the project for RTL mode, type in the following command.

aws::make_rtl

## Adding existing RTL template sources

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the hdk/common/shell_stable/new_cl_template/design directory.  

Select Scan and add RTL includes files into project

Select Copy sources into project to add the source files to local vivado project.  The templates are stored in the local vivado project and can be modified in Vivado or a text editor.

Select Add sources from subdirectories.

### Template Overview
cl_template_defines.vh – Verilog header file where user puts in `define based upon the design.
cl_template.sv – Top level file where user adds in logic, modules and `include .inc files to disable interfaces not used in the shell.

### Include files
If certain shell interfaces are not enabled, the user needs to use the .inc provided in HDK to disable the interface in cl_template.sv.  See the example designs for examples on using these .inc files.

### Add Existing RTL
In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the directories or files needed.

Select Scan and add RTL includes files into project

#### Import Only
Deselect Copy sources into project to link to the source files.
#### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.

### Adding/Importing IP
To add new IP to the design, select IP Catalog, find the particular IP and configure, and generate with Global synthesis mode (Out of Context is not supported at this time).  The template .vho/.veo can be used to insert the IP into the RTL.

To import IP do the following.

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources.

Add the XCI file of the IP or IPs.  Make sure to generate with Global synthesis mode (Out of Context is not supported at this time).

#### Import Only
Deselect Copy sources into project to link to the source files.
#### Copy to Project 
Select Copy sources into project to add the source files to local vivado project.



Adding simulation sources from template System Verilog

Work in process 

Simulation/system behavior should be verified before attempting the implementation flows.

Modifying Constraints

The following files are added to the vivado project automatically.

cl_clocks_aws.xdc – Top level clock constraints for the CL.  This file should not be touched as it's dynamically created during the synthesis process.

cl_synth_aws.xdc - Timing constraints between sh_ddr module and DDR4 IP. This file should be disabled in the Vivado project if no DDR4 instances are in the CL.

cl_synth_user.xdc – User can modify this file for the the CL for synthesis (I.E creating new clock structures with clock generator/using clocks in different Shell MMCM).

cl_pnr_user.xdc – User can modify this file for constraints between the CL/SH for implementation(place/route).  Floorplanning is done in this file if necessary.


Implementing the Design
Right click on impl_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.
