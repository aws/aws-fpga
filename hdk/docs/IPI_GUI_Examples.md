# GUI Workflow with Vivado IP Integrator Quickstart Examples

## Table of Content

1. [Overview](#overview)

2. [IP Integrator Examples](#ipiex)

3. [CL Examples using IP Integrator](#rtlex)

4. [IP Integrator Example with AXI GPIO/AXI BRAM](#ipitut)

5. [IP Integrator Design Modular Reference Tutorial-hello\\_world](#ipimodtut)

6. [IP Integrator Example using HLS IP (DDS)](#ipitut_hls)

7. [Adding Existing RTL Tutorial-cl\\_hello\\_world](#rtlexistut_world)

8. [Adding Existing RTL Tutorial-cl\\_dram\\_dma](#rtlexistut_dram)

9. [Starting from Scratch RTL Design](#rtlscrtut)



<a name="overview"></a>
# Overview  

This document is an overview of the IP Integrator examples provided through the HLx environment.

Prior to starting you should have completed [Vivado Setup Instructions](./IPI_GUI_Vivado_Setup.md) to help setup and get familar with the Vivado GUI and IP Integrator.

All of the examples have been integrated into an automated flow that automatically generates the Vivado project.

<a name="ipiex"></a>
# IP Integrator Examples

This section covers IP Integrator example designs that can help you get familar with the automated project generation flow and IP Integrator.

Current examples include the following:

[hello\\_world](../cl/examples/hello\_world\_hlx/README.md)

[cl\\_ipi\\_cdma\\_test](../cl/examples/cl\_ipi\_cdma\_test\_hlx/README.md)

[cl\\_hls\\_dds](../cl/examples/cl\_hls\_dds\_hlx/README.md)

[cl\\_hello\\_world\\_ref](../cl/examples/cl\_hello\_world\_ref\_hlx/README.md)


Select the above link for detailed information on the design and how to get started with using that design.


<a name="rtlex"></a>
# CL Examples using IP Integrator

The following CL examples cover using an automated RTL example design with Vivado.  The examples are based on the HDK cl/examples directory (ex: cl\_hello\_world and cl\_dram\_dma).

Current examples include the following:

[cl\\_hello\\_world](../cl/examples/cl\_hello\_world\_hlx/README.md)

[cl\\_dram\\_dma](../cl/examples/cl\_dram\_dma\_hlx/README.md)

Select the above link for detailed information on the design and how to get started with using that design.


<a name="ipitut"></a>
# IP Integrator Example Tutorial with AXI GPIO and AXI BRAM (hello\_world)

The IPI example turtorial will cover how to configure the AWS IP with the BAR1 Interface (AXI4-Lite Master Interface) and the PCIS Interface (AXI4 Master). 

The AXI GPIO IP is added to the design to control the VLED.  Also, the AXI BRAM is added to the design for the PCIS Interface (AXI4 Master).

The VLED is set based upon writing 0xAAAA into the AXI GPIO (0x0) slave register to drive VLED.  The value is read using the Verilog task tb.get\_virtual\_led or fpga-get-virtual-led on F1.

The PCIS Interfaces writes ASCII data into the AXI BRAM memory space and reads back from these address to print out “Hello World!” in simulation or on F1.

## Create Directory Structure and Vivado Project 

Change directories to hdk/cl/examples

Create a directory in examples like hello\_world\_vivado

Change directories into hello\_world\_vivado/

Start Vivado by typing vivado in the bash console.

Create a project any device by typing the following command in Vivado's TCL Tab.

create\_project -name hello\_world

Type in the following TCL command which changes the project settings for AWS and creates the block diagram with the AWS IP added.

aws::make\_ipi


## Configuring the Block Diagram


### Configuring AWS IP

Double click on the AWS IP block.  Under IP Interfaces select Use BAR1 Register Interface (M\_AXI\_BAR1), Use PCI Slave-access Interface (M\_AXI\_PCIS), and Use Auxiliary (non-AXI) Signal Ports.  This enables the AXI4-Lite Master Interface (for AXI GPIO), AXI4 Master Interface (for AXI BRAM) and the VLED/VDIP input/outputs.  Select OK.

The AWS IP is configured for one clock using the Group-A Clock with the default clock recipe which configures a 125 MHz clock.

### Adding/Configuring AXI GPIO

Right click in the canvas and select Add IP...  Search for AXI GPIO and double click on AXI GPIO.

In the canvas for axi\_gpio\_0, double click on the block to configure the IP.

In the Re-customize IP Dialog Box, under the GPIO section select All Outputs and GPIO Width of 16. Select OK.

### Adding/Configuring AXI BRAM

Right click in the canvas, and select Add IP...  Search for AXI BRAM and double click on AXI BRAM Controller.

In the canvas for axi\_bram\_ctrl\_0, double click on the block to configure the IP.

Set the Data Width to 512 and click OK.  This is to match the 512-bit data width of the PCIS AXI4 Master Interface.

### Connecting the Design
Select Run Connection Automation at the top of the Block Diagram in the green highlighted section.

Select axi\_bram\_ctrl\_0/BRAM\_PORTA and then BRAM\_PORTB and select Auto.  For axi\_bram\_ctrl\_0/S\_AXI, make sure Master is set to /f1\_inst/M\_AXI\_PCIS and the rest of the options are Auto.

Select axi\_gpio\_0/S\_AXI.  Make sure Master is set to /f1\_inst/M\_AXI\_BAR1 and the rest of the options are Auto.

The axi\_gpio\_0/GPIO will be manually configured after Run Connection Automation.

Select OK.

Expand axi\_gpio\_0/GPIO by select the +.  Connect gpio\_io\_o[15:0] on the f1\_inst block and make a connection to status\_vled[15:0] and Run Connection Automation.

### Address Editor Tab
Select the Address Editor tab on top of the block diagram.

The AXI BRAM instance is configured with 64K address space by default starting at address 0xC0000000.  The address space can be increased or decreased by selecting a different value for Range.

The AXI GPIO instance has a 4K address space which is reflected in the addressing for M\_AXI\_BAR1 which starts at 0x00000000.

### Saving and Validating the Design

Save the block diagram and select Tools->Validate Design.

Select OK Once Validation is successful.

## Add simulation sources from example design (cl\_hello\_world)

In the Flow Navigator tab/Project Manager select Add Sources ->  Add or create simulation sources ->  Select Add Files.

Add the hdk/common/shell\_stable/hlx/hlx\_examples/build/IPI/hello\_world/verif/test\_cl.sv

Deselect Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

Select Add sources from subdirectories.

Select Include all design sources for simulation.  Then click Finish.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names (should already be configured).

CL\_NAME=cl\_top

TEST\_NAME=test\_cl

Click OK, Click Apply, Click OK to go back into the Vivado project.

## Running Simulation
Select Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.  Note if Critical Warnings appear click OK and  the following command needs to run two times.  This is a known issue and will be addressed in later versions of the design.

run -all

## Adding Constraints for Design

No additional constraints are needed for this design.


## Implementing the Design/Tar File

Right click on impl\_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.


## CL Example Software

The runtime software must be compiled for the AFI to run on F1.

Copy the software directory to any directory and compile with the following commands.

    $ cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/hello_world/software
    $ cd software
    $ make all
    $ sudo ./test_cl

<a name="ipitut_hls"></a>

# IP Integrator Example Tutorial with HLS IP (DDS)

The DDS IP described in XAPP1299  is connected to AWS F1  IP where BAR1 is used for control of the IP and DDR-C (shell DDR) is the memory used for the two AXI Master outputs of the IP(sine and cosine wave generation with 1024 samples).  The host reads back the values written into the memory (simulation-one address read/software-all data written into a text file sine.txt/cosine.txt located in /home/centos ).  Refer to XAPP1299 application note for more details about the IP generated by C code through HLS.

The HLS IP is stored in the hdk/common/shell\_v071417d3/hlx/design/ip directory.  Generated IPs should following the same structure as this HLS IP and extracted in the correct directory structure for the Vivado repository to pick up the IP.

## Create Directory Structure and Vivado Project 

Invoke vivado

Change directories where the project will be stored.  Create a new project with the following command.  

create\_project -name cl\_hls\_dds

Then create the base IPI design with the following command.

aws::make\_ipi

## Configuring the Block Diagram


### Configuring AWS IP

In the Block Diagram, double click on f1\_inst and select the appropriate settings for the AWS IP based upon system for the HLS IP.  In this case, select Use DDR4-C in Shell, select Use PCI Slave-access Interface (M\_AXI\_PCIS), and select Use BAR1 Register Interface (M\_AXI\_BAR1).  Under Clock Signals, for Number of Group-A Clocks select 2 and for Group-A Clock Recipe select 1 for 250 MHz for clk\_main\_a0 and 125 MHz for clk\_extra\_a1.  Click OK.

### Adding AXI GPIO and DDS IP

In the diagram, right click and select Add IP… and search for the HLS IP which is DDS and select the DDS IP.  Right click in the Diagram and Select Add IP ... and add AXI GPIO.

### Configuring AXI GPIO

Double click on the added AXI GPIO instance.  Under the GPIO section, select All Inputs and set GPIO Width to 1.  Click OK.

### Configuring DDS IP

Double click on the DDS IP instance.  Select the Data width to 512.  Note this selection will be done two times for the two AXI Masters under the ID width parameter.  For the first Base Address of target slave enter in 0x81000000 and for the second Base address of target slave enter in 0x82000000.  Click OK.

### Connecting the Design Part 1
Select Run Connection Automation at the top of the Block Diagram in the green highlighted section.

Select S\_AXI under axi\_gpio\_0.  For Clock source for Slave interface select  /f1\_inst/clk\_extra\_a1\_out (125 MHz).  Leave the rest of the options Auto.

Select s\_axi\_PROG\_BUS under dds\_0.  Leave all the options set to Auto.  

Select S\_AXI\_DDRC and select Crossbar clock source of Interconnect IP to  /f1\_inst/clk\_extra\_a0\_out (250 MHz).  Select OK.

In the Diagram Tab, select Run Connection Automation again.  Select m\_axi\_DDS\_OUTPUT1 under dds\_0 and leave all options Auto.  Select OK.

### Configuring AXI Smartconnect IP

In the block diagram, double click on the AXI Smartconnect instance.  Set the Number of Slave Interfaces to 3.  Click OK.  Connect M\_AXI\_PCIS on the AWS IP instance to S02\_AXI on the AXI Smartconnect instance.


### Connecting the Design Part 2

In the Block Design, expand the GPIO output by clicking on the +.  Connect the ddrc\_is\_ready output pin to the gpio\_io\_i[0:0] pin.  Connect the rst\_main\_n\_out on the AWS IP instance to the output pin to the ext\_rst\_in pin on the Processor System Reset instance.

In the Block Design, select the Address Editor Tab.

Right click on M\_AXI\_PCIS and select Auto Assign Address.

Expand f1\_inst/M\_AXI\_BAR1. For dds\_0 make sure Offset Address is 0x00_0000 and axi\_gpio\_0 is 0x01\_0000.

Expand dds\_0/Data\_m\_axi\_DDS_OUTPUT and dds\_0/Data\_m\_axi\_DDS\_OUTPUT1 address segments.  Set Range for both of these segments to 2G and Offset Address to 0x80000000 which is for the static DDR4 memory.  Note the IP addressing is 32-bits using 2GB DDR4 memory.

### Saving and Validating the Design

Save the block diagram and select Tools->Validate Design.

Select OK Once Validation is successful.

## Simulation

The simulation settings are already configured.

Click on Simulation->Run Simulation->Run Behavioral Simulation.

Add signals needed in the simulation.

Type in the following in the TCL console (could take 2 hours based upon machine).  Note if Critical Warnings appear click OK and that the following command needs to ran two times.  This is a known issue and will be addressed in later versions of the design.

run -all

## Implementing the Design/Tar file

In the Design Runs tab, right click on impl\_1 and select Launch Runs. Click OK in the Launch Runs Dialog Box.  Click OK in the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in example\_projects/cl\_hls\_dds.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.


## CL Example Software

The runtime software must be complied for the AFI to run on F1.

Copy the software directory to any directory and compile with the following commands.

    $ cp -r $HDK_COMMON_DIR/shell_stable/hlx/hlx_examples/build/IPI/cl_hls_dds/software
    $ cd software
    $ make all
    $ sudo ./test_cl


<a name="ipimodtut"></a>
# IP Integrator Design Modular Reference Tutorial with hello world RTL

## Overview

The hello\_world example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and the use of the Virtual LED and DIP switches. The hello\_world example implements two registers in the FPGA AppPF BAR0 memory space connected to the OCL AXI-L interface. The two registers are:

1. Hello World Register (offset 0x500)
2. Virtual LED Register (offset 0x504)

The logic for the original cl\_hello\_world example from github is contained in one RTL module (hello\_world.v).  In hello\_world.v, the top level ports are for AXI4-Lite interface, clock/reset and ports for VLED and VDIP which allows for IP packaging of the design and reuse with other flows/AXI4-Lite Master interfaces.  Note VIO logic is not included with this example from the original hello\_world.

## Create Directory Structure\Vivado Project 

Change directories to hdk/cl/examples

Create a directory in examples like cl\_hello\_world\_ref\_vivado

Change directories into cl\_hello\_world\_ref\_vivado/

Start Vivado by typing vivado in the console.

Create a project any device with the following command.

create\_project -name cl\_hello\_world\_ref

Type in the following command which changes the project settings for AWS and creates the block diagram with the AWS IP added.

aws::make\_ipi


## Adding existing RTL sources (hello\_world.v)

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the hdk/common/shell\_stable/hlx/hlx\_examples/build/IPI/cl\_hello\_world\_ref/design directory.

Add the cl/examples/common/design directory.

Select Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

## Configuring the Block Diagram

Double click on the AWS IP.  Under IP Interfaces select Use OCL Register Interface and Use Auxiliary (non-AXI) Signal Ports.  This enables the AXI4-Lite Master Interface and the VLED/VDIP input/outputs.

Select Run Connecting Automation on the top of the Block Diagram.  Select AUTO for Crossbar clock source of Interconnect IP/Clock source for Master interface/Clock source for Slave interface.  The default clock is the 125 MHz coming from clk\_main\_a0\_out from the f1\_inst.

Address spaces is configured as the default which the whole address space of OCL.  This can be changed in Address Editor for a smaller address space if necessary.

Select vled pin and connect to status\_vled on the f1\_inst block.

Select status\_vdip on the f1\_inst block and make a connection to vdip.

Right click on the connection between M\_AXI\_OCL on f1\_inst and S00\_AXI on f1\_inst\_axi\_periph and select Debug.

Click on Run Connection Automation and click on for System ILA to be added to the design.  If necessary the AXI-MM Protocol Checker can be selected when debugging new IPs.

Save the block diagram and select Tools->Validate Design.

Select OK Once Validation is successful.

## Add simulation sources from example design (cl\_hello\_world)

Add or create simulation sources.  Select Add Files.

Add the cl/examples/cl\_hello\_world/verif/tests/test\_hello\_world.sv

Deselect Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources. 

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

Select all design sources for simulation.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names.

CL\_NAME=cl\_top

TEST\_NAME=test\_hello\_world

Click OK, Click Apply, Click OK to back into the Vivado project.

## Running Simulation
Select Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.  Note if Critical Warnings appear click OK and that the following command needs to ran two times.  This is a known issue and will be addressed in later versions of the design.

run -all

## Adding constraints for design

No additional constraints are needed for this design.


## Implementing the Design/Tar File

Right click on impl\_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

## CL Example Software

The runtime software must be complied for the AFI to run on F1.

Use the software in cl/examples/cl\_hello\_world

    $ cd cl/cl_hello_world/software/runtime/
    $ make all
    $ sudo ./test_hello_world


<a name="rtlexistut_world"></a>
# Adding Example RTL Tutorial-cl\_hello\_world

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project.  This example uses cl\_hello\_world from the github examples directory.


## Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl\_hello\_world\_vivado

Change directories into cl\_hello\_world\_vivado/


For the clock recipes and IDs set the following system variables (these match cl\_hello\_world example).

export CLOCK\_A\_RECIPE=0

export CLOCK\_B\_RECIPE=0

export CLOCK\_C\_RECIPE=0

export device\_id=0xF000

export vendor\_id=0x1D0F

export subsystem\_id=0x1D51

export subsystem\_vendor\_id=0xFEDD


Start Vivado by typing vivado in the console.

Type in the following to create a generic project.

create\_project -name cl\_hello\_world

To setup the project for RTL mode, type in the following command.

aws::make\_rtl


## Adding existing RTL sources (cl\_hello\_world)

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the cl/examples/cl\_hello\_world/design directory. 

Add the cl/examples/common/design directory.

Select Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

## Add simulation sources from example design (cl\_hello\_world)

Add or create simulation sources.  Select Add Files.
Add the <cl\_dir>/verif/tests/test\_hello\_world.sv

Deselect Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

Select all design sources for simulation.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names.

CL\_NAME=cl\_hello\_world

TEST\_NAME=test\_hello\_world

Click OK, Click Apply, Click OK to back into the Vivado project.

## Running Simulation
Select  Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

## Adding constraints from example design (cl\_hello\_world)
### Option 1
Constraints can be copied and pasted from opening the original XDCs in a text editor and copying the constraints into the project .xdc files.

For cl\_hello\_world, copy the following into the cl\_pnr\_user.xdc in the Source->Constraints->cl\_pnr\_user.xdc.  Note this is only for cl\_hello\_world.

set\_false\_path -from [get\_cells CL/vled\_q\_reg*]

### Option 2
Overriding the .xdc in the Vivado project.

cl\_synth\_user.xdc/cl\_pnr\_user.xdc can be copied over from the /build/constraints area to the imported area of the Vivado project like the following.

<example\_design>/build/constraints/ to <project\_name>.srcs/constrs\_1/imports/subscripts

### Option 3
Deleting the existing .xdc in the Vivado project and import constraints or copy constraints into Vivado project. 

Delete cl\_synth\_user.xdc and cl\_pnr\_user.xdc in the Source->Constraints tab.

In Flow Navigator select Add Sources and select Add or create constraints.

For cl\_synth\_user.xdc and cl\_pnr\_user.xdc select the minus (-) button.  Select Add Files and go to the hdk/cl/examples/<cl\_example>/build/constraints directory.  Select cl\_pnr\_user.xdc and cl\_synth\_user.xdc.

#### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy constraints files into project to link to the source files.

#### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy constraints files into project to add the source files to local Vivado project.

In the Sources/Hierarchy Tab, select cl\_pnr\_user.xdc and go to Source File Properties.
Under the General Tab, deselect Enabled and select Implementation Box only.
In Properties Tab, select PROCESSING\_ORDER to be LATE.

## Implementing the Design/Tar File
Right click on impl\_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

The completed .tar file is located in <project>.runs/faas\_1/build/checkpoints/to\_aws/<timestamp>.Developer\_CL.tar.  For information on how to create a AFI/GAFI with .tar from the design, following to the How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide documentation.

## CL Example Software

The runtime software must be complied for the AFI to run on F1.

Use the software in cl/examples/cl\_hello\_world

    $ cd cl/cl_hello_world/software/runtime/
    $ make all
    $ sudo ./test_hello_world


<a name="rtlexistut_dram"></a>
# Adding Example RTL Tutorial-cl\_dram\_dma

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project.  This example uses cl\_dram\_dma from the github examples directory.

Make sure the [HLx Setup Instructions](./IPI_GUI_Vivado_Setup.md) are followed before continuing.

## Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl\_dram\_dma\_vivado

Change directories into cl\_dram\_dma\_vivado/

For the clock recipes and IDs set the following system variables (these match cl\_dram\_dma example).

export CLOCK\_A\_RECIPE=0

export CLOCK\_B\_RECIPE=0

export CLOCK\_C\_RECIPE=0

export device\_id=0xF001

export vendor\_id=0x1D0F

export subsystem\_id=0x1D51

export subsystem\_vendor\_id=0xFEDC


Start Vivado by typing vivado in the console.

Type in the following to create a generic project.

create\_project -name cl\_dram\_dma

To setup the project for RTL mode, type in the following command.

aws::make\_rtl


## Adding existing RTL sources (cl\_dram\_dma)

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the cl/examples/cl\_dram\_dma/design directory.

Add the cl/examples/common/design directory.

Select Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.


Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

## Add simulation sources from example design (cl\_dram\_dma)
cl\_dram\_dma example has several system verilog tests (test\_ddr.sv, test\_dram\_dma.sv, test\_ini.sv, test\_peek\_poke.sv, test\_peek\_poke\_pcis\_axsize.sv).

Add or create simulation sources.  Select Add Files and individually add in the .sv files needed.

Add the <cl\_dir>/verif/tests/<tests\_to\_add>.sv

Deselect Scan and add RTL includes files into project

### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

Select all design sources for simulation.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names.

CL\_NAME=cl\_dram\_dma

For TEST\_NAME choose the name of the .sv used (don’t put .sv at the end of the line).

Below is an example.

TEST\_NAME=test\_dram\_dma

Click OK, Click Apply, Click OK to back into the Vivado project.

## Running Simulation
Select  Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.

run -all

## Adding constraints from example design (cl\_dram\_dma)

### Option 1
Constraints can be copied and pasted from opening the original XDCs in a text editor and copying the constraints into the project .xdc files.

### Option 2
Overriding the .xdc in the Vivado project.

cl\_synth\_user.xdc/cl\_pnr\_user.xdc can be copied over from the /build/constraints area to the imported area of the Vivado project like the following.

<example\_design>/build/constraints/ to <project\_name>.srcs/constrs\_1/imports/subscripts

### Option 3
Deleting the existing .xdc in the Vivado project and import constraints or copy constraints into Vivado project. 

Delete cl\_synth\_user.xdc and cl\_pnr\_user.xdc in the Source->Constraints tab.

In Flow Navigator select Add Sources and select Add or create constraints.

For cl\_synth\_user.xdc and cl\_pnr\_user.xdc select the minus (-) button.

Select Add Files and go to the hdk/cl/examples/<cl\_example>/build/constraints directory.

Select cl\_pnr\_user.xdc and cl\_synth\_user.xdc.

#### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy constraints files into project to link to the source files.

#### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy constraints files into project to add the source files to local Vivado project.

In the Sources/Hierarchy Tab, select cl\_pnr\_user.xdc and go to Source File Properties.
Under the General Tab, deselect Enabled and select Implementation Box only.
In Properties Tab, select PROCESSING\_ORDER to be LATE.

## Implementing the Design
Right click on impl\_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.

## CL Example Software

The runtime software must be complied for the AFI to run on F1.  Note the EDMA driver must be installed before running on F1.

Use the software in cl/examples/cl\_dram\_dma

    $ cd cl/cl_dram_dma/software/runtime/
    $ make all
    $ sudo ./test_dram_dma


<a name="rtlscrtut"></a>

# Starting from Scratch RTL Design

## Overview

This example shows how to add existing RTL, simulation RTL, and constraints into a Vivado project based upon template files provided from github.

Make sure the [HLx Setup Instructions](./IPI_GUI_Vivado_Setup.md) are followed before continuing.

## Create Directory Structure\Vivado Project and System Variables 

Change directories to hdk/cl/examples

Create a directory in examples like cl\_template or the proposed design name.

Change directories into cl\_template/

For the clock recipes and IDs set the following system variables which are defaults.
These values can be changed later either in the bash shell or in Vivado based upon the design's needs.

export CLOCK\_A\_RECIPE=0

export CLOCK\_B\_RECIPE=0

export CLOCK\_C\_RECIPE=0

export device\_id=0xF000

export vendor\_id=0x1D0F

export subsystem\_id=0x1D51

export subsystem\_vendor\_id=0xFEDD


Start Vivado by typing vivado in the console.

Type in the following to create a generic project (change the project name to the proposed design name).

create\_project -name cl\_template

aws::make\_rtl


## Adding existing RTL template sources

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the hdk/common/shell\_stable/new\_cl\_template/design directory.  

Select Scan and add RTL includes files into project

Select Copy sources into project to add the source files to local Vivado project.  The templates are stored in the local Vivado project and can be modified in Vivado or a text editor.

Select Add sources from subdirectories.

### Template Overview
cl\_template\_defines.vh – Verilog header file where user puts in generic `define based upon the design.

cl\_template.sv – Top level file where user adds in logic, modules and `include .inc files to disable interfaces not used in the shell.

### Include files

If certain shell interfaces are not enabled, the user needs to use the .inc provided in HDK to disable the interface in cl\_template.sv.  See the example designs for examples on using these .inc files.

### Add Existing RTL

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources and select Add Directories.

Add the directories or files needed.

Select Scan and add RTL includes files into project

#### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

#### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.


Select Copy sources into project to add the source files to local Vivado project.

### Adding/Importing IP
To add new IP to the design, select IP Catalog, find the particular IP and configure, and generate with Global synthesis mode (Out of Context is not supported at this time).  The template .vho/.veo can be used to insert the IP into the RTL.

To import IP do the following.

In Flow Navigator->Under Project Manager select Add Sources.  Select Add or create design sources.

Add the XCI file of the IP or IPs.  Make sure to generate with Global synthesis mode (Out of Context is not supported at this time).

#### Import Only - Sources are not copied to the Vivado project and pointed to outside of the Vivado project.

Deselect Copy sources into project to link to the source files.

#### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

### Adding simulation sources from template System Verilog

Simulation/system behavior should be verified before attempting the implementation flows.

In the Flow Navigator tab/Project Manager select Add Sources.  Add or create simulation sources.  Select Add Files.

Add the hdk/common/shell\_stable/hlx/hlx\_examples/verif/test\_cl.sv

Deselect Scan and add RTL includes files into project

### Copy to Project - Sources are copied to the Vivado project where the user can modify the sources without impact to the original sources.

Select Copy sources into project to add the source files to local Vivado project.

Select Add sources from subdirectories.

Select Include all design sources for simulation.  Then click Finish.

Right click on SIMULATION in the Project Manager and select Simulation Settings…

For Verilog options select the … box and change the following names (should all ready be configured).

CL\_NAME=cl\_top

TEST\_NAME=test\_cl

Click OK, Click Apply, Click OK to back into the Vivado project.

Modify test\_cl.sv based upon interfaces used in the design.  Examples are provided in test\_cl.sv for a majority of the interfaces.

## Running Simulation

Select Simulation->Run Simulation->Run Behavioral Simulation from the Flow Navigator Tab.

Add signals needed in the simulation.

Type in the following in the TCL console.  Note if Critical Warnings appear click OK and that the following command needs to ran two times.  This is a known issue and will be addressed in later versions of the design.

run -all

## Modifying Constraints

The following files are added to the Vivado project automatically.

cl\_clocks\_aws.xdc – Top level clock constraints for the CL.  This file should not be touched as it's dynamically created during the synthesis process.

cl\_synth\_aws.xdc - Timing constraints between sh\_ddr module and DDR4 IP. This file should be disabled in the Vivado project if no DDR4 instances are in the CL.

cl\_synth\_user.xdc – User can modify this file for the the CL for synthesis (I.E creating new clock structures with clock generator/using clocks in different Shell MMCM).

cl\_pnr\_user.xdc – User can modify this file for constraints between the CL/SH for implementation(place/route).  Floorplanning is done in this file if necessary.


## Implementing the Design
Right click on impl\_1 and select Launch Runs… and Click OK.

Click OK on the Missing Synthesis Results Dialog Box.

This will run both synthesis and implementation.
