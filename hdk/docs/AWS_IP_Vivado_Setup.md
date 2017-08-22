# HLx Setup/Vivado Overview/AWS IP Readme

## Table of Content

1. [Overview](#overview)
2. [HDK Install](#hdksdkinst)
3. [HLx Install](#hlxinst)
4. [Vivado Overview](#vivado) 
5. [AWS IP Overview](#ipover)
6. [Vivado Flows Overview](#projover)


<a name="overview"></a>
# Overview  

This document covers how to clone github, source hdk and how to installed the HLx environment.  In addition, information about the AWS IP and general information about Vivado projects (IP Integrator/RTL) are discussed.

After setup, the [Vivado HLx AWS Tutorials and Examples](./AWS_Tutorials_Examples.md) documentation is for new designs, example designs, and tutorials.

<a name="hdksdkinst"></a>
Follow the sections of Xilinx Vivado Tools, License Requirements and HDK Installation and Environment Setup.

This will setup the license, clone the github, and setup the HDK environment.

At this time on-premise flow is highly recommended with the HLx flow.

<a name="hlxinst"></a>

# HLx Install

Open the following file in a text editor ~/.Xilinx/Vivado/init.tcl or ~/.Xilinx/Vivado/Vivado_init.tcl

If the file doesn't exist, change directories into ~/.Xilinx/Vivado and use the following command to create the file.

touch Vivado_init.tcl

Get the absolute path of the $HDK\_SHELL\_DIR with the following command.

echo $HDK\_SHELL\_DIR

In init.tcl or Vivado\_init.tcl, add the following line based upon the $HDK\_SHELL\_DIR path.

source <output from echo $HDK\_SHELL\_DIR>/hlx/hlx_setup.tcl

Everytime when vivado is invoked, this script will always be sourced and features of this script are available.

<a name="vivado"></a>

# Vivado Overview

This section is a basic overview of the Vivado GUI and features that are discussed in the tutorials and examples in the HLx environment.  The GUI environment enables users at all experience levels to quickly set project options and strategies to meet their design requirements and enables interactive reports and design views to help quickly close any issues with timing or area.     

IP Integrator is a design entry tool in the Vivado HLx Design Suite.  It lets developers connect IPs at a block level and generates a "what you see is what you get" Register Transfer Language (RTL) file, either in VHDL or Verilog format.  The IP Integrator flow enhances the standard RTL flow and gives the developer access to designer assistance features which include:


- Simplified connectivity of IPs through interface based connections

- Block automation that adds helper IPs like Interconnects, DMAs, or other support blocks based upon an IP’s configuration

- Connectivity automation to route interfaces, clocks and resets between blocks

- Design Rule Checks (DRCs) to ensure proper interface connectivity and clock domain crossing

- Advanced hardware debug capabilities that enable the developer to debug at a transaction level



For more detailed information and methodology design guidelines refer to the following documentation:

- <a href="https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_2/ug892-vivado-design-flows-overview.pdf">ug892-vivado-design-flows-overview.pdf</a>
- <a href="https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_2/ug994-vivado-ip-subsystems.pdf">ug994-vivado-ip-subsystems.pdf</a>
- <a href="https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_2/ug949-vivado-design-methodology.pdf">ug949-vivado-design-methodology.pdf</a>



The below screenshot is from the Vivado GUI which is discussed in the sections below.


![Diagram](./images/hlx/vivado_gui.jpg)

## Sources Tab

The box in yellow contains the design sources.

### Sources/Hierarchy Tab

This tab categories the sources in three different categories.

Design Sources folder is for synthesis/implementation sources.  Constraints folder is for timing constraints (XDC).  Simulation Sources folder is for simulation only sources.

Clicking on a particular file will provide information in the Properties tab (under Sources).  In this tab, the user can change how the file is used in the design flow.

For RTL/IP sources can be marked for synthesis/implementation/simulation or synthesis/implementation and/or simulation only.  XDCs can be marked for synthesis/implementation or synthesis only or implementation only.

### Sources/IP Sources

When IP is created or imported the IP sources are shown in this tab.  Expanding the IP/Instantiation Template, users have the templates to add the IP into the RTL.  At this moment Synthesis Options on the IP should be Global only.

## Flow Navigator

The Flow Navigator is in the green box.

### PROJECT MANAGER

PROJECT MANAGER section allows to Add Sources like RTL/IP/XDC sources, Language Templates for common RTL constructs/XDCs/DEBUG, and IP Catalog to add IPs to the project.  This portion of the flow targets the RTL flow.

When invoking IP Catalog, the user can search for a particular IP or look through the different categories of IP and it’s the responsibility of the user to add and connect the IP into the user RTL.  


### IP INTEGRATOR

This section allows the user to open and modify the Block Design and the Generate Block Design after the design is validated.  The framework of the Block Design with the AWS IP and board are already created with the HLx flow so Create Block Design isn’t necessary.

Double clicking on any IP in the BD brings up the Re-customize IP Dialog Box where IP settings can be reviewed or modified.  When connecting designs, Connection Automation is available to automatically connect interfaces.

### SIMULATION

This section allows to change simulation settings by right clicking on SIMULATION and invoking simulations by clicking Run Simulation->Run Behavioral Simulation. 

### RTL ANALYSIS

By clicking on Open Elaborate Design, the RTL files in the design are analyzed where the user can check RTL structures and syntax before the synthesis stage.

### SYNTHESIS

By right clicking on SYNTHESIS, the user is able to view Synthesis Settings and Launch Synthesis.  After synthesis stage is complete, clicking on Open Synthesized Design will open the post synthesis checkpoint for analysis.  This stage is necessary for developing timing constraints for the CL.

### IMPLEMENTATION

By right clicking on IMPLEMENTATION, the user is able to view Implementation Settings and Launch Implementation.  After implementation stage is complete, clicking on Open Implementation Design will open the post implementation checkpoint for analysis of the SH/CL.

## TCL Commands

The orange box is where TCL commands are entered.  The TCL Console Tab above the orange box reports the output of the TCL command.

## Design Runs Tab

The blue box is where the Design Runs are located with similar functionality as the Flow Navigator/SYNTHESIS and Flow Navigator/IMPLEMENTATION sections. The examples and tutorials mention how to use synth\_1 and impl\_1 to build the design.


<a name="ipover"></a>

# AWS IP Overview

To configure the AWS IP, double click on the AWS IP in the Block Diagram (BD) after the IP Integrator Block Diagram is created.  This is discussed in the [Vivado HLx AWS Tutorials and Examples](./AWS_Tutorials_Examples.md).

When the Re-customize IP GUI appears, four catagories appear for IP configuration.

## Enable IP Interfaces

Select the Box to enable an interface.  When enabling interfaces the block diagram on the left will be updated based upon interfaces/ports/clocks.

See [AWS Shell Interface Specification](./AWS_Shell_Interface_Specification.md) on information about AXI Interfaces and ports.

Enable DDR4-A in CL

Enable DDR4-B in CL

Use DDR4-C in Shell

Enable DDR4-D in CL

Use PCI Slave-access Interface (M\_AXI\_PCIS)

Use PCI Master-access Interface (S\_AXI\_PCIM)

Use SDA Register Interface (M\_AXI\_SDA)

Use OCL Register Interface (M\_AXI\_OCL)

Use BAR1 Register Interface (M\_AXI\_BAR1)

Use Auxiliary (non-AXI) Signal Ports - (VLED,IRQ,VDIP,GLCOUNT,FLR ports)

![Diagram](./images/hlx/aws_ip.jpg)


## Clock Signals

Review the clock recipes listed in [clock_recipes.csv](./clock_recipes.csv) to configure clocks based upon the design.
 
Select the number of clocks(highest extra clock number needed) used based upon clock recipe for Group-A, Group-B, Group-C.

Note if needing _a3 clock, this value would be set to 4 for Group-A

Configure the Clock Recipe for Group-A, Group-B, Group-C.

Note Group-A Clock Recipe of 0 would be A0 based upon the clock_recipes.csv

Values of generated clocks are seen in the GUI.

![Diagram](./images/hlx/aws_ip_clock.jpg)

## CL Partition ID

The Vendor ID, Device ID, Subsystem Vendor ID, Subsystem ID can be configured.

For now these default values match typically AWS examples and shouldn't be modified at this time.

Shell Version is a read only value that matches the version supported by the AWS IP.

## Advanced
Number of pipeline stages - Range is between 1-4 pipeline stages for the stats interface for DDR4 in the CL. Number of pipelines depends on the size/complexity of the design.


<a name="projover"></a>
# Vivado Flows Overview

The HLx environment supports IP Integrator, RTL, HLS flows in Vivado and this section will discuss these
flows from a top level. Refer to [Vivado HLx AWS Tutorials and Examples](./AWS_Tutorials_Examples.md) for more details.


## RTL

Users can add in existing AWS RTL from examples and new AWS template CL files from the AWS RTL flow. Also, user can
add custom generated Verilog/System Verilog/VHDL files.

For using IPs, at this time global mode is only supported. OOC is not supported at this time.

![Diagram](./images/hlx/rtl_dram_dma_sources.jpg)

## IP Integrator

Users can add in Vivado IP into the block diagram to create/stitch a full design easily. In addition, the user can add custom IP to the block diagram through RTL module referencing flow using user RTL in the project.

![Diagram](./images/hlx/ipi_mod_ref.jpg)

## HLS

Users can add developed/generated HLS IPs in either RTL/IP Integrator flows using an IP Repository.

![Diagram](./images/hlx/ipi_hls.jpg)

## General Environment

### Design Constraints in Project

Timing analysis and setting timing constraints/floorplans is discussed in the timing closure documentation.

The following top level clocks from the Shell (MMCM in the Shell to the CL) are generated dynamically based upon clock recipe’s used with the AWS flow.
The user can’t modify these constraints as they are dynamically created before synthesis.

cl\_clocks\_aws.xdc – Top level clock constraints for the CL.

The following .xdc file is only available with the RTL flow provided by the AWS env for synthesis.  This file should be disabled in the vivado project
if DDR4 memories are not in the CL design(critical warnings could show up).

cl\_synth\_aws.xdc - Timing constraints between sh_ddr module and DDR4 IP.

The following .xdc files are available to the user.

cl\_synth\_user.xdc – Timing constraints in the CL(I.E creating new clock structures with clock generator/using clocks in different Shell MMCM).

cl\_pnr\_user.xdc – Timing constraints between the CL/SH.  Floorplanning is done in this xdc if necessary.



### Synthesis/Implementation

Timing analysis and setting appropriate synthesis settings/implementation directives are discussed in the timing closure documentation.

By default, synthesis is using Default directive and -max\_uram\_cascade\_height is set to 1. The user can set max\_uram\_cascade\_height in the More Options section of Design Run Settings Tab by right clicking on Synth\_1->Open Run.

By default, all implementation steps are using the Explore directive.

If needing to change implementation settings, only change the tool directives in the Design Run Settings tab by right clicking on Impl_1->Change Run Settings… .
Change only directives for opt_design ,place_design, phys_opt_design, and route_design.  Do not change Strategy options as this overrides certain options in the HLx environment at this time.


