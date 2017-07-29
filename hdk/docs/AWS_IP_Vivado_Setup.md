# HLx Setup/AWS IP README

## Table of Content

1. [Overview](#overview)
2. [HDK Install](#hdksdkinst)
3. [HLx Install](#hlxinst)
4. [AWS IP Overview](#ipover)
5. [Vivado Project Overview](#projover)


<a name="overview"></a>
# Overview  

This document covers how to clone github, source hdk and how to installed the HLx environment.
In addition, information about the AWS IP and Vivado projects (IP Integrator/RTL) structure is discussed.

After setup, the AWS Vivado Flows and/or AWS Vivado Example Tutorials documents can be used for
new designs, example designs, and tutorials.

<a name="hdksdkinst"></a>
Follow the sections of Xilinx Vivado Tools and 
License Requirements and HDK Installation and Environment Setup.

This will setup the license, clone the github, and setup the HDK environment.

At this time on-premise flow is highly recommended with the HLx flow.

<a name="hlxinst"></a>
# HLx Install
Open the following file in a text editor ~/.Xilinx/Vivado/init.tcl or ~/.Xilinx/Vivado/Vivado_init.tcl

Get the absolute path of the HDK_DIR with the following command.

echo $HDK_DIR

In init.tcl, add the following line based upon the HDK_SHELL_DIR path.

source <output from echo $HDK_SHELL_DIR>/hlx/hlx_setup.tcl

When vivado in invoked, this script will always be sourced and features of this script are available.

<a name="ipover"></a>
# AWS IP Overview
To configure the AWS IP, double click on the AWS IP in the canvas.

When the Re-customize IP GUI appears, four catagories appear for IP configuration.

## Enable IP Interfaces

Select Box to enable interface.  When enabling interfaces
the block diagram on the left will be updated based upon interfaces/ports.

See AWS Shell Interface Specification on information about AXI Interfaces and ports.

Enable DDR4-A in CL

Enable DDR4-B in CL

Use DDR4-C in Shell

Enable DDR4-D in CL

Use PCI Slave-access Interface (M_AXI_PCIS)

Use PCI Master-access Interface (S_AXI_PCIM)

Use SDA Register Interface (M_AXI_SDA)

Use OCL Register Interface (M_AXI_OCL)

Use BAR1 Register Interface (M_AXI_BAR1)

Use Auxiliary (non-AXI) Signal Ports - (VLED,IRQ,VDIP,GLCOUNT,FLR ports)


## Clock Signals
Review the clock recipes listing in clock_recipes.csv to configure clocks based upon the design.
 
Select the number of clocks(highest extra clock number needed) used based upon clock recipe for Group-A, Group-B, Group-C.

Note if needing _a3 clock, this value would be set to 4 for Group-A

Configure the Clock Recipe for Group-A, Group-B, Group-C.

Note Group-A Clock Recipe of 0 would be A0 based upon the clock_recipes.csv

Values of generated clocks are seen in the GUI.

## CL Partition ID
The Vendor ID, Device ID, Subsystem Vendor ID, Subsystem ID can be configured.
For now these default values match typically AWS examples and shouldn't be modified
at this time.

Shell Version is a read only value that matches the version supported by the AWS IP.

## Advanced
Number of pipeline stages - Range is between 1-4 pipeline stages for the stats interface for DDR4 in the CL.
			    Number of pipelines depends on the size/complexity of the design.


<a name="projover"></a>
The HLx environment supports IP Integrator, RTL, HLS flows in Vivado and this section will discuss these
flows from a top level. Refer to AWS_Tutorials_Examples and AWS_Vivado_Flows.md for more details.


## RTL
User will be able to add in AWS existing/new AWS template CL files from the AWS RTL flow. Also, user can
add custom generated Verilog/System Verilog/VHDL files.

At this time global mode is only supported for IPs.  OOC is not supported at this time.

Image of source tab

## IP Integrator
User can add in Vivado IP into the block diagram canvas to create/stitch a full design easily. In addition, the user can
add custom IP to the block diagram through RTL module referencing flow using user RTL in the project.

Image of BD

## HLS
User can add developed/generated HLS IPs in either RTL/IP Integrator flow using an IP Repository.

Image of BD with HLS

## General Environment
Image of Vivado project

### Design Constraints in Project
Timing analysis and setting timing constraints/floorplans is discussed in the timing closure documentation.

The following top level clocks from the Shell (MMCM in the Shell to the CL) are generated dynamically based upon clock recipe’s used with the AWS flow.
The user can’t modify these constraints as they are dynamically created before synthesis.

cl_clocks_aws.xdc – Top level clock constraints for the CL.

The following .xdc file is only available with the RTL flow provided by the AWS env for synthesis.  This file should be disabled in the vivado project
if DDR4 memories are not in the CL design(critical warnings could show up).

cl_synth_aws.xdc - Timing constraints between sh_ddr module and DDR4 IP.

The following .xdc files are available to the user.

cl_synth_user.xdc – Timing constraints in the CL(I.E creating new clock structures with clock generator/using clocks in different Shell MMCM).

cl_pnr_user.xdc – Timing constraints between the CL/SH.  Floorplanning is done in this xdc if necessary.



### Synthesis/Implementation
Timing analysis and setting appropriate synthesis settings/implementation directives are discussed in the timing closure documentation.

By default synthesis is using Default directive.

By default all implementation steps are using the Explore directive.

If needing to change these settings, only change the directives and not the global strategy as this overrides the HLx environment at this time.

