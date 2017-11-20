# AWS FPGA HDK Common Library

This directory includes the shell versions, scripts, timing constraints and compile settings required during the AFI generation process. 
Developers should not modify or remove these files.

## /scripts

The [scripts] (./scripts) contains a script used to notify a developer that their build job is complete as well as a script used to copy the specific AWS Shell design checkpoint (DCP) to the appropriate directory during the HDK setup process ([hdk_setup.sh](../../hdk_setup.sh)). 

## /shell_stable

The shell_stable soft link points to the shell version contained in this directory that is the current, qualified shell version that can be used by developers. Other shell versions may be available for reference but they are likely older, or exploratory.

## /shell_v#\#\#\#\#\#\#\# #

Each shell release contains files specific to that release. These files are stored in a shell directory with the version included in the directory name. For example, the [shell_v071417d3](shell_v071417d3) directory contains files specific to Shell Version 0x071417d3.

## /software

The [software](software) directory contains common software files used in the HDK. 

## /verif 

The [verif directory](./verif) includes reference verification modules to be used as Bus Functional Models (BFM) as the external interface to simulate the Custom Logic (CL).
It includes a simple model of the DRAM interface around the FPGA.
It also includes a simple model of the 

