# AWS FPGA HDK Common Library

This directory includes scripts, timing constraints and compile settings required during the AFI generation process. 
Developers should not modify or remove these files.

## /verif 

The [verif directory](./verif) includes reference verification modules to be used as Bus Functional Models (BFM) as the external interface to simulate the Custom Logic (CL).
It includes a simple model of the DRAM interface around the FPGA.
It also includes a simple model of the 

[DOCNOTE - winefred: i think we should hide the SPI/UC piece from here as developers are not expected to know or use that]
[DOCNOTE - winefred: should we keep the PCI BFM or only offer AXI? i'm torn here,  between simplicity of AXI vs the need to model the DMA, interrupts etc]

## /lib 

[DOCNOTE - winefred: i dont know what you wanted to have in this /lib, but all the files look the same and have a lot of encryption keys]

## /build

The [build directory](./build) tncludes the mandatory timing-constraints files required by AWS under `/common/build/constraints`.

The `/common/build/scripts` have auxilary scripts that would be used during the CL build.

The `/common/build/checkpoints` have the checkpoint for AWS Shell. This is used during the CL build process since the final AFI is built out of CL + AWS Shell.


