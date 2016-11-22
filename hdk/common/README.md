# AWS FPGA HDK Common Library
<span style="display: inline-block;">
[![API Reference](http://img.shields.io/badge/api-reference-blue.svg)](http://docs.aws.amazon.com/techdoc/fpga)
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

This directory directory include AWS-provided script, timing constraints and compile settings required during the AFI generation process. 

Developers should not change these files

## /verif 

The /verif directory include reference verification modules to be used as BFM (Bus-functional) as the external interface for simulation the Custom Logic

In includes a simple model of the DRAM interface around the FPGA.

It also includes a simple model of the 

[DOCNOTE - winefred: i think we should hide the SPI/UC piece from here as developers are not expected to know or use that]
[DOCNOTE - winefred: should we keep the PCI BFM or only offer AXI? i'm torn here,  between simplicity of AXI vs the need to model the DMA, interrupts etc]

## /lib 

[DOCNOTE - winefred: i dont know what you wanted to have in this /lib, but all the files look the same and have a lot of encryption keys]

## /build

Includes the mandatory timing constraints files required by AWS under `/common/build/constraints`.

The `/common/build/scripts` have auxilary scripts that would be used during the CL build

The `/common/build/checkpoints` have the checkpoint for AWS Shell, that is used during the developer's CL build process since the final AFI is built out of CL + AWS Shell.


