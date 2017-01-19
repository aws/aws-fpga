# AWS FPGA HDK Common Library
<span style="display: inline-block;">
[![API Reference](http://img.shields.io/badge/api-reference-blue.svg)](http://docs.aws.amazon.com/techdoc/fpga)
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

This directory includes scripts, timing constraints and compile settings required during the AFI generation process. 
Developers should not modify or remove these files.

## /verif 

The [verif directory](./verif) includes reference verification modules to be used as Bus Functional Models (BFM) as the external interface to simulate the Custom Logic (CL).
It includes a simple model of the DRAM interface around the FPGA.
It also includes a simple model of the 

## /lib 


## /build

The [build directory](./build) includes the mandatory timing-constraints files required under `/common/build/constraints`.

The `/common/build/scripts` have auxiliary scripts that are used during the CL build.

The `/common/build/checkpoints` have the design checkpoint (DCP) for AWS Shell. This is used during the CL build process since the final AFI is built out of CL + AWS Shell.


