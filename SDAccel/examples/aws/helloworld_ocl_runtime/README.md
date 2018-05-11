# Hello World OpenCL Example Runtime


## :exclamation:  NOTE: If this is your first time using F1, To go through the full SDAccel application development flow  you should read [Quick Start Guide to Accelerating your C/C++ application on an AWS F1 FPGA Instance with SDAccel](../../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Filelist Description](#description)
3. [Execution](#execute)
4. [Hello World OCL Example Metadata](#metadata)


<a name="overview"></a>
## Overview

This example is a simple OpenCL application. It will highlight the basic execution flow of an OpenCL application on F1 instance.
You Need to be on F1 Instance to be able to execute this application.

<a name="description"></a>
## Filelist Description

```
helloworld -- Executable application file
helloworld_ocl_afi_id.txt  -- lists public afi information to load for this example
helloworld_ocl_agfi_id.txt -- list public agfi id of the afi to load for this example 
README.md
vector_addition.hw.xilinx_aws-vu9p-f1_dynamic_5_0.awsxclbin --awsxclbin file with xclbin metadata used by application to load the afi.

```

<a name="execute"></a>
##Execution

Command sequence

```
 >>$sudo sh
sh-4.2# source /opt/Xilinx/SDx/2017.4.rte.dyn/setup.sh 
sh-4.2# ./helloworld

```

<a name="metadata"></a>
## Hello World Example Metadata

| Key    | Value      |
|--------|------------|
|afi id  | afi-0a5834fb22d6d2cf4 |
|agfi id | agfi-0f40cddd82319b777 |



