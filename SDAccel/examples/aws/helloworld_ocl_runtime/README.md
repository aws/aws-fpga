# Hello World OpenCL Example Runtime


## :exclamation:  NOTE: If this is your first time using F1, To go through the full SDAccel application development flow  you should read [Quick Start Guide to Accelerating your C/C++ application on an AWS F1 FPGA Instance with SDAccel](../../../README.md)

## Table of Contents

1. [Overview](#overview)
2. [Filelist Description](#description)
3. [Execution](#execute)
4. [Hello World OCL Example Metadata](#metadata)


<a name="overview"></a>
## Overview

This example is a simple OpenCL application. It will highlight the basic execution flow of an OpenCL application on F1 instance using a precompiled AFI.
You Need to be on F1 Instance to be able to execute this application.

<a name="description"></a>
## Filelist Description

```
helloworld -- Executable application file
helloworld_ocl_afi_id.txt  -- lists public afi information to load for this example
helloworld_ocl_agfi_id.txt -- list public agfi id of the afi to load for this example 
README.md
vector_addition.hw.xilinx_aws-vu9p-f1-04261818_dynamic_5_0.awsxclbin --awsxclbin file with xclbin metadata used by application to load the afi.
```

<a name="execute"></a>
## Execution

#### :exclamation: PLEASE NOTE: xclbin & awsxclbin file formats have changed from SDx 2018.3 onwards. xclbin & awsxclbin files generated using earlier SDx versions are not compatible with 2018.3/2019.1 based XRTs. If you are using a 2018.3/2019.1 based XRT, please copy over awsxclbin & helloworld executable files provided in the 2018.3_2019.1 subdirectory to this folder.

```
sudo fpga-clear-local-image -S 0
sudo -E /bin/bash
source $AWS_FPGA_REPO_DIR/sdaccel_runtime_setup.sh
./helloworld
```

<a name="metadata"></a>
## Hello World Example Metadata

| Key    | Region  |  SDx 2017.4 or 2018.2 | SDx 2018.3 or 2019.1 |
|--------|---------|-----------------------------|------------------|
|afi id  | us-east-1(N. Virginia) | afi-0532379b26ea13f26 | afi-0c8210915ce9bab5c |
|afi id  | us-west-2(oregon) | afi-0ab098d3fbfc43c7e | afi-01e237aa978aa74de |
|afi id  | eu-west-1 (Ireland) | afi-0ae1c5a82237c676f | afi-0370da8e8d6e7ca3d |
|agfi id | all regions | agfi-05f652c8a09435190 | agfi-046565baf5ce48c86 |



