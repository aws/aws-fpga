# AWS FPGA HDK
<span style="display: inline-block;">
[![API Reference](http://img.shields.io/badge/api-reference-blue.svg)](http://docs.aws.amazon.com/techdoc/fpga)
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)


AWS FPGA HDK is the official kit for developing an Amazon FPGA Image (AFI) which can be loaded on FPGAs in FPGA-enabled EC2 instances. 

Check out our [release notes](./release_notes.md) for information about the latest bug fixes, updates, and features added to the HDK.

## Overview

AWS FPGA HDK includes all the design files and scripts required to generate an Amazon FPGA Image (AFI). Developers can download the HDK and use it in their preferred design environment. AWS offers the `FPGA Developer AMI` on [AWS Marketplace](https://aws.amazon.com/marketplace) with the required tools to develop, simulate and build an AFI.  

### Content of the release

The [documents directory](./docs) provides the specification for the AWS Shell to Custom Logic (CL) interface, and best practices for CL design and development.

The [common directory](./common) includes scripts, timing constraints and compile settings required during the AFI generation process. Developers should not change these files.

The [Custom Logic (cl) directory](./cl) is where the Custom Logic is expected to be developed. It includes a number of exmples under the [examples directory](./cl/examples), as well as a placeholder for developer's own Custom Logic under [developer_designs directory](./cl/developer_designs).  

The HDK also includes test benches for each provided example, and instructions on how to run RTL-level simulations.

## Getting Started

### Have an instance or server with Xilinx Vivado tools and License

To get started, the developer needs to have a development environment with Xilinx tools installed. An easy way to get this by using AWS FPGA Developer AMI and following the instructions inside the README.md of that AMI.

### Install the HDK and setup environment

AWS FPGA HDK can be cloned to your EC2 instance or server by executing:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_setup.sh

### Try out a "Hello World" example and others

The [Getting started with CL examples](./cl/examples/Getting_Started_With_CL_Examples.md) walks you through how to build, register and use an AFI. 
The [Hello World readme](./cl/examples/cl_hello_world/README.md) provides steps to build an AFI from the provided Hello World example CL, and how load it on an F1 instance.
Other examples are available in the [examples directory](./cl/examples), each with its own README.md file.


### Start your own Custom Logic design

The [start your own CL design](./cl/developer_designs/README.md) will guide you on how to setup your own CL project environment.

### Simulate your Custom Logic design

You can use Vivado XSIM simulator, or bring your own simulator (like Synopsys', Mentor's, or Cadence).
Follow the [verification environment setup](https://github.com/aws/aws-fpga/wiki/Simulating-CL-Designs-(RTL-Simulation)#introduction) to run these simulations

### Build and submit the Custom Logic to AWS for generating an AFI

You can follow the [build scripts readme](./common/shell_current/new_cl_template/build/README.md) for step-by-step instructions on how to setup the scripts and run the build process.
This [checklist](./cl/CHECKLIST_BEFORE_BUILDING_CL.md) should be consulted before you start the build process.

## FAQ

### Does the HDK Include DMA?
Current release of the HDK does not include DMA. Upcoming releases will include both Xilinx's XDMA and AWS EDMA in the HDK and their respective drivers in the SDK.

### Does the HDK support OpenCL?

### Does the HDK support SDAccel?

### Does the HDK support Chipscope?
AWS FPGA design is provisioned to support chipscope, and developers will have access to chipscope in one of the upcoming HDK and SDK releases.

### Does HDK support Partial Reconfiguration?
AWS F1 instances support partial configuration (PR), and the AFI is actually a PR bitstream. Using [AWS EC2 FPGA API](../sdk/management/fpga_image_tools), the users can load/unload AFIs.



