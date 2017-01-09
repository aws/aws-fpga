

AWS FPGA HDK is the official kit for developing an Amazon FPGA Image (AFI) which can be loaded on FPGAs in FPGA-enabled EC2 instances (i.e. F1 Instance).

Check out the [release notes](../RELEASE_NOTES.md) for information about the latest bug fixes, updates, and features added to the HDK.

## Table of Contents
1. [Overview] (#overview)
2. [Getting Started] (#gettingstarted)
    - [Xilinx Vivado Tools and License Requirements] (#vivado)
    - [HDK Installation and Environment Setup] (#setup)
    - [Custom Logic (CL) Examples] (#examples)
    - [Start Custom Logic (CL) Design] (#startcl)
    - [Simulate Custom Logic (CL) Design] (#simcl)
    - [Build Custom Logic (CL) Design for AWS] (#buildcl)

## Overview <a name="overview"></a>

The AWS FPGA HDK includes all the design files and scripts required to generate an Amazon FPGA Image (AFI). Developers can download the HDK and use it in their preferred design environment. AWS offers the `FPGA Developer AMI` on the [AWS Marketplace](https://aws.amazon.com/marketplace) with the required tools to develop, simulate, and build an AFI.

**NOTE:** The HDK is developed and tested in a **Linux** environment only

### Content of the release

The [documents directory](./docs) provides the specification for the AWS Shell (SH) to Custom Logic (CL) interface, and best practices for CL design and development.

The [common directory](./common) includes scripts, timing constraints and compile settings required during the AFI generation process. Developers should not change these files.

The [Custom Logic (cl) directory](./cl) is where the Custom Logic is expected to be developed. It includes a number of examples under the [examples directory](./cl/examples), as well as a placeholder for the developer's own Custom Logic under [developer_designs directory](./cl/developer_designs).  

The HDK also includes test benches for each provided example, and instructions on how to run RTL-level simulations.

## Getting Started <a name="gettingstarted"></a>

### Have an instance or server with Xilinx Vivado tools and License <a name="vivado"></a>

To get started, the developer needs to have a development environment with Xilinx Vivado tools installed. An easy way to get this by using the AWS FPGA Developer AMI and following the instructions inside the README.md of that AMI.

Please refer to the [release notes](../RELEASE_NOTES.md) for the exact version of Vivado tools, and the required license components.

### Install the HDK and setup environment <a name="setup"></a>

The AWS FPGA HDK can be cloned to your EC2 instance or server by executing:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_setup.sh

### Try out a "Hello World" example and others <a name="examples"></a>

The [Getting started with CL examples](./cl/examples/Getting_Started_With_CL_Examples.md) walks you through how to build, register, and use an AFI. 
The [Hello World readme](./cl/examples/cl_hello_world/README.md) provides the steps to build an AFI from the provided Hello World example CL, and how to load it on an F1 instance.
Other examples are available in the [examples directory](./cl/examples), each with its own README.md file.


### Start your own Custom Logic design <a name="startcl"></a>

The [start your own CL design](./cl/developer_designs/README.md) will guide you on how to setup your own CL project environment.

### Simulate your Custom Logic design <a name="simcl"></a>

You can use Vivado XSIM simulator, or bring your own simulator (like Synopsys', Mentor's, or Cadence).
Follow the [verification environment setup](https://github.com/aws/aws-fpga/wiki/Simulating-CL-Designs-(RTL-Simulation)#introduction) to run these simulations

### Build and submit the Custom Logic to AWS for generating an AFI <a name="buildcl"></a>

You can follow the [build scripts readme](./common/shell_current/new_cl_template/build/README.md) for step-by-step instructions on how to setup the scripts and run the build process.
This [checklist](./cl/CHECKLIST_BEFORE_BUILDING_CL.md) should be consulted before you start the build process.


