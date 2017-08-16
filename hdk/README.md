
# AWS FPGA Hardware Development Kit (HDK)

AWS FPGA HDK is the official kit provided by AWS to facilitate RTL development (Verilog/VHDL) of an Amazon FPGA Image (AFI).

Useful resources:
* Check out the [release notes](../RELEASE_NOTES.md) for information about the latest bug fixes, updates, and features added to the HDK.
* [FAQ](../aws-fpga/FAQs.md)

## Table of Contents
1. [Overview](#overview)
2. [Getting Started](#gettingstarted)
    - [Xilinx Vivado Tools and License Requirements](#vivado)
    - [HDK Installation and Environment Setup](#setup)
    - [Custom Logic (CL) Examples](#examples)
    - [Start Custom Logic (CL) Design](#startcl)
    - [Simulate Custom Logic (CL) RTL Design](#simcl)
    - [Build Custom Logic (CL) Design to send to AWS](#buildcl)
3. [Vivado HLx Setup/Environment](#vivadohlx)    

<a name="overview"></a>
## Overview 

The AWS FPGA HDK includes all the design files and scripts required to build an Amazon FPGA Image (AFI) from RTL (Verilog/VHDL) custom design. Developers can download the HDK and use it in their preferred design environment: In the cloud or on-premise. AWS offers the [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) with pre-installed tools to develop, simulate, and build an AFI.

**NOTE:** The HDK is developed and tested in a **Linux** environment only

### Content of the release

The [documents directory](./docs) provides the specification for the AWS Shell (SH) to Custom Logic (CL) interface, best practices for CL design and development, an overview of the PCI memory map and how would runtime software 

The [common directory](./common) includes common environment setup scripts, common build scripts and constraints files, IP library like the DRAM controller, as well as AWS Shell Design Checkpoint (DCP). This directory make include multiple AWS Shell directories: The main recommended for production environment is under `shell_stable` directory, which other Shell directories may be provided for experimental or preview of upcoming AWS Shells.

Developers should not change any file in the `/common` directory.

The [Custom Logic (cl) directory](./cl) is where the Custom Logic is expected to be developed (For RTL-based development using Verilog/VHDL). It includes a number of examples under the [examples directory](./cl/examples), as well as a placeholder for the developer's own Custom Logic under [developer_designs directory](./cl/developer_designs).  

The HDK also includes test benches for each provided example, and instructions on how to run RTL-level simulations.

<a name="gettingstarted"></a>
## Getting Started 

### Have an instance or server with Xilinx Vivado tools and License <a name="vivado"></a>

To get started, the developer needs to have a development environment with Xilinx Vivado tools installed. An easy way to get this by using the [AWS FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) which comes with all the tools and required licenses pre-installed.

For developers who like to work on-premise or different AMI in the cloud, follow the [required license for on-premise document](./docs/on_premise_licensing_help.md).

Please refer to the [release notes](../RELEASE_NOTES.md) or the [supported Vivado version](./supported_vivado_versions.txt) for the exact version of Vivado tools, and the required license components.

 <a name="setup"></a>
### Install the HDK and setup environment

The AWS FPGA HDK can be cloned to your EC2 instance or server by executing:

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_setup.sh

Note that sourcing `hdk_setup.sh` will set a few environment variables that are used throughout the examples in the HDK.  It should be re-sourced in each new terminal.

### Try out a "Hello World" example and others <a name="examples"></a>

The [Examples readme](./cl/examples/README.md) provides an overview of all the steps to turn a Custom Logic (CL) into an Amazon FPGA Image (AFI) to be used on AWS EC2 FPGA-enabled instances. 

The [Hello World readme](./cl/examples/cl_hello_world/README.md) provides the steps to build an AFI from the provided Hello World example CL, and how to load it on an F1 instance.

Other examples are available in the [examples directory](./cl/examples), each with its own README.md file. 

The [Examples Table](./cl/examples/cl_examples_list.md) summarize which capabilities are demonstrated in each example.

<a name="startcl"></a>
### Start your own Custom Logic design (RTL flow, using Verilog/VHDL)

The [start your own CL design](./cl/developer_designs/Starting_Your_Own_CL.md) will guide you on how to setup your own CL project environment once the HDK is set up.

<a name="simcl"></a>
### Simulate your Custom Logic design (RTL Simulation)

You can use Vivado XSIM simulator, or bring your own simulator (like Synopsys' VCS, Mentor's Questa, or Cadence Incisive).
Follow the [RTL simulation environment setup](./docs/RTL_Simulating_CL_Designs.md#introduction) to run these simulations

### Build and submit the Custom Logic to AWS for generating an AFI <a name="buildcl"></a>

You can follow the [build scripts readme](./common/shell_v04151701/new_cl_template/build/README.md) for step-by-step instructions on how to setup the scripts and run the build process.
This [checklist](./cl/CHECKLIST_BEFORE_BUILDING_CL.md) should be consulted before you start the build process.

<a name="vivadohlx"></a>
## Vivado HLx Overview

The Vivado HLx allows users to use Vivado in project mode to create designs or importing designs using RTL or IP Integrator flows.
The below documentation covers the setup, tutorials of RTL/IP Integrator flows and FAQ.  Users are recommended to read all documents before starting any design.

[HLx Setup README](./docs/IPI_GUI_Vivado_Setup.md)

[HLx Flows](./docs/IPI_GUI_Flows.md)

[HLx Tutorials/Examples](./docs/IPI_GUI_Examples.md)

[HLx FAQ](./docs/IPI_GUI_Vivado_FAQ.md)
