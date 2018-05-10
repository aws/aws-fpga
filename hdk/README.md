
# AWS FPGA Hardware Development Kit (HDK)

AWS FPGA HDK is the official kit provided by AWS to facilitate RTL development (Verilog/VHDL) of an Amazon FPGA Image (AFI).

Useful resources:
* Check out the [release notes](../RELEASE_NOTES.md) for information about the latest bug fixes, updates, and features added to the HDK.
* [FAQ](../FAQs.md)

## Table of Contents
1. [Overview](#overview)
2. [Getting Started](#gettingstarted)
    - [Xilinx Vivado Tools and License Requirements](#vivado)
    - [HDK Installation and Environment Setup](#setup)
    - [Custom Logic (CL) Examples](#examples)
    - [Start Custom Logic (CL) Design](#startcl)
    - [Simulate Custom Logic (CL) RTL Design](#simcl)
    - [Build Custom Logic (CL) Design to send to AWS](#buildcl)
3. [Vivado IP Integrator (IPI) and GUI Workflow](#ipi)

<a name="overview"></a>
## Overview

The AWS FPGA HDK includes all the design files and scripts required to build an Amazon FPGA Image (AFI) from RTL (Verilog/VHDL) custom design. Developers can download the HDK and use it in their preferred design environment: In the cloud or on-premises. AWS offers the [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) with pre-installed tools to develop, simulate, and build an AFI.

**NOTE:** The HDK is developed and tested in a **Linux** environment only

### Content of the release

The [documents directory](./docs) provides the specification for the AWS Shell (SH) to Custom Logic (CL) interface, best practices for CL design and development, an overview of the PCI memory map and how would runtime software

The [common directory](./common) includes common environment setup scripts, common build scripts and constraints files, IP library like the DRAM controller, as well as AWS Shell Design Checkpoint (DCP). This directory make include multiple AWS Shell directories: The main recommended for production environment is under `shell_stable` directory, which other Shell directories may be provided for experimental or preview of upcoming AWS Shells.

Developers should not change any file in the `/common` directory.

The [Custom Logic (cl) directory](./cl) is where the Custom Logic is expected to be developed (For RTL-based development using Verilog/VHDL). It includes a number of examples under the [examples directory](./cl/examples), as well as a placeholder for the developer's own Custom Logic under [developer_designs directory](./cl/developer_designs).

The HDK also includes test benches for each provided example, and instructions on how to run RTL-level simulations.

<a name="gettingstarted"></a>
## Getting Started

### Have an EC2 instance or on-premises server installed with Xilinx Vivado tools and License <a name="vivado"></a>

To get started, the developer needs to have a development environment with Xilinx Vivado tools installed. An easy way to get this by using the [AWS FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) which comes with all the tools and required licenses pre-installed.

For developers who like to work on-premises or different AMI in the cloud, follow the [required license for on-premises document](./docs/on_premise_licensing_help.md).

Please refer to the [release notes](../RELEASE_NOTES.md) or the [supported Vivado version](../supported_vivado_versions.txt) for the exact version of Vivado tools, and the required license components.

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

You can follow the [build scripts readme](./common/shell_v071417d3/new_cl_template/build/README.md) for step-by-step instructions on how to setup the scripts and run the build process.
This [checklist](./cl/CHECKLIST_BEFORE_BUILDING_CL.md) should be consulted before you start the build process.

<a name="ipi"></a>
## GUI Workflow with Vivado IP Integrator (IPI)

Developers have the option of working in a GUI mode using Vivado IPI. With IPI you can create complex F1 custom designs on a graphical interface design canvas. The HDK development kit provides AWS FPGA IP which will help you quickly develop your custom designs by enabling you to quickly drop in IP blocks into your design.

The IPI flow isolates the Custom Logic (CL) from the shell, allowing the developer to focus on differentiating logic and leave the heavy lifting, undeferentiated hardware interfaces development to the AWS FPGA Shell. Generating a logic diagram is simplified with designer automation that connects RTL, IP, and peripherals like DDR and PCIe in a correct by construction flow. The “what you see is what you get” tool generates the equivalent code by instantiating the underlying IP and RTL with access via the Vivado project to the entire FPGA hardware design flow. A video walk through of this flow for a simple diagram is available at https://www.xilinx.com/video/hardware/using-vivado-ip-integrator-and-amazon-f1.html. This flow example is a good starting point for developers who want to quickly add IP blocks with high performance access to multiple external memories.

The IPI RTL flow enables the developer a single graphical environment to add sources and IP, simulate, synthesize the RTL, and then stitch together the Custom Logic (CL) with the Shell’s design checkpoint (DCP). For design debug, developers can easily instantiate logic analyzers or other debug logic, investigate timing and resource reports, and quickly link from implementation messages to the design view and source code when applicable. This flow is a good starting point for experts in RTL design or designs who have a minimal amount of interconnection between RTL modules.

The below documentation covers the setup, tutorials of the IPI flows and IPI FAQ. Developers are advised to read all documents before starting thier first AWS FPGA design with IPI.

[IPI Setup](./docs/IPI_GUI_Vivado_Setup.md)

[IPI Tutorials/Examples](./docs/IPI_GUI_Examples.md)

[IPI Developer Flow](./docs/IPI_GUI_Flows.md)

[IPI FAQ](./docs/IPI_GUI_Vivado_FAQ.md)
