<span style="display: inline-block;">

# Table of Contents

1. [Overview of AWS EC2 FPGA Development Kit](#overviewdevkit)
    - [Development environments](#overviewdevenv)
    - [Runtime environments](#overviewrunenv)
    - [Example applications](#overviewexapps)
    - [Development tools](#overviewdevtools)
2. [Getting Started](#gettingstarted)
3. [FPGA Developer AMI available on AWS Marketplace](#devAmi)
4. [FPGA Hardware Development Kit (HDK)](#fpgahdk)
5. [FPGA Software Development Kit (SDK)](#fpgasdk)
6. [OpenCL Development Environment with Amazon EC2 F1 FPGA Instances to accelerate your C/C++ applications](#sdaccel)
7. [Developer Support](#devSupport)
8. [Recommended Documentation](#doccontents)
9. [Github tips and tricks](#githubtipstricks)


<a name="overviewdevkit"></a>
# Overview of AWS EC2 FPGA Development Kit

The AWS EC2 FPGA Development Kit is provided by AWS to support development and runtime on [AWS FPGA instances](https://aws.amazon.com/ec2/instance-types/f1/).  Amazon EC2 FPGA instances are high-performance compute instances with field programmable gate arrays (FPGAs) that are programmed to create custom hardware accelerations in EC2. F1 instances are easy to program and AWS provides everything needed to develop, simulate, debug, compile and run hardware accelerated applications.  Using the [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ), developers create an FPGA design. Once the FPGA design (also called CL - Custom logic) is complete, developers create the Amazon FPGA Image (AFI), and deploy it to the F1 instance in just a few clicks. AFIs are reusable, shareable and can be deployed in a scalable and secure way.
![Alt text](hdk/docs/images/f1-Instance-How-it-Works-flowchart.jpg)

<a name="overviewdevenv"></a>
## Overview of Development Environments

| Development Environment     | Description | Accelerator Language   | Development Tool | Debug Options| Typical Developer / FPGA Experience |
| --------|---------|---------|-------|-------|-------|
| [Software Defined Accelerator Development - SDAccel](SDAccel/README.md) | Development experience leverages an optimized compiler to allow easy new accelerator development or migration of existing C/C++/openCL, Verilog/VHDL to AWS FPGA instances | C/C++/OpenCL, Verilog/VHDL (RTL) | SDx/Vivado (GUI or scipt) | SW/HW Emulation, Simulation, GDB, Virtual JTAG (Chipscope) | SW or HW Developer with zero FPGA experience |
| [Hardware Accelerator Development - HDK](hdk/README.md) | Fully custom hardware development experience provides hardware developers with the tools required for developing AFIs for AWS FPGA instances  | Verilog/VHDL | Vivado | Simulation, Virtual JTAG | HW Developer with advanced FPGA experience |
| [IP Integrator or High Level Synthesis (HLx)](hdk/docs/IPI_GUI_Vivado_Setup.md) | Graphical interface development experience for integrating IP and high level synthesis development | Verilog/VHDL/C | Vivado (GUI) | Simulation, Virtual JTAG | HW Developer with intermediate FPGA experience |

<a name="overviewrunenv"></a>
## Overview of Runtime Environments

| Runtime Environment     | Hardware Interface | Host Code Language   | FPGA Tools |
| --------|---------|---------|-------|
| [C/C++ Software Defined Accelerator Development](SDAccel/README.md) | OpenCL APIs, [XOCL Driver](./sdk/linux_kernel_drivers/xocl), [HAL](SDAccel/userspace/src2) | C/C++ | [SDK](./sdk), SDx |
| [Hardware Accelerator Development](hdk/README.md) | [XDMA Driver](sdk/linux_kernel_drivers/xdma/README.md), [peek/poke](sdk/userspace/README.md) | C/C++ | [SDK](./sdk), Vivado |
| [IP Integrator or High Level Synthesis (HLx)](hdk/docs/IPI_GUI_Vivado_Setup.md) | [XDMA Driver](sdk/linux_kernel_drivers/xdma/README.md), [peek/poke](sdk/userspace/README.md) | C/C++ | [SDK](./sdk), Vivado |

<a name="overviewdevtools"></a>
## Overview of Development Tools

| Tool     | Development/Runtime | Tool location | Description |
| --------|---------|---------|---------|
| SDx 2017.4 | Development | [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) | Used for [Software Defined Accelerator Development](SDAccel/README.md) |
| Vivado 2017.4 | Development | [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) | Used for [Hardware Accelerator Development](hdk/README.md) |
| FPGA AFI Management Tools | Runtime | [SDK - fpga\_mgmt\_tools](sdk/userspace/fpga_mgmt_tools) | Command-line tools used for FPGA management while running on the F1 instance |
| Virtual JTAG | Development (Debug) | [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) | Runtime debug waveform |
| wait\_for\_afi | Development | [wait\_for\_afi.py](shared/bin/scripts/wait_for_afi.py) | Helper script that notifies via email on AFI generation completion |
| notify\_via\_sns | Development | [notify\_via\_sns.py](shared/bin/scripts/notify_via_sns.py) | Notifies developer when design build process completes |
| AFI Administration | Development | [Copy](hdk/docs/copy_fpga_image.md), [Delete](hdk/docs/delete_fpga_image.md), [Describe](hdk/docs/describe_fpga_images.md), [Attributes](hdk/docs/fpga_image_attributes.md) | AWS CLI EC2 commands for managing your AFIs |


NOTE: For on-premises development, SDx/Vivado must have the correct license and use one of the [supported versions of SDx/Vivado](./supported_vivado_versions.txt). The FPGA HDK+SDK [Release Notes](./RELEASE_NOTES.md) may contain additional information.  The following links have more information on on-premises development:  [Vivado requirements](hdk/docs/on_premise_licensing_help.md) and [SDx requirements](SDAccel/docs/On_Premises_Development_Steps.md)

<a name="overviewexapps"></a>
## Overview of Example Applications
| Accelerator Application     | Example | Development Environment   | Description |
| --------|---------|---------|-------|
| Custom hardware | [cl\_hello\_world](hdk/cl/examples/cl_hello_world) | HDK - RTL (Verilog) | Simple [getting started example](hdk/README.md) with minimal hardware |
| Custom hardware | [cl\_dram\_dma](hdk/cl/examples/cl_dram_dma) | HDK - RTL (Verilog) | Demonstrates CL connectivity to the F1 shell and connectivity to/from all DDRs |
| Custom hardware IP integration example using a GUI | [cl\_dram\_dma\_hlx](hdk/cl/examples/cl_dram_dma_hlx) | HLx - Verilog  | Demonstrates CL connectivity to the F1 shell and connectivity to/from DRAM using the Vivado IP Integrator GUI |
| Digital Up-Converter using High Level Synthesis | [cl\_hls\_dds\_hlx](hdk/cl/examples/cl_hls_dds_hlx) | HLx - C-to-RTL  | Demonstrates an example application written in C that is synthesized to RTL (Verilog) |
| Security   | [AES, RSA, SHA1](https://github.com/Xilinx/SDAccel_Examples/tree/master/security) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration to speed up security software algorithms  |
| Computer Vision   | [Affine, Convolve, Huffman, IDCT](https://github.com/Xilinx/SDAccel_Examples/tree/master/vision) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration to speed up image detection algorithms  |
| Misc Algorithms   | [Kmeans, SmithWaterman, MatrixMult](https://github.com/Xilinx/SDAccel_Examples/tree/master/acceleration) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration to compute, sorting and search algorithms  |
| Financial   | [Blacksholes, Heston](https://github.com/KitAway/FinancialModels_AmazonF1) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration on Monte Carlo financial models  |
| Custom Hardware with Software Defined Acceleration   | [RTL Kernels](https://github.com/Xilinx/SDAccel_Examples/tree/master/getting_started/rtl_kernel) | SDAccel - RTL (Verilog) + C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates a quick method for developing new or migrating existing hardware designs (RTL) |
| File Compression   | [GZip](https://github.com/Xilinx/Applications/tree/master/GZip) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration to speed up GZIP compression on an FPGA |
| WebP Image Compression   | [WebP](https://github.com/Xilinx/Applications/tree/master/webp) | SDAccel - C/C++/OpenCL  | Developed using software defined acceleration, this example demonstrates methods of using hardware acceleration to speed up WebP encoder application on an FPGA |

<a name="gettingstarted"></a>
# Getting Started

### New to AWS?
If you are new to AWS, we recommend you start with [AWS getting started training](https://aws.amazon.com/getting-started/), to learn how to use AWS EC2, S3 and the AWS CLI.  These services are required to start developing accelerations for AWS FPGAs. For example, creating an AFI requires [AWS CLI](http://docs.aws.amazon.com/cli/latest/userguide/cli-chap-getting-started.html) installed and the execution of `aws s3 <action>` (`aws ec2 create-fpga-image`).

### New to AWS FPGAs and setting up a development environment?
The developer kit is supported for Linux operating systems only.  You have the choice to develop on AWS EC2 using the [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) or on-premises. Within a linux environment, you should execute `git clone https://github.com/aws/aws-fpga.git` to download the latest release to your EC2 Instance or local server. Using a SSH connection, execute `git clone git@github.com:aws/aws-fpga.git`. [To get help with connecting to Github via SSH](https://help.github.com/articles/connecting-to-github-with-ssh/).

Before you start our first AWS FPGA design, we recommend to go through one of the step-by-step guides.  The guides will walk through development steps for hello world examples.  Based on the tables above, pick the development environment that best fits your needs and use the guide to get started:
  * For fastest way to get started on FPGA accelerator development, start with the software defined development environment.  The guide starts with the [SW Hello World example](SDAccel/README.md).
    * Next use the same guide to develop using the C/C++/openCL/RTL based [80+ examples on github](./SDAccel/examples/xilinx_2017.4).
  * For custom hardware development (HDK) environment, start with the [HDK Hello World example](hdk/README.md).
    * Next use the same guide to develop using the [cl\_dram\_dma](hdk/cl/examples/cl_dram_dma).

### In-depth training and resources
Once you completed your hello world examples, we recommend diving deeper into a training workshop or application notes
 * Software-defined [re:Invent 2017 Workshop](https://github.com/awslabs/aws-fpga-app-notes/blob/master/reInvent17_Developer_Workshop/README.md) demonstrates a video encoder acceleration and how to debug and optimize your accelerator.
 * Custom hardware developers need to learn about how the hardware accelerator interfaces to the F1 Shell
  * [Shell Interface](hdk/docs/AWS_Shell_Interface_Specification.md)
  * [Shell Address Map](hdk/docs/AWS_Fpga_Pcie_Memory_Map.md)
  * [Programmer view of the FPGA](./hdk/docs/Programmer_View.md)
  * [Virtual JTAG](hdk/docs/Virtual_JTAG_XVC.md)
  * [Application for methods of interfacing the host application to the Hardware accelerator](https://github.com/awslabs/aws-fpga-app-notes)

<a name="devAmi"></a>
# FPGA Developer AMI

The [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) is available on the AWS marketplace without a software charge and includes free tools and drivers needed for FPGA development on EC2 instances. FPGA development runs on several [EC2 instance types](https://aws.amazon.com/ec2/instance-types/). Given the large size of the FPGA used inside the AWS FPGA instances, the implementation tools require 32GiB Memory (ex: c4.4xlarge, m4.2xlarge, r4.xlarge, t2.2xlarge). c4.4xlarge and c4.8xlarge would provide the fastest execution time with 30 and 60GiB of memory respectively. Developers who want to save on cost, could start coding and run simulations on low-cost instances, like t2.2xlarge, and move to the aforementioned larger instances to run the synthesis of their acceleration code.

Currently, AWS marketplace includes multiple versions of the FPGA developer AMI, supporting Xilinx SDx 2017.4 and 2017.1 toolchain versions. The following compatibility table describes the mapping of developer kit version to AMI version:

| Developer Kit Version   | Tool Version Supported     |  Compatible FPGA developer AMI Version     |
|-----------|-----------|------|
| 1.3.0-1.3.6 | 2017.1 | v1.3.5 |
| 1.3.7-1.3.X | 2017.1 | v1.3.5-v1.3.X (Xilinx SDx 2017.1) |
| 1.3.7-1.3.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |
| 1.4.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |

<a name="fpgahdk"></a>
# Hardware Development Kit (HDK)

The [HDK directory](./hdk/README.md) contains useful information, examples, and scripts for developers wanting to start building Amazon FPGA Images (AFI).  It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any on-premises server or an EC2 instance. The developer kit is not required if you plan to use a pre-built AFI shared from another developer.

<a name="sdaccel"></a>
# Software-defined Development Environment

The software-defined development environment allows customers to compile their C/C++/OpenCL code into the FPGA as kernels, and use OpenCL APIs to pass data to the FPGA. Software developers with no FPGA experience will find a familiar development experience that supercharges cloud applications.

In addition, this development environment (also called SDAccel) allows the mix of C/C++ and RTL accelerator designs into a C/C++ software based development environment.  This method enables faster prototyping using C/C++ while supporting manual optimization of critical blocks within RTL.  This approach is similar to optimizing time critical functions using software compiler optimization methods.

This developer kit has 80+ examples to help you get started on FPGA acceleration.  To get started, review the [Software-defined development environment readme](SDAccel/README.md).

<a name="fpgasdk"></a>
# Runtime Tools (SDK)

The [SDK directory](./sdk/README.md) includes the runtime environment required to run on EC2 FPGA instances. It includes the drivers and tools to manage the AFIs that are loaded on the FPGA instance. The SDK isn't required during the AFI development process; it is only required once an AFI is loaded onto an EC2 FPGA instance. The following sdk resources are provided:
  * Linux Kernel Drivers - The developer kit includes three drivers:
    * [XDMA Driver](sdk/linux_kernel_drivers/xdma/README.md) - DMA interface to/from HDK accelerators.
    * [XOCL Driver](sdk/linux_kernel_drivers/xocl) - DMA interface with software defined accelerators (also called hardware kernels).
    * [EDMA Driver](sdk/linux_kernel_drivers/edma/README.md) - Legacy DMA interface to/from HDK accelerators.
  * [FPGA Libraries](sdk/userspace/fpga_libs) - APIs used by C/C++ host applications.
  * [FPGA Management Tools](sdk/userspace/fpga_mgmt_tools/README.md) - AFI management APIs for runtime loading/clearing FPGA image, gathering metrics and debug interface on the F1 instance.

<a name="devSupport"></a>
# Developer Support

The [**Amazon FPGA Development User Forum**](https://forums.aws.amazon.com/forum.jspa?forumID=243&start=0) is the first place to go to post questions, learn from other users and read announcements from the EC2 FPGA team.

* Click the "Watch" button in GitHub upper right corner to get regular updates.
* We recommend you will join the [AWS forum](https://forums.aws.amazon.com/forum.jspa?forumID=243) to engage with the FPGA developer community and get help when needed (both AWS and Xilinx engineers monitor this forum).
* In case you can't see "Your Stuff" details, you will need to logout using the logout button on the forums page and log back in again.

<a name="doccontents"></a>
# Documentation Overview

The documentation is located throughout this developer kit, therefore, to help developers find information quicker the table below consolidates a list of key documents:

| Topic | Document Name |  Description |
|-----------|-----------|------|
| Developer Kit Features | [RELEASE\_NOTES](./RELEASE_NOTES.md), [Errata](./ERRATA.md) | Release notes and Errata for all developer kit features,  excluding the shell  |
| Frequently asked questions | [FAQ](./FAQs.md), [Errata](./ERRATA.md) | Q/A are added based on developer feedback and common AWS forum questions  |
| F1 Shell (HDK) | [AWS\_Shell\_RELEASE\_NOTES](./hdk/docs/AWS_Shell_RELEASE_NOTES.md), [AWS\_Shell\_ERRATA](./hdk/docs/AWS_Shell_ERRATA.md) | Release notes and Errata for F1 shell |
| F1 Shell (HDK) | [AWS\_Shell\_Interface\_Specification](hdk/docs/AWS_Shell_Interface_Specification.md) | Shell-CL interface specification for HDK developers building AFI |
| AWS setup | [Setup\_AWS\_CLI\_and\_S3\_Bucket](SDAccel/docs/Setup_AWS_CLI_and_S3_Bucket.md) | Setup instructions for preparing for AFI creation |
| SDx graphical interface (SDAccel) | [README\_GUI](SDAccel/docs/README_GUI.md) | Instructions using the SDx GUI for software defined acceleration development and debug |
| Software defined acceleration using RTL (SDAccel) | [Debug\_RTL\_Kernel](SDAccel/docs/Debug_RTL_Kernel.md) | Instructions on debugging RTL Kernel |
| Software defined acceleration Run time (SDAccel) | [Create\_Runtime\_AMI](SDAccel/docs/Create_Runtime_AMI.md) | Instructions on creating a runtime AMI |
| Host Application (HDK) | [Programmer\_View](hdk/docs/Programmer_View.md) | Host application to CL interface specification |
| CL Debug (HDK) | [Virtual\_JTAG\_XVC](hdk/docs/Virtual_JTAG_XVC.md) | Debugging CL using Virtual JTAG (Chipscope)  |
| CL/Shell Simulation (HDK) | [RTL\_Simulating\_CL\_Designs](hdk/docs/RTL_Simulating_CL_Designs.md) | Shell-CL simulation specification |
| Driver (HDK) | [README](sdk/linux_kernel_drivers/xdma/README.md) | Describes the DMA driver (XDMA) used by HDK examples and includes a link to an installation guide |
| Shell Timeout and AXI Protocol Protection | [HOWTO\_detect\_shell\_timeout](hdk/docs/HOWTO_detect_shell_timeout.md) | The shell will terminate transactions after a time period or on an illegal transaction.  This describes how to detect and gather data to help debug CL issues caused by timeouts. |
| AFI Power | [afi\_power](hdk/docs/afi_power.md) | Helps developers with understanding AFI power and preventing power violations on the F1 instance |
| AFI Management | [README](sdk/userspace/fpga_mgmt_tools/README.md) | CLI documentation for managing AFI on the F1 instance |
| AFI Administration | [copy\_fpga\_image](hdk/docs/copy_fpga_image.md), [delete\_fpga\_image](hdk/docs/delete_fpga_image.md), [describe\_fpga\_images](hdk/docs/describe_fpga_images.md), [fpga\_image\_attributes](hdk/docs/fpga_image_attributes.md) | CLI documentation for administering AFIs |
| AFI Creation Error Codes | [create\_fpga\_image\_error\_codes](hdk/docs/create_fpga_image_error_codes.md) | CLI documentation for managing AFIs |
| Developing on-premises | [HDK: on\_premise\_licensing\_help](hdk/docs/on_premise_licensing_help.md), [SDAccel: On\_Premises\_Development\_Steps](SDAccel/docs/On_Premises_Development_Steps.md) | Guidance for developer wanting to develop AFIs from on-premises instead of using the [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) running on AWS EC2 |


<a name="githubtipstricks"></a>
# Github tips and tricks
  * [Cloning the repository](https://help.github.com/articles/cloning-a-repository/)
  * [Forking the repository](https://help.github.com/articles/fork-a-repo/)
  * [Searching code](https://help.github.com/articles/searching-code/) and [advanced search syntax](https://help.github.com/articles/understanding-the-search-syntax/)
  * [Finding files](https://help.github.com/articles/finding-files-on-github/)
  * Simply replace github.com with gitprint.com to generate a printable PDF




