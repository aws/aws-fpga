# Small Shell
This branch provides a Small Shell which is 30% smaller in size than the F1.X.1.4 Shell. Small Shell F1.S.1.0 occupies only 14 Clock Regions worth of real estate in the FPGA: 10 Clock Regions in Middle SLR, and 4 Clock Regions in Bottom SLR. Smaller physical footprint of the Shell F1.S.1.0 increases the available resources to the CL. This feature is available in Shell [F1.S.1.0](./hdk/common/shell_v04182104) provided in this developer kit.

⚠️ <b>NOTE:</b> Small Shell does not include DMA capability. Customers should implement their own DMA engine in the CL, or use [SDE IP](sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md) provided in the Developer Kit.

⚠️ <b>NOTE:</b> CL's with Small Shell F1.S.1.0 require Xilinx 2020.2 tools

⚠️ <b>NOTE:</b> Vitis, HLx and IPI flows are not supported with Small Shell since DMA engine is not included.

Following table shows the resources available to CL in comparison with F1.X.1.4 Shell:

|FPGA Resource Type	|Total Resource in VU9P FPGA	|Available for CL with F1.X.1.4 Shell	|Available for CL with Small Shell F1.S.1.0	|Improvement	|Improvement %	|
|---	|---	|---	|---	|---	|---	|
|CLB LUT	|1,181,768	|895,200	|980,272	|85,072	|9.50%	|
|LUT as Logic	|1,181,768	|895,200	|980,272	|85,072	|9.50%	|
|LUT as Memory	|591,840	|450,720	|493,004	|42,284	|9.38%	|
|CLB Registers	|2,363,536	|1,790,400	|1,960,544	|170,144	|9.50%	|
|CARRY8	|147,721	|111,900	|122,534	|10,634	|9.50%	|
|Block RAM Tile	|2,160	|1,680	|1,824	|144	|8.57%	|
|URAM	|960	|560	|636	|76	|13.57%	|
|DSPs	|6,840	|5,640	|6,000	|360	|6.38%	|
|MMCM	|30	|20	|23	|3	|15.00%	|

**Additional Features:**

1. Improved FPGA <-> Host Performance by 5-20% due to increase in Number of PCIM Outstanding Read Transactions to 64. This allows CL to issue more number of read requests over PCIM and therefore achieving higher performance. This results in ~20% increase in performance for smaller read request lengths = 0x1 and 0x3; and ~5% increase in performance for request lengths = 0x7, 0xF, 0x1F and 0x3F.
2. Small Shell reduces routing congestion and ease timing closure because of additional resources in the Bottom SLR.
3. AWS recommends customers to place their DMA Engine in Bottom SLR because the PCIM interface between Shell<->CL is now moved to Bottom SLR.

# Table of Contents
1. [Overview of AWS EC2 FPGA Development Kit](#overview-of-aws-ec2-fpga-development-kit)
1. [Getting Started](#getting-started)
    - [Getting Familiar with AWS](#getting-familiar-with-aws)
    - [First time setup](#setting-up-development-environment-for-the-first-time)
    - [Quickstarts](#quickstarts)
1. [Documentation Overview](#documentation-overview)
1. [Developer Support](#developer-support)

# Overview of AWS EC2 FPGA Development Kit

AWS EC2 FPGA Development Kit is a set of development and runtime tools to develop, simulate, debug, compile and run hardware accelerated applications on [Amazon EC2 F1 instances](https://aws.amazon.com/ec2/instance-types/f1/).
It is distributed between this github repository and FPGA Developer AMI - [Centos](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) / [AL2](https://aws.amazon.com/marketplace/pp/B08NTMMZ7X) provided by AWS with no cost of development tools.

⚠️ <b>NOTE:</b> The developer kit is supported for Linux operating systems only.

## Development Flow
After creating an FPGA design (also called CL - Custom logic), developers can create an Amazon FPGA Image (AFI) and easily deploy it to an F1 instance. AFIs are reusable, shareable and can be deployed in a scalable and secure way.

![Alt text](hdk/docs/images/f1-Instance-How-it-Works-flowchart.jpg)

## Development Environments

| Development Environment | Description | Accelerator Language | Hardware Interface | Debug Options| Typical Developer |
| --------|---------|-------|---------|-------|-------|
| [Hardware Accelerator Development using Vivado](hdk/README.md) | Fully custom hardware development experience provides hardware developers with the tools required for developing AFIs for AWS FPGA instances  | Verilog/VHDL | [XDMA Driver](sdk/linux_kernel_drivers/xdma/README.md), [peek/poke](sdk/userspace/README.md) | Simulation, Virtual JTAG | HW Developer with advanced FPGA experience |

> For on-premise development, Vivado must have the [correct license and use one of the supported tool versions](./docs/on_premise_licensing_help.md).

## FPGA Developer AMI

The [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) is available on the AWS marketplace without a software charge and includes tools needed for developing FPGA Designs to run on AWS F1.

Given the large size of the FPGA used inside AWS F1 Instances, Xilinx tools work best with 32GiB Memory.
z1d.xlarge/c5.4xlarge and z1d.2xlarge/c5.8xlarge instance types would provide the fastest execution time with 30GiB+ and 60GiB+ of memory respectively.
Developers who want to save on cost, could start coding and run simulations on low-cost instances, like t2.2xlarge, and move to the aforementioned larger instances to run the synthesis of their acceleration code.

AWS marketplace offers multiple versions of the FPGA Developer AMI. The following compatibility table describes the mapping of currently supported developer kit versions to AMI versions:

| Developer Kit Version | Tool Version Supported | Compatible FPGA Developer AMI Version |
|-----------|-----------|------|
| 1.4.18+ | 2020.2 | v1.10.X (Xilinx Vivado/Vitis 2020.2) |

# Getting Started

### Getting familiar with AWS
If you have never used AWS before, we recommend you start with [AWS getting started training](https://aws.amazon.com/getting-started/), and focus on the basics of the [AWS EC2](https://aws.amazon.com/ec2/) and [AWS S3](https://aws.amazon.com/s3/) services.
Understanding the fundamentals of these services will make it easier to work with AWS F1 and the FPGA Developer Kit.

FPGA Image generation and EC2 F1 instances are supported in the us-east-1 (N. Virginia), us-west-2 (Oregon), eu-west-1 (Ireland) and us-gov-west-1 ([GovCloud US](https://aws.amazon.com/govcloud-us/)) [regions](https://aws.amazon.com/about-aws/global-infrastructure/).

> ⚠️ <b>NOTE:</b> By default, your AWS Account will have an EC2 F1 Instance launch limit of 0.
> Before using F1 instances, you will have to open a [Support Case](https://console.aws.amazon.com/support/home#/case/create) to increase the EC2 Instance limits to allow launching F1 instances.

### Setting up development environment for the first time

You have the choice to develop on AWS EC2 using the [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) or on-premise.

> ℹ️ <b>INFO:</b> We suggest starting with the FPGA Developer AMI with [build instances](#fpga-developer-ami) on EC2 as it has Xilinx tools and licenses setup for you to be able to quickly get into development.

> ℹ️ <b>INFO:</b> For on-premise development, you will need to have [Xilinx tools and licenses available for you to use](./docs/on_premise_licensing_help.md)

1. Start a Build Instance first to start your development.
    > 💡 <b>TIP:</b> This instance does not have to be an F1 instance. You only require an F1 instance to run your AFI's(Amazon FPGA Image) once you have gone through your design build and AFI creation steps.

    > ℹ️ <b>INFO:</b> If you need to follow GUI Development flows, please checkout our [Developer Resources](./developer_resources/README.md) where we provide Step-By-Step guides to setting up a GUI Desktop.
1. Clone the small_shell branch of [FPGA Developer Kit](https://github.com/aws/aws-fpga) on your instance.  
    ```git clone -b small_shell https://github.com/aws/aws-fpga.git```  
1. Follow the quickstarts from the next section. 
1. Review the [F1.S.1.0 shell migration guide](./hdk/docs/AWS_Small_Shell_Migration_Guidelines.md) for help with migrating from shell F1.X.1.4 to small shell F1.S.1.0
### Quickstarts
Before you create your own AWS FPGA design, we recommend that you go through one of the step-by-step Quickstart guides:

| Description | Quickstart | Next Steps |
|----|----|----|
| Custom Hardware Development(HDK) | [HDK hello_world Quickstart](hdk/README.md) | [CL to Shell and DRAM connectivity example](./hdk/cl/examples/cl_dram_dma), [Virtual Ethernet Application](./sdk/apps/virtual-ethernet) using the [Streaming Data Engine](./hdk/cl/examples/cl_sde) |

# Documentation Overview

Documentation is located throughout this developer kit and the table below consolidates a list of key documents to help developers find information:

| Topic | Document Name |  Description |
|-----------|-----------|------|
| AWS setup | [Setup AWS CLI and S3 Bucket](./docs/Setup_AWS_CLI_and_S3_Bucket.md) | Setup instructions for preparing for AFI creation |
| Developer Kit | [RELEASE NOTES](./RELEASE_NOTES.md) | Release notes for all developer kit features, excluding the shell  |
| Developer Kit | [Errata](./ERRATA.md) | Errata for all developer kit features, excluding the shell  |
| Migration Guidelines | [Migration guide](./hdk/docs/AWS_Small_Shell_Migration_Guidelines.md) | Migration guidelines for moving from XDMA shell F1.X.1.4 to small shell F1.S.1.0 |
| F1 Shell | [AWS Shell RELEASE NOTES](./hdk/docs/AWS_Shell_RELEASE_NOTES.md) | Release notes for F1 shell |
| F1 Shell | [AWS Shell ERRATA](./hdk/docs/AWS_Shell_ERRATA.md) | Errata for F1 shell |
| F1 Shell | [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) | Shell-CL interface specification for HDK developers building AFI |
| F1 Shell - Timeout and AXI Protocol Protection | [How to detect a shell timeout](hdk/docs/HOWTO_detect_shell_timeout.md) | The shell will terminate transactions after a time period or on an illegal transaction.  This describes how to detect and gather data to help debug CL issues caused by timeouts. |
| HDK - Host Application | [Programmer View](./hdk/docs/Programmer_View.md) | Host application to CL interface specification |
| HDK - CL Debug | [Debug using Virtual JTAG](./hdk/docs/Virtual_JTAG_XVC.md) | Debugging CL using Virtual JTAG (Chipscope)  |
| HDK - Simulation | [Simulating CL Designs](./hdk/docs/RTL_Simulating_CL_Designs.md) | Shell-CL simulation specification |
| HDK - Driver | [README](./sdk/linux_kernel_drivers/xdma/README.md) | Describes the XDMA driver used by HDK examples and includes a link to an installation guide |
| AFI | [AFI Management SDK](./sdk/userspace/fpga_mgmt_tools/README.md) | CLI documentation for managing AFI on the F1 instance |
| AFI - EC2 CLI | [copy\_fpga\_image](./hdk/docs/copy_fpga_image.md), [delete\_fpga\_image](./hdk/docs/delete_fpga_image.md), [describe\_fpga\_images](./hdk/docs/describe_fpga_images.md), [fpga\_image\_attributes](./hdk/docs/fpga_image_attributes.md) | CLI documentation for administering AFIs |
| AFI - Creation Error Codes | [create\_fpga\_image\_error\_codes](hdk/docs/create_fpga_image_error_codes.md) | CLI documentation for managing AFIs |
| AFI - Power | [FPGA Power, recovering from clock gating](./hdk/docs/afi_power.md) | Helps developers with understanding FPGA power usage, preventing power violations on the F1 instance and recovering from a clock gated slot. |
| On-premise Development | [Tools, Licenses required for on-premise development](./docs/on_premise_licensing_help.md) | Guidance for developer wanting to develop AFIs from on-premises instead of using the [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) |
| Frequently asked questions | [FAQ](./FAQs.md)| Q/A are added based on developer feedback and common AWS forum questions  |


# Developer Support

* The [**Amazon FPGA Development User Forum**](https://forums.aws.amazon.com/forum.jspa?forumID=243&start=0) is the first place to go to post questions, learn from other users and read announcements.
    * We recommend joining the [AWS forums](https://forums.aws.amazon.com/forum.jspa?forumID=243) to engage with the FPGA developer community, AWS and Xilinx engineers to get help.

* You could also file a [Github Issue](https://github.com/aws/aws-fpga/issues) for support. We prefer the forums as this helps the entire community learn from issues, feedback and answers.
    * Click the "Watch" button in GitHub upper right corner to get regular updates.
