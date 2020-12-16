# User Controlled DDR Autoprecharge preview

This is a preview of a new user controlled autoprecharge feature that provides the `cl_sh_ddr_awuser` and
`cl_sh_ddr_aruser` user bits in the DDR-C(Shell) Controller to control DDR Autoprecharge. The feature is provided by the AWS Shell v12142010.

A use-case of the new shell is provided in the [cl_dram_dma example](./hdk/cl/examples/cl_dram_dma/README.md) 
and the user bits are tied off to 0. You can follow the same steps to create your own CL using the new shell. The CL build scripts will automatically point to the new shell.

⚠️ <b>NOTE:</b> CL's with Shell v12142010 require Xilinx 2020.1 Toolset with patch AR75524. The Patch will be automatically applied 
when you run `hdk_setup.sh`

Patch AR75524 allows Xilinx 2020.1 toolset to generate the DDR controller IP with user bits to control DDR Autoprecharge.

⚠️ <b>NOTE:</b> Shell v12142010 is only available to use in `us-east-1` and on F1.16XL instances.


# Table of Contents
1. [Getting Started](#getting-started)
    - [Getting Familiar with AWS](#getting-familiar-with-aws)
    - [First time setup](#setting-up-development-environment-for-the-first-time)
    - [Quickstarts](#quickstarts)
1. [Documentation Overview](#documentation-overview)
1. [Developer Support](#developer-support)

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
1. Clone the [FPGA Developer Kit](https://github.com/aws/aws-fpga) on your instance.
    ```git clone https://github.com/aws/aws-fpga.git```
1. Follow the quickstarts from the next section.

### Quickstarts
Before you create your own AWS FPGA design, we recommend that you go through one of the step-by-step Quickstart guides:

| Description | Quickstart | 
|----|----|
| Custom Hardware Development(HDK) |  [CL to Shell and DRAM connectivity example](./hdk/cl/examples/cl_dram_dma) |


# Documentation Overview

Documentation is located throughout this developer kit and the table below consolidates a list of key documents to help developers find information:

| Topic | Document Name |  Description |
|-----------|-----------|------|
| AWS setup | [Setup AWS CLI and S3 Bucket](./SDAccel/docs/Setup_AWS_CLI_and_S3_Bucket.md) | Setup instructions for preparing for AFI creation |
| Developer Kit | [RELEASE NOTES](./RELEASE_NOTES.md), [Errata](./ERRATA.md) | Release notes and Errata for all developer kit features, excluding the shell  |
| Developer Kit | [Errata](./ERRATA.md) | Errata for all developer kit features, excluding the shell  |
| F1 Shell | [AWS Shell RELEASE NOTES](./hdk/docs/AWS_Shell_RELEASE_NOTES.md) | Release notes for F1 shell |
| F1 Shell | [AWS Shell ERRATA](./hdk/docs/AWS_Shell_ERRATA.md) | Errata for F1 shell |
| F1 Shell | [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md) | Shell-CL interface specification for HDK developers building AFI |
| F1 Shell - Timeout and AXI Protocol Protection | [How to detect a shell timeout](hdk/docs/HOWTO_detect_shell_timeout.md) | The shell will terminate transactions after a time period or on an illegal transaction.  This describes how to detect and gather data to help debug CL issues caused by timeouts. |
| HDK - Host Application | [Programmer View](./hdk/docs/Programmer_View.md) | Host application to CL interface specification |
| HDK - CL Debug | [Debug using Virtual JTAG](./hdk/docs/Virtual_JTAG_XVC.md) | Debugging CL using Virtual JTAG (Chipscope)  |
| HDK - Simulation | [Simulating CL Designs](./hdk/docs/RTL_Simulating_CL_Designs.md) | Shell-CL simulation specification |
| HDK - Driver | [README](./sdk/linux_kernel_drivers/xdma/README.md) | Describes the DMA driver (XDMA) used by HDK examples and includes a link to an installation guide |
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
