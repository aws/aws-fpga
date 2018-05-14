<span style="display: inline-block;">

# Table of Contents

1. [AWS EC2 FPGA Hardware and Software Development Kits](#devkit)
    - [FPGA Developer AMI available on AWS Marketplace](#devAmi)
    - [FPGA Hardware Development Kit Workflow(HDK)](#fpgahdk)
    - [GUI Workflow with Vivado IP Integrator (IPI)](#ipi)
    - [FPGA Software Development Kit (SDK)](#fpgasdk)
    - [OpenCL Development Environment with Amazon EC2 F1 FPGA Instances to accelerate your C/C++ applications](#sdaccel)
    - [Developer Support](#devSupport)
2. [Building an example AFI](#buildingAnExample)
    - [Prerequisites](#buildingafiprereq)
    - [Using an AFI on EC2 FPGA Instances](#usingAfi)

<a name="devkit"></a>
# AWS EC2 FPGA Hardware and Software Development Kits

The AWS EC2 FPGA Hardware and Software Development Kits consists of three components: Hardware development workflows for developing Amazon FPGA Image (AFI) with the [HDK](./hdk), Software development workflows for developing AFI with [OpenCL/C/C++](./SDAccel) and [SDK](./sdk) for using AFIs on FPGA-enabled EC2 instances [such as F1](https://aws.amazon.com/ec2/instance-types/f1/).

Execute `git clone https://github.com/aws/aws-fpga.git` to download this HDK+SDAccel+SDK release to your EC2 Instance or local server.
For an SSH connection execute `git clone git@github.com:aws/aws-fpga.git`. [To get help with connecting to Github via SSH](https://help.github.com/articles/connecting-to-github-with-ssh/)

The [Release Notes](./RELEASE_NOTES.md) and [Errata](./ERRATA.md) list supported features, programming environments, and known restrictions.

**NOTE: This developer kit is tested and supported for Linux operating systems, for the time being, other OSs haven't been tested by AWS**

Please click the "Watch" button in GitHub upper right corner to stay posted.

<a name="devAmi"></a>
## FPGA Developer AMI

AWS Marketplace offers the [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) for development on EC2 instances. The FPGA Developer AMI comes with Xilinx tools and AWS CLI pre-installed.  The HDK examples and quick start can be run on any [C4/C5/M4/M5/R4/T2.2XLARGE](https://aws.amazon.com/ec2/instance-types/) EC2 instance. Given the large size of the FPGA used in AWS FPGA instances, the implementation tools require 32GiB Memory (ex: C4.4XLarge, M4.2XLarge, R4.XLarge, T2.2XLarge). C4.4XLarge and C4.8XLarge would provide the fastest execution time with 30 and 60GiB of memory respectively.

This release supports Xilinx SDx 2017.4 and 2017.1.  The compatibility table describes the mapping of developer kit version to [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) version:  

| Developer Kit Version   | Tool Version Supported     |  Compatible FPGA developer AMI Version     |
|-----------|-----------|------|
| 1.3.0-1.3.6 | 2017.1 | v1.3.5 |
| 1.3.7-1.3.X | 2017.1 | v1.3.5-v1.3.X (Xilinx SDx 2017.1) |
| 1.3.7-1.3.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |

FPGA developer kit version is listed in [hdk_version.txt](./hdk/hdk_version.txt)

FPGA developer kit supported tool versions are listed in [supported_vivado_versions](./supported_vivado_versions.txt)

<a name="fpgahdk"></a>
## FPGA HDK

The [HDK directory](./hdk) contains useful information and scripts for developers wanting to start building Amazon FPGA Images (AFI).  It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any on-premises server or an EC2 instance. The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI. The following resources provide further details:

[HDK README](./hdk/README.md)

[AWS FPGA Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)

[FPGA PCIe Address Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md)

<a name="ipi"></a>
## GUI Workflow with Vivado IP Integrator (IPI)

Developers have the option of working in a GUI mode using Vivado IPI.  With IPI you can create complex F1 custom designs on a graphical interface design canvas.  The HDK development kit provides AWS FPGA IP which will help you quickly develop your custom designs by enabling you to quickly drop in IP blocks into your design.

The IPI flow isolates the Custom Logic (CL) from the shell, allowing the developer to focus on differentiating logic and leave the heavy lifting, undifferentiated hardware interfaces development to the AWS FPGA Shell.  Generating a logic diagram is simplified with designer automation that connects RTL, IP, and peripherals like DDR and PCIe in a correct by construction flow.  The “what you see is what you get” tool generates the equivalent code by instantiating the underlying IP and RTL with access via the Vivado project to the entire FPGA hardware design flow.  A video walk through of this flow for a simple diagram is available at https://www.xilinx.com/video/hardware/using-vivado-ip-integrator-and-amazon-f1.html.  This flow example is a good starting point for developers who want to quickly add IP blocks with high performance access to multiple external memories.

The IPI RTL flow enables the developer a single graphical environment to add sources and IP, simulate, synthesize the RTL, and then stitch together the Custom Logic (CL) with the Shell’s design checkpoint (DCP).  For design debug, developers can easily instantiate logic analyzers or other debug logic, investigate timing and resource reports, and quickly link from implementation messages to the design view and source code when applicable.  This flow is a good starting point for experts in RTL design or designs who have a minimal amount of interconnection between RTL modules.

The below documentation covers the setup, tutorials of the IPI flows and IPI FAQ.  Developers are advised to read all documents before starting their first AWS FPGA design with IPI.  

[IPI Setup](./hdk/docs/IPI_GUI_Vivado_Setup.md)

[IPI Tutorials/Examples](./hdk/docs/IPI_GUI_Examples.md)

[IPI Developer Flow](./hdk/docs/IPI_GUI_Flows.md)

[IPI FAQ](./hdk/docs/IPI_GUI_Vivado_FAQ.md)

<a name="fpgasdk"></a>
## FPGA SDK

The [SDK directory](./sdk) includes the runtime environment required to run on EC2 FPGA instances. It includes the drivers and tools to manage the AFIs that are loaded to EC2 FPGA instance slots. The SDK isn't required during the AFI development process; it is only required once an AFI is loaded onto an EC2 FPGA instance. The following resources provide further details:

[SDK README](./sdk/README.md)

[Access FPGA From Linux Applications](./hdk/docs/Programmer_View.md)

[AFI Management Tools](./sdk/userspace/fpga_mgmt_tools/README.md)

<a name="sdaccel"></a>
## OpenCL Development Environment with Amazon EC2 F1 FPGA Instances to accelerate your C/C++ applications

The OpenCL development environment allows customers to use OpenCL with Amazon EC2 F1 FPGA Instances to accelerate their C/C++ applications. Software developers with little to no FPGA experience, will find a familiar development experience and now can use the cloud-scale availability of FPGAs to supercharge their applications.

Kernels are expressed in OpenCL or C/C++ and accelerated by implementing them in custom FPGA hardware. In addition, the development environment from Xilinx called SDAccel allows the acceleration to be performed using pre-existing RTL designs.

This developer kit has 50+ examples to help you get started on FPGA acceleration.  To get started, review the [SDAccel README](SDAccel/README.md)

<a name="devSupport"></a>
## Developer Support

The [**Amazon FPGA Development User Forum**](https://forums.aws.amazon.com/forum.jspa?forumID=243&start=0) is the first place to go to post questions, learn from other users and read announcements from the EC2 FPGA team.

* To be notified on important messages click on the “Watch Forum” button on the right side of the screen.
* In case you can't see "Your Stuff" details, you will need to logout using the logout button on the forums page and log back in again.

<a name="buildingAnExample"></a>
# Building a Custom Logic AFI for AWS FPGA Instances

Developers can build their own Custom Logic (CL) and deploy it on AWS.
The CL must comply with the [AWS Shell Interface Specifications](./hdk/docs/AWS_Shell_Interface_Specification.md), and pass through the build scripts.

The [CL Examples directory](./hdk/cl/examples) is provided to assist developers in creating a functional CL implementation. Each example includes:

1. The source code for the example under the `/design` directory.
2. The timing, clock and placement constraints files, scripts for compiling the example design. (This requires running in an instance/server that have Xilinx tools and license installed. Developers are recommended to use the FPGA Development AMI available free of charge on [AWS Marketplace](#devAmi)).
3. The final build, called Design Checkpoint (DCP) that can be submitted for AWS to generate the AFI.
4. An AFI-ID for a pre-generated AFI that matches the example design.
5. Software source code required on the FPGA-enabled instance to run the example.
6. Software binary that can be loaded on an FPGA-enabled instance to test the AFI.

In summary:

- An AFI can be created using the files in #1, #2, and #3. The AFI creation can take place on any EC2 instance or on-premises.
- The AFI can be used in an EC2 F1 instance by using the files in #4, #5 and #6.

By following the example CLs, a developer will learn how to interface to the AWS Shell of the FPGA, compile the source code to create an AFI, and load/run an AFI from the F1 instance for use.


<a name="buildingafiprereq"></a>
### Prerequisites
* AWS FPGA HDK and SDK run in Linux environment only.

* The build stage uses Xilinx's Vivado tool set. In case you build on-premises you should have an installed Vivado that has the correct license.  Please check for [supported versions of Vivado](./supported_vivado_versions.txt). [Release Notes](./RELEASE_NOTES.md) may contain additional information.
* Executing `aws s3 <action>` and `aws ec2 create-fpga-image` require having AWS CLI installed, having an active AWS account, and the server/instance has been configured with your credentials and the same AWS region as your S3 bucket via `aws configure` command line. It’s also required that your instance and the S3 bucket where the tarball reside in will be in the same AWS region.  Please refer to [AWS documentation for help with configuring the AWS CLI.](http://docs.aws.amazon.com/cli/latest/userguide/cli-chap-getting-started.html)

The [Getting started with CL examples](./hdk/cl/examples/README.md) guide provides step-by-step instructions to build an AFI from one of the provided examples, register it with AWS, and load it on an EC2 FPGA instance.

<a name="usingAfi"></a>
## Using an AFI on EC2 FPGA Instances
Now that you have built an AFI, or if you want to use one of the example pre-built AFIs provided by AWS, you need to launch an EC2 FGPA Instance, and install the SDK as detailed at: [SDK Quick Start](./sdk/README.md)


