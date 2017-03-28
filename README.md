<span style="display: inline-block;">

# Table of Contents

1. [AWS EC2 FPGA Hardware and Software Development Kits](#devkit)
    - [FPGA Hardware Development Kit (HDK)](#fpgahdk)
    - [FPGA Software Development Kit (SDK)](#fpgasdk)
    - [FPGA Developer AMI available on AWS Marketplace](#devAmi)
    - [Developer Support](#devSupport)
2. [Quick Start] (#quickstart)
    - [Building an example AFI](#buildingAnExample)
    - [Using an AFI on EC2 FPGA instace](#usingAfi)
    - [Starting a new CL](#clExamples)

<a name="devkit"></a>
# AWS EC2 FPGA Hardware and Software Development Kits 

This release includes two portions: [HDK](./hdk) for developing Amazon FPGA Image (AFI),  and [SDK](./sdk) for using AFI on FPGA-enabled EC2 instances [such as F1](https://aws.amazon.com/ec2/instance-types/f1/).

Execute `git clone https://github.com/aws/aws-fpga.git` to download this HDK+SDK release to your EC2 Instance or local server.
For an SSH connection execute `git clone git@github.com:aws/aws-fpga.git`. [Help with connecting to Github via SSH] (https://help.github.com/articles/connecting-to-github-with-ssh/)

The [Release Notes](./RELEASE_NOTES.md) document covers the list of supported features, programming environment, and known restrictions.

**NOTE: The HDK and SDK are tested and supported for Linux operating systems, for the time being, other OSs haven't been tested by AWS**

Please click the "Watch" button in GitHub upper right corner to stay posted.

<a name="fpgahdk"></a>
## FPGA HDK 

The [HDK directory](./hdk) is recommended for developers wanting to start building Amazon FPGA Images (AFI). It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any server or EC2 instance. The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI. The following resources provide further details:

[HDK README](./hdk/README.md)
        
[AWS FPGA Shell Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)
        
[FPGA PCIe Address Map](./hdk/docs/AWS_Fpga_Pcie_Memory_Map.md)
        
<a name="fpgasdk"></a>
## FPGA SDK

The [SDK directory](./sdk) includes the runtime environment required to run on EC2 FPGA instances. It includes the drivers and tools to interact with AFIs that are loaded to EC2 FPGA instance slots. The SDK is not required during the AFI development process; it is only required once the AFI is loaded onto an EC2 FPGA instance. The following resources provide further details:

[SDK readme](./sdk/README.md)

[Access FPGA From Linux Applications](./hdk/docs/Programmers_View.md)

[AFI Management Tools](./sdk/management/fpga_mgmt_tools/README.md)

<a name="fpgasdaccel"></a>
## SDAccel - Comming soon

The [sdaccel directory](./sdaccel) includes the environment required to run opencl/sdaccel flow on EC2 instances. It includes the drivers and tools to interact with AFIs that are loaded to EC2 FPGA instance slots. 

[Developing with OpenCL/SDAccel](./hdk/docs/OpenCL_SDAccel_Development.md)

<a name="devAmi"></a>
## FPGA Developer AMI 

AWS Marketplace offers the [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) for development on EC2 instances. The FPGA Developer AMI comes with Xilinx tools and AWS CLI pre-installed.  The HDK examples and quick start can be run on any [C4/M4/R4](https://aws.amazon.com/ec2/instance-types/) EC2 instance. Given the large size of the FPGA used in AWS FPGA instances, the implementation tools require a minimum 15GiB Memory while 32GiB is recommended (C4.4XLarge, M4.2XLarge, R4.XLarge). C4.4XLarge and C4.8XLarge would provide the fastest execution time with 30 and 60GiB of memory respectively.

<a name="devSupport"></a>
## Developer Support 

[**AWS FPGA Development User Forum**](https://forums.aws.amazon.com/index.jspa): the FPGA development user forum is the first place to go to post questions, suggestions and read announcements from the AWS FPGA team. To gain access to the user forum:

* Login to https://forums.aws.amazon.com/index.jspa 
* **Note** *During the preview, the first time you login, click on "Your Stuff" where you will see your forums username and userID at the end of the URL. Email your userID to f1-preview@amazon.com with "FPGA forum access" in the subject line, in order to receive forum access.*
* To be notified on important messages, posts you will need to click the “Watch Forum” button on the right side of the screen.
* In case you can't see "Your Stuff" details, you will need to logout using the logout button on the forums page and log back in again. 
 
<a name="quickstart"></a>
# Quick Start 

<a name="buildingAnExample"></a>
## Building an Example AFI 

By following a few steps, you would have downloaded the HDK, compiled and built one of the example Custom Logic (CL) designs included with the HDK, and registered it with AWS. [Building a Custom Logic (CL) implementation for AWS FPGA instances](./hdk/cl/examples#overview-on-process-for-building-a-custom-logic-cl-implementation-for-aws-fpga-instances)

#### Prerequisites
* AWS FPGA HDK and SDK run in Linux environment only.
* If you can not access GitHub repository, please request access permission from your AWS representative.
* The build stage uses Xilinx's Vivado tool set. You should have an installed Vivado that is supported.  Please check for [supported versions of Vivado](./hdk/supported_vivado_versions.txt). [Release Notes](./RELEASE_NOTES.md) may contain additional information.
* Executing `aws s3 <action>` and `aws ec2 create-fpga-image` require having AWS CLI installed, having an active AWS account, and the server/instance has been configured with your credentials and the same AWS region as your S3 bucket via `aws configure` command line. It’s also required that your instance and the S3 bucket where the tarball reside in will be in the same AWS region. 


```
$ git clone https://github.com/aws/aws-fpga.git # Step 1:  Download the HDK and SDK code
$ cd aws-fpga                                   # Step 2:  Move to the root directory
$ source hdk_setup.sh                           # Step 3:  Set up the HDK environment variables, downloads shell from S3, runs tool version checks
$ cd hdk/cl/examples/cl_hello_world             # Step 4:  Change directory to one of the provided examples
$ export CL_DIR=$(pwd)                          # Step 5:  Define this directory as the root for the CL design
$ cd build/scripts                              # Step 6:  The build directory for synthesizing, placement, timing etc
$ source aws_build_dcp_from_cl.sh               # Step 7:  Generate a placed-and-routed design checkpoint (DCP)
$ cd $CL_DIR/build/checkpoints/to_aws           # Step 8:  This directory includes the DCP file
$ aws s3 mb s3://<bucket-name>                  # Step 9:  Create an S3 bucket (choose a unique bucket name)
$ aws s3 cp *.Developer_CL.tar \                # Step 10: Upload the file to S3
         s3://<bucket-name>/
$ create-fpga-image \                           # Step 11: Ingest the generated DCP to create an AFI
        --afi-name <afi-name> \
	--afi-description <afi-description> \
	--dcp-bucket <dcp-bucket-name> \
	--dcp-key <tarball-name> \
	--logs-bucket <logs-bucket-name> \
	--logs-key <logs-folder>
```
**NOTE**: The DCP generation (`Step 7` above) can take up to several hours to complete.  We recommend to initiate the generation in a way that prevents interruption.  For example, if working on a remote machine, we recommend using window management tools such as [`screen`](https://www.gnu.org/software/screen/manual/screen.html) to mitigate potential network disconnects.  

<a name="usingAfi"></a>
## Using an AFI on EC2 FPGA Instances

Now that you have built an AFI, or if you want to use one of the example pre-built AFIs provided by AWS, you need to launch an EC2 FGPA Instance, and install the SDK as detailed at: [SDK Quick Start](./sdk/README.md)


<a name="clExamples"></a>
## Need to build a new Custom Logic and register it as an AFI?

The [Getting started with CL examples](./hdk/cl/examples/README.md) guide provides step-by-step instructions to build an AFI from one of the provided examples, register it with AWS, and load it on an EC2 FPGA instance.
