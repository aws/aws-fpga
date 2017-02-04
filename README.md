<span style="display: inline-block;">

# Table of Contents

1. [AWS EC2 FPGA Hardware and Software Development Kits] (#devkit)
    - [FPGA Hardware Development Kit (HDK)] (hdk/README.md)
        - [AWS FPGA Shell Specification](hdk/docs/AWS_Shell_Interface_Specification.md)
        - [Developing with OpenCL/SDAccel](hdk/docs/OpenCL_SDAccel_Development.md)
        - [FPGA PCIe Address Map](hdk/docs/AWS_Fpga_Pcie_Memory_Map.md)
    - [FPGA Software Development Kit (SDK)] (sdk/README.md)
        - [Access FPGA From Linux Applications] (hdk/docs/Programmers_View.md)
        - [AFI Management Tools](sdk/management/fpga_image_tools/README.md)
    - [FPGA Developer AMI available on AWS Marketplace](#devAmi)
    - [Developers' support](#devSupport)
2. [Quick Start] (#quickstart)
    - [Building an example AFI](#buildingAnExample)
    - [Using an AFI on EC2 F1 instace](#usingAfi)
    - [Starting a new CL](#clExamples)

# AWS EC2 FPGA Hardware and Software Development Kits <a name="devkit"></a>

This release includes two portions: [HDK](./hdk) for developing Amazon FPGA Image (AFI),  and [SDK](./sdk) for using AFI on FPGA-enabled EC2 instances [such as F1](https://aws.amazon.com/ec2/instance-types/f1/).

Execute `git clone http://github.com/aws/aws-fpga` to download this HDK+SDK release to your EC2 Instance or local server.
For an SSH connection execute `git clone git@github.com:aws/aws-fpga.git`.

The [Release Notes](./RELEASE_NOTES.md) document covers the list of supported features, programming environment, and known restrictions.

**NOTE: The HDK and SDK are tested and supported for Linux operating systems, for the time being, other OSs haven't been tested by AWS**

Please click the "Watch" button in GitHub upper right corner to stay posted.

## FPGA HDK

The [HDK directory](./hdk) is recommended for developers wanting to start building Amazon FPGA Images (AFI). It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any server or EC2 instance. The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI.

Execute [`source ./hdk_setup.sh`](./hdk_setup.sh) to setup the environment variables required by the rest of the HDK scripts.

## FPGA SDK

The [SDK directory](./sdk) includes the drivers and runtime environment required by any EC2 Instance running on F1. It includes the drivers and tools to interact with pre-built AFIs that are loaded to EC2 F1 FPGAs. The SDK is not required during the AFI development process; it is only required once the AFI is loaded onto an F1 instance.

## FPGA Developer AMI <a name="devAmi"></a>

AWS recommends the use of the F1 FPGA developer AMI for development on EC2 instances.  The HDK examples and quick start can be run on any [C4/M4/R4](https://aws.amazon.com/ec2/instance-types/) EC2 instance. But given the large size of the FPGA used in F1, the implementation tools require a minimum 15GiB Memory while 32GiB is optimal (C4.4XLarge or bigger, M4.2XLarge or bigger, R4.XLarge or bigger). C4.4XLarge and C4.8XLarge would provide the fastest execution time with 30 and 60GiB of memory respectively. 

During private access period in order to start using the AMI your AWS account needs to be whitelisted.  Once you are whitelisted, from the AWS console you will have access to AMIs:

* Make sure you are in N. Virginia (us-east-1).  
* Go to EC2->Launch Instance->My AMIs
* Select the ‘Shared with me’ box on the Ownership tab on the left.
* FPGA developer AMI will be prefixed with F1 

## Developer Support <a name="devSupport"></a>

*FPGA development AMI* During private access period, developers are emailed with details on how to get started with the FPGA Development AMI, terms and conditions and additional information on how to get started using F1 instances.  

[**AWS FPGA Users' Forum**](https://forums.aws.amazon.com/index.jspa): the FPGA development user forum is the first place to go to post questions, suggestions and receive important announcements. To gain access to the user forum, please go to https://forums.aws.amazon.com/index.jspa and login. During the preview, the first time you login, click on "Your Stuff" where you will see your forums username and userID at the end of the URL. Please email these to f1-preview@amazon.com with "FPGA forum access" in the subject line, in order to receive forum access. To be notified on important messages, posts you will need to click the “Watch Forum” button on the right side of the screen.

 
# Quick Start <a name="quickstart"></a>

## Building an Example AFI <a name="buidAnExample"></a>

By following the next few steps, you would have downloaded the HDK, compiled and built one of the example Custom Logic (CL) designs included in this HDK, and registered it with AWS.  

#### Prerequisites
* AWS FPGA HDK and SDK run in Linux environment only.
* If you can not access GitHub repository, please request access permission from your AWS representative.
* The build stage uses Xilinx's Vivado tool set. You should have an installed Vivado and Vivado License Manager (See [Release Notes](./RELEASE_NOTES.md) for details on the version).
* Executing `aws s3 <action>` and `aws ec2 create-fpga-image` require having AWS CLI installed, having an active AWS account, and the server/instance has been configured with your credentials and AWS region via `aws configure` command line.
* AWS offers FPGA Developer AMI with all Xilinx's Vivado tools and AWS CLI pre-installed.

**NOTE**: The DCP generation (`Step 7`) can take up to several hours to complete. 
We recommend that you initiate the generation in a way that prevents interruption. 
For example, if working on a remote machine, we recommend using window management tools such as [`screen`](https://www.gnu.org/software/screen/manual/screen.html) to mitigate potential network disconnects.  

```
$ git clone https://github.com/aws/aws-fpga     # Step 1:  Download the HDK and SDK code
$ cd aws-fpga                                   # Step 2:  Move to the root directory
$ source hdk_setup.sh                           # Step 3:  Set up the HDK environment variables
$ cd hdk/cl/examples/cl_simple                  # Step 4:  Change directory to one of the provided examples
$ export CL_DIR=$(pwd)                          # Step 5:  Define this directory as the root for the CL design
$ cd build/scripts                              # Step 6:  The build directory for synthesizing, placement, timing etc
$ source aws_build_dcp_from_cl.sh               # Step 7:  Generate a placed-and-routed design checkpoint (DCP)
$ cd $CL_DIR/build/checkpoints/to_aws           # Step 8:  This directory includes the DCP file
$ aws s3 mb s3://<bucket-name>                  # Step 9:  Create an S3 bucket (choose a unique bucket name)
$ aws s3 cp *.SH_CL_routed.dcp \                # Step 10: Upload the DCP file to S3
        s3://<bucket-name>/cl_simple.dcp
$ aws ec2 create-fpga-image \                   # Step 11: Ingest the generated DCP to create an AFI  
        --fpga-image-architecture xvu9p \
        --shell-version 0x11241611 \
        --fpga-pci-id deviceId=0x1d50,vendorId=0x6789,subsystemId=0x1d51,subsystemVendorId=0xfedc \
        --input-storage-location Bucket=<bucket-name>,Key=cl_simple.dcp
        --name MyFirstDCP
        --logs-storage-location Bucket=<bucket-name>,Key=logs/
```


## Using an AFI on EC2 F1<a name="usingAfi"></a>

Now that you have built an AFI, or if you want to use one of the example pre-built AFIs provided by AWS, you need to launch an EC2 F1 Instance, and install the SDK:

You can setup and install the SDK with the following few steps.  Note that the first two steps may be skipped if you have already run them in the above HDK setup.

```
$ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
$ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
$ source sdk_setup.sh                         # Set up the envronment variables, build and install the SDK
```

**NOTE:** The `sdk_setup.sh` would install the [FPGA management tools](./sdk/management/fpga_image_tools/README.md) if they are not already available in `/usr/bin`. The `sdk_setup.sh` requires having `gcc` installed.  if it is not installed, try running the next command to install it on Amazon Linux, Centos or Redhat distributions:

```
$ sudo yum groupinstall -y “Development Tools"
```

## Need to build a new Custom Logic and register it as an AFI?<a name="clExamples"></a>

The [Getting started with CL examples](./hdk/cl/examples/README.md) guide provides step-by-step instructions to build an AFI from one of the provided examples, register it with AWS, and load it on an EC2 F1 instance.

