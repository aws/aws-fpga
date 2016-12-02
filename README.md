<span style="display: inline-block;">
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

# AWS EC2 FPGA Hardware and Software Development Kit

This release includes two portions: [HDK](./hdk) for developing Amazon FPGA Image (AFI),  and [SDK](./sdk) for using AFI on FPGA-enabled EC2 instances [such as F1](https://aws.amazon.com/ec2/instance-types/f1/).

Execute `git clone http://github.com/aws/aws-fpga` to download this HDK+SDK release to your EC2 Instance or local server.

**NOTE: The HDK and SDK are tested and supported for Linux operating systems, for the time being, other OSs haven't been tested by AWS**

Please click the "Watch" button in GitHub upper right corner to stay posted.

## FPGA HDK

The [HDK directory](./hdk) is recommended for developers wanting to start building Amazon FPGA Images (AFI). It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any server or EC2 instance. AWS recommends the use of the [FPGA Developer AMI on AWS Marketplace](https//aws.amazon.com/marketplace/AmazonFPGAAmi). The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI.

Execute [`source ./hdk_setup.sh`](./hdk_setup.sh) to setup the environment variables required by the rest of the HDK scripts.

## FPGA SDK

The [SDK directory](./sdk) includes the drivers and runtime environment required by any EC2 Instance running on F1. It includes the drivers and tools to interact with pre-built AFIs that are loaded to EC2 F1 FPGAs. The SDK is not required during the AFI development process; it is only required once the AFI is loaded onto an F1 instance.

# Quick Start

## Building an Example AFI

By following the next few steps, you would have downloaded the HDK, compiled and built one of the example Custom Logic (CL) designs included in this HDK, and registered it with AWS.  You can run these steps on any EC2 instance, with [C4](https://aws.amazon.com/ec2/instance-types/) and [M4](https://aws.amazon.com/ec2/instance-types/) being the recommended instance types for performance.

#### Prerequisites
* AWS FPGA HDK and SDK run in Linux environment only.
* If you can not access GitHub repository, please request access permission from your AWS representative.
* The build stage uses Xilinx's Vivado tool set. You should have an installed Vivado and Vivado License Manager (See [Release Notes](./RELEASE_NOTES.md) for details on the version).
* Executing `aws s3 <action>` and `aws ec2 create-fpga-image` require having AWS CLI installed, having an active AWS account, and the server/instance has been configured with your credentials and AWS region via `aws configure` command line.
* AWS offers FPGA Developer AMI with all Xilinx's Vivado tools and AWS CLI pre-installed.
* We recommend executing the following steps inside a [`screen`](https://www.gnu.org/software/screen/manual/screen.html) window to avoid interrupting the DCP generation command (`Step #7`) which can take up to several hours. 

```
$ git clone https://github.com/aws/aws-fpga   # Step 1: Download the HDK and SDK code
$ cd aws-fpga                                 # Step 2: Move to the root directory
$ source hdk_setup.sh                         # Step 3: Set up the HDK environment variables
$ cd hdk/cl/examples/cl_simple                # Step 4: Change directory to one of the provided examples
$ export CL_DIR=$(pwd)                        # Step 5: Define this directory as the root for the CL design
$ cd build/scripts                            # Step 6: The build directory for synthesizing, placement, timing etc
$ vivado -mode batch -source create_dcp_from_cl.tcl     # Step 7: Generate a placed-and-routed design checkpoint (DCP) 
$ cd $CL_DIR/build/checkpoints/to_aws         # Step 8: This directory includes the DCP file
$ ﻿aws s3 mb s3://<bucket-name>                # Step 9: Create an S3 bucket (choose a unique bucket name)
$ aws s3 cp *.SH_CL_routed.dcp \              # Step 10: Upload the DCP file to S3
      s3://<bucket-name>/cl_simple.dcp
$ aws ec2 create-fpga-image \                 # Step 11: Ingest the generated DCP to create an AFI  
      --fpga-image-architecture xvu9p \
      --shell-version 0x11241611 \
      --fpga-pci-id deviceId=0x1d50,vendorId=0x6789,subsystemId=0x1d51,subsystemVendorId=0xfedc \
      --input-storage-location Bucket=<bucket-name>,Key=cl_simple.dcp
```

**NOTE**: The `aws ec2 create-fpga-image` command-line API is coming soon and subject to change.

## Using an AFI on EC2 F1

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

## Need to build a new Custom Logic and register it as an AFI?

The [Getting started with CL examples](./hdk/cl/examples/Getting_Started_With_CL_Examples.md) guide provides step-by-step instructions to build an AFI from one of the provided examples, register it with AWS, and load it on an EC2 F1 instance.

