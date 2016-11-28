<span style="display: inline-block;">
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

# AWS EC2 FPGA Hardware and Software Development Kit

This release includes two portions: [HDK](./hdk) for developing Amazon FPGA Image (AFI),  and [SDK](./sdk) for using AFI on FPGA-enabled EC2 instances [such as F1](https://aws.amazon.com/ec2/instance-types/f1/).

Execute `git clone http://github.com/aws/aws-fpga` to download this HDK+SDK release to your EC2 Instance or local server.

**NOTE: The HDK and SDK are tested and supported for Linux operating systems, other OSes haven't been tested by AWS**

Please click the "Watch" button in github upper right corner to stay posted.

## FPGA HDK

The [HDK directory](./hdk) is recommended for developers wanting to start building Amazon FPGA Images (AFI). It includes the development environment, simulation, build and AFI creation scripts.  The HDK can be installed on any server or EC2 instance. AWS recommends the use of the [FPGA Developer AMI on AWS Marketplace](https//aws.amazon.com/marketplace/AmazonFPGAAmi). The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI.

Execute [`source ./hdk_setup.sh`](./hdk_setup.sh) to setup the environment variables required by the rest of the HDK scripts.

## FPGA SDK

The [SDK directory](./sdk) includes the drivers and runtime environment required by any EC2 Instance running on F1. It includes the drivers and tools to interact with pre-built AFIs that are loaded to EC2 F1 FPGAs. The SDK is not required during the AFI development process; it is only required once the AFI is loaded onto an F1 instance.

# Quick Start

## Building an Example AFI

By following the next few steps, you would have downloaded the HDK, compiled and built one of the example Custom Logic (CL) designs included in this HDK, and registered it with AWS.  You can run these steps on any EC2 instance, with [C4](https://aws.amazon.com/ec2/instance-types/) and [M4](https://aws.amazon.com/ec2/instance-types/) being the recommended instance types for performance.

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source hdk_setup.sh                         # Set up the environment variables
    $ cd hdk/cl/examples/cl_simple                # Change directory to one of the provided examples
    $ export CL_DIR=$(pwd)                        # Define this directory as the root for the CL design
    $ cd build/scripts                            # The build directory for synthesizing, placement, timing etc
    $ vivado -mode batch -source create_dcp_from_cl.tcl   # Make sure Xilinx Vivado is installed and Vivado License Manager is running
    $ aws ec2 createFpgaImage TBD TBD TBD         # Make sure you have aws account, aws-cli installed, and you ran `aws configure`

## Using an AFI on EC2 F1

Now that you have built an AFI, or if you want to use one of the example pre-built AFIs provided by AWS, you need to launch an instance on EC2 F1, and have the SDK installed:

You can setup and install the SDK with the following few steps.  Note that the first two steps may be skipped if you have already ran them in the above HDK setup.

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source sdk_setup.sh                         # Set up the envronment variables, build and install the SDK

## Need to build a new Custom Logic and register it as AFI?

The [Getting started with CL examples](./hdk/cl/examples/Getting_Started_With_CL_Examples.md) guide provides step-by-step instructions to build an AFI from one of the provided examples, register it with AWS, and load it on an EC2 F1 instance.

