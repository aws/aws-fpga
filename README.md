<span style="display: inline-block;">
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

# AWS EC2 FPGA Hardware and Software Development Kit

This release include two portions: [HDK](./hdk) for developing Amazon FPGA Image (AFI),  and [SDK](./sdk) for using AFI on FPGA-enabled [EC2 instances like F1](https://aws.amazon.com/ec2/instance-types/f1/)

call `git clone http://github.com/aws/aws-fpga` to download this HDK+SDK release to your EC2 Instance or local server.

Please click the "Watch" button in github upper right corner to stay updated.

## FPGA HDK

The [HDK directory](./hdk) includes the development environment, simulation, build and AFI creation scripts, and recommended for developers wanting to start building Amazon FPGA Images (AFI).  The HDK can be installed in any server or EC2 instance. AWS recommend to developers to use the [FPGA Developer AMI on AWS Marketplace place](https//aws.amazon.com/marketplace/AmazonFPGAAmi) and install the HDK there. The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI.

Call [`source ./hdk_setup.sh`](./hdk_setup.sh) to setup the environment variables needed for the rest of the HDK scripts to work.

## FPGA SDK

The [SDK directory](./sdk) includes the drivers and runtime environment required by any EC2 Instance running on F1. It has the drivers and tools to interact with pre-built AFIs that are loaded to EC2 F1 FPGAs. The SDK is not required during the AFI design and build process, they are only required once you load the AFI into an F1 instance.

# Quick start

By running the next few steps, you would have downloaded the HDK+SDK, compile and build on of the sampled Custom Logics (CL), and register it with AWS

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source hdk_setup.sh                         # Set up the environment variables
    $ cd hdk/cl/examples/cl_simple                # Change directory to one of the provided examples
    $ export CL_DIR=$(pwd)                        # Define this directory as the root for the CL design
    $ cd build/scripts                            # The build directory for synthesizing, placement, timing etc
    $ vivado -mode batch -source create_dcp_from_cl.tcl   # make sure you have vivado installed and vivado license manager running
    $ aws ec2 createFpgaImage TBD TBD TBD         # Make sure you have aws account, aws-cli installed, and you ran `aws configure`

You can setup and install the SDK with these few steps.  Note that the first two steps may be skipped if you have already ran them in the above HDK setup.

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source sdk_setup.sh                         # Set up the envronment variables
    $ cd sdk                                      # Change directories to the top-level SDK directory       
    $ sdk_install.sh                              # Build and install the SDK

## Building, Registering and Using an AFI 

The [Getting started with CL examples](./hdk/cl/examples/Getting_Started_With_CL_Examples.md) can walk you through step by step how to build an AFI from one of the provided example, registers with AWS, and run it on an EC2 F1 instance.

