<span style="display: inline-block;">
[![Join the chat at https://gitter.im/aws/aws-fpga](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/aws/aws-fpga?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

# AWS EC2 FPGA Hardware and Software Development Kit

call `git clone http://github.com/aws/aws-fpga` to download this HDK+SDK release to your EC2 Instance or local server.

This release include two portions: HDK for developing Amazon FPGA Image (AFI),  and SDK for using AFI on FPGA-enabled EC2 instances like F1 [![aws.amazon.com/ec2/f1]]

Please click the "Watch" botton in github upper right corner to stay updated.

## FPGA HDK

The HDK directory includes the development environment, simulation, build and AFI creation scripts, and recommended for developers wanting to start building Amazon FPGA Images (AFI).  The HDK can be installed in any server or EC2 instance. AWS recommend to developers to use the "FPGA Developer AMI" on AWS Marketplace place [![aws.amazon.com/marketplace/AmazonFPGAAmi]] and install the HDK there. The HDK is not required if you are using a pre-built AFI and not planning to build your own AFI.

Call `source ./hdk_setup.sh` to setup the environment variables needed for the rest of the HDK scripts to work

## FPGA SDK

The SDK directory includes the drivers and runtime environment required by any EC2 Instance running on F1. It has the drivers and tools to interact with a pre-built AFIs that are loaded to EC2 F1 FPGAs. The SDK is not required during the AFI design and build process, they are only required once you load the AFI into an F1 instance.




