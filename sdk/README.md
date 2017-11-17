# AWS EC2 FPGA Software Development Kit

This directory includes the drivers and runtime environment required by any EC2 FPGA Instance. The drivers and tools are used to interact with pre-built AFIs that are loaded to EC2 FPGA Instance FPGAs.

The [SDK userspace directory](./userspace) contains the [Amazon FPGA Image (AFI) Management Tools](./userspace/fpga_mgmt_tools/README.md), which includes both the source code to the AFI Management Tools as well as detailed descriptions of the commands to use on an F1 instance.

The SDK is **NOT** used to build or register AFI, rather it is only used for managing and deploying pre-built AFIs. For building and registering AFIs, please refer to the [HDK](../hdk/README.md).

**NOTE:** This SDK is designed and tested for Linux environments only.

# Quick Start

## Using an AFI on an EC2 FPGA Instance

You can setup and install the SDK with the following few steps.  Note that the first two steps may be skipped if you have already ran them in the above HDK setup.

    $ git clone https://github.com/aws/aws-fpga   # Fetch the HDK and SDK code
    $ cd aws-fpga                                 # Move to the root directory of the repository before running the next script
    $ source sdk_setup.sh                         # Set up the envronment variables, build and install the SDK


**NOTE:** The `sdk_setup.sh` would install the [FPGA management tools](./userspace/fpga_mgmt_tools/README.md) if they are not already available in `/usr/bin`. The `sdk_setup.sh` requires having `gcc` installed.  if it is not installed, try running the next command to install it on Amazon Linux, Centos or Redhat distributions:

```
$ sudo yum groupinstall -y "Development Tools"
```

## Notes for Ubuntu or other Debian based systems

To install gcc with apt-get, execute:

```
$ sudo apt-get update
$ sudo apt-get install build-essential
```
