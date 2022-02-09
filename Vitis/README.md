# Quick Start Guide to Accelerating your C/C++ application on an AWS F1 FPGA Instance with Vitis

There are three steps for accelerating your application on an Amazon EC2 FPGA instance using the software-defined development flow:
1. Build the host application, and the Xilinx FPGA binary
2. Create an AFI
3. Run the FPGA accelerated application on AWS FPGA instances

This quick start guide will utilize a simple "Hello World" Vitis example to get you started.

It is highly recommended you read the documentation and utilize software and hardware emulation prior to running on F1.
The F1 HW Target compile time is ~50 minutes, therefore, software and hardware emulation should be used during development.


# Table of Content

1. [Overview](#overview)
2. [Prerequisites](#prerequisites)
   * [AWS Account, F1/EC2 Instances, On-Premises, AWS IAM Permissions, AWS CLI and S3 Setup](#iss)
   * [Github and Environment Setup](#gitsetenv)
3. [Build the host application, Xilinx FPGA binary and verify you are ready for FPGA acceleration](#createapp)
   * [Emulate the code](#emu)
     * [Software Emulation](#swemu)
     * [Hardware Emulation](#hwemu)
   * [Build the host application and Xilinx FPGA Binary](#hw)
4. [Create an Amazon FPGA Image (AFI)](#createafi)
5. [Run the FPGA accelerated application on F1](#runonf1)
6. [Additional Vitis Information](#read)


<a name="overview"></a>
# Overview
* Vitis is a complete development environment for applications accelerated using Xilinx FPGAs
* It leverages the OpenCL heterogeneous computing framework to offload compute intensive workloads to the FPGA
* The accelerated application is written in C/C++, OpenCL or RTL with OpenCL APIs

<a name="prerequisites"></a>
# Prerequisites
<a name="iss"></a>
## AWS Account, F1/EC2 Instances, On-Premises, AWS IAM Permissions, AWS CLI and S3 Setup (One-time Setup)
* [Setup an AWS Account](https://aws.amazon.com/free/)
* Launch an instance using the [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) which comes pre-installed with Vitis and required licenses.
  * You may use this F1 instance to [build your host application and Xilinx FPGA binary](#createapp), however, it is more cost efficient to either:
     * Launch the [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on a compute EC2 instance, with a minimum of 30GiB RAM), **OR**
     * Follow the [On-Premises Instructions](../docs/on_premise_licensing_help.md) to purchase and install a license from Xilinx.
* Setup AWS IAM permissions for creating FPGA Images (CreateFpgaImage and DescribeFpgaImages). [EC2 API Permissions are described in more detail](http://docs.aws.amazon.com/AWSEC2/latest/APIReference/ec2-api-permissions.html).  It is highly recommended that you validate your AWS IAM permissions prior to proceeding with this quick start.  By calling the [DescribeFpgaImages API](../hdk/docs/describe_fpga_images.md) you can check that your IAM permissions are correct.
* [Setup AWS CLI and S3 Bucket](docs/Setup_AWS_CLI_and_S3_Bucket.md) to enable AFI creation.
* Install optional [packages](packages.txt) required to run all examples. If you do not install these packages, some examples may not work properly. The setup scripts will warn you of any missing packages.
* Additional dependencies may get flagged during the AWS Vitis scripts as warnings or errors.

<a name="gitsetenv"></a>
## Github and Environment Setup
* Clone this github repository and source the *vitis_setup.sh* script:
```
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source vitis_setup.sh
```

* Sourcing the *vitis_setup.sh* script:
  * Downloads and sets the correct AWS Platform:
    * AWS Vitis Platform that contains the dynamic hardware that enables Vitis kernels to run on AWS F1 instances.
    * Valid platforms for shell_v04261818: `AWS_PLATFORM_201920_3` (Default) AWS F1 Vitis platform.
  * Sets up the Xilinx Vitis example submodules.
  * Installs the required libraries and package dependencies.
  * Run environment checks to verify supported tool/lib versions.

<a name="createapp"></a>
# 1. Build the host application, Xilinx FPGA binary and verify you are ready for FPGA acceleration

This section will walk you through creating, emulating and compiling your host application and FPGA Binary

<a name="emu"></a>
# Emulate your Code

The main goal of emulation is to ensure functional correctness and to determine how to partition the application between the host CPU and the FPGA.
HW/SW Emulation does not require use of actual FPGA's and can be run on any compute instances. Using non-F1 EC2 compute instances for initial development will help reduce costs.

<a name="swemu"></a>
## Software (SW) Emulation

For CPU-based (SW) emulation, both the host code and the FPGA binary code are compiled to run on an x86 processor.
SW Emulation enables developers to iterate and refine the algorithms through fast compilation.
The iteration time is similar to software compile and run cycles on a CPU.

The instructions below describe how to run the Vitis SW Emulation flow using the Makefile provided with a simple "hello world" example

```
    $ cd $VITIS_DIR/examples/xilinx/hello_world
    $ make clean
    $ make run TARGET=sw_emu DEVICE=$AWS_PLATFORM all
```

For more information on how to debug your application in a SW Emulation environment.

<a name="hwemu"></a>
## Hardware (HW) Emulation

The Vitis hardware emulation flow enables the developer to check the correctness of the logic generated for the FPGA binary. This emulation flow invokes the hardware simulator in the Vitis environment to test the functionality of the code that will be executed on the FPGA Custom Logic.

The instructions below describe how to run the HW Emulation flow using the Makefile provided with a simple "hello world" example:

```
    $ cd $VITIS_DIR/examples/xilinx/hello_world
    $ make clean
    $ make run TARGET=hw_emu DEVICE=$AWS_PLATFORM all
```
For more information on how to debug your application in a HW Emulation environment.

<a name="hw"></a>
# Build the Host Application and Xilinx FPGA Binary

The Vitis system build flow enables the developer to build their host application as well as their Xilinx FPGA Binary.

The instructions below describe how to build the Xilinx FPGA Binary and host application using the Makefile provided with a simple "hello world" example:

```
    $ cd $VITIS_DIR/examples/xilinx/hello_world
    $ make clean
    $ make TARGET=hw DEVICE=$AWS_PLATFORM all
```

NOTE: If you encounter an error with  `No current synthesis run set`, you may have previously run the [HDK IPI examples](../hdk/docs/IPI_GUI_Vivado_Setup.md) and created a `Vivado_init.tcl` file in `~/.Xilinx/Vivado`. This will cause [problems](https://forums.aws.amazon.com/thread.jspa?threadID=268202&tstart=25) with the build process, thus it is recommended to remove it before starting a hardware system build.

<a name="createafi"></a>
# 2. Create an Amazon FPGA Image (AFI)

*The Vitis Flow only supports AFI's created with Device ID 0xF010 and Vendor ID 0x1D0F.*

The runtime drivers are designed to only bind to 0xF010 and 0x1042(Cleared AFI) and loading AFI's from your application that provide other Device/Vendor ID's will require restarting the Xilinx MPD.

This assumes you have:
* [Compiled your host application and Xilinx FPGA Binary](#hw)
* Validated your code using [SW/HW Emulation](#emu) and you are ready to create an AFI and test on F1.
* [Setup AWS CLI and S3 bucket](docs/Setup_AWS_CLI_and_S3_Bucket.md) for AFI creation

The [create_vitis_afi.sh](./tools/create_vitis_afi.sh) script is provided to facilitate AFI creation from a Xilinx FPGA Binary, it:
* Takes in your Xilinx FPGA Binary \*.xclbin file
* Calls *aws ec2 create_fpga_image* to generate an AFI under the hood
* Generates a \<timestamp\>_afi_id.txt which contains the identifiers for your AFI
* Creates an AWS FPGA Binary file with an \*.awsxclbin extension that is composed of: Metadata and AGFI-ID.
     * **This \*.awsxclbin is the AWS FPGA Binary file that will need to be loaded by your host application to the FPGA**

```
    $ $VITIS_DIR/tools/create_vitis_afi.sh -xclbin=<input_xilinx_fpga_binary_xclbin_filename>
		-o=<output_aws_fpga_binary_awsxclbin_filename_root> \
		-s3_bucket=<bucket-name> -s3_dcp_key=<dcp-folder-name> -s3_logs_key=<logs-folder-name>
```

**Save the \*.awsxclbin, you will need to copy it to your F1 instance along with your executable host application.**

**NOTE**: *Attempting to load your AFI immediately on an F1 instance will result in an 'Invalid AFI ID' error.
Please wait until you confirm the AFI has been created successfully.*

Refer to [FAQ](./docs/FAQ.md) for details.

## Tracking the status of your registered AFI

The \*_afi_id.txt file generated by the create_vitis_afi.sh also includes the two identifiers for your AFI:
- **FPGA Image Identifier** or **AFI ID**: this is the main ID used to manage your AFI through the AWS EC2 CLI commands and AWS SDK APIs.
    This ID is regional, i.e., if an AFI is copied across multiple regions, it will have a different unique AFI ID in each region.
    An example AFI ID is **`afi-06d0ffc989feeea2a`**.
- **Global FPGA Image Identifier** or **AGFI ID**: this is a global ID that is used to refer to an AFI from within an F1 instance.
    For example, to load or clear an AFI from an FPGA slot, you use the AGFI ID.
    **This is embedded into the AWS FPGA Binary \*.awsxclbin file generated by create_vitis_afi.sh.**
    Since the AGFI IDs is global (by design), it allows you to copy a combination of AFI/AMI to multiple regions, and they will work without requiring any extra setup.
    An example AGFI ID is **`agfi-0f0e045f919413242`**.


Use the [describe-fpga-images](../hdk/docs/describe_fpga_images.md) API to check the AFI state during the background AFI generation process.

```
    $ aws ec2 describe-fpga-images --fpga-image-ids <AFI ID>
```

When AFI creation completes successfully, the output should contain:
```
    ...
    "State": {
        "Code": "available"
    },
    ...
```

If the “State” code indicates the AFI generation has "failed", the AFI creation logs can be found in the bucket location (```s3://<bucket-name>/<logs-folder-name>```) provided to create_vitis_afi.sh above. These will detail the errors encountered during the AFI creation process.

For help with AFI creation issues, see [create-fpga-image error codes](../hdk/docs/create_fpga_image_error_codes.md)


<a name="runonf1"></a>
# 3. Run the FPGA accelerated application on Amazon FPGA instances

* Start an FPGA instance using [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) and check the AMI [compatibility table](../README.md#fpga-developer-ami) and [runtime compatibility table](./docs/Create_Runtime_AMI.md#runtime-ami-compatibility-table). Alternatively, you can [create your own Runtime AMI](docs/Create_Runtime_AMI.md) for running your Vitis applications on Amazon FPGA instances.
   * *Assuming the developer flow (compilation) was done on a separate build instance you will need to:*
     * Copy the compiled host executable (exe) to the new F1 instance
     * Copy the \*.awsxclbin AWS FPGA binary file to the new instance
     * Copy any data files required for execution to the new instance
     * [Clone the github repository to the new F1 instance and install runtime drivers](#gitsetenv)

* To setup tools, runtime environment & execute your Host Application:
    ```
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source vitis_runtime_setup.sh   # Other runtime env settings needed by the host app should be setup after this step
    # Wait till the MPD service has initialized. Check systemctl status mpd
    $ ./hello_world ./vadd.awsxclbin
    ```
* The runtime setup script also starts the Xilinx XRT Message Proxy Daemon(MPD) service. To learn more about the XRT implementation, check the [XRT Instructions](./docs/XRT_installation_instructions.md#mpd)

<a name="read"></a>
# Additional Vitis Information

* [Vitis User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_2/ug1393-vitis-application-acceleration.pdf)

* [Vitis Product Info](https://www.xilinx.com/products/design-tools/vitis.html)

* [XRT Documentation](https://xilinx.github.io/XRT/master/html/)

* [XRT MPD Documentation](https://xilinx.github.io/XRT/master/html/cloud_vendor_support.html)
