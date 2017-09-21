# Quick Start Guide to Accelerating your C/C++ application on an AWS F1 FPGA Instance with SDAccel

There are three simple steps for accelerating your application on an AWS F1 instance:
1. Build the host application, Xilinx FPGA binary and verify you are ready for FPGA acceleration 
2. Create an AFI 
3. Run the FPGA accelerated application on AWS FPGA instances

This quick start guide will use a simple "Hello World" SDAccel example to get you started


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
6. [Additional SDAccel Information](#read)


<a name="overview"></a>
# Overview
* SDAccel is a complete development environment for applications accelerated with Xilinx FPGAs
* It leverages the OpenCL heterogeneous computing framework to offload compute intensive workloads to the FPGA
* The accelerated application is written in C/C++ with OpenCL APIs
* The code for the FPGA binary can be written in C/C++, OpenCL or RTL
* Once you have gone through this quick start example. See the [SDAccel GUI Guide](./docs/README_GUI.md) to access the fully integrated Eclipse-based environment with built-in debug, profiling and performance analysis tools. 



<a name="prerequisites"></a>
# Prerequisites
<a name="iss"></a>
## AWS Account, F1/EC2 Instances, On-Premises, AWS IAM Permissions, AWS CLI and S3 Setup (One-time Setup)
* [Setup an AWS Account](https://aws.amazon.com/free/)
* Launch an [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) which comes pre-installed with SDAccel and required licenses on an F1 instance
  * You may use this F1 instance to [Build your Host Application and Xilinx FPGA Binary](#createapp), however, it may be more cost efficient to either: 
     * Launch a second [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) on a lower cost EC2 instance, with a minimum of 30GiB RAM), **OR** 
     * Follow the [On-Premises Instructions](../../hdk/docs/on_premise_licensing_help.md) to install and obtain a license from Xilinx.
* Setup AWS IAM permissions for creating FPGA Images (CreateFpgaImage and DescribeFpgaImages). [EC2 API Permissions are described in more detail](http://docs.aws.amazon.com/AWSEC2/latest/APIReference/ec2-api-permissions.html) <!-- #TBF Is there a better guide (syntax/links to for explicitly making this update? -->
* [Setup AWS CLI and S3 Bucket](docs/Setup_AWS_CLI_and_S3_Bucket.md) to enable AFI creation.




<a name="gitsetenv"></a>
## Github and Environment Setup (Once per new instance or machine)
* Clone this github repository and source the *sdaccel_setup.sh* script. This will take care of: 
  * Downloading the required files:
    * [AWS Platform](./aws_platform/xilinx_aws-vu9p-f1_4ddr-xpr-2pr_4_0) that allows Xilinx FPGA Binary files to target AWS F1 instances 
    * [AFI Creation script](./tools/create_sdaccel_afi.sh) that generates an AFI and AWS FPGA Binary from a Xilinx FPGA Binary
    * [SDAccel HAL](./userspace) source code and binary files for mapping SDAccel/OpenCL runtime libraries to AWS FPGA instance.
  * Installing  the required libraries and drivers

   ```
       $ git clone https://github.com/aws/aws-fpga-preview.git $AWS_FPGA_REPO_DIR  
       $ cd $AWS_FPGA_REPO_DIR                                         
       $ source sdaccel_setup.sh
   ```

 
<a name="createapp"></a>
# 1. Build the host application, Xilinx FPGA binary and verify you are ready for FPGA acceleration

This section will walk you through creating, emulating and compiling your host application and FPGA Binary

Start by sourcing the setup for the Xilinx SDAccel Emulation and Build Environment
```
    $ source $XILINX_SDX/settings64.sh 
```

<a name="emu"></a>
# Emulate your Code

The main goal of emulation is to ensure functional correctness and to determine how to partition the application between the host CPU and the FPGA. 

<a name="swemu"></a>
## Software (SW) Emulation

For CPU-based (SW) emulation, both the host code and the FPGA binary code are compiled to run on an x86 processor. The SW Emulation enables developer to iterate and refine the algorithms through fast compilation. The iteration time is similar to software compile and run cycles on a CPU. 

The instructions below describe how to run the SDAccel SW Emulation flow using the Makefile provided with a simple "hello world" example

```
    $ cd $SDACCEL_DIR/examples/xilinx/getting_started/host/helloworld_ocl/          
    $ make clean                                                                 
    $ make check TARGETS=sw_emu DEVICES=$AWS_PLATFORM all     
```

For more information on how to debug your application in a SW Emulation environment, please see the [SDAccel Debug Guide](./docs/SDAccel_HLS_Debug.md).  

<a name="hwemu"></a>
## Hardware (HW) Emulation

The SDAccel hardware emulation flow enables the developer to check the correctness of the logic generated for the FPGA binary. This emulation flow invokes the hardware simulator in the SDAccel environment to test the functionality of the code that will be executed on the FPGA Custom Logic. 

The instructions below describe how to run the HW Emulation flow using the Makefile provided with a simple "hello world" example: 

```
    $ cd $SDACCEL_DIR/examples/xilinx/getting_started/host/helloworld_ocl/             
    $ make clean                                                                   
    $ make check TARGETS=hw_emu DEVICES=$AWS_PLATFORM all      
```
For more information on how to debug your application in a HW Emulation environment, please see the [SDAccel Debug Guide](./docs/SDAccel_HLS_Debug.md).  

<a name="hw"></a>
# Build the Host Application and Xilinx FPGA Binary

The SDAccel system build flow enables the developer to build their host application as well as their Xilinx FPGA Binary.  

The instructions below describe how to build the Xilinx FPGA Binary and host application using the Makefile provided with a simple "hello world" example: 

```
    $ cd $SDACCEL_DIR/examples/xilinx/getting_started/host/helloworld_ocl/           
    $ make clean                                                             
    $ make TARGETS=hw DEVICES=$AWS_PLATFORM all   
```

Now that you have built your Xilinx FPGA binary, see [SDAccel Power Analysis Guide](./docs/SDAccel_Power_Analysis.md) for more details on how to analyze power for your binary.

<a name="createafi"></a>
# 2. Create an Amazon FPGA Image (AFI) 

This assumes you have: 
* [Compiled your host application and Xilinx FPGA Binary](#hw)
* Validated your code using [SW/HW Emulation](#emu) and you are ready to create an AFI and test on F1.
* [Setup AWS CLI and S3 bucket](docs/Setup_AWS_CLI_and_S3_Bucket.md) for AFI creation  

The [create_sdaccel_afi.sh](./tools/create_sdaccel_afi.sh) script is provided to facilitate AFI creation from a Xilinx FPGA Binary, it:
* Takes in your Xilinx FPGA Binary \*.xclbin file
* Calls *aws ec2 create_fgpa_image* to generate an AFI under the hood
* Generates a \<timestamp\>_afi_id.txt which contains the identifiers for your AFI
* Creates an AWS FPGA Binary file with an \*.awsxclbin extension that is composed of: Metadata and AGFI-ID. 
     * **This \*.awsxclbin is the AWS FPGA Binary file that will need to be loaded by your host application to the FPGA**

```
    $ $SDACCEL_DIR/tools/create_sdaccel_afi.sh -xclbin=<input_xilinx_fpga_binary_xclbin_filename> 
		-o=<output_aws_fpga_binary_awsxclbin_filename_root> \
		-s3_bucket=<bucket-name> -s3_dcp_key=<dcp-folder-name> -s3_logs_key=<logs-folder-name>
```

**Save the \*.awsxclbin, you will need to copy it to your F1 instance along with your executable host application.**

**NOTE**: *Attempting to load your FPGA Binary immediately on an F1 instance will result in an 'Invalid AFI ID' error.
Please wait until you confirm the AFI is created successfully.*

## Tracking the status of your registered AFI  

The \*_afi_id.txt file generated by the create_sdaccel_afi.sh also includes the two identifiers for your AFI:
- **FPGA Image Identifier** or **AFI ID**: this is the main ID used to manage your AFI through the AWS EC2 CLI commands and AWS SDK APIs.
    This ID is regional, i.e., if an AFI is copied across multiple regions, it will have a different unique AFI ID in each region.
    An example AFI ID is **`afi-06d0ffc989feeea2a`**.
- **Global FPGA Image Identifier** or **AGFI ID**: this is a global ID that is used to refer to an AFI from within an F1 instance.
    For example, to load or clear an AFI from an FPGA slot, you use the AGFI ID. 
    **This is embedded into the AWS FPGA Binary \*.awsxclbin file generated by create_sdaccel_afi.sh.**
    Since the AGFI IDs is global (by design), it allows you to copy a combination of AFI/AMI to multiple regions, and they will work without requiring any extra setup.
    An example AGFI ID is **`agfi-0f0e045f919413242`**.


Use the [describe-fpga-images](../../hdk/docs/describe_fpga_images.md) API to check the AFI state during the background AFI generation process.  

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

If the “State” code indicates the AFI generation has "failed", the AFI creation logs can be found in the bucket location (```s3://<bucket-name>/<logs-folder-name>```) provided to create_sdaccel_afi.sh above. These will detail the errors encountered during the AFI creation process.

For help with AFI creation issues, see [create-fpga-image error codes](../../hdk/docs/create_fpga_image_error_codes.md)

 


<a name="runonf1"></a>
# 3. Run the FPGA accelerated application on F1

Here are the steps:
* Start an F1 instance using [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ). Currently, the developer AMI is the only supported AMI for running SDAccel applications on F1.
   * *Assuming the developer flow (compilation) was done on a separate instance you will need to:*
     * Copy the compiled host executable (exe) to new instance
     * Copy the \*.awsxclbin AWS FPGA binary file to the new instance
     * Copy any data files required for execution to the new instance
     * [Clone the github repository to the new F1 instance and install runtime drivers](#gitsetenv)

* Ensure the host application can find and load the \*.awsxclbin AWS FPGA binary file. 
<!--
---------

(--Delete once Xilinx Github examples start looking for \*.awsxclbin--)

* *By default the host application in this example looks for a \*.xclbin FPGA binary file, while the AWS FPGA binary file generated by create_sdaccel_afi.sh is called \*.awsxclbin.* 
* *The \*.awsxclbin AWS FPGA binary will need to be renamed to \*.xclbin so that the host application can find it* 
```
    $ cd $SDACCEL_DIR/examples/xilinx/getting_started/host/helloworld_ocl/           
    $ rename "s/.xclbin/.xclbin_backup/" xclbin/*.xclbin         # This creates a backup for the  build XCLBIN is not overwritten 
    $ rename "s/.awsxclbin/.xclbin/" xclbin/*.awsxclbin          # Rename awsxclbin binary to xclbin so host application can pick it up
```
---------
-->
* Source the Runtime Environment & Execute your Host Application
```
    $ sudo sh
    # source /opt/Xilinx/SDx/2017.1.rte/setup.sh   # Other runtime env settings needed by the host app should be setup after this step 
    # ./helloworld 
```


<a name="read"></a>
# Additional SDAccel Information

* [SDAccel Guide for Amazon F1](docs/SDAccel_Guide_AWS_F1.md)

* [OpenCL memory model video](https://www.youtube.com/watch?v=c4a8uQ4AnMI)

* [OpenCL application structure video](https://www.youtube.com/watch?v=hUiX8rBcNzw)

* [SDAccel Environment tutorial](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1021-sdaccel-intro-tutorial.pdf)

* [SDAccel User Guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1023-sdaccel-user-guide.pdf)

* [SDAccel Environment optimization guide](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_1/ug1207-sdaccel-optimization-guide.pdf)
