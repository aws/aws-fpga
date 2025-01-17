# Quick Start Guide to Accelerating your C/C++ application on AWS EC2 F2 (FPGA) Instances with Vitis

This quick start guide will utilize a simple `hello_world` Vitis example to get you started.

# Table of Contents

1. [Overview](#1-overview)
2. [Prerequisites](#2-prerequisites)
   * 2.1 [AWS Account and F2/EC2 Instances](#21-aws-account-and-f2ec2-instances)
   * 2.2 [GitHub and Environment Setup](#22-github-and-environment-setup)
3. [Design Emulation and Synthesis](#3-emulating-your-code)
    * 3.1 [Emulate the code](#31-emulation)
        * 3.1.1 [Hardware Emulation](#311-hardware-hw-emulation)
    * 3.2 [Results and Artifacts](#32-results-and-artifacts)
4. [Next Steps](#4-next-steps)
    * 4.1. [Examining Run Data](#41-examining-run-data)
5. [Additional Resources](#5-additional-vitis-information)

<a name="overview"></a>
# 1. Overview
* Vitis is a complete development environment for applications accelerated using AWS EC2 F2 (FPGA) instances
* It leverages the OpenCL heterogeneous computing framework to offload compute intensive workloads to F2 instances
* The accelerated application is written in C/C++, OpenCL and/or Verilog/VHDL

<a name="prerequisites"></a>
# 2. Prerequisites
<a name="iss"></a>
## 2.1 AWS Account and F2/EC2 Instances
* Getting Familiar with AWS - If you have never used AWS before, we recommend you start with AWS getting started training, and focus on the basics of the AWS EC2 and AWS S3 services. Understanding the fundamentals of these services will make it easier to work with AWS F2 instances and the FPGA Developer Kit.  [Setup an AWS Account](https://aws.amazon.com/free/)
* FPGA developer AMI (2024.1) - available for on-cloud F2 development with AMD tools pre-installed and free to use on AWS EC2 for F2 development. Customers can use this AMI to design, simulate, and build their designs. Given the large size of the FPGA used for F2, AMD tools work best with at least 4 vCPU's and 32GiB Memory. We recommend Compute Optimized and Memory Optimized instance types to successfully run the synthesis of acceleration code. Developers may start coding and run simulations on low-cost General Purpose instances types. Launch an instance using a pre-installed with Vitis and required licenses.

<a name="gitsetenv"></a>
## 2.2 GitHub and Environment Setup
* Clone this github repository, export your AWS IAM credentials, and source the *vitis_setup.sh* script:
```
    cd aws-fpga
    source vitis_setup.sh
```

* Sourcing the [vitis_setup.sh](../vitis_setup.sh) script does the following:
  * Downloads and sets the correct AWS Platforms:
    * AWS EC2 F2 Vitis platform package that contains the dynamic hardware that enables Vitis kernels to run on AWS F2 instances
    * Valid platforms for shell_stable: `AWS_PLATFORM_202401_0` (Default) AWS F2 Vitis platform
  * Sets up the Vitis example directories
  * Installs the required libraries and package dependencies
  * Runs environment checks to verify supported tool/lib versions
  * Gathers dependencies needed to install the [Xilinx Runtime](https://github.com/Xilinx/XRT/tree/2024.1) (XRT)

If the script has successfully set up all of the tools and the environment, you will see the following message:

``` bash
INFO: #-------------------------------------------------------------------------------#
INFO: How to run hardware emulation or synthesis on an example
INFO: cd vitis/examples/vitis_examples/hello_world
INFO: hw_file_check
INFO: #----------------------------- Emulation ---------------------------------------#
INFO: make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION
INFO: #-------------------------------------------------------------------------------#
INFO: Vitis Setup PASSED.
```

<a name="build"></a>
# 3. Emulating Your Code

Vitis hardware emulation is a cycle-accurate emulation of your accelerator design. This section will walk you through the emulation process.

<a name="emu"></a>
## 3.1 Emulation

The main goal of hardware emulation is to insure functional correctness and determine how to partition the application between the host CPU and the FPGA.
Hardware emulation does not require use of actual FPGAs and can be run on any compute instance. Using non-F2 EC2 compute instances during initial development reduces cost.

<a name="hwemu"></a>
### 3.1.1 Hardware (HW) Emulation

The Vitis hardware emulation flow enables the developer to check the correctness of the logic generated by the tools. This emulation flow invokes the hardware simulator in the Vitis environment to test the functionality of the code.

To perform hardware emulation for any given example, run the following commands:

``` bash
cd $AWS_FPGA_REPO_DIR
cd vitis/examples/vitis_examples
```

After listing the contents of `vitis/examples/vitis_examples`, navigate to your desired example.

Prior to starting a hardware emulation run, run the `hw_file_check` command to insure that all files required for simulation are present. If all required files are present, you will see `All required simulation files are present!`. Otherwise, the missing files' names will be displayed. These files can always be reobtained from the `aws-fpga` repository if they are deleted or renamed at any point.

The most critical file in each example directory is the `Makefile`. Some examples will have sub-examples, whose `Makefiles` are located in the associated subdirectory.

Note the presence of the `Makefile` in this subdirectory. Some examples will have sub-examples, whose `Makefiles` are located in the associated subdirectory.

> [!WARNING]
> A Makefile is required in order to run hardware emulation for all designs/examples

We recommend running hardware emulation in the background to prevent disruption due to the compute intensity and time needed for completion. Prefixing commands with `nohup` and ending them with an `&` will insure more reliable execution.

Once you've verified that all required files are present in the current example directory, start the hardware emulation run with the following command:

``` bash
nohup make build TARGET=hw_emu PLATFORM=$SHELL_EMU_VERSION &
```

The same command can be used for all Vitis examples after running `vitis_setup.sh`.

<a name="resultsandartifacts"></a>
### 3.2 Results and Artifacts

Once the emulation/build has completed, you will see either a `TEST PASSED`, or a relevant error message.

Upon successful emulation/build completion, you will notice that a build directory has been created in the example's directory:

``` bash
aws-fpga/vitis/examples/vitis_examples/
        hello_world/
                build_dir.hw_emu.xilinx_aws-vu47p-f2_202410_1/
```

**This directory will contain the .xclbin file, as well as other artifacts, depending on the example run:**

Hardware emulation:

``` bash
drwxrwxr-x  2 ubuntu ubuntu     4096 Aug 15 17:58 ./
drwxr-xr-x 13 ubuntu ubuntu     4096 Aug 15 18:51 ../
-rw-rw-r--  1 ubuntu ubuntu 46324262 Aug 15 17:58 vadd.link.xclbin
-rw-rw-r--  1 ubuntu ubuntu    11777 Aug 15 17:58 vadd.link.xclbin.info
-rw-rw-r--  1 ubuntu ubuntu    38652 Aug 15 17:58 vadd.link.xclbin.link_summary
-rw-rw-r--  1 ubuntu ubuntu 46324302 Aug 15 17:58 vadd.xclbin
-rw-rw-r--  1 ubuntu ubuntu     4414 Aug 15 17:58 vadd.xclbin.package_summary
```

<a name="next-steps"></a>
# 4. Next Steps

<a name="run-data"></a>
## 4.1 Examining Run Data

After a hardware simulation run, there are three files that contain very important information:

* `vadd.xclbin.info`
    * A text report of the generated device binary
* `vadd.xclbin.link_summary`
    * A summary report of the linking process which generated the device binary
* `vadd.link.xclbin.link_summary`
    * Contains an estimate of system performance
* `xrt.run_summary`
    * A summarized report of events captured during application runtime

The first three of these files can be found in the newly-generated directory prefixed with `build_dir.hw_emu.`. The xrt run summary file can be found in the example directory.

<a name="read"></a>
# 5. Additional Vitis Information

* [Vitis Documentation Hub](https://docs.amd.com/r/en-US/Vitis-Tutorials-Getting-Started)
