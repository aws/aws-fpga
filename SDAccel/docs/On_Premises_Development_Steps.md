# On-Premises Development and F1 Deployment Guide

The SDAccel flow for F1 supports the following development models:
- Cloud based development on AWS EC2 cloud instances
- On-premises development on your own local workstations

In both cases, the final binaries are deployed on an AWS F1 instance and the [FPGA Developer AMI on AWS Marketplace](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) is required for running on F1

This guide provides step-by-step instructions for getting started with the on-premises flow and covers the following:
1. Installing and licensing SDAccel in your own environment
2. Building your application on-premises with SDAccel
3. Executing your application on F1

## Prerequisites
Before going through the steps described in this document, the user should have completed at least once the steps described in the [AWS SDAccel README] in the cloud.  After completing the README steps, you will be familiar with the developer environment and will be ready to setup your own environment. 

## Requirements
* The supported Operating Systems for SDaccel On-premises development are:
   * Red Hat Enterprise Workstation/Server 7.2 and 7.3 (64-bit)		 
   * Red Hat Enterprise Workstation 6.7 and 6.8 (64-bit)		 
   * CentOS 6.8, CentOS 7.3 (64-bit)		 
   * Ubuntu Linux 16.04.1 LTS (64-bit)		 
* gcc5.x or later is required to compile your OpenCL host code in order to use C++14 features (cl2.hpp). 
   * It is recommended that you use the Xilinx xcpp g++ wrapper to compile your host code.
   * xcpp simply uses system g++ if it is gcc5.x or later, otherwise it uses the g++ provided by SDAccel.

# 1. Installing and licensing SDAccel in your own environment

## Downloading the SDAccel Development Environment
In order to develop any SDAccel application on-premises, you will need to install the same version of SDAccel as deployed on AWS F1. The SDAccel installer can be found here:

https://www.xilinx.com/member/forms/download/xef.html?filename=Xilinx_SDx_op_2017.4_0411_1_Lin64.bin

This requires a Xilinx login. If you do not have an existing Xilinx account, select **Create your account**.

## Requesting a license

New Xilinx users will also need to obtain an on-premises license of Vivado. The users can request node-locked or floating license from the following page (Links are at Right side of the page):   

https://www.xilinx.com/products/design-tools/acceleration-zone/ef-vivado-sdx-vu9p-op-fl-nl.html

## Cloning the aws-fpga Git repository
The AWS Github repository contains all the necessary platform definition files and setup scripts to run SDAccel and build a design for F1 instances. It also contains numerous examples that will help you learn more about SDAccel.  

Execute the following commands on your local machine to clone the Github repository and configure the SDAccel environment:
```
    $ git clone https://github.com/aws/aws-fpga.git
    $ cd aws-fpga                                      
    $ source sdaccel_setup.sh
```

**Note**: Sourcing sdaccel_setup.sh may show some errors as it also tries to install runtime drivers which requires sudo access. These errors are nonintrusive, and you can ignore these messages. 


# 2. Building your design on-premises with SDAccel

These steps will show you how to:
- Confirm you are able to run SDAccel on your local machine
- Generate binaries which you can then deploy on the F1 instance.

When using Github examples, you can execute same sets of commands that you have used on an AWS EC2 instance.

## Starting the GUI
To invoke the SDAccel GUI, type the following command:
```
    $ sdx
```

Once you have confirmed the GUI invokes correctly, you can close it.
The following steps show how to run this example from the command line.

## Running SW Emulation

Execute the following commands to run the SW Emulation step for the SDAccel 'hello world' example:

```
    $ cd SDAccel/examples/xilinx/getting_started/host/helloworld_ocl/
    $ make clean
    $ make check TARGETS=sw_emu DEVICES=$AWS_PLATFORM all
```

## Running HW Emulation

Execute the following commands to run the HW Emulation step for the SDAccel 'hello world' example:

```
    $ cd SDAccel/examples/xilinx/getting_started/host/helloworld_ocl/
    $ make clean
    $ make check TARGETS=hw_emu DEVICES=$AWS_PLATFORM all
```

## Building for F1 Deployment

Execute the following commands to build the application for execution on AWS F1:

```
    $ cd SDAccel/examples/xilinx/getting_started/host/helloworld_ocl/
    $ make clean
    $ make TARGETS=hw DEVICES=$AWS_PLATFORM all
```

The build process will generate the host and FPGA binaries.  
1. Host binary: ./helloworld  
2. FPGA binary: ./xclbin/vector_addition.hw.xilinx_aws-vu9p-f1-04261818_dynamic_5_0.xclbin


These binary files are ready to be uploaded to F1.

# 3. Uploading and executing on F1

In this section we will cover the following steps:
 - Upload your application built on-premises to the AWS cloud 
 - Execute your application on F1

## Uploading the application to AWS

Upload the host and kernel binaries to AWS using the provided PEM file, public IP address of the instance, and login id. 
```
    $ scp -i ~/<pem-name>.pem <Host binary> <login-id>@<host-ip>:/home/<login-id>/<target directory>/.
    $ scp -i ~/<pem-name>.pem <Kernel binary> <login-id>@<host-ip>:/home/<login-id>/<target directory>/.
```

## Executing your application on F1

The steps required to deploy and execute your uploaded applocation are the same as if the application had been developed in the cloud:
- Log-in to F1
- Open a new shell
- Install the SDAccel environment
- Copy all the necessary files
- If a new .xclbin has been uploaded, created and register a new AFI
- Execute your application

All these are described in the [AWS SDAccel README]

	
# Additional Resources

The [AWS SDAccel README].

Xilinx web portal for [Xilinx SDAccel documentation] and for [Xilinx SDAccel GitHub repository]

Links pointing to **2017.4** version of the user guides

[UG1023: SDAccel Environment User Guide][UG1023 2017.4]

[UG1021: SDAccel Environment Tutorial: Getting Started Guide (including emulation/build/running on H/W flow)][UG1021 2017.4]

[UG1207: SDAccel Environment Optimization Guide][UG1207 2017.4]

[UG1238: SDx Development Environment Release Notes, Installation, and Licensing Guide][UG1238 2017.4]

[SDAccel_landing_page]: https://www.xilinx.com/products/design-tools/software-zone/sdaccel.html
[VHLS_landing_page]: https://www.xilinx.com/products/design-tools/vivado/integration/esl-design.html
[Vivado_landing_page]: https://www.xilinx.com/products/design-tools/vivado.html

[latest SDAccel Environment User Guide]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1023-sdaccel-user-guide.pdf
[latest UG1021]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1021-sdaccel-intro-tutorial.pdf
[latest SDAccel Environment Optimization Guide]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug1207-sdaccel-optimization-guide.pdf
[latest UG949]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug949-vivado-design-methodology.pdf
[latest UG902]: https://www.xilinx.com/cgi-bin/docs/rdoc?v=latest;d=ug902-vivado-high-level-synthesis.pdf

[UG1023 2017.4]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1023-sdaccel-user-guide.pdf
[UG1021 2017.4]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1021-sdaccel-intro-tutorial.pdf
[UG1207 2017.4]: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1207-sdaccel-optimization-guide.pdf
[UG1238 2017.4]:http://www.xilinx.com/support/documentation/sw_manuals/xilinx2017_4/ug1238-sdx-rnil.pdf
[Xilinx SDAccel documentation]: https://www.xilinx.com/products/design-tools/software-zone/sdaccel.html#documentation
[Xilinx SDAccel GitHub repository]: https://github.com/Xilinx/SDAccel_Examples

[SDAccel download and License instructions]:https://github.com/aws/aws-fpga/blob/master/hdk/docs/on_premise_licensing_help.md
[Vivado download]:https://www.xilinx.com/products/design-tools/acceleration-zone/ef-vivado-sdx-vu9p-op-fl-nl.html
[SDAccel Download Page]: https://www.xilinx.com/registration/sign-in.html?oamProtectedResource=wh%3Dwww.xilinx.com%20wu%3D%2Fmember%2Fforms%2Fdownload%2Fxef.html%3Ffilename%3DXilinx_SDx_op_2017.1_sdx_0715_1_Lin64.bin%26akdm%3D0%20wo%3D1%20rh%3Dhttp%3A%2F%2Fwww.xilinx.com%20ru%3D%252Fmember%252Fforms%252Fdownload%252Fxef.html%20rq%3Dfilename%253DXilinx_SDx_op_2017.1_sdx_0715_1_Lin64.bin%2526akdm%253D0
[AWS SDAccel Readme]: ../README.md
