# Introduction

This simple hello_world example would build a Custom Logic that will enable the instance to "peak" and "pook" registers in the memory space of Custom Logic inside the FPGA.

The walkthrough is split into two parts: 

  Part 1: How to download the HDK, build the Custom Logic, and register it with AWS to get an AFI-id. 
  Part 2: Once you have a registered AFI, how to use it on an F1 instance.

**NOTE:** All the command lines mentioned in this document are targeting Linux environments only.

# Part 1: How to build and register hello_world

To begin, the developer need to have a serverr or EC2 instance with Xilinx Vivado tools installed and license server running. For example, by running on AWS FPGA Developer AMI provided on [AWS Marketplace](https://aws.amazon.com/marketplace)

## 0. Download and configure the HDK to the source directory on the instance in case you haven't done so far

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_shell.sh

## 1. Pick the cl_hello_world example and move to its directory

    $ cd $HDK_DIR/cl/examples/cl_hello_world
    $ export CL_DIR=$(pwd)

Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value. Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the How to create your own CL Readme

## 2. Build the CL before submitting to AWS

NOTE This step requires you have Xilinx Vivado Tools installed as well Vivado License:

    $ vivado -mode batch        # Run this command to see if vivado is installed
    $ sudo perl /home/centos/src/project_data/license/license_manager.pl -status  # To check if license server is up. this command is for AWS-provided FPGA Development machine, the license manager can be in different directory in your systems

The next script two steps will go through the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA

    $ cd $CL_DIR/build/scripts
    $ vivado -mode batch -source create_dcp_from_cl.tcl 

## 3. Submit the Design Checkpoint to AWS to register the AFI

If you have access to AWS SDK with support for FPGA API (aws ec2 createFpgaImage)

TBD

During F1 preview and before AWS EC2 FPGA API are available

To submit the dcp, createan S3 bucket for submitting the design and upload the tar zipped archive into that bucket. Then, add a policy to that bucket allowing our team's account (Account ID: 682510182675) read/write permissions. A [TBD] example of the S3 permissions process is included in the /build/scripts directory. Submit an email to AWS (email TBD) providing the following information:

1) Name of the logic design
2) Generic Desription of the logic design
3) PCI IDs (Device, Vendor, Subsystem, SubsystemVendor),
4) Location of the DCP object (bucket name and key),
5) Location of the directory to write logs (bucket name and key)
6) Version of the Shell.

After the AFI generation is complete, AWS will write the logs back into the bucket location provided by the developer and notify them by email, including the AFI IDs used to manage and launch an AFI from within an Instance.

# Part 2: How to load and test Hello World registered AFI from within an F1 instance

To follow the next steps, you have to run an instance on F1. AWS recommend you run an instance with latest Amazon Linux that have the FPGA management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

## 4. Make sure you have AWS CLI configured and AWS FPGA management tools

    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and region (typically us-east-1)
    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source sdk_setup.sh

## 5. Associate the AFI with your instance

You can associate more than one AFI with your instance. the Association process just makes sure you have the permission to use the specific AFI-Id(s) but it doesn't load the image to the FPGA

    $ aws ec2 associateFpgaImage --fpga-image-id <AFI_ID> --instance-id <instance0id

## 6. Load the AFI to FPGA slot 3

Run's the fpga-describe-local-image on slot 0 to confirm that the FPGA is cleared, and you should see similar output to the 4 lines below:

$ sudo fpga-describe-local-image -S 0 -H

Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
AFI           0             none          cleared         1
Type        VendorId    DeviceId      DBDF
AFIDEVICE    0x1d0f      0x1042    0000:00:17.0
Then loading the example AFI to FPGA slot 0. (you should have the AFI ID or AGFI ID from step 3 above.

$ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdefg
Now, you can verify the status of the previous load command:

$ sudo fpga-describe-local-image -S 0 -H

7. Call the specific Hello World specific software

[TBD]
