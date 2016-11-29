# Overview on process for building a Custom Logic (CL) implementation for AWS FPGA instances

The developer can build custom Logic (CL) as deploy on AWS as long as the CL complies with [AWS Shell Specification](https://github.com/aws/aws-fpga/hdk/doc/AWS_Shell_Interface_Specifications.md), and go through the build scripts. 

The [CL Examples directory](https://github.com/aws/aws-fpga/tree/master/hdk/cl/examples) is provided to assist developers in creating a
functional Custom Logic implementation. Each example includes:

    1) The design source code for the example included in the `/design` directory.

    2) The timing, clock and placement constraints files, scripts for compiling the example design. (This requires running in an instacne/server that have Xilinx tools and license install. Developers are recommended to use "FPGA Development AMI" available free of charge on AWS Marketplace"

    3) The final build, called Design CheckPoint (DCP) that can be submitted for AWS to generate the AFI

    4) An AFI-ID for a pre-generated AFI that matches the example design

    5) Software source code for any software needed in the FPGA enabled instance to run the example

    6) Software binary that can be loaded on an F1 instance to test the AFI. 

To summarize:

**An AFI can be created using the files in 1, 2, and 3. The AFI creation can take place on any EC2 instance or on-premise services**

**The AFI can be used in an EC2 F1 instance by using the files in 4, 5 and 6.**

By following the example CLs, a Developer could understand how to interface to the AWS Shell of the FPGA, compile design source code to create an AFI, and load an AFI from the F1 instance for use.

# Step by step guide how to create an AFI from one of the CL examples

As a pre-requested to building the AFI, the developer should have an instance/server with Xilinx vivado tools and license. The "FPGA Developer AMI" provided free of charge on AWS Marketplace will be an ideal place to start an instance from. See the README.md on the AMI for the details how to launch the FPGA Developer's AMI, install the tools and set up the license.

**NOTE:** *steps 1 through 3 can be done on any server or EC2 instance, C4/C5 instances are recommended for fastest build time*

**NOTE:** *You can skip steps 0 through 3 if you are not interested in the build process.  Step 4 through 6 will show you how to use one of the predesigned AFI*

### 0. Download and configure the HDK to the source directory on the instance.

        $ git clone https://github.com/aws/aws-fpga
        $ cd aws-fpga
        $ source hdk_shell.sh
    
### 1. Pick one of the examples and move to its directory

There are couple of ways to start a new CL: one option is to copy one of the examples provided in the HDK and modify the design files, scripts and constrains directory.

Alternatively, by creating a new directory, setup the environment variables, and prepare the project datastructure:

        $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to any other example
        $ export CL_DIR=$(pwd)
        
Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the [How to create your own CL Readme](../developer_designs/README.md)

### 2. Build the CL before submitting to AWS

**NOTE** *This step requires you have Xilinx Vivado Tools installed as well Vivado License:*

        $ vivado -mode batch        # Run this command to see if vivado is installed
        $ sudo perl /home/centos/src/project_data/license/license_manager.pl -status  # To check if license server is up. this command is for AWS-provided FPGA Development machine, the license manager can be in different directory in your systems
    
The next script two steps will go through the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA

        $ cd $CL_DIR/build/scripts
        $ vivado -mode batch -source create_dcp_from_cl.tcl 
        
### 3. Submit the Design Checkpoint to AWS to register the AFI

#### If you have access to AWS SDK with support for FPGA API (`aws ec2 createFpgaImage`)
TBD

#### During F1 preview and before AWS EC2 FPGA API are available

To submit the dcp, createan S3 bucket for submitting the design and upload the tar zipped archive into that bucket. Then, add a policy to that bucket allowing our team's account (Account ID: 682510182675) read/write permissions. A [TBD] example of the S3 permissions process is included in the /build/scripts directory. Submit an email to AWS (email TBD) providing the following
information: 

1) Name of the logic design

2) Generic Desription of the logic design

3) PCI IDs (Device, Vendor, Subsystem, SubsystemVendor),

4) Location of the DCP object (bucket name and key),

5) Location of the directory to write logs (bucket name and key)

6) Version of the Shell. 


After the AFI generation is complete, AWS will write the logs back into the bucket location provided by the developer and notify them
by email, including the AFI IDs used to manage and launch an AFI from within an Instance.

# Step by step guide how to load and test a registered AFI from within an F1 instance

To follow the next steps, you have to run an instance on F1. AWS recommend you run an instance with latest Amazon Linux that have the FPGA management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

## 4. Make sure you have AWS CLI configured and AWS FPGA management tools

        $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and region (typically us-east-1)
        $ git clone https://github.com/aws/aws-fpga
        $ cd aws-fpga
        $ source sdk_setup.sh
        
## 5. Associate the AFI with your instance

You can associate more than one AFI with your instance. the Association process just make sure you have the permission to use the specific AFI-Id(s).

        $ aws ec2 associateFpgaImage --fpga-image-id <AFI_ID> --instance-id <instance0id
        
## 6. Load the AFI

Run's the `fpga-describe-local-image` on slot 0 to confirm that the FPGA is cleared, and you should see similar output to the 4 lines below:

    $ sudo fpga-describe-local-image -S 0 -H

    Type    FpgaImageSlot    FpgaImageId    StatusName    StatusCode
    AFI           0             none          cleared         1
    Type        VendorId    DeviceId      DBDF
    AFIDEVICE    0x1d0f      0x1042    0000:00:17.0

Then loading the example AFI to FPGA slot 0. (you should have the AFI ID or AGFI ID from step 3 above. 

    $ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdefg

Now, you can verify the status of the previous load command:

    $ sudo fpga-describe-local-image -S 0 -H

## 7. Call the specific CL example software

[Validating CL Designs](https://github.com/aws/aws-fpga/wiki/Validating-CL-Designs#quick-start)
