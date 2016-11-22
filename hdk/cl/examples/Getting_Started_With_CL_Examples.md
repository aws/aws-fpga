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

# Follow these steps to create an AFI from one of the CL example:

As a pre-requested to building the AFP, the developer should have an instance/server with Xilinx vivado tools and license. The "FPGA Developer AMI" provided free of charge on AWS Marketplace will be an ideal place to start an instance from. See the README.md on the AMI for the details how to launch the FPGA Developer's AMI, install the tools and set up the license.

**NOTE:** *steps 1 through 3 can be done on any server or EC2 instance, C4/C5 instances are recommended for fastest build time*


### 1. Download and configure the HDK to the source directory on the instance.

        $ git clone https://github.com/aws/aws-fpga
        $ cd aws-fpga
        $ source hdk_shell.sh
    
### 2. Pick one of the examples and move to its directory

There are couple of ways to start a new CL: one option is to copy one of the examples provided in the HDK and modify the design files, scripts and constrains directory.

Alternatively, by creating a new directory, setup the environment variables, and prepare the project datastructure:

        $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to any other example
        $ export CL_DIR=$(pwd)
        
Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the [How to create your own CL Readme](../developer_designs/README.md)


### 3. Build the CL before submitting to AWS

**NOTE** *Before starting this step, please make yourself familiar with the [checklist](../CHECKLIST BEFORE BUILDING_CL.md)*

**NOTE** *This step requires you have Xilinx Vivado Tools installed as well Vivado License:*
    $ vivado -mode batch        # Run this command to see if vivado is installed
    $ sudo perl /home/centos/src/project_data/license/license_manager.pl -status  # To check if license server is up. this command is for AWS-provided FPGA Development machine, the license manager can be in different directory in your systems
    
Run this script to start Vivado and
generate a Design Checkpoint
\$(CL\_DIR)/build/scripts/create\_dcp\_from\_cl.tcl A detailed version
of the Vivado design flow is included in the /build/scripts directory.
Refer to \$HDK\_DIR/cl/CHECKLIST.txt file to see verification steps that
should be performed on any new design. Example cl designs meet the
checklist criteria by default.

Submit the dcp file to AWS to generate an AFI. To submit the dcp, create
an S3 bucket for submitting the design and upload the zipped archive
into that bucket. Then, add a policy to that bucket allowing our team's
account (Account ID: 682510182675) read/write permissions. A README
example of the S3 permissions process is included in the /build/scripts
directory. Submit an email to AWS (email TBD) providing the following
information: 1) Name of the logic design, 2) Generic Desription of the
logic design, 3) PCI IDs (Device, Vendor, Subsystem, SubsystemVendor),
4)Location of the DCP object (bucket name and key), 4) Location of the
directory to write logs (bucket name and key), and 5) Version of the
Shell. After the AFI generation is complete, AWS will write the logs
back into the bucket locaiton provided by the developer and notify them
by email, including the AFI IDs used to manage and launch an AFI from
within an Instance.

**Follow these steps to load and test an AFI from within an F1
instance:**

Take the FPGA Developer AMI and create a private AMI from the FPGA
Developer AMI. See the FPGA Developer AMI for details on creating a
run-time FGPA AMI. The AMI ID is needed to associate the AFI with the
running instance.

Call the AWS CLI associate-fpga-image --fpga-image-id &lt;AFI ID&gt;
\[--image-id &lt;AMI ID&gt;\] This call will associate the AFI ID with
the AMI ID. Once complete, the AFI ID can be loaded on to any F1
instance running that AMI ID.

Purchase and launch an F1 instance with the run-time FPGA AMI. From the
running instance, call the FPGA Management Tools API command load\_afi
--afi-id &lt;AFI ID&gt; -- slot&lt;0&gt;. This will load the AFI
specified into the only FPGA in the F1.2XL instance. See the FPGA
Management Tools README in /sdk for more details on the FPGA Management
Tools APIs.

Load and run the software for the example cl on the running instance
from the sdk/examples directory that matches the example cl AFI that was
loaded.
