# How to build and submit your Custom Logic (CL) to AWS 

# Table of Contents

1. [Overview of AFI Build process] (#buildoverview)
2. [Build procedure step by step] (#stepbystep)
3. [Build strategies and parallel builds] (#strategies)
4. [About Encrption during build process] (#buildencryption)
5. [Advanced Notes] (#buildadvanced notes)
6. [Build Frequently Asked Questions] (#buildfaq)



## Overview <a name="buildoverview"></a>

Once the developer has a functional design, the next steps are to: synthesize the design into basic FPGA cells, perform place-and-route, and check that the design meets the timing/frequency constraints. This could be an iterative process. Upon success, the developer will need to pass the output of the flow to AWS for final AFI creation.

The developer needs to transfer to AWS a tar file that includes the encrypted placed-and-routed design checkpoints (referred to as DCP throughout this document) and [manifest](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md): The DCP includes the complete developer design that meets timing/frequency constraints, placement boundaries  within the allocated CL area on the FPGA, and the functional requirements laid out in the [Shell Interface Specification](https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#overview).  The [manifest.txt](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md) should include key parameters needed for registering and loading the AFI like target frequency.

To assist in this process, AWS provides a reference DCP that includes the shell (SH) logic with a black-boxed CL under: `$HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp`

AWS also provides out-of-the-box generic script called `aws_build_dcp_from_cl.sh` that is used for test compile a few examples like `CL_simple` design as if they were developer code. These reference examples can serve as starting points for new designs. The output of AWS-provided scripts will create a a tar file, with both the encrypted placed-and-routed DCP and the corresponding `manifest.txt`, which AWS will use to generate final bitstreams.

To ease and experiment with multiple implementation methods for DCP to meet placement and timing constrains, the `aws_build_dcp_from_cl.sh` provides multiple choices for implementation strategy , invokved throught `-strategy` option. Please call `aws_build_dcp_from_cl.sh -help` for the list of supported capabilities

Advanced developers can use different scripts, tools, and techniques (e.g., regioning),  with the  condition that they submit both the `manifest.txt` and "encrypted placed-and-routed design checkpoints (DCP)" in a single tar file, that passes final checks which are included in the build scripts.  (TBD - final_check_dcp).

## Build Procedure <a name="stepbystep"></a>

The following describes the step-by-step procedure to build developer CLs. Some of these steps can be modified or adjusted based on developer experience and design needs. 

A developer can execute `$HDK_SHELL_DIR/build/scripts/aws_build_dcp_from_cl.sh` to check the environment, setup the build directory, invoke Xilinx Vivado to create the encrypted placed-and-routed DCP (which include AWS Shell + Developer CL), create the [`manifest.txt`](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md) that AWS will ingest through the CreateFpgaImage EC2 API. Executing this script also entails encryption of developer-specified RTL files. Further details on invoking the script from Vivado are provided below.

### 1) Pre-requisite: Environment Variables and Tools

 1. The environment variable `HDK_SHELL_DIR` should have been set. This is usually done by executing `source hdk_setup.sh` from the HDK root directory
 2. The environment variable `CL_DIR` should have been set pointing to the root directory where the CL exists. The CL root directory should have the `/build` and `/design` subdirectories. One way to make sure to have the right directory is to execute `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh`
 3. Developer have Xilinx Vivado tools installed, with the supported version by the HDK, and with proper license. If the developer is using AWS supplied [FPGA Development AMI](https://aws.amazon.com/marketplace/AmazonFPGAAmi) from AWS marketplace, it includes the README.md how to setup up the tools and license.  

### 2) Encrypt Source Files

As a pre-cursor to the build process,  modify the `$CL_DIR/build/scripts/encrypt.tcl` script to include all the CL source files, so the script can encrypt and copy them to the `$CL_DIR/build/src_post_encryption` directory.

### 3) Prepare for the CL Build 

Modify the `$CL_DIR/build/scripts/create_dcp_from_cl.tcl` script to include: 
 1. The list of CL encrypted files in `$CL_DIR/build/src_post_encryption`.
 2. The list of CL specific timing and placement constraints in `$CL_DIR/build/constraints`.
 3. The specific constraints and design file for IP any included in your CL (e.g., DDR4).

### 4) Build 

Run the build from the `$CL_DIR/build/scripts` directory as follows:

    $ ./aws_build_dcp_from_cl.sh
          
This performs:
 - Synthesis of CL.
 - Implementation of CL with AWS Shell.
 - Generation of Design Checkpoint (DCP) for AWS ingestion with the associated logs.
 - Generation of the corresponding manifest.txt.
  
To aid developers in build verification, there is a final step in the build script that emulates 
the process that AWS uses to generate bitstreams from a developer DCP.

The outputs are:
 - `$CL_DIR/build/checkpoints/*`: Various checkpoints generated during the build process.
 - `$CL_DIR/build/to_aws/SH_CL_routed.dcp`: Encrypted placed-and-routed design checkpoint for AWS ingestion.
 - `$CL_DIR/build/reports/*`: Various build reports (generally, check_timing/report_timing).
 - `$CL_DIR/build/src_post_encryption/*`: Encrypted developer source.
 - `$CL_DIR/build/constraints/*`: Implementation constraints.

A developer may need to iterate multiple times through this process until arriving upon an error-free run.

### 5) Submit the final tar file to AWS to register the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tar-zipped archive into that bucket. 
You will need to prepare the following information:

1. Name of the logic design.
2. Generic description of the logic design.
3. PCI IDs: Device, Vendor, Subsystem, SubsystemVendor.
4. Location of the object containing the tar file(S3 bucket name and key).
5. Location of the S3 bucket to write logs (S3 bucket name and key).
6. Version of the AWS Shell.

To upload your DCP to S3, 

    $ ﻿aws s3 mb s3://<bucket-name>                # Create an S3 bucket (choose a unique bucket name)
    $ aws s3 cp *.SH_CL_routed.dcp \              # Upload the DCP file to S3
             s3://<bucket-name>/cl_simple.dcp

To create an AFI from the generated DCP, you need to execute the `aws ec2 create-fpga-image` command as follows: 

    $ aws ec2 create-fpga-image \                   
        --fpga-image-architecture xvu9p \
        --shell-version <shell_version> \
        --fpga-pci-id deviceId=<device_id>,vendorId=<vendor_id>,subsystemId=<subsystem_id>,subsystemVendorId=<subsystem_vendor_id> \
        --input-storage-location Bucket=<bucket-name>,Key=cl_simple.dcp
        --name MyCL
        --logs-storage-location Bucket=<bucket-name>,Key=logs/

The output of this command includes two identifiers that refer to your AFI:
- Amazon FPGA Image Identifier or AFI ID: this is the main ID used to manage your AFI through the AWS EC2 CLI commands and AWS SDK APIs. 
    This ID is regional, i.e., if an AFI is copied across multiple regions, it will have a different unique AFI ID in each region.
    An example AFI ID is `afi-01234567890abcdef`. 
- Amazon Global FPGA Image Identifier or AGFI ID: this is a global ID that is used to refer to an AFI from within an F1 instance.
    For example, to load or clear an AFI from an FPGA slot, you use the AGFI ID.
    Since the AGFI IDs are global identifiers, you can copy a combination of AFI/AMI to multiple regions, and they will work without requiring any extra setup. 
    An example AGFI ID is `agfi-01234567890abcdef`.

After the AFI generation is complete, AWS will put the AFI generation logs into the bucket location provided by the developer and notify them
by email using Amazon Simple Notification Service (Amazon SNS).

**NOTE**: Preview-program customers without access to the AWS CLI EC2 action `create-fpga-image` should instead follow the instructions [here](https://github.com/aws/aws-fpga/tree/master/hdk/cl/examples#method-2-during-f1-preview-and-before-aws-ec2-cli-action-create-fpga-image-is-available).  

## Build Stratergies and Parallel Builds <a name="buildstratgies"></a>

Developers' may face challenges fitting the CL design into the FPGA due to routing congestion, placement congestion, or not being able to meet timing. This is a typical challenge in FPGA and chip development.

AWS script `./aws_build_dcp_from_cl.sh` offer an optional flag to set one of handful implementation strategies, which would automatically different directives to various build steps. You can learn about the various strategy options by running `$ ./aws_build_dcp_from_cl.sh -help`.

If you are running on one EC2 instances with 31GiB or more DRAM, you could run multiple builds concurrently for the same CL, but calling the build script multiple times with different `-strategy` options, taking advantage of the large vCPU count typically available on EC2 instance, as each build would typically consume between 1 to 8 vCPUs throughout the entire run of a given build.

## About Encryption <a name="buildencryption"></a>

Developer RTL is encrypted using IEEE 1735 V2 encryption.  This level of encryption protects both the raw source files and the implemented design.  


## Advanced Notes <a name="buildadvancednotes"></a>

* The included implementation flow is a baseline flow.  It is possible to add advanced commands/constraints (e.g, rejoining) to the flow.
* Developers are free to modify the flow, but the final output must be a tar file with manifest.txt and the combined (AWS Shell + CL), encrypted, placed-and-routed design checkpoint,.

# Frequently Asked Questions <a name="buildfaq"></a>


1. What are the different files that a developer needs to provide to AWS?

2. How do I ensure that the DCP I create will generate a good bistream at AWS?

3. What should I do my design is not meeting timing?

4. My design was meeting timing, but even without changes, subsequent builds are not meeting timing?

5. "pr_verify" is complaining that the design checkpoints are incompatible. What should I do?

6. What version of Vivado do I need to use?
