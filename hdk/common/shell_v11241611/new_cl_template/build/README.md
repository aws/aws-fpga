# How to Build and Submit your Custom Logic (CL) to AWS (RTL Flow)

# Table of Contents

1. [Overview of AFI Build process] (#buildoverview)
2. [Build procedure step by step] (#stepbystep)
3. [Build strategies and parallel builds] (#strategies)
4. [About Encrption during build process] (#buildencryption)
5. [Advanced Notes] (#buildadvanced notes)
6. [Build Frequently Asked Questions] (#buildfaq)



## Overview <a name="buildoverview"></a>

Once the developer has a functional RTL design, the next steps are to: synthesize the design into basic FPGA cells, perform place-and-route, and check that the design meets the timing/frequency constraints. This could be an iterative process. Upon success, the developer will need to pass the output of the flow to AWS for final AFI creation.

The developer needs to transfer to AWS a tar file that includes the encrypted placed-and-routed design checkpoints (referred to as DCP throughout this document) and [manifest](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md): The DCP includes the complete developer design that meets timing/frequency constraints, placement boundaries within the allocated CL area on the FPGA, and the functional requirements laid out in the [Shell Interface Specification](https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#overview).  The [manifest.txt](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md) should include key parameters needed for registering and loading the AFI like target frequency.

Few reference [CL examples](https://github.com/aws/aws-fpga/blob/master/hdk/cl/examples) can serve as starting points for new designs.  

AWS provides out-of-the-box generic script called `aws_build_dcp_from_cl.sh` that performs complete build process from RTL (verilog for example). The output of AWS-provided scripts will create a a tar file, with both the encrypted placed-and-routed DCP and the corresponding `manifest.txt`, which AWS will use to generate final bitstreams.

To ease and experiment with multiple implementation methods for DCP to meet placement and timing constrains, the `aws_build_dcp_from_cl.sh` provides multiple choices for implementation strategy, invoked by the `-strategy` option. Please call `aws_build_dcp_from_cl.sh -help` for the list of supported capabilities.

Advanced developers can use different scripts, tools, and techniques (e.g., regioning),  with the  condition that they submit both the `manifest.txt` and **encrypted placed-and-routed design checkpoints (DCP)** in a single tar file, that passes final checks which are included in the build scripts.  (TBD - final_check_dcp).

## Build Procedure <a name="stepbystep"></a>

The following describes the step-by-step procedure to build developer CLs. Some of these steps can be modified or adjusted based on developer experience and design needs. 

A developer can execute `$HDK_SHELL_DIR/build/scripts/aws_build_dcp_from_cl.sh` which validates that the environment variables and directory structure is set properly, setup the build directory, invoke Xilinx Vivado to create the encrypted placed-and-routed DCP (which include AWS Shell + Developer CL), create the [`manifest.txt`](https://github.com/aws/aws-fpga/tree/master/hdk/docs/AFI_manifest.md) that AWS will ingest through the `create-fpga-mage` EC2 API. Executing this script also entails encryption of developer-specified RTL files. Further details on invoking the script from Vivado are provided below.

### 1) Pre-requisite: Environment Variables and Tools

 1. The environment variables `HDK_DIR` and `HDK_SHELL_DIR` should have been set. This is usually done by executing `source hdk_setup.sh` from the HDK root directory  
 
 2. The environment variable `CL_DIR` should have been set pointing to the root directory where the CL exists. The CL root directory should have the `/build` and `/design` subdirectories. One way to make sure to have the right directory is to execute `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh`
 
 3. Developer have Xilinx Vivado tools installed, with the supported version by the HDK, and with proper license. If the developer is using AWS supplied [FPGA Development AMI](https://aws.amazon.com/marketplace/AmazonFPGAAmi) from AWS marketplace, it already include Vivado tools and license.  

### 2) Encrypt Source Files

As a pre-cursor to the build process,  modify the `$CL_DIR/build/scripts/encrypt.tcl` script to include all the CL source files, so the script can encrypt and copy them to the `$CL_DIR/build/src_post_encryption` directory.

### 3) Prepare for the CL Build 

Modify the `$CL_DIR/build/scripts/create_dcp_from_cl.tcl` script to include: 
 1. The list of CL encrypted files in `$CL_DIR/build/src_post_encryption`. (They can be the duplicate file list of what in `$CL_DIR/build/scripts/encrypt.tcl`)
 2. The list of CL specific timing and placement constraints in `$CL_DIR/build/constraints`.
 3. The specific constraints and design file for IP any included in your CL (e.g., DDR4).

### 4) Build <a name="strategies"></a>

Run the build script, aws_build_dcp_from_cl.sh, from the `$CL_DIR/build/scripts` directory.

The build script performs:
 - Synthesis of CL.
 - Implementation of CL with AWS Shell.
 - Generation of Design Checkpoint (DCP) for AWS ingestion with the associated logs.
 - Generation of the corresponding manifest.txt.
  
In order to help developers close timing goals and successfully build their designs efficiently, the build script provides the means to synthesize with different strategies. The different strategies alter the directives used by the synthesis tool. For example, some directives might specify additional optimizations to close timing, while others may specify less effort to minimize synthesis time for designs that can more easily close timing and area goals. Since every design is different, some strategies may provide better results than anothers. If a developer has trouble successfully building their design with one strategy it is encouraged that they try a different strategy. The strategies are described in more detail below.

Build script usage:

    $ ./aws_build_dcp_from_cl.sh  [-h | -H | -help] [-script <vivado_script>] [-strategy <BASIC | DEFAULT | EXPLORE | TIMING | CONGESTION>]

Options:

* -script \<vivado_script>
       * Use the specified vivado script. The default script create_dcp_from_cl.tcl will be used if a script is not specified.

* -h, -H, -help
       * Print a usage message.

* -strategy \<BASIC | EXPLORE | TIMING | CONGESTION | DEFAULT>
       * Use the specified strategy to alter the directives used during synthesis. The DEFAULT strategy will be used if a strategy is not specified.

Strategy descriptions:

* BASIC
  * This is the basic flow in Vivado and contains the mandatory steps to be able to build a design. It is designed to provide a good balance betwwen runtime and Quality of Results (QOR).

* EXPLORE
  * This is a high-effort flow which is designed to give improved QOR results at the expense of runtime.
  
* TIMING
  * This flow is designed for more aggressive timing optimization at the expense of runtime and congestion.
  
* CONGESTION
  * This flow is designed to insert more aggressive whitespace to alleviate routing congestion.
  
* DEFAULT
  * This is an additional high-effort flow that results in improved QOR results for the example design at the expense of runtime.
  
In addition, in order to aid developers with build verification, there is a final step in the build script that emulates the process that AWS uses to generate bitstreams from a developer DCP.

The outputs of the build script are:
 - `$CL_DIR/build/checkpoints/*`: Various checkpoints generated during the build process.
 - `$CL_DIR/build/to_aws/SH_CL_routed.dcp`: Encrypted placed-and-routed design checkpoint for AWS ingestion.
 - `$CL_DIR/build/to_aws/manifest.txt`: Encrypted placed-and-routed design checkpoint for AWS ingestion.
 - `$CL_DIR/build/reports/*`: Various build reports (generally, check_timing/report_timing).
 - `$CL_DIR/build/src_post_encryption/*`: Encrypted developer source.

A developer may need to iterate multiple times through this process until arriving upon an error-free run.

### 5) Submit the final tar file to AWS to register the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tarball file into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. PCI IDs: Device, Vendor, Subsystem, SubsystemVendor (See https://github.com/aws/aws-fpga/blob/master/hdk/docs/Choosing_PCIe_ID_for_AFI.md)
4. Location of the tarball file object in S3.
5. Location of an S3 directory where AWS would write back logs of the AFI creation *(Optional)*. This would be required to get the **.ltx** file needed if Virtual JTAG and Xilinx LIA/VIO debug cores to be used.
6. Update mandatory parameters in the [manifest file](./../../../../docs/AFI_Manifest.md)

**NOTE**: *The PCI IDs for the example CLs should be found in the README files in the respective CL example directory.*
If you are building a custom CL, then you need to incorporate these values in your design as shown in the [AWS Shell Interface Specifications](https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#pcie-ids).*

To upload your tarball file to S3, you can use any of [the tools supported by S3](http://docs.aws.amazon.com/AmazonS3/latest/dev/UploadingObjects.html)).
For example, you can use the AWS CLI as follows:

    $ aws s3 mb s3://<bucket-name>                # Create an S3 bucket (choose a unique bucket name)
    $ aws s3 cp *.Developer_CL.tar \              # Upload the file to S3
             s3://<bucket-name>/

Now you need to provide AWS (Account ID: 365015490807) the appropriate [read/write permissions](http://docs.aws.amazon.com/AmazonS3/latest/dev/example-walkthroughs-managing-access-example2.html) to your S3 buckets.
Below is a sample policy.

**NOTE**: *The AWS Account ID has changed, please ensure you are using the correct Account ID listed here.*

    {
        "Version": "2012-10-17",
        "Statement": [
            {
                "Sid": "Bucket level permissions",
                "Effect": "Allow",
                "Principal": {
                    "AWS": "arn:aws:iam::365015490807:root"
                },
                "Action": [
                    "s3:ListBucket"
                ],
                "Resource": "arn:aws:s3:::<bucket_name>"
            },
            {
                "Sid": "Object read permissions",
                "Effect": "Allow",
                "Principal": {
                    "AWS": "arn:aws:iam::365015490807:root"
                },
                "Action": [
                    "s3:GetObject"
                ],
                "Resource": "arn:aws:s3:::<dcp_bucket_name>/<dcp_filename>"
            },
            {
                "Sid": "Folder write permissions",
                "Effect": "Allow",
                "Principal": {
                    "AWS": "arn:aws:iam::365015490807:root"
                },
                "Action": [
                    "s3:PutObject"
                ],
                "Resource": "arn:aws:s3:::<log_bucket_name>/*"
            }
        ]
    }

To create an AFI execute, make sure you update needed parameters in the [manifest file](./../../../../docs/AFI_Manifest.md) and then call the `create-fpga-image` command as follows:

    $ aws ec2 create-fpga-image \
        --input-storage-location Bucket=<bucket-name>,Key=<tarball-name> \
        --name <cl-name> \
        --description <description> \
        --logs-storage-location Bucket=<bucket-name>,Key=logs/

The output of this command includes two identifiers that refer to your AFI:
- **FPGA Image Identifier** or **AFI ID**: this is the main ID used to manage your AFI through the AWS EC2 CLI commands and AWS SDK APIs.
    This ID is regional, i.e., if an AFI is copied across multiple regions, it will have a different unique AFI ID in each region.
    An example AFI ID is **`afi-01234567890abcdef`**.
- **Glogal FPGA Image Identifier** or **AGFI ID**: this is a global ID that is used to refer to an AFI from within an F1 instance.
    For example, to load or clear an AFI from an FPGA slot, you use the AGFI ID.
    Since the AGFI IDs is global (by design), it allows you to copy a combination of AFI/AMI to multiple regions, and they will work without requiring any extra setup.
    An example AGFI ID is **`agfi-01234567890abcdef`**.

After the AFI generation is complete, AWS will put the logs into the bucket location provided by the developer and notify them
by email.

**NOTE**: *Attempting to associate the AFI to an AMI before the AFI is ready will result in an `InvalidFpgaImageID.Unavailable` error.
Please wait until you receive a confirmation email from AWS indicating the creation process is complete.*

## Build Strategies and Parallel Builds <a name="buildstratgies"></a>

Developers may face challenges fitting the CL design into the FPGA due to routing congestion, placement congestion, or not being able to meet timing. These are typical challenges in FPGA and chip development.

AWS script `./aws_build_dcp_from_cl.sh` offers an optional flag to set one of a few useful implementation strategies, which would automatically different directives to various build steps. You can learn about the various strategy options by running `$ ./aws_build_dcp_from_cl.sh -help`.

If you are running on one of the EC2 compute instances with 31GiB DRAM or more, you could run multiple builds concurrently for the same CL, but calling the build script multiple times with different `-strategy` options, taking advantage of the large vCPU count typically available on EC2 instances, as each build would typically consume between 1 to 8 vCPUs throughout the entire run of a given build.

## About Encryption <a name="buildencryption"></a>

Developer RTL is encrypted using IEEE 1735 V2 encryption.  This level of encryption protects both the raw source files and the implemented design.  


## Advanced Notes <a name="buildadvanced notes"></a>

* The included implementation flow is a baseline flow.  It is possible to add advanced commands/constraints (e.g, rejoining) to the flow.
* Developers are free to modify the flow, but the final output must be a tar file with manifest.txt and the combined (AWS Shell + CL), encrypted, placed-and-routed design checkpoint,.

# Frequently Asked Questions <a name="buildfaq"></a>


1. What are the different files that a developer needs to provide to AWS?

2. How do I ensure that the DCP I create will generate a good bistream at AWS?

3. What should I do my design is not meeting timing?

4. My design was meeting timing, but even without changes, subsequent builds are not meeting timing?

5. "pr_verify" is complaining that the design checkpoints are incompatible. What should I do?

6. What version of Vivado do I need to use?
