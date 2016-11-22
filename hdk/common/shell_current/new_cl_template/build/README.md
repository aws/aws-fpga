# How to build and submit your Custom Logic (CL) to AWS 


## Overview

Once the developer has a functional design, the next steps are to: synthesize the design into basic FPGA cells, perform place-and-route, and check that the design meets the timing/frequency constraints. This could be an iterative process. Upon success, the developer will need to pass the output of the flow to AWS for final AFI creation.

The developer needs to transfer to AWS the encrypted placed-and-routed design checkpoints (referred to as DCP throughout this document). The DCP includes the complete developer design that meets timing/frequency constraints, placement boundraries within the allocated CL area on the FPGA, and the functional requirements laid out in the Shell Interface Specification file.

To assist in this process, AWS provides a reference DCP that includes the shell (SH) logic with a black-boxed CL under: 
      '$HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp'

AWS also provides out-of-the-box scripts that compile a few examples like "CL_simple" design as if they were developer code. These reference examples can serve as starting points for new designs. The AWS-provided scripts create an encrypted placed-and-routed DCP that AWS will use to generate final bitstreams. 

Advanced developers can use different scripts, tools, and techniques (e.g., regioning),  with the  condition that they submit "encrypted placed-and-routed design checkpoints", that pass final checks that are included in the build scripts.  (TBD - final_check_dcp).

The following section covers the step-by-step procedure. Some of these steps can be modified or adjusted based on developer experience and design needs. 

## Build Procedure
   
Overview: A developer can call '$HDK_SHELL_DIR/build/scripts/create_dcp_from_cl.tcl' in Xilinx Vivado to create the encrypted placed-and-routed DCP (which include AWS Shell + Developer CL) that AWS will ingest through the createFpgaImage EC2 API.
Calling this script also entails encryption of developer-specified RTL files. Further details on invoking the script from Vivado are provided below.

Steps: 

### 1) Pre-requisite: Environment Variables and tools

	1a) The environment variables `HDK_SHELL_DIR` should have been set. This is usually done by called `source hdk_setup.sh` from the hdk root directory
	1b) the environment variable `CL_DIR` should have been set pointing to the root directory where the CL exists. the CL root directory should have the `/build` and `/design` subdirectories. One way to make sure to have the right directory is to use `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh`
	1c) Developer have Xilinx vivado tools installed, with the supported version by the HDK, and with proper license. If the developer is using AWS supplied "FPGA Development AMI" from AWS marketplace, it includes the README.md how to setup up the tools and license  

### 2) Encrypt source files

As a pre-cursor to the encryption and build proces,  modify the `$CL_DIR/build/scripts/encrypt.tcl` to include all the CL source files, so the script can encrypt them and copy to `$CL_DIR/build/src_post_encryption` directory

### 3) Modify the `$CL_DIR/build/scripts/build_dcp_from_cl` 

to include all the 
	3a) The list of CL encrypted files in `$CL_DIR/build/src_post_encryption`
	3b) The list of CL specific timing and placement constraints in `$CL_DIR/build/constraints`
	3c) The specific constraints and design file for IP included in your CL like DDR4

### 4) Run the build 

from the '$CL_DIR/build/scripts' folder as follows:
          `vivado -mode batch -source create_dcp_from_cl.tcl`
      This runs:
         - Synthesis of CL
         - Implementation of CL with AWS Shell
         - Generates design checkpoint for AWS ingestion and associated logs
  
### 5) Validate the results by emulation AWS ingestion process

To aid developers in build verification, AWS also provides a script ('$CL_DIR/build/scripts/emulate_AWS_ingestion_process.tcl') that emulates 
the process that AWS uses to generate bitstreams from a developer DCP. The script can be run as follows:
          `vivado -mode batch -source emulate_AWS_ingestion_process.tcl`

   Outputs:
      - '$CL_DIR/build/checkpoints/*': Various checkpoints generated during the build process
      - '$CL_DIR/build/to_aws/SH_CL_routed.dcp': Encrypted placed-and-routed design checkpoint for AWS ingestion
      - '$CL_DIR/build/reports/*': Various build reports (generally, check_timing/report_timing)
      - '$CL_DIR/build/src_post_encryption/*': Encrypted developer source
      - '$CL_DIR/build/constraints/*': Implementation constraints

   A developer may need to iterate multiple times through this process until arriving upon an error-free run.


## About Encryption 
   Developer RTL is encrypted using IEEE 1735 V2 encryption.  This level of encryption protects both the raw source and the implemented design.  


## Advanced Notes
   - The included implementation flow is a baseline flow.  It is possible to add advanced commands/constraints (e.g, regioning) to the flow.
   - Developers are free to modify the flow, but the final output must be a combined (AWS Shell + CL), encrypted, placed-and-routed design checkpoint.

# Frequently Asked Questions


1. What are the different files that a developer needs to provide to AWS?

2. How do I ensure that the DCP I create will generate a good bistream at AWS?

3. What should I do my design is not meeting timing?

4. My design was meeting timing, but even without changes, subsequent builds are not meeting timing?

5. "pr_verify" is complaining that the design checkpoints are incompatible. What should I do?

6. What version of Vivado do I need to use?


# Ingestion Flow for preview program customers (per EC2 FPGA APIs are available)


This section describes the flow for developers to ingest their encrypted placed-and-routed DCP into the LogicFarm service. The flow assumes the CreateFpgaImage API is still not available. It simply involves uploading an object into an S3 bucket and providing the LogicFarm team read-access to that object. To receive logs of the bitstream generation, the developer also needs to provide write-access to an S3 bucket that they own. 

1. Developer creates an S3 bucket, and uploads the zipped archive into that bucket.

2. Developer adds a policy to that bucket allowing our team's account (Account ID: 682510182675) read/write permissions. Here's an example: http://docs.aws.amazon.com/AmazonS3/latest/dev/example-walkthroughs-managing-access-example2.html

A sample bucket policy to enable AWS FPGA team read/write access to a bucket:

{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Sid": "Bucket level permissions",
            "Effect": "Allow",
            "Principal": {
                "AWS": "arn:aws:iam::682510182675:root"
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
                "AWS": "arn:aws:iam::682510182675:root"
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
                "AWS": "arn:aws:iam::682510182675:root"
            },
            "Action": [
                "s3:PutObject"
            ],
            "Resource": "arn:aws:s3:::<log_bucket_name>/*"
        }
    ]
}

4. The developer communicates with AWS FPGA team (email TBD) providing us the following information:

Name of the logic design
Desription of the logic design
PCI IDs (Device, Vendor, Subsystem, SubsystemVendor)
Location of the DCP object (bucket name and key). 
Location of the directory to write logs (bucket name and key)
Version of the Shell

5. After the AFI generation is complete, we will write the logs back into the bucket locaiton provided by the developer and notify them by email, including the AFI and AGFI IDs.

