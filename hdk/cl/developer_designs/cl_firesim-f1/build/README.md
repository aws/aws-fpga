# How to build and submit your Custom Logic (CL) to AWS 

# Table of Contents

1. [Overview of AFI Build process](#buildoverview)
2. [Build procedure step by step](#stepbystep)
3. [Build strategies and parallel builds](#strategies)
4. [About Encryption during build process](#buildencryption)
5. [Advanced Notes](#buildadvanced_notes)
6. [Build Frequently Asked Questions](#buildfaq)


<a name="buildoverview"></a>
## Overview 

Once the developer has a functional design, the next steps are to: synthesize the design into basic FPGA cells, perform place-and-route, and check that the design meets the timing/frequency constraints. This could be an iterative process. Upon success, the developer will need to pass the output of the flow to AWS for final AFI creation.

The developer needs to transfer to AWS a tar file that includes the encrypted placed-and-routed design checkpoint (referred to as DCP throughout this document) and [manifest](./../../../../docs/AFI_Manifest.md). The DCP includes the complete developer design that meets timing/frequency constraints, placement boundaries  within the allocated CL area on the FPGA, and the functional requirements laid out in the [Shell Interface Specification](./../../../../docs/AWS_Shell_Interface_Specification.md#overview).  The [manifest.txt](./../../../../docs/AFI_Manifest.md) should include key parameters needed for registering and loading the AFI, such as target frequency.

To assist in this process, AWS provides a reference DCP that includes the shell (SH) logic with a black-boxed CL under: `$HDK_SHELL_DIR/build/checkpoints/from_aws/SH_CL_BB_routed.dcp`

AWS also provides an out-of-the-box generic script called `aws_build_dcp_from_cl.sh` that is used to test compile a few examples, such as the `cl_hello_world` design, as if they were developer code. These reference examples can serve as starting points for new designs. The output of the AWS-provided scripts will create a tar file, with both the encrypted placed-and-routed DCP and the corresponding `manifest.txt`, which AWS will use to generate the final bitstream.

AWS provides multiple options to generate a DCP that meets placement and timing constraints. The `aws_build_dcp_from_cl.sh` provides multiple choices for implementation strategies, invoked by the `-strategy` option. For more details refer to [Build Strategies](#strategies) below or call `aws_build_dcp_from_cl.sh -help` for the list of supported capabilities.

Advanced developers can use different scripts, tools, and techniques (e.g., regioning), with the condition that they submit both the `manifest.txt` and "encrypted placed-and-routed design checkpoint (DCP)" in a single tar file that passes final checks.

<a name="stepbystep"></a>
## Build Procedure 

The following describes the step-by-step procedure to build developer CLs. Some of these steps can be modified or adjusted based on developer experience and design needs. 

A developer can execute `$HDK_SHELL_DIR/build/scripts/aws_build_dcp_from_cl.sh` to check the environment, setup the build directory, invoke Xilinx Vivado to create the encrypted placed-and-routed DCP (which include AWS Shell + Developer CL), create the [`manifest.txt`](./../../../../docs/AFI_Manifest.md) that AWS will ingest through the CreateFpgaImage EC2 API. Executing this script also entails encryption of developer-specified RTL files. Further details on invoking the script from Vivado are provided below.

### 1) Pre-requisite: Environment Variables and Tools

 1. The environment variable `HDK_SHELL_DIR` should have been set. This is usually done by executing `source hdk_setup.sh` from the HDK root directory
 2. The environment variable `CL_DIR` should have been set pointing to the root directory where the CL exists. The CL root directory should have the `/build` and `/design` subdirectories. One way to make sure to have the right directory is to execute `source $(HDK_DIR)/cl/developer_designs/prepare_new_cl.sh`
 3. Developer have Xilinx Vivado tools installed, with the supported version by the HDK, and with proper license. If the developer is using AWS supplied [FPGA Development AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) from AWS marketplace, it includes the README.md how to setup up the tools and license.  

### 2) Encrypt Source Files

CL Encryption is required and AFI creation will fail if your CL source files are not encrypted.  As a pre-cursor to the build process,  modify the `$CL_DIR/build/scripts/encrypt.tcl` script to include all the CL source files, so the script can encrypt and copy them to the `$CL_DIR/build/src_post_encryption` directory.

### 3) Prepare for the CL Build 

Modify the `$CL_DIR/build/scripts/create_dcp_from_cl.tcl` script to include: 
 1. The list of CL encrypted files in `$CL_DIR/build/src_post_encryption`.
 2. The list of CL specific timing and placement constraints in `$CL_DIR/build/constraints`.
 3. The specific constraints and design file for IP any included in your CL (e.g., DDR4).

### 4) Build 

Run the build script, aws_build_dcp_from_cl.sh, from the `$CL_DIR/build/scripts` directory.

The build script performs:
 - Synthesis of CL.
 - Implementation of CL with AWS Shell.
 - Generation of Design Checkpoint (DCP) for AWS ingestion with the associated logs.
 - Generation of the corresponding manifest.txt.
  
<a name="strategies"></a>  
#### Build Strategies   
In order to help developers close timing goals and successfully build their designs efficiently, the build script provides the means to synthesize with different strategies. The different strategies alter the directives used by the synthesis tool. For example, some directives might specify additional optimizations to close timing, while others may specify less effort to minimize synthesis time for designs that can more easily close timing and area goals. Since every design is different, some strategies may provide better results than another build strategies. If a developer has trouble successfully building their design with one strategy it is encouraged that they try a different strategy, or run a few strategies in parallel using the FPGA Developer AMI. The strategies are described in more detail below.

Build script usage:

    $ ./aws_build_dcp_from_cl.sh [ [-script <vivado_script>] | [-strategy BASIC | DEFAULT | EXPLORE | TIMING | CONGESTION] [-clock_recipe_a A0 | A1 | A2] [-clock_recipe_b B0 | B1 | B2 | B3 | B4 | B5] [-clock_recipe_c C0 | C1 | C2 | C3] [-uram_option 2 | 3 | 4] [-foreground] [-notify] | [-h] | [-H] | [-help] ]
Options:

* -script \<vivado_script>
       * Use the specified vivado script. The default script create_dcp_from_cl.tcl will be used if a script is not specified.

* -h, -H, -help
       * Print a usage message.

* -strategy \<BASIC | EXPLORE | TIMING | CONGESTION | DEFAULT>
       * Use the specified strategy to alter the directives used during synthesis. The DEFAULT strategy will be used if a strategy is not specified.

* -clock_recipe_a \<A0 ... An>
       * Use the Clock Group A clock frequencies defined for the specified Clock Group A recipe. This is an optional argument and the default value will be A0. Refer to the [Clock Group Recipes Table](./../../../../docs/clock_recipes.csv).

* -clock_recipe_b \<B0 ... Bn>
       * Use the Clock Group B clock frequencies defined for the specified Clock Group B recipe. This is an optional argument and the default value will be B0. Refer to the [Clock Group Recipes Table](./../../../../docs/clock_recipes.csv).

* -clock_recipe_c \<C0 ... Cn>
       * Use the Clock Group C clock frequencies defined for the specified Clock Group C recipe. This is an optional argument and the default value will be C0. Refer to the [Clock Group Recipes Table](./../../../../docs/clock_recipes.csv).

* -uram_option \<2 | 3 | 4>
       * Use the specified URAM option to define the percentage of URAM sites used for the design. A value of 2 indicates 50%, a value of 3 indicates 75%, and a value of 4 indicates 100%. This is an optional argument and the default value will be 2.

* -foreground
       * Run the build in the foreground such that all output will go to the terminal and the build may be terminated if the terminal is closed. This option is useful if you want to wait for the build to complete. This option is safe if the terminal is running on the AWS instance, for example on a GUI desktop on the instance.

* -notify
       * Send e-mail to notify user once the build is complete.  Requires setup described in `$HDK_DIR/README.md`.

Strategy descriptions:

* BASIC
  * This is the basic flow in Vivado and contains the mandatory steps to be able to build a design. It is designed to provide a good balance between runtime and Quality of Results (QOR).

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
 - `$CL_DIR/build/reports/*`: Various build reports (generally, check_timing/report_timing).
 - `$CL_DIR/build/src_post_encryption/*`: Encrypted developer source.
 - `$CL_DIR/build/constraints/*`: Implementation constraints.

A developer may need to iterate multiple times through this process until arriving upon an error-free run.

### 5) Submit the final tar file to AWS to register the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tarball file into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. PCI IDs: Device, Vendor, Subsystem, SubsystemVendor.
4. Location of the tarball file object in S3.
5. Location of an S3 directory where AWS would write back logs of the AFI creation.
6. Version of the AWS Shell.

**NOTE**: *The PCI IDs for the example CLs should be found in the README files in the respective CL example directory.
If you are building a custom CL, then you need to incorporate these values in your design as shown in the [AWS Shell Interface Specifications](./../../../../docs/AWS_Shell_Interface_Specification.md#misc).*

[Refer to step 3 for instructions on how to submit the Design Checkpoint to AWS](./../../../../README.md)

<a name="buildstratgies"></a>
## Build Strategies and Parallel Builds 

Developers may face challenges fitting the CL design into the FPGA due to routing congestion, placement congestion, or not being able to meet timing. These are typical challenges in FPGA and chip development.

AWS script `./aws_build_dcp_from_cl.sh` offers an optional flag to set one of a few useful implementation strategies, which would automatically different directives to various build steps. You can learn about the various strategy options by running `$ ./aws_build_dcp_from_cl.sh -help`.

If you are running on one of the EC2 compute instances with 31GiB DRAM or more, you could run multiple builds concurrently for the same CL, but calling the build script multiple times with different `-strategy` options, taking advantage of the large vCPU count typically available on EC2 instances, as each build would typically consume between 1 to 8 vCPUs throughout the entire run of a given build.

<a name="buildencryption"></a>
## About Encryption 

Developer RTL can encrypted using IEEE 1735 V2 encryption. This level of encryption protects both the raw source files and the implemented design.  

By default, our scripts encrypt all CL RTLs that we provide and we encourage you to do so too.

<a name="buildadvanced_notes"></a>
## Advanced Notes 

* The included implementation flow is a baseline flow.  It is possible to add advanced commands/constraints (e.g, rejoining) to the flow.
* Developers are free to modify the flow, but the final output must be a tar file with manifest.txt and the combined (AWS Shell + CL), encrypted, placed-and-routed design checkpoint,.

<a name="buildfaq"></a>
# Frequently Asked Questions 


**Q: What are the different files that a developer needs to provide to AWS?**
The developer should submit a tar file that contains the placed-and-routed DCP along with the required manifest.txt file.

**Q: What should I do my design is not meeting timing?**
The developer should evaluate the timing path to identify a solution that may include design changes or additional constraints. Additionally, the developer can try using one of the different build strategies that may help resolve the timing violations.

**Q: My design was meeting timing, but even without changes, subsequent builds are not meeting timing?**
This may happen due to various reasons. The developer should investigate the timing violation regardless of the lack of design changes. Additionally, the developer can try using one of the different build strategies that may help resolve the timing violations.

**Q: "pr_verify" is complaining that the design checkpoints are incompatible. What should I do?**
The developer can double-check that the AWS Shell DCP, SH_CL_BB_routed.dcp, was downloaded properly from the S3 bucket to the `hdk/common/shell_stable/build/checkpoints/from_aws` directory during the [hdk_setup.sh](../../../../../hdk_setup.sh) step and that there aren't errors in the build log. 

**Q: What version of Vivado do I need to use?**
The valid version of Vivado is verified during the [hdk_setup.sh](../../../../../hdk_setup.sh) step.

