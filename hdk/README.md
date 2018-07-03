# AWS FPGA Hardware Development Kit (HDK)

## Table of Contents
1. [HDK Overview](#overview)
2. [Getting Started](#gettingstarted)
    - [AWS Account, F1/EC2 Instances, On-Premises, AWS IAM Permissions, AWS CLI and S3 Setup (One-time Setup)](#iss)
    - [Install the HDK and setup environment](#setup)
    - [Review examples](#examples)
3. [How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide](#endtoend)
    - [Fast path to running CL Examples on FPGA Instance](#fastpath)
    - [Step 1. Pick one of the examples and move to its directory](#step1)  
    - [Step 2. Build the CL](#step2)
    - [Step 3. Submit the Design Checkpoint to AWS to Create the AFI](#step3)
    - [Step 4. Setup AWS FPGA Management tools](#step4)
    - [Step 5. Load the AFI](#step5)
    - [Step 6. Validating using the CL Example Software](#step6)
4. [Simulate Custom Logic (CL) RTL Design](#simcl)
5. [Start your own Custom Logic design (RTL flow, using Verilog or VHDL)](#buildcl)

<a name="overview"></a>
## HDK Overview

* The HDK provides developers with information, examples and scripts to build a fully custom hardware accelerator on F1.  A fully custom hardware accelerator may take months to develop and developer must be familiar with:
  * Scripting (shell, tcl)
  * RTL (Verilog or VHDL) development
  * Synthesis tools and the iterative process of identifying timing critical paths and optimizing hardware to meet timing
  * Familiarity with concepts related to designing for FPGAs, DMA, DDR, AXI protocol and linux drivers
  * RTL simulation 
  * Experience with simulation debug or FPGA runtime waveform viewer debug methods
* Developers not familiar with these areas should start with [software defined acceleration](../SDAccel/README.md)    
* Developers with existing RTL IP that are not familiar with the areas listed above should start with RTL Kernel development using [software defined acceleration](../SDAccel/README.md).
* Developers looking for a faster HDK development path, should start with RTL Kernel development using [software defined acceleration](../SDAccel/README.md) 

* The [documents directory](./docs) provides the specification for the AWS Shell (SH) to Custom Logic (CL) interface:
  * [Shell Interface](./docs/AWS_Shell_Interface_Specification.md)
  * [Shell Address Map](./docs/AWS_Fpga_Pcie_Memory_Map.md)
  * [Programmer view of the FPGA](./docs/Programmer_View.md)
  * [Virtual JTAG](./docs/Virtual_JTAG_XVC.md)
  * [Simulating RTL Design using testbenches and shell simulation model](./docs/RTL_Simulating_CL_Designs.md)
  * [Analyzing Power](./docs/afi_power.md)
  * [Detecting a shell timeout](./docs/HOWTO_detect_shell_timeout.md)
  
* The [common directory](./common) includes common environment setup scripts, common build scripts and constraints files and IP libraries like the DRAM controller. This directory includes a production shell which is reference under `shell_stable` directory.  The AWS Shell Design Checkpoint (DCP) will be downloaded into the common directory from S3 during hdk setup.
  * Developers should not need to change any file under the `/common` directory
  * `shell_stable` directory contains the files needed by developers to build a CL using a current production shell.

* The [Custom Logic (cl) directory](./cl) is where the Custom Logic is expected to be developed (For RTL-based development using Verilog or VHDL). It includes a number of examples under the [examples directory](./cl/examples), as well as a placeholder for the developer's own Custom Logic under [developer_designs directory](./cl/developer_designs).  For more details on the examples, see the [examples table](./cl/examples/cl_examples_list.md).

<a name="gettingstarted"></a>
## Getting Started

<a name="iss"></a>
#### AWS Account, F1/EC2 Instances, On-Premises, AWS IAM Permissions, AWS CLI and S3 Setup (One-time Setup)
* [Setup an AWS Account](https://aws.amazon.com/free/)
* Launch an instance using the [FPGA Developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) which comes pre-installed with Vivado and required licenses.  Given the large size of the FPGA used inside the AWS FPGA instances, the implementation tools require 32GiB Memory (ex: c4.4xlarge, m4.2xlarge, r4.xlarge, t2.2xlarge). c4.4xlarge and c4.8xlarge would provide the fastest execution time with 30 and 60GiB of memory respectively. Developers who want to save on cost, would start coding and run simulations on low-cost instances, like t2.2xlarge, and move to the aforementioned larger instances to run the synthesis of their acceleration code.  Follow the [On-Premises Instructions](docs/on_premise_licensing_help.md) to purchase and install a license from Xilinx.
  * This release supports Xilinx SDx 2017.4 only.  The compatibility table describes the mapping of developer kit version to [FPGA developer AMI](https://aws.amazon.com/marketplace/pp/B06VVYBLZZ) version:  

| Developer Kit Version   | Tool Version Supported     |  Compatible FPGA developer AMI Version     |
|-----------|-----------|------|
| 1.3.0-1.3.6 | 2017.1 | v1.3.5 |
| 1.3.7-1.3.X | 2017.1 | v1.3.5-v1.3.X (Xilinx SDx 2017.1) |
| 1.3.7-1.3.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |
| 1.4.X | 2017.4 | v1.4.0-v1.4.X (Xilinx SDx 2017.4) |

* FPGA developer kit version is listed in [hdk_version.txt](./hdk_version.txt)

* FPGA developer kit supported tool versions are listed in [supported\_vivado\_versions](../supported_vivado_versions.txt)

* Setup AWS IAM permissions for creating FPGA Images (CreateFpgaImage and DescribeFpgaImages). [EC2 API Permissions are described in more detail](http://docs.aws.amazon.com/AWSEC2/latest/APIReference/ec2-api-permissions.html).  It is highly recommended that you validate your AWS IAM permissions prior to proceeding with this quick start.  By calling the [DescribeFpgaImages API](docs/describe_fpga_images.md) you can check that your IAM permissions are correct.

* [Setup AWS CLI and S3 Bucket](../SDAccel/docs/Setup_AWS_CLI_and_S3_Bucket.md) to enable AFI creation.
  * To install the AWS CLI, please follow the [AWS CLI Installation guide](http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and default region

Use the aws-cli [region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) command line argument to override the profile default region.  Supported regions include: us-east-1, us-west-2, eu-west-1 and us-gov-west-1.

<a name="setup"></a>
#### Install the HDK and setup environment

The AWS FPGA HDK can be cloned to your EC2 instance or server by executing:

When using the developer AMI:  ```AWS_FPGA_REPO_DIR=/home/centos/src/project_data/aws-fpga```
    
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source hdk_setup.sh

Note that sourcing `hdk_setup.sh` will set required environment variables that are used throughout the examples in the HDK.  DDR simulation models and DCP(s) are downloaded from S3 during hdk setup.  New terminal or xterm requires `hdk_setup.sh` to be rerun.  

<a name="examples"></a>
#### Review examples 

The [Examples readme](./cl/examples/cl_examples_list.md) provides an overview of all examples available to developers.

<a name="endtoend"></a>
## How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide

<a name="fastpath"></a>
#### Fast path to running CL Examples on FPGA Instance

For developers that want to skip the development flow and start running the examples on the FPGA instance.  You can skip steps 1 through 3 if you are not interested in the development process.  Step 4 through 6 will show you how to use one of the predesigned AFI examples.  By using the public AFIs, developers can skip the build flow steps and jump to step 4. [Public AFIs are available for each example and can be found in the example/README](cl/examples/cl_hello_world/README.md#metadata).  

<a name="step1"></a>
#### Step 1. Pick one of the examples and start in the example directory

It is recommended that you complete this step-by-step guide using HDK hello world example.  Next use this same guide to develop using the [cl\_dram\_dma](cl/examples/cl_dram_dma).  When your ready, copy one of the examples provided and modify the design files, scripts and constraints directory.

    $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to cl_dram_dma, cl_uram_example or cl_hello_world_vhdl
    $ export CL_DIR=$(pwd)

Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each example follows the recommended directory structure to match the expected structure for HDK simulation and build scripts.

<a name="step2"></a>
#### Step 2. Build the CL

This [checklist](./cl/CHECKLIST_BEFORE_BUILDING_CL.md) should be consulted before you start the build process.

**NOTE** *This step requires you to have Xilinx Vivado Tools and Licenses installed*

    $ vivado -mode batch        # Verify Vivado is installed.

Executing the `aws_build_dcp_from_cl.sh` script will perform the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA.
The output is a tarball file comprising the DCP file, and other log/manifest files, formatted as `YY_MM_DD-hhmm.Developer_CL.tar`.
This file would be submitted to AWS to create an AFI. By default the build script will use Clock Group A Recipe A0 which uses a main clock of 125 MHz.

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.sh

In order to use a 250 MHz main clock the developer can specify the A1 Clock Group A Recipe as in the following example:

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.sh -clock_recipe_a A1

Other clock recipes can be specified as well. More details on the [Clock Group Recipes Table](./docs/clock_recipes.csv) and how to specify different recipes can be found in the following [README](./common/shell_v04261818/new_cl_template/build/README.md).

**NOTE**: *The DCP generation can take up to several hours to complete, hence the `aws_build_dcp_from_cl.sh` will run the main build process (`vivado`) in within a  `nohup` context: This will allow the build to continue running even if the SSH session is terminated half way through the run*

To be notified via e-mail when the build completes:

1. Set up notification via SNS:

```
    $ export EMAIL=your.email@example.com
    $ $HDK_COMMON_DIR/scripts/notify_via_sns.py

```

2. Check your e-mail address and confirm subscription
3. When calling `aws_build_dcp_from_cl.sh`, add on the `-notify` switch
4. Once your build is complete, an e-mail will be sent to you stating "Your build is done."
5. For each example the known warnings are documented in warnings.txt file located in the $CL_DIR/build/scripts directory
   [cl\_hello\_world warnings](cl/examples/cl_hello_world/build/scripts/warnings.txt )
   [cl\_dram\_dma warnings](cl/examples/cl_dram_dma/build/scripts/warnings.txt )
   [cl\_uram\_example warnings](cl/examples/cl_uram_example/build/scripts/warnings.txt )

<a name="step3"></a>
#### Step 3. Submit the Design Checkpoint to AWS to Create the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tarball file into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. Location of the tarball file object in S3.
4. Location of an S3 directory where AWS would write back logs of the AFI creation.
5. AWS region where the AFI will be created.  Use [copy-fpga-image](./docs/copy_fpga_image.md) API to copy an AFI to a different region.

To upload your tarball file to S3, you can use any of [the tools supported by S3](http://docs.aws.amazon.com/AmazonS3/latest/dev/UploadingObjects.html).

For example, you can use the AWS CLI as follows:

Create a bucket and folder for your tarball, then copy to S3
```
    $ aws s3 mb s3://<bucket-name> --region <region>   # Create an S3 bucket (choose a unique bucket name)
    $ aws s3 mb s3://<bucket-name>/<dcp-folder-name>/   # Create folder for your tarball files
    $ aws s3 cp $CL_DIR/build/checkpoints/to_aws/*.Developer_CL.tar \       # Upload the file to S3
             s3://<bucket-name>/<dcp-folder-name>/

     NOTE: The trailing '/' is required after <dcp-folder-name>
```
Create a folder for your log files        
```    
    $ aws s3 mb s3://<bucket-name>/<logs-folder-name>/  # Create a folder to keep your logs
    $ touch LOGS_FILES_GO_HERE.txt                     # Create a temp file
    $ aws s3 cp LOGS_FILES_GO_HERE.txt s3://<bucket-name>/<logs-folder-name>/  #Which creates the folder on S3
    
    NOTE: The trailing '/' is required after <logs-folder-name>
```             

Start AFI creation. 
```
    $ aws ec2 create-fpga-image \
        --region <region> \
        --name <afi-name> \
        --description <afi-description> \
        --input-storage-location Bucket=<dcp-bucket-name>,Key=<path-to-tarball> \
        --logs-storage-location Bucket=<logs-bucket-name>,Key=<path-to-logs> \
	[ --client-token <value> ] \
	[ --dry-run | --no-dry-run ]
	
    NOTE: <path-to-tarball> is <dcp-folder-name>/<tar-file-name>
          <path-to-logs> is <logs-folder-name>
```

The output of this command includes two identifiers that refer to your AFI:
- **FPGA Image Identifier** or **AFI ID**: this is the main ID used to manage your AFI through the AWS EC2 CLI commands and AWS SDK APIs.
    This ID is regional, i.e., if an AFI is copied across multiple regions, it will have a different unique AFI ID in each region.
    An example AFI ID is **`afi-06d0ffc989feeea2a`**.
- **Glogal FPGA Image Identifier** or **AGFI ID**: this is a global ID that is used to refer to an AFI from within an F1 instance.
    For example, to load or clear an AFI from an FPGA slot, you use the AGFI ID.
    Since the AGFI IDs is global (by design), it allows you to copy a combination of AFI/AMI to multiple regions, and they will work without requiring any extra setup.
    An example AGFI ID is **`agfi-0f0e045f919413242`**.

The [describe-fpga-images](./docs/describe_fpga_images.md) API allows you to check the AFI state during the background AFI generation process.
You must provide the **FPGA Image Identifier** returned by `create-fpga-image`:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-06d0ffc989feeea2a
```

You can use the [wait_for_afi.py](./docs/wait_for_afi.md) script to wait for the AFI creation to complete and then optionally
send an email with the results.

The AFI can only be loaded to an instance once the AFI generation completes and the AFI state is set to `available`: 
```
    {
        "FpgaImages": [
            {
			    ...
                "State": {
                    "Code": "available"
                },
			    ...
                "FpgaImageId": "afi-06d0ffc989feeea2a",
			    ...
            }
        ]
    }

```

After the AFI generation is complete, AWS will put the logs into the bucket location (```s3://<bucket-name>/<logs-folder-name>```) provided by the developer. The presence of these logs is an indication that the creation process is complete. Please look for either a “State” file indicating the state of the AFI (e.g., available or failed), or the Vivado logs detailing errors encountered during the creation process.  For help with AFI creation issues, see [create-fpga-image error codes](./docs/create_fpga_image_error_codes.md)

**NOTE**: *Attempting to load the AFI immediately on an instance will result in an `Invalid AFI ID` error.
Please wait until you confirm the AFI is created successfully.*

**NOTE**: *Attempting to load the AFI in a region different from where the AFI was created will result in an `Invalid AFI ID` error.  AFIs need to be copied to regions.*
The [copy-fpga-image](./docs/copy_fpga_image.md) API allows you to copy the AFI to other regions and avoid the time consuming `create-fpga-image` process. Copy will also preserve the source Global AFI ID and minimize region-specific changes to your instance code or scripts.

#### Step by step guide how to load and test a registered AFI from within an F1 instance

To follow the next steps, you have to launch an F1 instance.
AWS recommends that you launch an instance with latest Amazon Linux that has the FPGA Management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

<a name="step4"></a>
#### Step 4. Setup AWS FPGA Management tools

The FPGA Management tools are required to load an AFI onto an FPGA.  Depending on your AMI used to run the F1 instance, these steps may have been completed already.
```
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source sdk_setup.sh
```
To install the AWS CLI, please follow [AWS CLI Installation guide](http://docs.aws.amazon.com/cli/latest/userguide/installing.html).
```
    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and instance region (us-east-1, us-west-2, eu-west-1 or us-gov-west-1)
```
<a name="step5"></a>
#### Step 5. Load the AFI

You can now use the FPGA Management tools, from within your F1 instance, to load your AFI onto an FPGA on a specific slot.
Make sure you clear any AFI you have previously loaded in your slot:
```
    $ sudo fpga-clear-local-image  -S 0
```

You can also invoke the `fpga-describe-local-image` command to learn about which AFI, if any, is loaded onto a particular slot.
For example, if the slot is cleared (`slot 0` in this example), you should get an output similar to the following:

```
    $ sudo fpga-describe-local-image -S 0 -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       none                    cleared           1        ok               0       <shell_version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0
```

If fpga-describe-local-image API call returns a status 'Busy', the FPGA is still performing the previous operation in the background. Please wait until the status is 'Cleared' as above.

Now, let us try loading your AFI to FPGA `slot 0`:

```
    $ sudo fpga-load-local-image -S 0 -I agfi-0f0e045f919413242
```


**NOTE**: *The FPGA Management tools use the AGFI ID (not the AFI ID).*

Now, you can verify that the AFI was loaded properly.  The output shows the FPGA in the “loaded” state after the FPGA image "load" operation.  The "-R" option performs a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id.
```
    $ sudo fpga-describe-local-image -S 0 -R -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       agfi-0f0e045f919413242  loaded            0        ok               0       <shell version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x6789      0x1d50      0000:00:0f.0
```
    
<a name="step6"></a>
#### Step 6. Validating using the CL Example Software

Each CL Example comes with a runtime software under `$CL_DIR/software/runtime/` subdirectory. You will need to build the runtime application that matches your loaded AFI.   

```
    $ cd $CL_DIR/software/runtime/
    $ make all
    $ sudo ./test_hello_world
```

For additional information per example, review the README.md located in the $CL_DIR/README.md

<a name="simcl"></a>
## Simulate your Custom Logic design (RTL Simulation)

You can use Vivado XSIM simulator, or bring your own simulator (like Synopsys' VCS, Mentor's Questa, or Cadence Incisive).
Follow the [RTL simulation environment setup](./docs/RTL_Simulating_CL_Designs.md#introduction) to run these simulations

<a name="buildcl"></a>
## Start your own Custom Logic design (RTL flow, using Verilog or VHDL)

* Before starting your new design review the specification for the AWS Shell (SH) to Custom Logic (CL) [interface](./docs/AWS_Shell_Interface_Specification.md).
* Try the [debug flow](docs/Virtual_JTAG_XVC.md) and understand the [shell timeout behavior](docs/HOWTO_detect_shell_timeout.md).
* When your ready, copy an example to [start your own CL design](./cl/developer_designs/Starting_Your_Own_CL.md) and make a simple modification to get familiar with customizing the hardware developer kit for your development needs.



