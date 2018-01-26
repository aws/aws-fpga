# How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide

As a pre-requisite to building the AFI, the developer should have an instance/server with Xilinx Vivado Tools and the necessary Licenses. The "FPGA Developer AMI" provided free of charge on AWS Marketplace will be an ideal place to start an instance from. See the README.md on the AMI for the details how to launch the FPGA Developer's AMI, install the tools and set up the license.

**NOTE:** *It is recommended that steps 1 through 3 be done on an EC2 instance with 32GiB or greater. C4/C5 instances are recommended for fastest build time.*

**NOTE:** *You can skip steps 0 through 3 if you are not interested in the build process.  Step 4 through 6 will show you how to use one of the predesigned AFI examples.*

### Fast path to running CL Examples on FPGA Instance

For developers that want to skip the build flow and start running the examples on the FPGA instance.  [Public AFIs are available for each example.](./cl_hello_world/README.md#metadata).  By using the public AFIs, developers can skip the build flow steps and jump to step 4.



### 0. Setup the HDK and install AWS CLI

When using the developer AMI:  ```AWS_FPGA_REPO_DIR=/home/centos/src/project_data/aws-fpga```
    
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source hdk_setup.sh

To install the AWS CLI, please follow the instructions here: (http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and default region

Use the aws-cli [region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) command line argument to override the profile default region.  Supported regions include: us-east-1, us-west-2, eu-west-1 and us-gov-west-1.

### 1. Pick one of the examples and move to its directory

There are couple of ways to start a new CL: one option is to copy one of the examples provided in the HDK and modify the design files, scripts and constrains directory.

Alternatively, by creating a new directory, setup the environment variables, and prepare the project datastructure:

    $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to any other example
    $ export CL_DIR=$(pwd)

Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the [How to create your own CL](../developer_designs/Starting_Your_Own_CL.md) readme.

### 2. Build the CL

**NOTE** *This step requires you to have Xilinx Vivado Tools and Licenses installed*

    $ vivado -mode batch        # Verify Vivado is installed.

Executing the `aws_build_dcp_from_cl.sh` script will perform the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA.
The output is a tarball file comprising the DCP file, and other log/manifest files, formatted as `YY_MM_DD-hhmm.Developer_CL.tar`.
This file would be submitted to AWS to create an AFI. By default the build script will use Clock Group A Recipe A0 wich uses a main clock of 125 MHz.

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.sh

In order to use a 250 MHz main clock the developer can specify the A1 Clock Group A Recipe as in the following example:

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.sh -clock_recipe_a A1

Other clock recipes can be specified as well. More details on the [Clock Group Recipes Table](../../docs/clock_recipes.csv) and how to specify different recipes can be found in the following [README](../../common/shell_v071417d3/new_cl_template/build/README.md).

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


### 3. Submit the Design Checkpoint to AWS to Create the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tarball file into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. Location of the tarball file object in S3.
4. Location of an S3 directory where AWS would write back logs of the AFI creation.
5. AWS region where the AFI will be created.  Use [copy-fpga-image](../../docs/copy_fpga_image.md) API to copy an AFI to a different region.

To upload your tarball file to S3, you can use any of [the tools supported by S3](http://docs.aws.amazon.com/AmazonS3/latest/dev/UploadingObjects.html)).
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

The [describe-fpga-images](../../docs/describe_fpga_images.md) API allows you to check the AFI state during the background AFI generation process.
You must provide the **FPGA Image Identifier** returned by `create-fpga-image`:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-06d0ffc989feeea2a
```

You can use the [wait_for_afi.py](../../docs/wait_for_afi.md) script to wait for the AFI creation to complete and then optionally
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

After the AFI generation is complete, AWS will put the logs into the bucket location (```s3://<bucket-name>/<logs-folder-name>```) provided by the developer. The presence of these logs is an indication that the creation process is complete. Please look for either a “State” file indicating the state of the AFI (e.g., available or failed), or the Vivado logs detailing errors encountered during the creation process.  For help with AFI creation issues, see [create-fpga-image error codes](../../docs/create_fpga_image_error_codes.md)

**NOTE**: *Attempting to load the AFI immediately on an instance will result in an `Invalid AFI ID` error.
Please wait until you confirm the AFI is created successfully.*

**NOTE**: *Attempting to load the AFI in a region different from where the AFI was created will result in an `Invalid AFI ID` error.  AFIs need to be copied to regions.*
The [copy-fpga-image](../../docs/copy_fpga_image.md) API allows you to copy the AFI to other regions and avoid the time consuming `create-fpga-image` process. Copy will also preserve the source Global AFI ID and minimize region-specific changes to your instance code or scripts.

## Step by step guide how to load and test a registered AFI from within an F1 instance

To follow the next steps, you have to launch an F1 instance.
AWS recommends that you launch an instance with latest Amazon Linux that has the FPGA Management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

### 4. Setup AWS FPGA Management tools

The FPGA Management tools are required to load an AFI onto an FPGA.  Depending on your AMI used to run the F1 instance, these steps may have been completed already.
```
    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source sdk_setup.sh
```
To install the AWS CLI, please follow the instructions here: (http://docs.aws.amazon.com/cli/latest/userguide/installing.html).
```
    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and instance region (us-east-1, us-west-2, eu-west-1 or us-gov-west-1)
```
  
### 5. Load the AFI

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

If the describe returns a status 'Busy', the FPGA is still performing the previous operation in the background. Please wait until the status is 'Cleared' as above.

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
    

### 6. Validating using the CL Example Software

Each CL Example comes with a runtime software under `$CL_DIR/software/runtime/` subdirectory. You will need to build the runtime application that matches your loaded AFI.   

```
    $ cd $CL_DIR/software/runtime/
    $ make all
    $ sudo ./test_hello_world
```

For additional information, see the README.md located in the $CL_DIR/README.md
