# Step by step guide on how to create an AFI from one of the CL examples

As a pre-requisite to building the AFI, the developer should have an instance/server with Xilinx Vivado Tools and the necessary Licenses. The "FPGA Developer AMI" provided free of charge on AWS Marketplace will be an ideal place to start an instance from. See the README.md on the AMI for the details how to launch the FPGA Developer's AMI, install the tools and set up the license.

**NOTE:** *Steps 1 through 3 can be done on any server or EC2 instance. C4/C5 instances are recommended for fastest build time.*

**NOTE:** *You can skip steps 0 through 3 if you are not interested in the build process.  Step 4 through 6 will show you how to use one of the predesigned AFI examples.*

### 0. Setup the HDK and install AWS CLI

    $ git clone https://github.com/aws/aws-fpga.git $AWS_FPGA_REPO_DIR
    $ cd $AWS_FPGA_REPO_DIR
    $ source hdk_setup.sh

To install the AWS CLI, please follow the instructions here: (http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and region (typically us-east-1)

During the F1 preview, not all FPGA-specific AWS CLI commands are available to the public.
To extend your AWS CLI installation, please execute the following:

    $ aws configure add-model --service-model file://$AWS_FPGA_REPO_DIR/sdk/aws-cli-preview/ec2_preview_model.json

**NOTE**: *The EC2 extension JSON file has been updated to enable support for the `create-fpga-image` command used in [Step 3](https://github.com/aws/aws-fpga/tree/master/hdk/cl/examples#3-submit-the-design-checkpoint-to-aws-to-register-the-afi).*

### 1. Pick one of the examples and move to its directory

There are couple of ways to start a new CL: one option is to copy one of the examples provided in the HDK and modify the design files, scripts and constrains directory.

Alternatively, by creating a new directory, setup the environment variables, and prepare the project datastructure:

    $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to any other example
    $ export CL_DIR=$(pwd)

Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the [How to create your own CL](../developer_designs/README.md) readme.

### 2. Build the CL

**NOTE** *This step requires you to have Xilinx Vivado Tools and Licenses installed*

    $ vivado -mode batch        # Verify Vivado is installed.

Executing the `aws_build_dcp_from_cl.sh` script will perform the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA.
The output is a tarball file comprising the DCP file, and other log/manifest files, formatted as `YY_MM_DD-hhmm.Developer_CL.tar`.
This file would be submitted to AWS to create an AFI.

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.sh

**NOTE**: *The DCP generation can take up to several hours to complete.
We recommend that you initiate the generation in a way that prevents interruption.
For example, if working on a remote machine, we recommend using window management tools such as [`screen`](https://www.gnu.org/software/screen/manual/screen.html) to mitigate potential network disconnects.*


### 3. Submit the Design Checkpoint to AWS to Register the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tarball file into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. Location of the tarball file object in S3.
4. Location of an S3 directory where AWS would write back logs of the AFI creation.

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

You can verify that the bucket policy grants the required permissions by running the following script:

    $ check_s3_bucket_policy.py \
	--dcp-bucket <dcp-bucket-name> \
	--dcp-key <path-to-tarball> \
	--logs-bucket <logs-bucket-name> \
	--logs-key <path-to-logs-folder>

To create an AFI execute the following command:

    $ aws ec2 create-fpga-image \
        --name <afi-name> \
        --description <afi-description> \
        --input-storage-location Bucket=<dcp-bucket-name>,Key=<path-to-tarball> \
        --logs-storage-location Bucket=<logs-bucket-name>,Key=<path-to-logs> \
	[ --client-token <value> ] \
	[ --dry-run | --no-dry-run ]

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

**NOTE**: *Attempting to load the AFI immediately on an instance will result in an `Invalid AFI ID` error.
Please wait until you receive a confirmation email from AWS indicating the creation process is complete.*

# Step by step guide how to load and test a registered AFI from within an F1 instance

To follow the next steps, you have to launch an F1 instance.
AWS recommends that you launch an instance with latest Amazon Linux that has the FPGA Management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

## 4. Setup AWS FPGA Management tools

The FPGA Management tools are required to load an AFI onto an FPGA.
To install these tools, execute the following:

    $ git clone https://github.com/aws/aws-fpga     # Not needed if you have installed the HDK as in Step 0.
    $ cd aws-fpga
    $ source sdk_setup.sh

## 5. Load the AFI

You can now use the FPGA Management tools, from within your F1 instance, to load your AFI onto an FPGA on a specific slot.
You can also invoke the `fpga-describe-local-image` command to learn about which AFI, if any, is loaded onto a particular slot.
For example, if the slot is cleared (`slot 0` in this example), you should get an output similar to the following:

    $ sudo fpga-describe-local-image -S 0 -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       none                    cleared           1        ok               0       <shell_version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:0f.0

Now, let us try loading your AFI to FPGA `slot 0`:

    $ sudo fpga-load-local-image -S 0 -I agfi-0123456789abcdefg

**NOTE**: *The FPGA Management tools use the AGFI ID (not the AFI ID).*

Now, you can verify that the AFI was loaded properly.  The output shows the FPGA in the “loaded” state after the FPGA image "load" operation.  The "-R" option performs a PCI device remove and recan in order to expose the unique AFI Vendor and Device Id.

    $ sudo fpga-describe-local-image -S 0 -R -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
    AFI          0       agfi-0123456789abcdefg  loaded            0        ok               0       <shell version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x6789      0x1d50      0000:00:0f.0

## 6. Validating using the CL Example Software

Please refer to the README.md included with each example.
