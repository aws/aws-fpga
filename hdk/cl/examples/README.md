# Overview on process for building a Custom Logic (CL) implementation for AWS FPGA instances

The developer can build their own Custom Logic (CL) and deploy it on AWS.
The CL must comply with the [AWS Shell specifications](../../docs/AWS_Shell_Interface_Specification.md), and pass through the build scripts.

The [CL Examples directory](https://github.com/aws/aws-fpga/tree/master/hdk/cl/examples) is provided to assist developers in creating a
functional CL implementation. Each example includes:

1. The design source code for the example under the `/design` directory.
2. The timing, clock and placement constraints files, scripts for compiling the example design. (This requires running in an instance/server that have Xilinx tools and license installed. Developers are recommended to use the "FPGA Development AMI" available free of charge on [AWS Marketplace](https://aws.amazon.com/marketplace/).
3. The final build, called Design CheckPoint (DCP) that can be submitted for AWS to generate the AFI.
4. An AFI-ID for a pre-generated AFI that matches the example design.
5. Software source code required on the FPGA-enabled instance to run the example.
6. Software binary that can be loaded on an FPGA-enabled instance to test the AFI.

In summary:

- An AFI can be created using the files in 1, 2, and 3. The AFI creation can take place on any EC2 instance or on premise.
- The AFI can be used in an EC2 F1 instance by using the files in 4, 5 and 6.

By following the example CLs, a developer should learn how to interface to the AWS Shell of the FPGA, compile the source code to create an AFI, and load an AFI from the F1 instance for use.

# Step by step guide on how to create an AFI from one of the CL examples

As a pre-requisite to building the AFI, the developer should have an instance/server with Xilinx Vivado Tools and the necessary Licenses. The "FPGA Developer AMI" provided free of charge on AWS Marketplace will be an ideal place to start an instance from. See the README.md on the AMI for the details how to launch the FPGA Developer's AMI, install the tools and set up the license.

**NOTE:** *Steps 1 through 3 can be done on any server or EC2 instance. C4/C5 instances are recommended for fastest build time.*

**NOTE:** *You can skip steps 0 through 3 if you are not interested in the build process.  Step 4 through 6 will show you how to use one of the predesigned AFI examples.*

### 0. Setup the HDK and install AWS CLI

    $ git clone https://github.com/aws/aws-fpga
    $ cd aws-fpga
    $ source hdk_shell.sh

To install the AWS CLI, please follow the instructions here: (http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and region (typically us-east-1)

During the F1 preview, not all FPGA-specific AWS CLI commands are available to the public.
To extend your AWS CLI installation, please execute the following:

    $ aws configure add-model --service-model file://$(pwd)/sdk/aws-cli-preview/ec2_preview_model.json

**NOTE**: *The EC2 extension JSON file has been updated to enable support for the `create-fpga-image` command used in [Step 3](https://github.com/aws/aws-fpga/tree/master/hdk/cl/examples#3-submit-the-design-checkpoint-to-aws-to-register-the-afi).*

### 1. Pick one of the examples and move to its directory

There are couple of ways to start a new CL: one option is to copy one of the examples provided in the HDK and modify the design files, scripts and constrains directory.

Alternatively, by creating a new directory, setup the environment variables, and prepare the project datastructure:

    $ cd $HDK_DIR/cl/examples/cl_hello_world    # you can change cl_hello_world to any other example
    $ export CL_DIR=$(pwd)

Setting up the CL_DIR environment variable is crucial as the build scripts rely on that value.
Each one of the examples following the recommended directory structure to match what's expected by the HDK simulation and build scripts.

If you like to start your own CL, check out the [How to create your own CL Readme](../developer_designs/README.md).

### 2. Build the CL

**NOTE** *This step requires you to have Xilinx Vivado Tools and Licenses installed*

    $ vivado -mode batch        # Verify Vivado is installed.

Executing the `aws_build_dcp_from_cl.tcl` script will perform the entire implementation process converting the CL design into a completed Design Checkpoint that meets timing and placement constrains of the target FPGA.
The output is a tarball file comprising the DCP file, and other log/manifest files, formatted as `YY_MM_DD-hhmm.Developer_CL.tar`.
This file would be submitted to AWS to create an AFI.

    $ cd $CL_DIR/build/scripts
    $ ./aws_build_dcp_from_cl.tcl

**NOTE**: *The DCP generation can take up to several hours to complete.
We recommend that you initiate the generation in a way that prevents interruption.
For example, if working on a remote machine, we recommend using window management tools such as [`screen`](https://www.gnu.org/software/screen/manual/screen.html) to mitigate potential network disconnects.*


### 3. Submit the Design Checkpoint to AWS to Register the AFI

To submit the DCP, create an S3 bucket for submitting the design and upload the tar-zipped archive into that bucket.
You need to prepare the following information:

1. Name of the logic design *(Optional)*.
2. Generic description of the logic design *(Optional)*.
3. PCI IDs: Device, Vendor, Subsystem, SubsystemVendor.
4. Location of the tarball object in S3.
5. Location of an S3 directory where AWS would write back logs of the AFI creation.
6. Version of the AWS Shell.

**NOTE**: *The PCI IDs for the example CLs should be found in the README files in the respective CL example directory.
If you are building a custom CL, then you need to incorporate these values in your design as shown in the [AWS Shell Interface Specifications](https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#pcie-ids).*

To upload your tarball to S3, you can use any of [the tools supported by S3](http://docs.aws.amazon.com/AmazonS3/latest/dev/UploadingObjects.html)).
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

To create an AFI execute the `create-fpga-image` command as follows:

    $ aws ec2 create-fpga-image \
        --fpga-image-architecture xvu9p \
        --shell-version <shell_version> \
        --fpga-pci-id DeviceId=<device_id>,VendorId=<vendor_id>,SubsystemId=<subsystem_id>,SubsystemVendorId=<subsystem_vendor_id> \
        --input-storage-location Bucket=<bucket-name>,Key=<tarball-name>
        --name <cl-name>
        --description <description>
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


# Step by step guide how to load and test a registered AFI from within an F1 instance

To follow the next steps, you have to launch an instance on F1.
AWS recommends that you launch an instance with latest Amazon Linux that has the FPGA Management tools included, or alternatively the FPGA Developer AMI with both the HDK and SDK.

## 4. Setup AWS FPGA Management tools

The FPGA Management tools are required to load an AFI onto an FPGA.
To install these tools, execute the following:

    $ git clone https://github.com/aws/aws-fpga     # Not needed if you have installed the HDK as in Step 0.
    $ cd aws-fpga
    $ source sdk_setup.sh

## 5. Associate the AFI with your AMI

To start using the AFI, you need to associate it with an [AMI (Amazon Machine Image)](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/AMIs.html) that you own.
Association means that any instance launched using a given AMI will be able to load the AFIs to the FPGAs as described in the next section.

You can associate multiple AFIs with your AMI.
There is a default limit of eight AFIs per AMI. If you need more, please reach out to AWS with your use case and we can adjust your limit.

FPGA Developer AMI's are owned by AWS and you can not associate your AFI with them.
If you are developing using the FPGA Developer AMI's, you will need to simply create a new image of your instance and that will create an AMI of your instance that you own.
You can use any of [the tools supported by EC2 tools to create an AMI](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/creating-an-ami-ebs.html).
For example, you can use the AWS CLI as follows:

    $ aws ec2 create-image --instance-id <Instance ID> --name <My Own Image Name>

This will create a new AMI of the current state of your instance and you would be able to associate an AFI with this AMI.
You would then have to launch an F1 Instance with this new AMI.

To associate an AFI to your AMI, simply invoke the following AWS CLI command:

    $ aws ec2 associate-fpga-image --fpga-image-id <AFI_ID> --image-id <AMI_ID>

**NOTE**: *The AWS CLI commands use the AFI ID (not the AGFI ID).*

## 6. Load the AFI

You can now use the FPGA Management tools, from within your F1 instance, to load your AFI onto an FPGA on a specific slot.
You can also invoke the `fpga-describe-local-image` command to learn about which AFI, if any, is loaded onto a particular slot.
For example, if the slot is cleared (`slot 0` in this example), you should get an output similar to the following:

    $ sudo fpga-describe-local-image -S 0 -H

    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ShVersion
    AFI          0       none                    cleared           1        <shell_version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:17.0

Now, let us try loading your AFI to FPGA `slot 0`:

    $ sudo fpga-load-local-image -S 0 -I <AGFI_ID>

**NOTE**: *The FPGA Management tools use the AGFI ID (not the AFI ID).*

Now, you can verify that the AFI was loaded properly:

    $ sudo fpga-describe-local-image -S 0 -H
    Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ShVersion
    AFI          0       <AGFI_ID>               loaded            0        <shell_version>
    Type  FpgaImageSlot  VendorId    DeviceId    DBDF
    AFIDEVICE    0       0x1d0f      0x1042      0000:00:17.0

## 7. Validating using the CL Example Software

Please refer to the
[Validating CL Designs](https://github.com/aws/aws-fpga/wiki/Validating-CL-Designs#quick-start)
Wiki page for methods to validate that your CL example design functions as expected.
