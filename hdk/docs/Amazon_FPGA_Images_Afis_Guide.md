# Amazon FPGA Images (AFIs) Guide

## Overview

Amazon FPGA Images (AFIs) are the compiled and encrypted FPGA designs that can be loaded onto AWS FPGA instances (F2). This guide explains how to create, manage, and understand AFIs in the AWS ecosystem.

## What are AFIs and AGFIs?

When you create an AFI, AWS provides two important identifiers:

| Identifier | Scope | Usage | Example |
|------------|-------|-------|---------|
| **AFI ID** (`FpgaImageId`) | Regional | Managing AFIs via AWS EC2 CLI/SDK APIs | `afi-06d0ffc989feeea2a` |
| **AGFI ID** (`FpgaImageGlobalId`) | Global | Loading AFIs onto FPGA slots from within instances | `agfi-0f0e045f919413242` |

### Amazon FPGA Image (AFI)

An AFI is a compiled, encrypted, and signed FPGA design that can be loaded onto AWS FPGA instances. AFIs are created from Design Checkpoint (DCP) files generated during the FPGA development process. An AFI ID is a regional identifier that changes when an AFI is copied across regions.

### Amazon Global FPGA Image ID (AGFI)

The AGFI is a **globally unique identifier** that references a specific AFI across all AWS regions enabling seamless AFI/AMI combinations. It's used by FPGA management tools within EC2 instances to load or manage AFIs on FPGA slots.

## AFI Creation Methods

### Prerequisites

- Design Checkpoint (DCP) tarball file
- Required AWS permissions

### Option 1: Programmatic AFI Creation (Recommended)

The AWS FPGA HDK provides a Python script for streamlined AFI creation once a DCP is generated. Developers can call [create_afi.py](../scripts/create_afi.py) (with required Python modules included in [start_venv.sh](../scripts/start_venv.sh)) without any arguments to interactively input their AFI parameters:

```bash
source $AWS_FPGA_REPO_DIR/hdk/scripts/start_venv.sh
$AWS_FPGA_REPO_DIR/hdk/scripts/create_afi.py
```

Alternatively, developers can read more in the help menu on how to pass all parameters in together:

```bash
$AWS_FPGA_REPO_DIR/hdk/scripts/create_afi.py --help
```

### Option 2: Manual AFI Creation

For more control over the AFI creation process, you can manually submit your DCP file using the AWS CLI tool.

#### Step 1: Prepare Your Environment

Set up your environment variables:

```bash
export DCP_BUCKET_NAME='your-dcp-bucket-name'
export DCP_FOLDER_NAME='your-dcp-folder'
export LOGS_BUCKET_NAME='your-logs-bucket-name'
export LOGS_FOLDER_NAME='your-logs-folder'
export REGION='aws-region-code-eg-us-east-1'
export DCP_TARBALL_TO_INGEST='path/to/your/YYYY_MM_DD-HHMMSS.Developer_CL.tar'
```

**Note**: Confirm your region supports FPGA images by checking the [Amazon EC2 instance types by Region index](https://docs.aws.amazon.com/ec2/latest/instancetypes/ec2-instance-regions.html)

#### Step 2: Create S3 Storage

Create S3 buckets and upload your DCP file:

```bash
# Create S3 bucket for DCP files
aws s3 mb s3://${DCP_BUCKET_NAME} --region ${REGION}

# Create folder for DCP files
aws s3 mb s3://${DCP_BUCKET_NAME}/${DCP_FOLDER_NAME}/

# Upload DCP tarball to S3
aws s3 cp ${DCP_TARBALL_TO_INGEST} s3://${DCP_BUCKET_NAME}/${DCP_FOLDER_NAME}/
```

Create storage for AFI creation logs:

```bash
# Create folder for logs
aws s3 mb s3://${LOGS_BUCKET_NAME}/${LOGS_FOLDER_NAME}/ --region ${REGION}

# Create placeholder file to establish the folder structure
touch LOGS_FILES_GO_HERE.txt
aws s3 cp LOGS_FILES_GO_HERE.txt s3://${LOGS_BUCKET_NAME}/${LOGS_FOLDER_NAME}/
```

**Important**: The trailing `/` is required after folder names in S3 paths.

#### Step 3: Submit AFI Creation Request

```bash
export DCP_TARBALL_NAME=$(basename ${DCP_TARBALL_TO_INGEST})
export CL_DESIGN_NAME='your-design-name'
export CL_DESIGN_DESCRIPTION="Description of your FPGA design"

# Submit AFI creation request
aws ec2 create-fpga-image \
    --name ${CL_DESIGN_NAME} \
    --description "${CL_DESIGN_DESCRIPTION}" \
    --input-storage-location Bucket=${DCP_BUCKET_NAME},Key=${DCP_FOLDER_NAME}/${DCP_TARBALL_NAME} \
    --logs-storage-location Bucket=${LOGS_BUCKET_NAME},Key=${LOGS_FOLDER_NAME}/ \
    --region ${REGION}

# expected response format:
{
    "FpgaImageId": "afi-09953582f46c45b17",
    "FpgaImageGlobalId": "agfi-0925b211f5a81b071"
}
```

The [create-fpga-images API](https://docs.aws.amazon.com/cli/latest/reference/ec2/create-fpga-image.html#output) or [AWS CLI FPGA Commands](./AWS_CLI_FPGA_Commands.md) documentation can be used to interpret your results.

## Monitoring AFI Creation

### Check AFI Status

Use the AFI ID returned by the `create-fpga-image` command to monitor the creation progress:

```bash
aws ec2 describe-fpga-images --fpga-image-ids afi-09953582f46c45b17 --region ${REGION}
```

The [describe-fpga-images API](https://docs.aws.amazon.com/cli/latest/reference/ec2/describe-fpga-images.html#output) or [AWS CLI FPGA Commands](./AWS_CLI_FPGA_Commands.md) documentation can be used to interpret your results.

## Using AFIs in FPGA Instances

Once your AFI is `available`, you can load it onto FPGA slots within F2 instances using the **AGFI ID**:

```bash
# Load AFI onto FPGA slot 0
sudo fpga-load-local-image -S 0 -I agfi-0925b211f5a81b071

# Verify AFI is loaded
sudo fpga-describe-local-image -S 0
```

## Troubleshooting

- **AFI creation fails**: Check the logs in your designated S3 logs folder
- **S3 permissions**: Verify your AWS credentials have appropriate S3 and EC2 permissions
- **DCP file format**: Ensure your DCP tarball follows [AWS FPGA HDK requirements](./../README.md#step-4-build-cl-design-check-point-dcp)
- For any issues with the devkit documentation or code, please open a [GitHub issue](https://github.com/aws/aws-fpga/issues) with all steps to reproduce
- For questions about F2 instances, please open a [re:Post issue with the 'FPGA Development' tag](https://repost.aws/tags/TAc7ofO5tbQRO57aX1lBYbjA/fpga-development)
