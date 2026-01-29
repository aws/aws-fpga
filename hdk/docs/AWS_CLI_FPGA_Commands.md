# AWS CLI FPGA Commands

To install the AWS CLI, please follow the [instructions here](http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

The AWS CLI FPGA commands allow you to manage your Amazon FPGA Images.

## `copy-fpga-image`

Use `aws ec2 copy-fpga-image` to copy AFIs between AWS regions.  The copy operation will use the target [EC2 endpoint](http://docs.aws.amazon.com/general/latest/gr/rande.html#ec2_region) as the destination region
(this is the aws-cli default region or specified by the [region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) argument).  The source region must be specified using `--source-region` argument.

Copy will assign the destination AFI a new AFI ID specific to that region, but will preserve the source Global AFI ID.  EC2 instances can use the same Global AFI ID on every region.

To allow copies, the source AFI must meet the following requirements:
* AFI must be owned by caller.  Access to an AFI does not grant sufficient permissions to copy it.
* AFI must be in `available` state.  Copy is not allowed if source AFI is in `pending`, `failed` or `unavailable` states.

### Example usage

* Show command manual page:
```
    $ aws ec2 copy-fpga-image help
```

* Copy AFI from same region (source: us-east-1, destination:us-east-1):
```
    $ aws ec2 copy-fpga-image --region us-east-1 --source-region us-east-1 --source-fpga-image-id afi-01a7ea9bafe3ef8cc
    {
        "FpgaImageId": "afi-0ccd812687c77c5b8"
    }
```

* Use `describe-fpga-images` with the response AFI ID to check copied AFI state:
```
    $ aws ec2 describe-fpga-images --region us-east-1 --fpga-image-ids afi-0ccd812687c77c5b8
    {
        "FpgaImages": [
            {
                "OwnerAlias": "amazon",
                "UpdateTime": "2017-07-26T19:09:24.000Z",
                "Name": "hello_world_1.3.0",
                "PciId": {
                    "SubsystemVendorId": "0xfedd",
                    "VendorId": "0x1d0f",
                    "DeviceId": "0xf000",
                    "SubsystemId": "0x1d51"
                },
                "FpgaImageGlobalId": "agfi-088bffb3ab91ca2d1",
                "State": {
                   "Code": "available"
                },
                "ShellVersion": "0x071417d3",
                "OwnerId": "095707098027",
                "FpgaImageId": "afi-0ccd812687c77c5b8",
                "CreateTime": "2017-07-26T18:42:42.000Z",
                "Description": "Hello World AFI"
            }
        ]
    }
```

* Copy AFI from another region (source: us-east-1, destination: us-west-2):
```
    $ aws ec2 copy-fpga-image --region us-west-2 --source-region us-east-1 --source-fpga-image-id afi-01a7ea9bafe3ef8cc
    {
        "FpgaImageId": "afi-0ccd812687c77c5b8"
    }
```

* Cross-region copies may take some time to transfer AFI resources to destination region.  AFI state will be `pending` while copy is in progress:
```
    $ aws ec2 describe-fpga-images --region us-west-2 --fpga-image-ids afi-0ccd812687c77c5b8

    {
        "UpdateTime": "2017-08-24T18:26:40.000Z",
        "Name": "copy",
        "State": {
            "Code": "pending"
        },
        "OwnerId": "095707098027",
        "FpgaImageId": "afi-0ec49a946f276c5f5",
        "CreateTime": "2017-08-24T18:26:40.000Z",
        "Description": "delete"
     }
```

* Cross-region copies cannot be fully validated before `copy-fpga-image` returns.  In case of failure, destination AFI state will include an error message:
```
    $ aws ec2 describe-fpga-images --region us-west-2 --fpga-image-ids afi-0a4a231c9804af6c6
    {
        "FpgaImages": [
            {
                "OwnerId": "095707098027",
                "FpgaImageId": "afi-0a4a231c9804af6c6",
                "State": {
                    "Message": "NOT_FOUND: Source image is not found or the user ID is not authorized to copy source image.",
                    "Code": "failed"
                },
                "CreateTime": "2017-08-24T21:18:56.000Z",
                "UpdateTime": "2017-08-24T21:19:00.000Z"
            }
        ]
    }

    $ aws ec2 describe-fpga-images --region us-west-2 --fpga-image-ids afi-0a4a231c9804af6c6
    {
        "FpgaImages": [
            {
                "OwnerId": "095707098027",
                "FpgaImageId": "afi-0a4a231c9804af6c6",
                "State": {
                    "Message": "INVALID_STATE: Source image is not in a suitable state to allow copying.",
                    "Code": "failed"
                },
                "CreateTime": "2017-08-24T21:18:56.000Z",
                "UpdateTime": "2017-08-24T21:19:00.000Z"
            }
        ]
    }
```

## `create-fpga-image`

An AFI is created using an AWS API called `aws ec2 create-fpga-image`. When calling the API, the developer passes a pointer to an S3 bucket which contains a tar file.  The tar file includes the encrypted and compiled fpga image(a.k.a. Design Checkpoint or DCP) and a mandatory `manifest.txt` file.

### Example Usage

* Show command manual page:
```
    $ aws ec2 create-fpga-image help
```

* AFI creation may take some time to transfer AFI resources to the destination region. AFI state will be `pending` while copy is in progress:
```
    $ aws ec2 create-fpga-image \
        --name <afi-name> \
        --description <afi-description> \
        --input-storage-location Bucket=<dcp-bucket-name>,Key=<path-to-tarball> \
        --logs-storage-location Bucket=<logs-bucket-name>,Key=<path-to-logs> \
	[ --client-token <value> ] \
	[ --dry-run | --no-dry-run ]
    {
        "FpgaImages": [
            {
                "FpgaImageId": "afi-<afi-id>",
                "FpgaImageGlobalId": "agfi-<agfi-id>",
                "Name": "<afi-name>",
                "Description": "<afi-description>",
                ...
                "State": {
                    "Code": "pending"
                },
                ...
            }
        ]
    }
```

Errors can occur when calling this API and this document provides the specification for the error codes.

<a id="error-codes"></a>
#### Error Codes

* `INACCESSIBLE_INPUT`
      *Error accessing resource in S3. Check permissions, naming, and ensure the bucket is within the same region as the API endpoint.*

* `INPUT_SIZE_ILLEGAL`
      *Input file size is not valid*

* `DCP_INTEGRITY_UNVERIFIED`
      *The DCP integrity SHA-256 hash does not match the provided DCP*

* `MANIFEST_NOT_FOUND`
      *No manifest file was found. See AWS FPGA HDK documentation for valid input format. We recommend using the scripts provided with AWS FPGA HDK*

* `MANIFEST_PARSE_FAILED`
      *Parsing the manifest file failed. We recommend using the scripts provided with AWS FPGA HDK*

* `SHELL_VERSION_INVALID`
      *The Shell Version provided is invalid*

* `SHELL_VERSION_DEPRECATED`
      *The Shell Version provided is deprecated*

* `PCIID_SYNTAX_INVALID`
      *PCI ID is not provided, wrongly formatted, or value is out of range valid range 1-65535 or 0x0001-0xFFFF*

* `PCIID_FORBIDDEN`
      *PCI ID value used is reserved. See AWS FPGA HDK documentation for reserved PCI*

* `CLK_ILLEGAL`
      *Provided clocks configuration is illegal. See AWS FPGA HDK documentation for supported clocks configuration*

* `CORRUPT_ARCHIVE`
      *Failed to parse the input tarball archive*

* `DCP_NOT_FOUND`
      *No DCP file was found with the supplied filename. See AWS FPGA HDK documentation for valid input format. We recommend using the scripts provided with AWS FPGA HDK*

* `UNSUPPORTED_DESIGN_LOGIC`
    *The FPGA image bitstream generation failed during design rule validation. If an S3 LogsStorageLocation was provided in the CreateFpgaImage request, review the captured bitstream generation logs saved to S3 under the FpgaImageId for this AFI. Examples of failures include:*

    *1. The design validation detected unsupported primitives in the customer logic. Certain FPGA primitives are restricted to maintain platform stability and ensure reliable operation of customer workloads. The following primitives are not supported: DNA_PORT, FRAME_ECC, MCAP, ICAP_TOP, ICAP_BOT, MASTER_JTAG, DCIRESET, EFUSE_USR, USR_ACCESS, STARTUP, BSCAN1, BSCAN2, BSCAN3, BSCAN4, SYSMON.* ***NOTE: This implementation follows the [design advisory issued by AMD](https://docs.amd.com/r/en-US/000038693). Refer to it for detailed information.***

    *2. We found a combinatorial loop in the CL design. Bitstream generation logs might show errors like ERROR: [DRC LUTLP-1] Combinatorial Loop Alert: 2 LUT cells form a combinatorial loop. Combinatorial loops are not allowed in CL designs and AFIs are not generated in such cases.*

* `UNKNOWN_BITSTREAM_GENERATE_ERROR`
      *An unclassified error occurred generating the FPGA image bitstream. If an S3 LogsStorageLocation was provided in the CreateFpgaImage request, review the captured bitstream generation logs saved to S3 under the FpgaImageId for this AFI.*

## `delete-fpga-image`

Use `aws ec2 delete-fpga-image` to delete an AFI.  Delete operations are restricted to the target region determined by the aws-cli default region or
[region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) argument.  Deleting an AFI in one region has no effect on AFIs in other regions.

Delete is not allowed if the AFI is public or shared with other accounts.  Use `describe-fpga-image-attribute` to check if an AFI is shared,
and `reset-fpga-image-attribute` to remove all load permissions.

Deleting an AFI does not affect AFIs already loaded onto FPGAs. Deleting only prevents new attempts to load an AFI onto an FPGA.  Note that, within a region, an AFI will
continue to be loadable as long as its Global AFI ID is available. Use `describe-fpga-images` with `fpga-image-global-id` filter to find AFIs with the same Global AFI ID.

If you want to create a fresh copy of a Global AFI ID in a region, the Global AFI ID must be fully deleted from the region by deleting all AFIs with the same Global AFI ID.
Use `describe-fpga-images` with `fpga-image-global-id` filter to find AFIs with the same Global AFI ID. The Global AFI ID is not fully deleted from a region for 6 hours
after all associated AFI IDs are deleted. Any AFIs copied to the region after the Global AFI ID is fully deleted will result in a fresh copy of the Global AFI ID.

An AFI will not be recoverable after deleting all copies in all regions.  Use [IAM Policies for Amazon EC2](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/iam-policies-for-amazon-ec2.html)
to restrict access to the API unless explicitly required (See [IAM best practices](http://docs.aws.amazon.com/IAM/latest/UserGuide/best-practices.html#grant-least-privilege)).
For example, include the following statement in your IAM policy to deny access to `DeleteFpgaImage`:

```
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Action": [
        "ec2:DeleteFpgaImage"
      ],
      "Effect": "Deny",
      "Resource": "*"
    }
  ]
}
```

### Example usage

* Show command manual page:
```
    $ aws ec2 delete-fpga-image help
```

* Delete AFI:
```
    $ aws ec2 --region us-east-1 delete-fpga-image --fpga-image-id afi-0e5361a69d2af203d
    {
        "Return": true
    }
```

### Common Error Messages

* Describe an AFI after delete:
```
    $ aws ec2 --region us-east-1 describe-fpga-images --fpga-image-ids afi-0e5361a69d2af203d

    An error occurred (InvalidFpgaImageID.NotFound) when calling the DescribeFpgaImages operation: Image ID 'afi-0e5361a69d2af203d' not found.
```

* Delete shared AFI
```
    $ aws ec2 --region us-east-1 delete-fpga-image --fpga-image-id afi-0e5361a69d2af203d

    An error occurred (OperationNotPermitted) when calling the DeleteFpgaImage operation: Operation not permitted for shared AFI
```

* Delete public AFI
```
    $ aws ec2 --region us-east-1 delete-fpga-image --fpga-image-id afi-0e5361a69d2af203d

    An error occurred (OperationNotPermitted) when calling the DeleteFpgaImage operation: Operation not permitted for public AFI
```

## `describe-fpga-images`

Use `aws ec2 describe-fpga-images` API to get information about all AFIs available to your AWS account.  The set of AFIs returned by `describe-fpga-images` includes:

* AFIs owned by your AWS account.
* AFIs owned by other AWS accounts for which you have been granted load permissions.
* Public AFIs.

The API provides various filters to get information about specific AFIs.  Invoke `aws ec2 describe-fpga-images help` to get an up-to-date list of available filters.  See **Example usage** section in this document for common filters.

AFI information is accessible using `describe-fpga-images` immediately after `create-fpga-image` returns with a valid `afiId`.  The information provided by `describe-fpga-images` includes AFI states to check the result of the bitstream generation process:

* `pending` AFI bitstream generation is in progress.
* `available` AFI is available for use by F2 instances.
* `failed` AFI bitstream generation failed.  The `State.Message` field provides the specific error code as described in [Error Codes](#error-codes).
* `unavailable` AFI is no longer available for use by F2 instances.


### Example response

The following response shows the AFI information provided by `describe-fpga-images`.  The AFIs shown in this case are the public AFIs generated from the example CLs in the HDK.

```
    {
        "FpgaImages": [
            {
                "OwnerAlias": "amazon",
                "UpdateTime": "2017-04-19T17:15:26.000Z",
                "Name": "cl_hellow_world_04151701",
                "PciId": {
                    "SubsystemVendorId": "0xfedd",
                    "VendorId": "0x1d0f",
                    "DeviceId": "0xf000",
                    "SubsystemId": "0x1d51"
                },
                "FpgaImageGlobalId": "agfi-0f0e045f919413242",
                "State": {
                    "Code": "available"
                },
                "ShellVersion": "0x04151701",
                "OwnerId": "095707098027",
                "FpgaImageId": "afi-0f0927bc2649e6259",
                "CreateTime": "2017-04-19T17:15:25.000Z",
                "Description": "cl_hello_world for shell 0x04151701"
            },
            {
                "OwnerAlias": "amazon",
                "UpdateTime": "2017-04-17T15:58:54.000Z",
                "Name": "cl_dram_dma_0415",
                "PciId": {
                    "SubsystemVendorId": "0xfedc",
                    "VendorId": "0x1d0f",
                    "DeviceId": "0xf001",
                    "SubsystemId": "0x1d51"
                },
                "FpgaImageGlobalId": "agfi-0d873e8b409f8e806",
                "State": {
                    "Code": "available"
                },
                "ShellVersion": "0x04151701",
                "OwnerId": "095707098027",
                "FpgaImageId": "afi-06d0ffc989feeea2a",
                "CreateTime": "2017-04-17T15:58:54.000Z",
                "Description": "cl_dram_dma_0415"
            }
        ]
    }
```

### Example usage

* Get all AFIs accessible to caller AWS account:
```
    $ aws ec2 describe-fpga-images
```

* Get AFI using a specific AFI ID:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-06d0ffc989feeea2a
```

* Get multiple AFIs by AFI IDs:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-06d0ffc989feeea2a afi-0f0927bc2649e6259
```

* Get AFIs owned by caller AWS account (i.e., exclude public AFIs and AFIs with load permissions):
```
    $ aws ec2 describe-fpga-images --owners self
```

* Get public AFIs owned by Amazon (this is the command used to retrieve the example response):
```
    $ aws ec2 describe-fpga-images --owners amazon
```

* Get AFIs owned by [AWS Marketplace](https://aws.amazon.com/marketplace):
```
    $ aws ec2 describe-fpga-images --owners aws-marketplace
```

* Get AFIs using explicit AWS account ID:
```
    $ aws ec2 describe-fpga-images --owners 095707098027
```

#### Use filters parameter

* Get AFIs using various filters:
```
    # Get AFIs by name
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=cl_dram_dma_0415"

    # Get AFIs in 'available' state
    $ aws ec2 describe-fpga-images --filters "Name=state,Values=available"

    # Get AFIs with shell version 0x04151701
    $ aws ec2 describe-fpga-images --filters "Name=shell-version,Values=0x04151701"

    # Get AFIs created at a specific time
    $ aws ec2 describe-fpga-images --filters "Name=create-time,Values=2017-04-17T15:58:54.000Z"
```

* Get AFIs using EC2 tagging filters (manage EC2 tags using
[create-tags](https://docs.aws.amazon.com/cli/latest/reference/ec2/create-tags.html),
[describe-tags](https://docs.aws.amazon.com/cli/latest/reference/ec2/describe-tags.html)
and [delete-tags](https://docs.aws.amazon.com/cli/latest/reference/ec2/delete-tags.html)):
```
    # Create a tag with key="key_1" and value="value_1"
    $ aws ec2 create-tags --resources afi-06d0ffc989feeea2a --tags Key=key_1,Value=value_1

    # Get all AFIs with tags
    $ aws ec2 describe-tags --filters "Name=resource-type,Values=fpga-image"

    # Get the tags for a specific AFI ID
    $ aws ec2 describe-tags --filters "Name=resource-id,Values=afi-06d0ffc989feeea2a"

    # Get AFIs with a tag key "key_1"
    $ aws ec2 describe-fpga-images --filters "Name=tag-key,Values=key_1"

    # Get AFIs with a tag value "value_1"
    $ aws ec2 describe-fpga-images --filters "Name=tag-value,Values=value"

    # Get AFIs with a tag key/value pair "key_1/value_1"
    $ aws ec2 describe-fpga-images --filters "Name=tag:key_1,Values=value_1"
```

* Get AFIs using wildcard filters (wildcards only usable in `filters` parameter):
```
    # Get AFIs created on 2017-04-17
    $ aws ec2 describe-fpga-images --filters "Name=create-time,Values=2017-04-17*"

    # Get AFIs if name starts with 'cl_'
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=cl_*"

    # Get AFIs with multiple wildcards
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=*_world_*"
```

#### Combine filters to find groups of AFIs

* Get all failed AFIs owned by caller AWS account:
```
    $ aws ec2 describe-fpga-images --owners self --filters "Name=state,Values=failed"
```

* Multiple filter values are evaluated as `OR` conditions:
```
    # Get both example AFIs by name
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=cl_dram_dma_0415,cl_hellow_world_04151701"

    # Get AFIs created on 2017-04-17 or 2017-04-19
    $ aws ec2 describe-fpga-images --filters "Name=create-time,Values=2017-04-17*,2017-04-19*"
```

* Multiple filters are evaluated as `AND` conditions:
```
    # Get AFIs by name AND created on 2017-04-17
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=cl_dram_dma_0415,cl_hellow_world_04151701" "Name=create-time,Values=2017-04-17*"

    # Same filter can be use multiple times, which can return an empty set
    $ aws ec2 describe-fpga-images --filters "Name=name,Values=cl_dram_dma_0415" "Name=name,Values=cl_hellow_world_04151701"
```

### Control command output

* Use the standard aws-cli `query` and `output` parameters to change the response format and displayed fields:
```
    $ aws ec2 describe-fpga-images --query 'FpgaImages[*].[FpgaImageGlobalId,UpdateTime,ShellVersion,State.Code,Name]' --output text --owners amazon
    agfi-02948a33d1a0e9665	2017-07-26T19:18:41.000Z	0x071417d3	available	dram_dma_1.3.0
    agfi-088bffb3ab91ca2d1	2017-07-26T19:09:24.000Z	0x071417d3	available	hello_world_1.3.0
    agfi-0f0e045f919413242	2017-04-19T17:15:26.000Z	0x04151701	available	cl_hellow_world_04151701
    agfi-0d873e8b409f8e806	2017-04-17T15:58:54.000Z	0x04151701	available	cl_dram_dma_0415
```

Find details on all available formatting options in [Controlling Command Output from the AWS Command Line Interface](http://docs.aws.amazon.com/cli/latest/userguide/controlling-output.html).

### Common Error Messages


* Invalid owner ID or filter alias:
```
    $ aws ec2 describe-fpga-images --owners 12345

    An error occurred (InvalidUserID.Malformed) when calling the DescribeFpgaImages operation: User ID '12345' is invalid
```

* Invalid AFI ID:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-06d0ffc989feeeXXX

    An error occurred (InvalidFpgaImageID.Malformed) when calling the DescribeFpgaImages operation: Image ID 'afi-06d0ffc989feeeXXX' is invalid
```

* AFI ID not found:
```
    $ aws ec2 describe-fpga-images --fpga-image-ids afi-03d027a3318440a77

    An error occurred (InvalidFpgaImageID.NotFound) when calling the DescribeFpgaImages operation: Image ID 'afi-03d027a3318440a77' not found
```

* Invalid filter name:
```
    $ aws ec2 describe-fpga-images --filters "Name=bad-filter,Values=value"

    An error occurred (InvalidParameterValue) when calling the DescribeFpgaImages operation: The filter 'bad-filter' is invalid
```

## `describe-fpga-image-attribute, modify-fpga-image-attribute and reset-fpga-image-attribute`

AWS provides the following EC2 operations to manage AFI attributes:
* `aws ec2 describe-fpga-image-attribute`: get AFI `name`, `description` and `loadPermission` attributes.
* `aws ec2 modify-fpga-image-attribute`: update AFI `name`, `description` and `loadPermission` attributes.
* `aws ec2 reset-fpga-image-attribute`: reset `loadPermission` attribute.

Supported AFI attributes include:
* `name`: user-defined AFI name
* `description`: user-defined AFI description
* `loadPermission`: user IDs and groups allowed to load the AFI.  Use `modify-fpga-image-attribute` and this attribute to control who can load your AFI:
  * User ID load permissions allow sharing AFIs to specific AWS accounts
  * Group load permissions only support `all` to make the AFI public or private

Load permissions can be updated only if the AFI is `available`.  Removing or resetting load permissions do not affect loaded AFIs, only prevents users with revoked permission from re-loading the AFI.

**NOTE**: AWS API documentation includes `productCodes` as a supported Fpga image attribute.  At this time, product codes are only available
for AWS marketplace use and not discussed in this documentation.

### Example usage

* Show command manual page:
```
    $ aws ec2 describe-fpga-image-attribute help
    $ aws ec2 modify-fpga-image-attribute help
    $ aws ec2 reset-fpga-image-attribute help
```

* Describe *name* attribute:
```
    $ aws ec2 --region us-east-1 describe-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --attribute name
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "Name": "cl_dram_dma.17_07_21-234442"
        }
    }
```

* Describe *description* attribute:
```
    $ aws ec2 --region us-east-1 describe-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --attribute description
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "Description": "cl_dram_dma example"
        }
    }
```

* Describe *load permissions* attribute:
```
    $ aws ec2 --region us-east-1 describe-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --attribute loadPermission
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "LoadPermissions": []
        }
    }
```

* Change AFI *name* attribute:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --name "new fpga image name"
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "Name": "new fpga image name"
        }
    }
```

* Change AFI *description* attribute:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --description "new fpga image description"
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "Description": "new fpga image description"
        }
    }
```

* Add user ID (AWS account) load permission:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --operation-type add --user-ids 095707098027
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "LoadPermissions": [
               {
                   "UserId": "095707098027"
               }
            ]
        }
    }
```

* Remove user ID (AWS account) load permission:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --operation-type remove --user-ids 095707098027
    {
        "FpgaImageAttribute": {
           "FpgaImageId": "afi-0e5361a69d2af203d",
           "LoadPermissions": []
        }
    }
```


* Make AFI public:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --operation-type add --user-groups all
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "LoadPermissions": [
                {
                    "Group": "all"
                }
            ]
        }
    }
```

* Make AFI private:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --operation-type remove --user-groups all
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0e5361a69d2af203d",
            "LoadPermissions": []
        }
    }
```

* Add load permission for multiple user IDs:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --operation-type add --user-ids 095707098027 951708639280
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0f42ec0869372c806",
            "LoadPermissions": [
                {
                    "UserId": "095707098027"
                },
                {
                    "UserId": "951708639280"
                }
            ]
        }
    }
```

* Update (add/remove) load permissions using `Shorthand Syntax`:
```
    $ aws ec2 --region us-east-1 modify-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --load-permission 'Add=[{UserId=524807397729}],Remove=[{UserId=095707098027},{UserId=951708639280}]'
    {
        "FpgaImageAttribute": {
            "FpgaImageId": "afi-0f42ec0869372c806",
            "LoadPermissions": [
                {
                    "UserId": "524807397729"
                }
            ]
        }
    }
```

* Reset all load permissions:
```
    $ aws ec2 --region us-east-1  reset-fpga-image-attribute --fpga-image-id afi-0e5361a69d2af203d --attribute loadPermission
    {
        "Return": true
    }
```
