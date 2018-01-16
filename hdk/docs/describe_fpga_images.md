# AWS EC2 API describe-fpga-images

Use `aws ec2 describe-fpga-images` API to get information about all AFIs available to your AWS account.  The set of AFIs returned by `describe-fpga-images` includes:

* AFIs owned by your AWS account.
* AFIs owned by other AWS accounts for which you have been granted load permissions.
* Public AFIs.

The API provides various filters to get information about specific AFIs.  Invoke `aws ec2 describe-fpga-images help` to get an up-to-date list of available filters.  See **Example usage** section in this document for common filters.

AFI information is accessible using `describe-fpga-images` immediately after `create-fpga-image` returns with a valid `afiId`.  The information provided by `describe-fpga-images` includes AFI states to check the result of the bitstream generation process:

* `pending` AFI bitstream generation is in progress.
* `available` AFI is available for use by F1 instances.
* `failed` AFI bitstream generation failed.  The `State.Message` field provides the specific error code as described in [create-fpga-image error codes](create_fpga_image_error_codes.md).
* `unavailable` AFI is no longer available for use by F1 instances.


## Example response

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

## Example usage

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

### Use filters parameter

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
[`create-tags`](https://docs.aws.amazon.com/cli/latest/reference/ec2/create-tags.html),
[`describe-tags`](https://docs.aws.amazon.com/cli/latest/reference/ec2/describe-tags.html)
and [`delete-tags`](https://docs.aws.amazon.com/cli/latest/reference/ec2/delete-tags.html)):
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


### Combine filters to find groups of AFIs

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

## Control command output

* Use the stadard aws-cli `query` and `output` parameters to change the response format and displayed fields:
```
    $ aws ec2 describe-fpga-images --query 'FpgaImages[*].[FpgaImageGlobalId,UpdateTime,ShellVersion,State.Code,Name]' --output text --owners amazon
    agfi-02948a33d1a0e9665	2017-07-26T19:18:41.000Z	0x071417d3	available	dram_dma_1.3.0
    agfi-088bffb3ab91ca2d1	2017-07-26T19:09:24.000Z	0x071417d3	available	hello_world_1.3.0
    agfi-0f0e045f919413242	2017-04-19T17:15:26.000Z	0x04151701	available	cl_hellow_world_04151701
    agfi-0d873e8b409f8e806	2017-04-17T15:58:54.000Z	0x04151701	available	cl_dram_dma_0415
```

Find details on all available formatting options in [Controlling Command Output from the AWS Command Line Interface](http://docs.aws.amazon.com/cli/latest/userguide/controlling-output.html).

## Common Error Messages


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
