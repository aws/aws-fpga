# AWS EC2 API copy-fpga-image

Use `aws ec2 copy-fpga-image` to copy AFIs between AWS regions.  The copy operation will use the target [EC2 endpoint](http://docs.aws.amazon.com/general/latest/gr/rande.html#ec2_region) as the destination region
(this is the aws-cli default region or specified by the [region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) argument).  The source region must be specified using `--source-region` argument.

Copy will assign the destination AFI a new AFI ID specific to that region, but will preserve the source Global AFI ID.  EC2 instances can use the same Global AFI ID on every region.

To allow copies, the source AFI must meet the following requirements:
* AFI must be owned by caller.  Access to an AFI does not grant sufficient permissions to copy it.
* AFI must be in `available` state.  Copy is not allowed if source AFI is in `pending`, `failed` or `unavailable` states.

## Example usage

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
