# AWS EC2 APIs describe-fpga-image-attribute, modify-fpga-image-attribute and reset-fpga-image-attribute

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

## Example usage

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
