# AWS EC2 API delete-fpga-image

Use `aws ec2 delete-fpga-image` to delete an AFI.  Delete operations are restricted to the target region determined by the aws-cli default region or 
[region](http://docs.aws.amazon.com/cli/latest/userguide/cli-command-line.html) argument.  Deleting an AFI in one region has no effect on AFIs in other regions.

Delete is not allowed if the AFI is public or shared with other accounts.  Use [describe-fpga-image-attribute](./fpga_image_attributes.md) to check if an AFI is shared,
and [reset-fpga-image-attribute](./fpga_image_attributes.md) to remove all load permissions.

Deleting an AFI does not affect AFIs already loaded onto FPGAs. Deleting only prevents new attempts to load an AFI onto an FPGA.  Note that, within a region, an AFI will 
continue to be loadable as long as its Global AFI ID is available. Use [describe-fpga-images](./describe_fpga_images.md) with `fpga-image-global-id` filter to find AFIs with the same Global AFI ID.

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

## Example usage

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

## Common Error Messages

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
