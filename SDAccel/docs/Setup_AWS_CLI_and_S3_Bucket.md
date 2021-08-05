## Setup CLI and Create S3 Bucket
The developer is required to create an S3 bucket for the AFI generation. The bucket will contain a tar file and logs which are generated from the AFI creation service. 

To install the AWS CLI, please follow the [instructions here](http://docs.aws.amazon.com/cli/latest/userguide/installing.html).

The AWS SDAccel scripts require JSON output format and the scripts will not work properly if you use any other output format types (ex: text, table).  JSON is the default output format of the AWS CLI.

```
    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page), region (us-east-1) and output (json) 
```
This S3 bucket will be used by the AWS scripts to upload your DCP to AWS for AFI generation which will be packaged into a tar file.  
Start by creating a bucket:
```
    $ aws s3 mb s3://<bucket-name> --region us-east-1  # Create an S3 bucket (choose a unique bucket name)
    $ touch FILES_GO_HERE.txt                          # Create a temp file
    $ aws s3 cp FILES_GO_HERE.txt s3://<bucket-name>/<dcp-folder-name>/  # Choose a dcp folder name 
```
The AFI creation process will generate logs and will be placed in your S3 bucket. These logs can be used for debug if the AFI generation fails.  
Next, create a folder for your log files:        
```    
    $ touch LOGS_FILES_GO_HERE.txt                     # Create a temp file
    $ aws s3 cp LOGS_FILES_GO_HERE.txt s3://<bucket-name>/<logs-folder-name>/  # Choose a logs folder name
```             
Once your AFI has been created successfully, you are free to delete the tar file and logs as needed.  Deleting these files will not delete or modify your AFI.
