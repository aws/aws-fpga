## Setup CLI and Create S3 Bucket

To install the AWS CLI, please follow the instructions here: (http://docs.aws.amazon.com/cli/latest/userguide/installing.html).
```
    $ aws configure         # to set your credentials (found in your console.aws.amazon.com page) and region (us-east-1)
```
Create a bucket and folder:
```
    $ aws s3 mb s3://<bucket-name> --region us-east-1  # Create an S3 bucket (choose a unique bucket name)
    $ aws s3 mb s3://<bucket-name>/<dcp-folder-name>   # Create folder for your tarball files
    $ touch FILES_GO_HERE.txt                          # Create a temp file
    $ aws s3 cp FILES_GO_HERE.txt s3://<bucket-name>/<dcp-folder-name>/  # Which creates the folder on S3
```
Create a folder for your log files        
```    
    $ aws s3 mb s3://<bucket-name>/<logs-folder-name>  # Create a folder to keep your logs
    $ touch LOGS_FILES_GO_HERE.txt                     # Create a temp file
    $ aws s3 cp LOGS_FILES_GO_HERE.txt s3://<bucket-name>/<logs-folder-name>/  # Which creates the folder on S3
```             

