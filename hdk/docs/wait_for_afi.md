# Wait for AFI Generation

The `create-fpga-image` command submits a customer's DCP to AWS to create an AFI in the background.
This process can take hours.
The `wait_for_afi.py` script will wait for the process to complete and then optionally 
send an email with the results.
The return code of the script will be 0 if the AFI was successfully created.
The script should be in your path after sourcing `hdk_setup.sh`.

The script uses the AWS Simple Notification Service (SNS) to send email
notifications so you must have permissions to create an SNS topic, add a
subscription, and publish to the SNS topic.
By default the topic name used is CREATE_AFI but the topic name can be
changed using the `--sns-topic` option.

Note: Please note that the developer kit is currently based on Python2 and wait_for_afi script requires boto3 installation compatible with Python2. An older version of boto3 compatible with Python2 can be installed, for example, using
sudo pip install boto3==1.16

Example usage:

`wait_for_afi.py --afi `*`AFI-ID`*` --notify --email `*`email-address`*

To get help and usage:

`wait_for_afi.py -h`
