#!/usr/bin/env python

## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

import argparse
import boto3
#from botocore.exceptions import ClientError
import json
import logging
import os
import pprint
import re
import sys

logger = logging.getLogger('logger')

pp = pprint.PrettyPrinter(indent = 4)

def s3_exists(bucket, key):
    try:
        s3_client = boto3.client('s3')
        results = s3_client.list_objects(Bucket=bucket, Prefix=key)
        return 'Contents' in results
    except:
        return False
    return True

if __name__ == '__main__':
    num_errors = 0
    
    parser = argparse.ArgumentParser()
    
    parser.add_argument('--shell-version', action = 'store', required = True, help = 'AWS shell version')
    parser.add_argument('--pci-device-id', action = 'store', required = True, help = '')
    parser.add_argument('--pci-vendor-id', action = 'store', required = True, help = '')
    parser.add_argument('--pci-subsystem-id', action = 'store', required = True, help = '')
    parser.add_argument('--pci-subsystem-vendor-id', action = 'store', required = True, help = '')
    parser.add_argument('--cl-name', action = 'store', required = True, help = 'Custom Logic name')
    parser.add_argument('--cl-description', action = 'store', required = True, help = 'Custom Logic description')
    parser.add_argument('--dcp-bucket', action = 'store', required = True, help = 'S3 bucket where DCP is stored')
    parser.add_argument('--dcp-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--logs-bucket', action = 'store', required = True, help = 'S3 bucket where AFI creation logs will be stored')
    parser.add_argument('--logs-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--dryrun', action = 'store_true', required = False, help = 'Only check S3 permissions. Do not actually create image.')
    parser.add_argument('--debug', action = 'store_true', required = False, help = 'Enable debug messages')
    
    args = parser.parse_args()
    
    logging_level = logging.INFO
    if (args.debug):
        logging_level = logging.DEBUG

    #logging_format = '%(levelname)s:%(asctime)s:%(filename)s,%(lineno)s: %(message)s'
    logging_format = '%(levelname)s:%(asctime)s: %(message)s'

    logger.setLevel(logging_level)

    fh = logging.StreamHandler()

    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)
    fh.setFormatter(formatter)
    logger.addHandler(fh)
    
    logger.info("Checking bucket permissions for the dcp and logs.")
    cmd = os.environ['HDK_DIR'] + "/common/scripts/check_s3_bucket_policy.py --dcp-bucket {} --dcp-key {} --logs-bucket {} --logs-key {}".format(args.dcp_bucket, args.dcp_key, args.logs_bucket, args.logs_key)
    if args.debug:
        cmd += ' --debug'
    logger.debug(cmd)
    rc = os.system(cmd)
    if rc:
        logger.error("S3 bucket permissions must be updated")
        sys.exit(2)
    logger.info("S3 bucket permissions are correct")
    
    # Check that input dcp tarball has been uploaded to S3
    if not s3_exists(args.dcp_bucket, args.dcp_key):
        logger.error("DCP tarball hasn't been uploaded to S3: s3://{}/{}".format(args.dcp_bucket, args.dcp_key))
        sys.exit(2)
    if not s3_exists(args.logs_bucket, args.logs_key):
        logger.error("Logs directory doesn't exist in S3: s3://{}/{}".format(args.logs_bucket, args.logs_key))
        sys.exit(2)
    cmd = "aws ec2 create-fpga-image --name {} --description '{}' --shell-version {} --fpga-pci-id DeviceId={},VendorId={},SubsystemId={},SubsystemVendorId={} --input-storage-location Bucket={},Key={} --logs-storage-location Bucket={},Key={}".format(
        args.cl_name, args.cl_description, args.shell_version, args.pci_device_id, args.pci_vendor_id, args.pci_subsystem_id, args.pci_subsystem_vendor_id, args.dcp_bucket, args.dcp_key, args.logs_bucket, args.logs_key)
    if args.dryrun:
        cmd += " --dryrun"
    logger.info(cmd)
    rc = os.system(cmd)
    if rc:
        logger.error("create-fpga-image failed with rc={}".format(rc))
        sys.exit(rc)
    
    sys.exit(0)
    