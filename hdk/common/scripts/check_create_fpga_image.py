#!/usr/bin/env python

# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Amazon Software License (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#    http://aws.amazon.com/asl/
#
# or in the "license" file accompanying this file. This file is distributed on
# an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

from __future__ import print_function
import argparse
import boto3
import logging
import os
import pprint
import sys

logger = logging.getLogger('logger')

pp = pprint.PrettyPrinter(indent=4)


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

    parser.add_argument('--afi-name', action='store', required=True, help='A name for the AFI.')
    parser.add_argument('--afi-description', action='store', required=True, help='A description for the AFI.')
    parser.add_argument('--dcp-bucket', action='store', required=True,
                        help='The S3 bucket containing the design checkpoint.')
    parser.add_argument('--dcp-key', action='store', required=True,
                        help='The location of the design checkpoint in DCP-BUCKET. The input must be a tar-ball in encrypted format.')
    parser.add_argument('--logs-bucket', action='store', required=True,
                        help='The S3 bucket where the AFI creation logs will be written.')
    parser.add_argument('--logs-key', action='store', required=True,
                        help='Folder in LOGS-BUCKETS where logs will be written.')
    parser.add_argument('--client-token', action='store', required=False, default=None,
                        help='Unique, case-sensitive identifier that you provide to ensure the idempotency of the request. For more information, see Ensuring Idem-potency.')
    parser.add_argument('--dry-run', action='store_true', required=False, default=False,
                        help='Do not actually create image.')
    parser.add_argument('--no-dry-run', action='store_true', required=False, default=False,
                        help='Override the --dry-run option. Really create the AFI.')
    parser.add_argument('--debug', action='store_true', required=False, help='Enable debug messages')

    args = parser.parse_args()

    logging_level = logging.INFO
    if args.debug:
        logging_level = logging.DEBUG

    logging_format = '%(levelname)s:%(asctime)s: %(message)s'

    logger.setLevel(logging_level)

    fh = logging.StreamHandler()

    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)
    fh.setFormatter(formatter)
    logger.addHandler(fh)

    # Check that input dcp tarball has been uploaded to S3
    if not s3_exists(args.dcp_bucket, args.dcp_key):
        logger.error("DCP tarball hasn't been uploaded to S3: s3://{0}/{1}".format(args.dcp_bucket, args.dcp_key))
        sys.exit(2)
    if not s3_exists(args.logs_bucket, args.logs_key):
        logger.error("Logs directory doesn't exist in S3: s3://{0}/{1}".format(args.logs_bucket, args.logs_key))
        sys.exit(2)
    cmd = "aws ec2 create-fpga-image --name {0} --description '{1}' --input-storage-location Bucket={2},Key={3} --logs-storage-location Bucket={4},Key={5}".format(
        args.afi_name, args.afi_description, args.dcp_bucket, args.dcp_key, args.logs_bucket, args.logs_key)
    if args.client_token:
        cmd += " --client_token {0}".format(args.client_token)
    if args.no_dry_run:
        cmd += " --no-dry-run"
    elif args.dry_run:
        cmd += " --dry-run"

    logger.info("Run the following command to generate AFI:\n" + cmd)

    sys.exit(0)
