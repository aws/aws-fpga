#!/usr/bin/env python2.7

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
import re
import sys
import traceback
try:
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__file__)

description = '''
Notify an email via SNS after DCP generqation completes.

Notifies an email address subscribed to an SNS topic.
If --email is not specified then looks for the EMAIL environment variable.
'''

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--sns-topic', action='store', required=False, default='FPGA_CL_BUILD', help="SNS topic name to create/use for notification. Defaults to FPGA_CL_BUILD)")
    parser.add_argument('--email', action='store', required=False, default=None, help="Email address to subscribe to the SNS topic. If not specified must set EMAIL environment variable.")
    parser.add_argument('--debug', action='store_true', default=False, help="Enable debug messages")
    args = parser.parse_args()

    if args.debug:
        logger.setLevel(logging.DEBUG)

    if args.email:
        email = args.email
    else:
        if os.environ.get('EMAIL') is None:
            logger.error('Set email address via --email or the EMAIL environment variable.')
            sys.exit(1)
        email = os.environ['EMAIL']

    topic_name = args.sns_topic

    topic_arn = aws_fpga_utils.create_sns_subscription(topic_name, email)

    sns_client = boto3.client('sns')
    pub_resp = sns_client.publish(TopicArn=topic_arn,
                           Message='Your FPGA CL build is complete.',
                           Subject='Your FPGA CL build is complete.')

    sys.exit(0)
