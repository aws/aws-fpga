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
import datetime
from datetime import datetime, timedelta
import logging
import os
import re
import sys
import time
import traceback
try:
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__file__)

SLEEP_SECONDS = 60
DEFAULT_MAX_DURATION_HOURS = 6

description = '''
Waits for AFI generation to complete.

Optionally notifies an email address subscribed to an SNS topic.
If --notify is used then --email is required.
'''

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--afi', action='store', required=True, help="AFI ID (not Global AFI ID)")
    parser.add_argument('--max-minutes', action='store', required=False, default=(DEFAULT_MAX_DURATION_HOURS * 60), help="Maximum minutes to wait. Default={}".format(DEFAULT_MAX_DURATION_HOURS * 60))
    parser.add_argument('--notify', action='store_true', default=False, required=False, help="Notify SNS topic when AFI generation completes.")
    parser.add_argument('--sns-topic', action='store', required=False, default='CREATE_AFI', help="SNS topic name to create/use for notification. Defaults to CREATE_AFI)")
    parser.add_argument('--email', action='store', required=False, default=None, help="Email address to subscribe to the SNS topic.")
    parser.add_argument('--debug', action='store_true', default=False, help="Enable debug messages")
    args = parser.parse_args()

    if args.debug:
        logger.setLevel(logging.DEBUG)

    start_time = datetime.utcnow()

    max_duration = timedelta(minutes=args.max_minutes)

    logger.info("Waiting for {} generation to complete.".format(args.afi))

    if args.notify:
        if not args.email:
            logger.error("--email required with --notify.")
            sys.exit(1)
        email = args.email
        topic_name = args.sns_topic
        logger.info("Will subscribe {} to SNS topic {} and notify the topic when complete".format(email, topic_name))

        topic_arn = aws_fpga_utils.create_sns_subscription(topic_name, email)

    # Wait for create-fpga-image to complete
    ec2_client = boto3.client('ec2')
    create_fpga_image_complete = False
    while not create_fpga_image_complete:
        afi_info = ec2_client.describe_fpga_images(FpgaImageIds=[args.afi])['FpgaImages'][0]
        afi_state = afi_info['State']['Code']
        logger.debug("State={}".format(afi_state))
        if afi_state != 'pending':
            if afi_state == 'available':
                logger.info('AFI generation passed and AFI is available')
            else:
                afi_message = afi_info['State']['Message']
                logger.error("AFI generation failed. State={} Message={}".format(afi_state, afi_message))
            create_fpga_image_complete = True
        else:
            current_time = datetime.utcnow()
            if (current_time - start_time) > max_duration:
                logger.error("Timed out waiting for AFI generation to complete.")
                sys.exit(1)
            time.sleep(SLEEP_SECONDS)
    passed = afi_state == 'available'

    if args.notify:
        if passed:
            subject = "create-fpga-image of {} passed".format(args.afi)
            message = "State={}".format(afi_state)
        else:
            subject = "create-fpga-image of {} failed".format(args.afi)
            message = "State={} Messsage={}".format(afi_state, afi_message)
        sns_client = boto3.client('sns')
        pub_resp = sns_client.publish(TopicArn=topic_arn,
                                      Subject=subject,
                                      Message=message)
    if passed:
        sys.exit(0)
    sys.exit(1)
