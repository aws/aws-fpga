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

import boto3
import datetime
from datetime import datetime, timedelta
import logging
import re
import time

def get_logger(name):
    logger = logging.getLogger(name)
    logger_console_handler = logging.StreamHandler()
    logger_formatter = logging.Formatter('%(levelname)s:%(asctime)s: %(message)s')
    logger_console_handler.setFormatter(logger_formatter)
    logger.addHandler(logger_console_handler)
    logger.setLevel(logging.INFO)
    return logger

logger = get_logger(__file__)

def create_sns_subscription(topic_name, email, wait_for_confirmation=True):
    WAIT_FOR_CONFIRMATION_DELAY = 10
    MAX_WAIT_FOR_CONFIRMATION_DELAY = timedelta(minutes=10)
    sns_client = boto3.client('sns')
    # Create the topic if it doesn't exist
    # If it already exists just returns the ARN of the existing topic.
    topic_arn = sns_client.create_topic(Name=topic_name)['TopicArn']
    logger.debug("topic_arn={}".format(topic_arn))
    
    # Search for existing subscription
    subscription_found = False
    list_resp = sns_client.list_subscriptions_by_topic(TopicArn=topic_arn)
    if 'Subscriptions' in list_resp:
        for subscription in list_resp['Subscriptions']:
            if subscription['Endpoint'] == email and subscription['Protocol'] == 'email':
                subscription_found = True
                logger.debug("{} already subscribed to {}".format(email, topic_name))
                subscription_arn = subscription['SubscriptionArn']
    
    # Create subscription if it doesn't already exist
    if not subscription_found:
        logger.info("Subscribing {} to the {} topic".format(email, topic_name))
        sub_resp = sns_client.subscribe(TopicArn=topic_arn, Protocol='email', Endpoint=email)
        subscription_arn = sub_resp['SubscriptionArn']
        logger.info("Subscription created.")
    logger.debug("Subscription ARN={}".format(subscription_arn))
    
    if wait_for_confirmation:
        # Make sure that subscription has been confirmed
        arn_re = re.compile(r'^arn:aws:sns:')
        subscription_confirmed = arn_re.match(subscription_arn)
        if not subscription_confirmed:
            logger.info("Waiting for subscription confirmation before continuing. Check your email.")
        start_time = datetime.utcnow()
        while not subscription_confirmed:
            time.sleep(WAIT_FOR_CONFIRMATION_DELAY)
            subscription_found = False
            list_resp = sns_client.list_subscriptions_by_topic(TopicArn=topic_arn)
            for subscription in list_resp['Subscriptions']:
                if subscription['Endpoint'] == email and subscription['Protocol'] == 'email':
                    subscription_found = True
                    subscription_arn = subscription['SubscriptionArn']
            if not subscription_found:
                logger.error("Subscription not found")
                raise RuntimeError("Subscription not found")
            subscription_confirmed = arn_re.match(subscription_arn)
            if subscription_confirmed:
                logger.info("Subscription confirmed")
            else:
                current_time = datetime.utcnow()
                if (current_time - start_time) > MAX_WAIT_FOR_CONFIRMATION_DELAY:
                    logger.error("Timed out waiting for SNS subscription confirmation.")
                    raise RuntimeError("Timed out waiting for SNS subscription confirmation.")
    
    return topic_arn
