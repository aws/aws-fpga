#!/usr/bin/env python

## =============================================================================
## Copyright 2016 Amazon.com, Inc. or its affiliates.
## All Rights Reserved Worldwide.
## =============================================================================

import os
import sys
import boto3

sns=boto3.client('sns')
topic_resp = sns.create_topic(Name="FPGA_CL_BUILD")
print topic_resp['TopicArn']


list_resp = sns.list_subscriptions_by_topic(TopicArn=topic_resp['TopicArn'])

print list_resp.get('Subscriptions')[0].get('Endpoint')

if os.environ.get('EMAIL') == None:
    print 'Please set your EMAIL environment variable to your address'
    sys.exit(1)

print "Your email address is %s" % os.environ.get('EMAIL')

if (os.environ.get('EMAIL') == list_resp.get('Subscriptions')[0].get('Endpoint')) == False:

    sub_resp = sns.subscribe(TopicArn=topic_resp['TopicArn'], Protocol='email', Endpoint=os.environ.get('EMAIL'))
    print sub_resp

pub_resp = sns.publish(TopicArn=topic_resp['TopicArn'],
                       Message='Your build is done',
                       Subject='test build is done')

sys.exit(0)
