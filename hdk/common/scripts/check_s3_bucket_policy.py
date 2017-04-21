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

import argparse
import boto3

try:
    from exceptions import ValueError
except ImportError:
    # Built-in in Python 3.x
    pass
import json
import logging
import pprint
import re
import sys

logger = logging.getLogger('logger')

pp = pprint.PrettyPrinter(indent=4)

aws_account = '365015490807'
aws_account_arn = 'arn:aws:iam::{0}:root'.format(aws_account)

description = '''Checks S3 permissions required for create-fpga-image.

This program uses the AWS CLI and requires credentials to be configured.
See $AWS_FPGA_REPO_DIR/README.md for instructions to configure your credentials.
'''


class PolicyStatement:
    def __init__(self, statement, principal=None):
        self.statement = statement
        self.principals_re = []
        self.actions_re = []
        self.notactions_re = []
        self.resources_re = []
        self.process_policy_statement(statement, principal)

    # Convert the policy pattern to a regular expression
    # Escape '.' and replace * with '.*'
    # Append a '$' so an exact match is required
    def escape_policy_pattern(self, policy_pattern):
        policy_pattern = re.sub(r'\.', '\.', policy_pattern)
        policy_pattern = re.sub(r'\*', '.*', policy_pattern)
        policy_pattern += '$'
        return policy_pattern

    def process_policy_statement(self, statement, principal=None):
        # If a principal is provided then it means that this is a role policy and there
        # should not be a 'Principal' clause in the statement because it is implicit

        if principal:
            if 'Principal' in statement:
                raise ValueError("'Principal not allowed in a role policy:\n{0}".format(pp.pformat(statement)))
            principals = [principal]
        else:
            principals = statement['Principal']['AWS']
            if not isinstance(principals, list):
                principals = [principals]
        for principal in principals:
            principal = re.sub(r'\.', '\.', principal)
            principal = re.sub(r'\*', '.*', principal)
            principal += '$'
            self.principals_re.append(principal)

        if 'Action' in statement:
            actions = statement['Action']
            if not isinstance(actions, list):
                actions = [actions]
            for action in actions:
                action = re.sub(r'\.', '\.', action)
                action = re.sub(r'\*', '.*', action)
                action += '$'
                self.actions_re.append(action)

        if 'NotAction' in statement:
            notactions = statement['NotAction']
            if not isinstance(notactions, list):
                notactions = [notactions]
            for notaction in notactions:
                notaction = re.sub(r'\.', '\.', notaction)
                notaction = re.sub(r'\*', '.*', notaction)
                notaction += '$'
                self.notactions_re.append(notaction)

        resources = statement['Resource']
        if not isinstance(resources, list):
            resources = [resources]
        for resource in resources:
            resource = re.sub(r'\.', '\.', resource)
            resource = re.sub(r'\*', '.*', resource)
            resource += '$'
            self.resources_re.append(resource)

        self.effect = statement['Effect']
        return

    def check_effect(self, principal, resource, action):
        result = ''
        for principal_re in self.principals_re:
            # Deny overrides any Allow
            if result == 'Deny': break
            if re.match(principal_re, principal):
                logger.debug("Found a policy for {0}:\n{1}".format(principal, pp.pformat(self.statement)))
                for resource_re in self.resources_re:
                    # Deny overrides any Allow
                    if result == 'Deny': break
                    if re.match(resource_re, resource):
                        for action_re in self.actions_re:
                            if re.match(action_re, action):
                                if self.effect == 'Allow':
                                    result = 'Allow'
                                else:
                                    result = 'Deny'
                                    # Deny overrides any Allow
                                    break
                        if len(self.notactions_re):
                            action_match = False
                            for notaction_re in self.notactions_re:
                                if re.match(notaction_re, action):
                                    action_match = True
                                    break
                            if not action_match:
                                if self.effect == 'Allow':
                                    # Allow all actions except those that match
                                    result = 'Allow'
                                elif self.effect == 'Deny':
                                    # Deny access for all actions that don't match
                                    result = 'Deny'
                                    # Deny overrides any Allow
                                    break
        return result


class S3PolicyChecker:
    def __init__(self, aws_account_arn, user_account_arn, dcp_bucket, dcp_key, dcp_bucket_policy, logs_bucket, logs_key,
                 logs_bucket_policy, user_policy_statements):
        self.aws_account_arn = aws_account_arn
        self.user_account_arn = user_account_arn
        self.dcp_bucket = dcp_bucket
        self.dcp_key = dcp_key
        self.dcp_bucket_policy = dcp_bucket_policy
        self.logs_bucket = logs_bucket
        self.logs_key = logs_key
        self.logs_bucket_policy = logs_bucket_policy
        self.user_policy_statements = user_policy_statements

        self.dcp_bucket_resource = 'arn:aws:s3:::{0}'.format(self.dcp_bucket)
        self.dcp_resource = 'arn:aws:s3:::{0}/{1}'.format(self.dcp_bucket, self.dcp_key)
        self.logs_bucket_resource = 'arn:aws:s3:::{0}'.format(self.logs_bucket)
        self.logs_resource = 'arn:aws:s3:::{0}{1}'.format(self.logs_bucket, self.logs_key)

        self.aws_can_list_dcp_bucket = False
        self.aws_cannot_list_dcp_bucket = False
        self.aws_can_get_dcp = False
        self.aws_cannot_get_dcp = False
        self.user_can_list_dcp_bucket = False
        self.user_cannot_list_dcp_bucket = False
        self.user_can_put_dcp = False
        self.user_cannot_put_dcp = False

        self.aws_can_list_logs_bucket = False
        self.aws_cannot_list_logs_bucket = False
        self.aws_can_put_logs = False
        self.aws_cannot_put_logs = False
        self.user_can_list_logs_bucket = False
        self.user_cannot_list_logs_bucket = False
        self.user_can_get_logs = False
        self.user_cannot_get_logs = False

        self.num_errors = 0

    def check_dcp_bucket_policy(self):
        logger.debug("Checking DCP bucket permissions")
        for statement in self.dcp_bucket_policy['Statement']:
            statement = PolicyStatement(statement)

            effect = statement.check_effect(self.aws_account_arn, self.dcp_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.aws_can_list_dcp_bucket = True
                logger.debug("Allows AWS to list the DCP bucket")
            elif effect == 'Deny':
                self.aws_cannot_list_dcp_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following DCP bucket policy statement will prevent AWS from listing the DCP bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.aws_account_arn, self.dcp_resource, 's3:GetObject')
            if effect == 'Allow':
                self.aws_can_get_dcp = True
                logger.debug("Allows AWS to get the DCP")
            elif effect == 'Deny':
                self.aws_cannot_get_dcp = True
                self.num_errors += 1
                logger.error(
                    "The following DCP bucket policy statement will prevent AWS from reading the DCP:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.dcp_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.user_can_list_dcp_bucket = True
                logger.debug("Allows you to list the DCP bucket")
            elif effect == 'Deny':
                self.user_cannot_list_dcp_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following DCP bucket policy statement will prevent you from listing the DCP bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.dcp_resource, 's3:PutObject')
            if effect == 'Allow':
                self.user_can_put_dcp = True
                logger.debug("Allows you to write the DCP")
            elif effect == 'Deny':
                self.user_cannot_put_dcp = True
                self.num_errors += 1
                logger.error(
                    "The following DCP bucket policy statement will prevent you from writing the DCP:\n{0}".format(
                        pp.pformat(statement.statement)))

    def check_logs_bucket_policy(self):

        # Check logs bucket for required permissions for user and AWS account
        logger.debug("Checking logs bucket permissions")
        for statement in self.logs_bucket_policy['Statement']:
            statement = PolicyStatement(statement)

            effect = statement.check_effect(self.aws_account_arn, self.logs_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.aws_can_list_logs_bucket = True
                logger.debug("Allows AWS to list the logs bucket")
            elif effect == 'Deny':
                self.aws_cannot_list_logs_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following logs bucket policy statement will prevent AWS from listing the logs bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.aws_account_arn, self.logs_resource, 's3:PutObject')
            if effect == 'Allow':
                self.aws_can_put_logs = True
                logger.debug("Allows AWS to write the AFI creation logs")
            elif effect == 'Deny':
                self.aws_cannot_put_logs = True
                self.num_errors += 1
                logger.error(
                    "The following logs bucket policy statement will prevent AWS from writing the AFI creation logs:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.logs_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.user_can_list_logs_bucket = True
                logger.debug("Allows you to list the logs bucket")
            elif effect == 'Deny':
                self.user_cannot_list_logs_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following DCP bucket policy statement will prevent you from listing the logs bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.logs_resource, 's3:GetObject')
            if effect == 'Allow':
                self.user_can_get_logs = True
                logger.debug("Allows you to get the AFI creation logs.")
            elif effect == 'Deny':
                self.user_cannot_get_logs = True
                self.num_errors += 1
                logger.error(
                    "The following logs bucket policy statement will prevent you from getting the AFI creation logs:\n{0}".format(
                        pp.pformat(statement.statement)))

    def check_user_policy(self):
        logger.debug("Checking user's permissions from IAM")
        for statement in self.user_policy_statements:
            # The principal is implicit because these are policies associated with the user or role
            statement = PolicyStatement(statement, self.user_account_arn)

            effect = statement.check_effect(self.user_account_arn, self.dcp_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.user_can_list_dcp_bucket = True
                logger.debug("Allows you to list the DCP bucket:\n{0}".format(pp.pformat(statement.statement)))
            elif effect == 'Deny':
                self.user_cannot_list_dcp_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following IAM policy statement will prevent you from listing the DCP bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.dcp_resource, 's3:PutObject')
            if effect == 'Allow':
                self.user_can_put_dcp = True
                logger.debug("Allows you to write the DCP:\n{0}".format(pp.pformat(statement.statement)))
            elif effect == 'Deny':
                self.user_cannot_put_dcp = True
                self.num_errors += 1
                logger.error("The following IAM policy statement will prevent you from writing the DCP:\n{0}".format(
                    pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.logs_bucket_resource, 's3:ListBucket')
            if effect == 'Allow':
                self.user_can_list_logs_bucket = True
                logger.debug("Allows you to list the logs bucket:\n{0}".format(pp.pformat(statement.statement)))
            elif effect == 'Deny':
                self.user_cannot_list_logs_bucket = True
                self.num_errors += 1
                logger.error(
                    "The following IAM policy statement will prevent you from listing the logs bucket:\n{0}".format(
                        pp.pformat(statement.statement)))

            effect = statement.check_effect(self.user_account_arn, self.logs_resource, 's3:GetObject')
            if effect == 'Allow':
                self.user_can_get_logs = True
                logger.debug("Allows you to get the AFI creation logs:\n{0}".format(pp.pformat(statement.statement)))
            elif effect == 'Deny':
                self.user_cannot_get_logs = True
                self.num_errors += 1
                logger.error(
                    "The following IAM policy statement will prevent you from getting the AFI creation logs:\n{0}".format(
                        pp.pformat(statement.statement)))

    def check(self):
        if self.dcp_bucket_policy:
            self.check_dcp_bucket_policy()
        if self.logs_bucket_policy:
            self.check_logs_bucket_policy()
        if self.user_policy_statements:
            self.check_user_policy()

        if not self.aws_can_list_dcp_bucket:
            self.num_errors += 1
        if not self.aws_can_get_dcp:
            self.num_errors += 1
        if not self.user_can_list_dcp_bucket:
            self.num_errors += 1
        if not self.user_can_put_dcp:
            self.num_errors += 1
        if not self.aws_can_list_logs_bucket:
            self.num_errors += 1
        if not self.aws_can_put_logs:
            self.num_errors += 1
        if not self.user_can_list_logs_bucket:
            self.num_errors += 1
        if not self.user_can_get_logs:
            self.num_errors += 1
        return self.num_errors

    def report(self):
        extra_dcp_statements = []
        extra_logs_statements = []
        if not self.aws_can_list_dcp_bucket:
            statement_str = '''
                {{
                    "Sid": "Bucket level permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:ListBucket"
                    ],
                    "Resource": "{dcp_bucket_resource}"
                }}'''.format(aws_account=aws_account, dcp_bucket_resource=self.dcp_bucket_resource)
            logger.error('''AWS can't list the DCP bucket.
            
    Add the following statement to the bucket policy for:
    {dcp_bucket}
            '''.format(dcp_bucket=self.dcp_bucket) + statement_str)
            extra_dcp_statements.append(statement_str)

        if not self.aws_can_get_dcp:
            statement_str = '''
                {{
                    "Sid": "Object read permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:GetObject"
                    ],
                    "Resource": "{dcp_resouce}"
                }}
    '''.format(aws_account=aws_account, dcp_resouce=self.dcp_resource)
            logger.error('''AWS can't read the DCP.
            
    Add the following statement to the bucket policy for:
    {dcp_bucket}
            '''.format(dcp_bucket=self.dcp_bucket) + statement_str)
            extra_dcp_statements.append(statement_str)

        if not self.user_can_list_dcp_bucket:
            statement_str = '''
                {{
                    "Sid": "Bucket level permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "{user_account_arn}"
                    }},
                    "Action": [
                        "s3:ListBucket"
                    ],
                    "Resource": "{dcp_bucket_resource}"
                }}
    '''.format(user_account_arn=self.user_account_arn, dcp_bucket_resource=self.dcp_bucket_resource)
            logger.error('''User can't list the DCP bucket
            
    Add the following statement to the bucket policy for:
    {dcp_bucket}
            '''.format(dcp_bucket=self.dcp_bucket) + statement_str)
            extra_dcp_statements.append(statement_str)

        if not self.user_can_put_dcp:
            statement_str = '''
                {{
                    "Sid": "Object write permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "{user_account_arn}"
                    }},
                    "Action": [
                        "s3:PutObject"
                    ],
                    "Resource": "{dcp_resource}"
                }}
    '''.format(user_account_arn=self.user_account_arn, dcp_resource=self.dcp_resource)
            logger.error('''User can't write the DCP
            
    Add the following statement to the bucket policy for:
    {dcp_bucket}
            '''.format(dcp_bucket=self.dcp_bucket) + statement_str)
            extra_dcp_statements.append(statement_str)

        if not self.aws_can_list_logs_bucket and (self.logs_bucket != self.dcp_bucket):
            statement_str = '''
                {{
                    "Sid": "Bucket level permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:ListObject"
                    ],
                    "Resource": "arn:aws:s3:::{logs_bucket}"
                }}
    '''.format(aws_account=aws_account, logs_bucket=self.logs_bucket)
            logger.error('''AWS can't list the the logs bucket
            
    Add the following statement to the bucket policy for:
    {logs_bucket}
            '''.format(logs_bucket=self.logs_bucket) + statement_str)
            extra_logs_statements.append(statement_str)

        if not self.aws_can_put_logs:
            statement_str = '''
                {{
                    "Sid": "Folder write permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:PutObject"
                    ],
                    "Resource": "{logs_resource}*"
                }}
    '''.format(aws_account=aws_account, logs_resource=self.logs_resource)
            logger.error('''AWS can't write the logs
            
    Add the following statement to the bucket policy for:
    {logs_bucket}
            '''.format(logs_bucket=self.logs_bucket) + statement_str)
            if self.logs_bucket == self.dcp_bucket:
                extra_dcp_statements.append(statement_str)
            else:
                extra_logs_statements.append(statement_str)

        if not self.user_can_get_logs:
            statement_str = '''
                {{
                    "Sid": "Object read permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "{user_account_arn}"
                    }},
                    "Action": [
                        "s3:GetObject"
                    ],
                    "Resource": "{logs_resource}*"
                }}
    '''.format(user_account_arn=self.user_account_arn, logs_resource=self.logs_resource)
            logger.error('''User can't get logs
            
    Add the following statement to the bucket policy for:
    {logs_bucket}
            '''.format(logs_bucket=self.logs_bucket) + statement_str)
            if self.logs_bucket == self.dcp_bucket:
                extra_dcp_statements.append(statement_str)
            else:
                extra_logs_statements.append(statement_str)

        if self.num_errors:
            logger.error('''You need to provide AWS (Account ID: {aws_account}) the appropriate [read/write permissions](http://docs.aws.amazon.com/AmazonS3/latest/dev/example-walkthroughs-managing-access-example2.html) to your S3 buckets.
    
    **NOTE**: *The AWS Account ID has changed, please ensure you are using the correct Account ID listed here.*
    
    See $HDK_DIR/cl/examples/README.md'''.format(aws_account=aws_account))

        if len(extra_dcp_statements):
            if self.dcp_bucket_policy:
                logger.info("Add the following statements to the {0} bucket policy:".format(self.dcp_bucket))
                for statement_str in extra_dcp_statements:
                    logger.info(statement_str)
            else:
                logger.info("You currently don't have a bucket policy for {0}".format(self.dcp_bucket))
                policy_str = '''
        {{
            "Version": "2012-10-17",
            "Statement": [
                {{
                    "Sid": "Bucket level permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:ListBucket"
                    ],
                    "Resource": "{dcp_bucket_resource}"
                }},
                {{
                    "Sid": "Object read permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:GetObject"
                    ],
                    "Resource": "{dcp_resource}"
                }}'''.format(aws_account=aws_account, dcp_bucket_resource=self.dcp_bucket_resource,
                             dcp_resource=self.dcp_resource)
                if self.logs_bucket == self.dcp_bucket:
                    policy_str += ''',
                    {{
                        "Sid": "Logs folder write permissions",
                        "Effect": "Allow",
                        "Principal": {{
                            "AWS": "arn:aws:iam::{aws_account}:root"
                        }},
                        "Action": [
                            "s3:PutObject"
                        ],
                        "Resource": "{logs_resource}*"
                    }}'''.format(aws_account=aws_account, logs_resource=self.logs_resource)
                policy_str += '''
                ]
            }'''
                logger.info("The following bucket policy will resolve the problem:\n{0}".format(policy_str))

        if (self.logs_bucket != self.dcp_bucket) and len(extra_logs_statements):
            if self.logs_bucket_policy:
                logger.info("Add the following statements to the {0} bucket policy:".format(self.logs_bucket))
                for statement_str in extra_logs_statements:
                    logger.info(statement_str)
            else:
                logger.info("You currently don't have a bucket policy for {0}".format(self.logs_bucket))
                policy_str = '''
        {{
            "Version": "2012-10-17",
            "Statement": [
                {{
                    "Sid": "Bucket level permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:ListBucket"
                    ],
                    "Resource": "{logs_bucket_resource}"
                }},
                {{
                    "Sid": "Folder write permissions",
                    "Effect": "Allow",
                    "Principal": {{
                        "AWS": "arn:aws:iam::{aws_account}:root"
                    }},
                    "Action": [
                        "s3:PutObject"
                    ],
                    "Resource": "{logs_resource}*"
                }}
            ]
        }}
    '''.format(aws_account=aws_account, logs_bucket_resource=self.logs_bucket_resource,
               logs_resource=self.logs_resource)
                logger.info("The following bucket policy will resolve the problem:\n{0}".format(policy_str))
        return self.num_errors


def test():
    user_account_arn = 'arn:aws:iam::user-account'
    dcp_bucket = 'dcp_bucket'
    dcp_bucket_resource = 'arn:aws:s3:::{0}'.format(dcp_bucket)
    dcp_key = 'dcp.tar'
    dcp_resource = 'arn:aws:s3:::{0}/{1}'.format(dcp_bucket, dcp_key)
    logs_bucket = 'logs_bucket'
    logs_bucket_resource = 'arn:aws:s3:::{0}'.format(logs_bucket)
    logs_key1 = '/'
    logs_key2 = '/logs/'
    dcp_logs_resource1 = 'arn:aws:s3:::{0}{1}'.format(dcp_bucket, logs_key1)
    dcp_logs_resource2 = 'arn:aws:s3:::{0}{1}'.format(dcp_bucket, logs_key2)
    logs_resource1 = 'arn:aws:s3:::{0}{1}'.format(logs_bucket, logs_key1)
    logs_resource2 = 'arn:aws:s3:::{0}{1}'.format(logs_bucket, logs_key2)

    # Test with no policies
    user_policy_statments_none = [
    ]
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, None,
                              logs_bucket, logs_key1, None, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 8

    # Test deny all user s3 with user policy
    user_policy_statments_deny_all = [
        {'Action': 's3:*',
         'Resource': '*',
         'Effect': 'Deny'
         }
    ]
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, None,
                              dcp_bucket, logs_key1, None, user_policy_statments_deny_all)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == True
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == True

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == True
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == True
    assert checker.num_errors == 12

    # Test deny all aws s3 with bucket policy
    dcp_bucket_policy_deny_all_aws = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn,
                              dcp_bucket, dcp_key, dcp_bucket_policy_deny_all_aws,
                              dcp_bucket, logs_key2, dcp_bucket_policy_deny_all_aws, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == True
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == True
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == True
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == True
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 12

    # Test deny all user s3 with bucket policy
    dcp_bucket_policy_deny_all_user = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [user_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn,
                              dcp_bucket, dcp_key, dcp_bucket_policy_deny_all_user,
                              dcp_bucket, logs_key2, dcp_bucket_policy_deny_all_user, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == True
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == True

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == True
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == True
    assert checker.num_errors == 12

    # Test deny all s3 with bucket policy
    dcp_bucket_policy_deny_all_user = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn, user_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn,
                              dcp_bucket, dcp_key, dcp_bucket_policy_deny_all_user,
                              dcp_bucket, logs_key1, dcp_bucket_policy_deny_all_user, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == True
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == True
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == True
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == True

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == True
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == True
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == True
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == True
    assert checker.num_errors == 16

    # Test allow and deny all s3 with bucket policy
    dcp_bucket_policy_allow_deny_all_user = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn, user_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn, user_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn,
                              dcp_bucket, dcp_key, dcp_bucket_policy_allow_deny_all_user,
                              dcp_bucket, logs_key1, dcp_bucket_policy_allow_deny_all_user, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == True
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == True
    assert checker.user_can_list_dcp_bucket == True
    assert checker.user_cannot_list_dcp_bucket == True
    assert checker.user_can_put_dcp == True
    assert checker.user_cannot_put_dcp == True

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == True
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == True
    assert checker.user_can_list_logs_bucket == True
    assert checker.user_cannot_list_logs_bucket == True
    assert checker.user_can_get_logs == True
    assert checker.user_cannot_get_logs == True
    assert checker.num_errors == 8

    # Test with all policy elements scalar
    dcp_bucket_policy_scalar = {
        'Statement': [
            {
                'Principal': {
                    'AWS': aws_account_arn,
                },
                'Action': 's3:*',
                'Resource': '*',
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, dcp_bucket_policy_scalar,
                              logs_bucket, logs_key2, dcp_bucket_policy_scalar, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 4

    # Test with all policy elements array
    dcp_bucket_policy_array = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn, user_account_arn],
                },
                'Action': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, dcp_bucket_policy_array,
                              logs_bucket, logs_key1, dcp_bucket_policy_array, user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == True
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == True
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == True
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == True
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 0

    # Test NotAction to allow everything but S3
    dcp_bucket_policy_notaction_allow_not_s3 = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'NotAction': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key,
                              dcp_bucket_policy_notaction_allow_not_s3,
                              logs_bucket, logs_key1, dcp_bucket_policy_notaction_allow_not_s3,
                              user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 8

    # Test NotAction to deny everything but S3
    dcp_bucket_policy_notaction_deny_not_s3 = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'NotAction': ['s3:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key,
                              dcp_bucket_policy_notaction_deny_not_s3,
                              logs_bucket, logs_key2, dcp_bucket_policy_notaction_deny_not_s3,
                              user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 8

    # Test NotAction to allow everything but IAM
    dcp_bucket_policy_notaction_allow_not_iam = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'NotAction': ['iam:*'],
                'Resource': ['*'],
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key,
                              dcp_bucket_policy_notaction_allow_not_iam,
                              logs_bucket, logs_key1, dcp_bucket_policy_notaction_allow_not_iam,
                              user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 4

    # Test NotAction to deny everything but iam
    dcp_bucket_policy_notaction_deny_user_not_iam = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [user_account_arn],
                },
                'NotAction': ['iam:*'],
                'Resource': ['*'],
                'Effect': 'Deny'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key,
                              dcp_bucket_policy_notaction_deny_user_not_iam,
                              logs_bucket, logs_key1, dcp_bucket_policy_notaction_deny_user_not_iam,
                              user_policy_statments_none)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == False
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == False
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == False
    assert checker.user_cannot_list_dcp_bucket == True
    assert checker.user_can_put_dcp == False
    assert checker.user_cannot_put_dcp == True

    assert checker.aws_can_list_logs_bucket == False
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == False
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == False
    assert checker.user_cannot_list_logs_bucket == True
    assert checker.user_can_get_logs == False
    assert checker.user_cannot_get_logs == True
    assert checker.num_errors == 12

    # Test like readme, 1 bucket
    dcp_bucket_policy_allow_aws_dcp_logs = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:ListBucket'],
                'Resource': [dcp_bucket_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:GetObject'],
                'Resource': [dcp_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:ListBucket'],
                'Resource': [dcp_bucket_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:PutObject'],
                'Resource': [dcp_logs_resource1 + '*'],
                'Effect': 'Allow'
            }
        ]
    }
    user_policy_statments_allow_all = [
        {'Action': 's3:*',
         'Resource': '*',
         'Effect': 'Allow'
         }
    ]
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key,
                              dcp_bucket_policy_allow_aws_dcp_logs,
                              dcp_bucket, logs_key1, dcp_bucket_policy_allow_aws_dcp_logs,
                              user_policy_statments_allow_all)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == True
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == True
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == True
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == True
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 0

    # Test like readme with separate buckets, empty logs key
    dcp_bucket_policy_allow_aws_dcp = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:ListBucket'],
                'Resource': [dcp_bucket_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:GetObject'],
                'Resource': [dcp_resource],
                'Effect': 'Allow'
            }
        ]
    }
    logs_bucket_policy_allow_aws_logs_bucket = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:ListBucket'],
                'Resource': [logs_bucket_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:PutObject'],
                'Resource': [logs_resource1 + '*'],
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, dcp_bucket_policy_allow_aws_dcp,
                              logs_bucket, logs_key1, logs_bucket_policy_allow_aws_logs_bucket,
                              user_policy_statments_allow_all)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == True
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == True
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == True
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == True
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 0

    # Test like readme with separate buckets, empty logs key
    logs_bucket_policy_allow_aws_logs_bucket_key = {
        'Statement': [
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:ListBucket'],
                'Resource': [logs_bucket_resource],
                'Effect': 'Allow'
            },
            {
                'Principal': {
                    'AWS': [aws_account_arn],
                },
                'Action': ['s3:PutObject'],
                'Resource': [logs_resource2 + '*'],
                'Effect': 'Allow'
            }
        ]
    }
    checker = S3PolicyChecker(aws_account_arn, user_account_arn, dcp_bucket, dcp_key, dcp_bucket_policy_allow_aws_dcp,
                              logs_bucket, logs_key2, logs_bucket_policy_allow_aws_logs_bucket_key,
                              user_policy_statments_allow_all)
    checker.check()
    checker.report()
    assert checker.aws_can_list_dcp_bucket == True
    assert checker.aws_cannot_list_dcp_bucket == False
    assert checker.aws_can_get_dcp == True
    assert checker.aws_cannot_get_dcp == False
    assert checker.user_can_list_dcp_bucket == True
    assert checker.user_cannot_list_dcp_bucket == False
    assert checker.user_can_put_dcp == True
    assert checker.user_cannot_put_dcp == False

    assert checker.aws_can_list_logs_bucket == True
    assert checker.aws_cannot_list_logs_bucket == False
    assert checker.aws_can_put_logs == True
    assert checker.aws_cannot_put_logs == False
    assert checker.user_can_list_logs_bucket == True
    assert checker.user_cannot_list_logs_bucket == False
    assert checker.user_can_get_logs == True
    assert checker.user_cannot_get_logs == False
    assert checker.num_errors == 0


if __name__ == '__main__':
    num_errors = 0

    parser = argparse.ArgumentParser(description=description, formatter_class=argparse.RawDescriptionHelpFormatter)

    parser.add_argument('--dcp-bucket', action='store', required=True, help='S3 bucket where DCP is stored')
    parser.add_argument('--dcp-key', action='store', required=True, help='DCP path in S3 bucket')
    parser.add_argument('--logs-bucket', action='store', required=True,
                        help='S3 bucket where AFI creation logs will be stored')
    parser.add_argument('--logs-key', action='store', required=True, help='DCP path in S3 bucket')
    parser.add_argument('--debug', action='store_true', required=False, help='Enable debug messages')
    parser.add_argument('--test', action='store_true', required=False, help='Run tests')

    args = parser.parse_args()

    logging_level = logging.INFO
    if (args.debug):
        logging_level = logging.DEBUG

    # logging_format = '%(levelname)s:%(asctime)s:%(filename)s,%(lineno)s: %(message)s'
    logging_format = '%(levelname)s: %(message)s'

    logger.setLevel(logging_level)

    fh = logging.StreamHandler()

    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)
    fh.setFormatter(formatter)
    logger.addHandler(fh)

    if args.test:
        test()
        logger.info("Tests passed")
        sys.exit(0)

    # Validate arguments
    if re.search(r'/', args.dcp_bucket):
        logger.error("Invalid DCP bucket name. Cannot contain '/' characters. Path should be in the key.")
        sys.exit(2)
    if re.search(r'/', args.logs_bucket):
        logger.error("Invalid logs bucket name. Cannot contain '/' characters. Path should be in the key.")
        sys.exit(2)

    dcp_bucket_resource = 'arn:aws:s3:::{0}'.format(args.dcp_bucket)
    dcp_resource = 'arn:aws:s3:::{0}/{1}'.format(args.dcp_bucket, args.dcp_key)
    logs_bucket_resource = 'arn:aws:s3:::{0}'.format(args.logs_bucket)
    # logs_key should begin and end in a /
    # logs_key should end in a /
    if args.logs_key == '':
        args.logs_key = '/'
    else:
        if args.logs_key[0] != '/':
            args.logs_key = '/' + args.logs_key
        if args.logs_key[-1] != '/':
            args.logs_key += '/'
    logs_resource = 'arn:aws:s3:::{0}{1}'.format(args.logs_bucket, args.logs_key)

    iam = boto3.client('iam')

    sts = boto3.client('sts')
    response = sts.get_caller_identity()
    logger.debug("Called by:")
    logger.debug(pp.pformat(response))
    user_account = response['Account']
    user_account_arn = response['Arn']
    user_id = response['UserId']
    logger.debug("User arn={0}".format(user_account_arn))

    # Get all policy statements for the user
    user_policy_statements = []
    arn_fields = user_account_arn.split(':')
    principal = arn_fields[5]
    matches = re.match('^(assumed-role|user)/(.+)', principal)
    if matches:
        user_type = matches.group(1)
        if user_type == 'assumed-role':
            role = matches.group(2)
            role_fields = role.split('/')
            role_name = role_fields[0]
            logger.debug("Assumed role={0}".format(role_name))
            # role_response = iam.get_role(RoleName = role_name)
            response = iam.list_attached_role_policies(RoleName=role_name)
            for attached_policy_info in response['AttachedPolicies']:
                policy_name = attached_policy_info['PolicyName']
                policy_arn = attached_policy_info['PolicyArn']
                policy_response = iam.get_policy(PolicyArn=attached_policy_info['PolicyArn'])
                policy_version = policy_response['Policy']['DefaultVersionId']
                policy_details = iam.get_policy_version(PolicyArn=policy_arn, VersionId=policy_version)
                policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve inline policies
            response = iam.list_role_policies(RoleName=role_name)
            for policy_name in response['PolicyNames']:
                policy_statement = iam.get_role_policy(RoleName=role_name, PolicyName=policy_name)['PolicyDocument'][
                    'Statement']
                user_policy_statements.extend(policy_statement)
        elif user_type == 'user':
            user_name = matches.group(2)
            logger.debug("User name={0}".format(user_name))
            response = iam.list_attached_user_policies(UserName=user_name)
            for attached_policy_info in response['AttachedPolicies']:
                policy_name = attached_policy_info['PolicyName']
                logger.debug("Attached policy: {0}".format(policy_name))
                policy_arn = attached_policy_info['PolicyArn']
                policy_response = iam.get_policy(PolicyArn=attached_policy_info['PolicyArn'])
                policy_version = policy_response['Policy']['DefaultVersionId']
                policy_details = iam.get_policy_version(PolicyArn=policy_arn, VersionId=policy_version)
                policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve inline policies
            response = iam.list_user_policies(UserName=user_name)
            for policy_name in response['PolicyNames']:
                logger.debug("Inline policy: {0}".format(policy_name))
                policy_statement = iam.get_user_policy(UserName=user_name, PolicyName=policy_name)['PolicyDocument'][
                    'Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve groups that user belongs to and get their policies
            response = iam.list_groups_for_user(UserName=user_name)
            for group_info in response['Groups']:
                group_name = group_info['GroupName']
                group_arn = group_info['Arn']
                logger.debug("User belongs to group: {0}".format(group_name))
                response = iam.list_attached_group_policies(GroupName=group_name)
                for attached_policy_info in response['AttachedPolicies']:
                    policy_name = attached_policy_info['PolicyName']
                    policy_arn = attached_policy_info['PolicyArn']
                    logger.debug("{0} attached policy: {1}".format(group_name, policy_name))
                    policy_response = iam.get_policy(PolicyArn=attached_policy_info['PolicyArn'])
                    policy_version = policy_response['Policy']['DefaultVersionId']
                    policy_details = iam.get_policy_version(PolicyArn=policy_arn, VersionId=policy_version)
                    policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                    user_policy_statements.extend(policy_statement)
                # Retrieve inline policies for group
                response = iam.list_group_policies(GroupName=group_name)
                for policy_name in response['PolicyNames']:
                    logger.debug("{0} inline policy: {1}".format(policy_name))
                    policy_statement = \
                    iam.get_group_policy(GroupName=group_name, PolicyName=policy_name)['PolicyDocument']['Statement']
                    user_policy_statements.extend(policy_statement)

    s3 = boto3.client('s3')
    try:
        response = s3.get_bucket_policy(Bucket=args.dcp_bucket)
        dcp_bucket_policy = json.loads(response['Policy'])
        logger.debug("The S3 bucket policy of {0} is:".format(args.dcp_bucket))
        logger.debug(pp.pformat(dcp_bucket_policy))
    except:
        num_errors += 1
        logger.info(
            "Couldn't get the bucket policy for {0}.\nEither the bucket policy doesn't exist or you don't have permission to access the bucket policy.".format(
                args.dcp_bucket))
        dcp_bucket_policy = None

    # If the logs are going into a different bucket then get the policy for the logs bucket.
    if args.logs_bucket == args.dcp_bucket:
        logs_bucket_policy = dcp_bucket_policy
    else:
        try:
            response = s3.get_bucket_policy(Bucket=args.logs_bucket)
            logs_bucket_policy = json.loads(response['Policy'])
            logger.debug("The S3 bucket policy of {0} is:".format(args.logs_bucket))
            logger.debug(pp.pformat(logs_bucket_policy))
        except:
            num_errors += 1
            logger.info(
                "Couldn't get the bucket policy for {0}.\nEither the bucket policy doesn't exist or you don't have permission to access the bucket policy.".format(
                    args.logs_bucket))
            logs_bucket_policy = None

    checker = S3PolicyChecker(aws_account_arn, user_account_arn, args.dcp_bucket, args.dcp_key, dcp_bucket_policy,
                              args.logs_bucket, args.logs_key, logs_bucket_policy, user_policy_statements)
    num_errors += checker.check()
    checker.report()

    if num_errors:
        logger.error("Failed")
        sys.exit(2)
    logger.info("Passed")
    sys.exit(0)
