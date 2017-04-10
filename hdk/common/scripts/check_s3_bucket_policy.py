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
#from botocore.exceptions import ClientError
import json
import logging
#import os
import pprint
import re
import sys

logger = logging.getLogger('logger')

pp = pprint.PrettyPrinter(indent = 4)

aws_account = '365015490807'
aws_account_arn = 'arn:aws:iam::{}:root'.format(aws_account)

description = '''Checks S3 permissions required for create-fpga-image.

This program uses the AWS CLI and requires credentials to be configured.
See $AWS_FPGA_REPO_DIR/README.md for instructions to configure your credentials.
'''

# Convert the policy pattern to a regular expression
# Escape '.' and replace * with '.*'
# Append a '$' so an exact match is required
def escape_policy_pattern(policy_pattern):
    policy_pattern = re.sub(r'\.', '\.', policy_pattern)
    policy_pattern = re.sub(r'\*', '.*', policy_pattern)
    policy_pattern += '$'
    return policy_pattern

def process_policy_statement(statement):
    principals_re = []
    if 'Principal' in statement:
        principals = statement['Principal']['AWS']
        if not isinstance(principals, list):
            principals = [principals]
        for principal in principals:
            principal = re.sub(r'\.', '\.', principal)
            principal = re.sub(r'\*', '.*', principal)
            principal += '$'
            principals_re.append(principal)
    actions = statement['Action']
    if not isinstance(actions, list):
        actions = [ actions ]
    actions_re = []
    for action in actions:
        action = re.sub(r'\.', '\.', action)
        action = re.sub(r'\*', '.*', action)
        action += '$'
        actions_re.append(action)
    resources = statement['Resource']
    if not isinstance(resources, list):
        resources = [ resources ]
    resources_re = []
    for resource in resources:
        resource = re.sub(r'\.', '\.', resource)
        resource = re.sub(r'\*', '.*', resource)
        resource += '$'
        resources_re.append(resource)
    effect = statement['Effect']
    return (principals_re, actions_re, resources_re, effect)
    
if __name__ == '__main__':
    num_errors = 0
    
    parser = argparse.ArgumentParser(description=description, formatter_class=argparse.RawDescriptionHelpFormatter)
    
    parser.add_argument('--dcp-bucket', action = 'store', required = True, help = 'S3 bucket where DCP is stored')
    parser.add_argument('--dcp-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--logs-bucket', action = 'store', required = True, help = 'S3 bucket where AFI creation logs will be stored')
    parser.add_argument('--logs-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--debug', action = 'store_true', required = False, help = 'Enable debug messages')
    
    args = parser.parse_args()
    
    logging_level = logging.INFO
    if (args.debug):
        logging_level = logging.DEBUG

    #logging_format = '%(levelname)s:%(asctime)s:%(filename)s,%(lineno)s: %(message)s'
    logging_format = '%(levelname)s: %(message)s'

    logger.setLevel(logging_level)

    fh = logging.StreamHandler()

    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)
    fh.setFormatter(formatter)
    logger.addHandler(fh)
    
    # Validate arguments
    if re.search(r'/', args.dcp_bucket):
        logger.error("Invalid DCP bucket name. Cannot contain '/' characters. Path should be in the key.")
        sys.exit(2)
    if re.search(r'/', args.logs_bucket):
        logger.error("Invalid logs bucket name. Cannot contain '/' characters. Path should be in the key.")
        sys.exit(2)
    
    dcp_bucket_resource = 'arn:aws:s3:::{}'.format(args.dcp_bucket)
    dcp_resource = 'arn:aws:s3:::{}/{}'.format(args.dcp_bucket, args.dcp_key)
    logs_bucket_resource = 'arn:aws:s3:::{}'.format(args.logs_bucket)
    # logs_key should begin and end in a /
    # logs_resource should end in a /
    if args.logs_key == '':
        args.logs_key = '/'
    else:
        if args.logs_key[0] != '/':
            args.logs_key = '/' + args.logs_key
        if args.logs_key[-1] != '/':
            args.logs_key += '/'
    logs_resource = 'arn:aws:s3:::{}{}'.format(args.logs_bucket, args.logs_key)
    
    iam = boto3.client('iam')
    
    sts = boto3.client('sts')
    response = sts.get_caller_identity()
    logger.debug("Called by:")
    logger.debug(pp.pformat(response))
    user_account = response['Account']
    user_account_arn = response['Arn']
    user_id = response['UserId']
    logger.debug("User arn={}".format(user_account_arn))
    
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
            logger.debug("Assumed role={}".format(role_name))
            #role_response = iam.get_role(RoleName = role_name)
            response = iam.list_attached_role_policies(RoleName = role_name)
            for attached_policy_info in response['AttachedPolicies']:
                policy_name = attached_policy_info['PolicyName']
                policy_arn = attached_policy_info['PolicyArn']
                policy_response = iam.get_policy(PolicyArn = attached_policy_info['PolicyArn'])
                policy_version = policy_response['Policy']['DefaultVersionId']
                policy_details = iam.get_policy_version(PolicyArn = policy_arn, VersionId = policy_version)
                policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve inline policies
            response = iam.list_role_policies(RoleName = role_name)
            for policy_name in response['PolicyNames']:
                policy_statement = iam.get_role_policy(RoleName = role_name, PolicyName = policy_name)['PolicyDocument']['Statement']
                user_policy_statements.extend(policy_statement)
        elif user_type == 'user':
            user_name = matches.group(2)
            logger.debug("User name={}".format(user_name))
            response = iam.list_attached_user_policies(UserName = user_name)
            for attached_policy_info in response['AttachedPolicies']:
                policy_name = attached_policy_info['PolicyName']
                logger.debug("Attached policy: {}".format(policy_name))
                policy_arn = attached_policy_info['PolicyArn']
                policy_response = iam.get_policy(PolicyArn = attached_policy_info['PolicyArn'])
                policy_version = policy_response['Policy']['DefaultVersionId']
                policy_details = iam.get_policy_version(PolicyArn = policy_arn, VersionId = policy_version)
                policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve inline policies
            response = iam.list_user_policies(UserName = user_name)
            for policy_name in response['PolicyNames']:
                logger.debug("Inline policy: {}".format(policy_name))
                policy_statement = iam.get_user_policy(UserName = user_name, PolicyName = policy_name)['PolicyDocument']['Statement']
                user_policy_statements.extend(policy_statement)
            # Retrieve groups that user belongs to and get their policies
            response = iam.list_groups_for_user(UserName = user_name)
            for group_info in response['Groups']:
                group_name = group_info['GroupName']
                group_arn = group_info['Arn']
                logger.debug("User belongs to group: {}".format(group_name))
                response = iam.list_attached_group_policies(GroupName = group_name)
                for attached_policy_info in response['AttachedPolicies']:
                    policy_name = attached_policy_info['PolicyName']
                    policy_arn = attached_policy_info['PolicyArn']
                    logger.debug("{} attached policy: {}".format(group_name, policy_name))
                    policy_response = iam.get_policy(PolicyArn = attached_policy_info['PolicyArn'])
                    policy_version = policy_response['Policy']['DefaultVersionId']
                    policy_details = iam.get_policy_version(PolicyArn = policy_arn, VersionId = policy_version)
                    policy_statement = policy_details['PolicyVersion']['Document']['Statement']
                    user_policy_statements.extend(policy_statement)
                # Retrieve inline policies for group
                response = iam.list_group_policies(GroupName = group_name)
                for policy_name in response['PolicyNames']:
                    logger.debug("{} inline policy: {}".format(policy_name))
                    policy_statement = iam.get_group_policy(GroupName = group_name, PolicyName = policy_name)['PolicyDocument']['Statement']
                    user_policy_statements.extend(policy_statement)
    
    s3 = boto3.client('s3')
    try:
        response = s3.get_bucket_policy(Bucket = args.dcp_bucket)
        dcp_bucket_policy = json.loads(response['Policy'])
        logger.debug("The S3 bucket policy of {} is:".format(args.dcp_bucket))
        logger.debug(pp.pformat(dcp_bucket_policy))
    except:
        num_errors += 1
        logger.info("Couldn't get the bucket policy for {}.\nEither the bucket policy doesn't exist or you don't have permission to access the bucket policy.".format(args.dcp_bucket))
        dcp_bucket_policy = None
    
    # If the logs are going into a different bucket then get the policy for the logs bucket.
    if args.logs_bucket == args.dcp_bucket:
        logs_bucket_policy = dcp_bucket_policy
    else:
        try:
            response = s3.get_bucket_policy(Bucket = args.logs_bucket)
            logs_bucket_policy = json.loads(response['Policy'])
            logger.debug("The S3 bucket policy of {} is:".format(args.logs_bucket))
            logger.debug(pp.pformat(logs_bucket_policy))
        except:
            num_errors += 1
            logger.info("Couldn't get the bucket policy for {}.\nEither the bucket policy doesn't exist or you don't have permission to access the bucket policy.".format(args.logs_bucket))
            logs_bucket_policy = None
        
    # Check DCP bucket for required permissions for user and AWS account
    aws_can_list_dcp_bucket = False
    aws_cannot_list_dcp_bucket = False
    aws_can_get_dcp = False
    aws_cannot_get_dcp = False
    user_can_list_dcp_bucket = False
    user_cannot_list_dcp_bucket = False
    user_can_put_dcp = False
    user_cannot_put_dcp = False
    if dcp_bucket_policy:
        logger.debug("Checking DCP bucket permissions")
        for statement in dcp_bucket_policy['Statement']:
            (principals_re, actions_re, resources_re, effect) = process_policy_statement(statement)
            for principal_re in principals_re:
                if re.match(principal_re, aws_account_arn):
                    logger.debug("Found a policy for AWS F1 account:\n{}".format(pp.pformat(statement)))
                    for resource_re in resources_re:
                        if re.match(resource_re, dcp_bucket_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:ListBucket'):
                                    if effect == 'Allow':
                                        aws_can_list_dcp_bucket = True
                                        logger.debug("Allows AWS to list the DCP bucket")
                                    else:
                                        aws_cannot_list_dcp_bucket = True
                                        num_errors += 1
                                        logger.error("The following DCP bucket policy statement will prevent AWS from listing the DCP bucket:\n{}".format(pp.pformat(statement)))
                        if re.match(resource_re, dcp_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:GetObject'):
                                    if effect == 'Allow':
                                        aws_can_get_dcp = True
                                        logger.debug("Allows AWS to get the DCP")
                                    else:
                                        aws_cannot_get_dcp = True
                                        num_errors += 1
                                        logger.error("The following DCP bucket policy statement will prevent AWS from reading the DCP:\n{}".format(pp.pformat(statement)))
                if re.match(principal_re, user_account_arn):
                    logger.debug("Found a policy for user account")
                    logger.debug(pp.pformat(statement))
                    for resource_re in resources_re:
                        if re.match(resource_re, dcp_bucket_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:ListBucket'):
                                    if effect == 'Allow':
                                        user_can_list_dcp_bucket = True
                                        logger.debug("Allows you to list the DCP bucket")
                                    else:
                                        user_cannot_list_dcp_bucket = True
                                        num_errors += 1
                                        logger.error("The following DCP bucket policy statement will prevent you from listing the DCP bucket:\n{}".format(pp.pformat(statement)))
                        if re.match(resource_re, dcp_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:PutObject'):
                                    if effect == 'Allow':
                                        user_can_put_dcp = True
                                        logger.debug("Allows you to write the DCP")
                                    else:
                                        user_cannot_put_dcp = True
                                        num_errors += 1
                                        logger.error("The following DCP bucket policy statement will prevent you from writing the DCP:\n{}".format(pp.pformat(statement)))
    
    aws_can_list_logs_bucket = False
    aws_cannot_list_logs_bucket = False
    aws_can_put_logs = False
    aws_cannot_put_logs = False
    user_can_list_logs_bucket = False
    user_cannot_list_logs_bucket = False
    user_can_get_logs = False
    user_cannot_get_logs = False
    if logs_bucket_policy:
        # Check logs bucket for required permissions for user and AWS account
        logger.debug("Checking logs bucket permissions")
        for statement in logs_bucket_policy['Statement']:
            (principals_re, actions_re, resources_re, effect) = process_policy_statement(statement)
            for principal_re in principals_re:
                if re.match(principal_re, aws_account_arn):
                    logger.debug("Found a policy for AWS F1 account:\n{}".format(pp.pformat(statement)))
                    for resource_re in resources_re:
                        if re.match(resource_re, logs_bucket_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:ListBucket'):
                                    if effect == 'Allow':
                                        aws_can_list_logs_bucket = True
                                        logger.debug("Allows AWS to list the logs bucket")
                                    else:
                                        aws_cannot_list_logs_bucket = True
                                        num_errors += 1
                                        logger.error("The following logs bucket policy statement will prevent AWS from listing the logs bucket:\n{}".format(pp.pformat(statement)))
                        if re.match(resource_re, logs_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:PutObject'):
                                    if effect == 'Allow':
                                        aws_can_put_logs = True
                                        logger.debug("Allows AWS to write the AFI creation logs")
                                    else:
                                        aws_cannot_put_logs = True
                                        num_errors += 1
                                        logger.error("The following logs bucket policy statement will prevent AWS from writing the AFI creation logs:\n{}".format(pp.pformat(statement)))
                if re.match(principal_re, user_account_arn):
                    logger.debug("Found a policy for user account")
                    logger.debug(pp.pformat(statement))
                    for resource_re in resources_re:
                        if re.match(resource_re, logs_bucket_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:ListBucket'):
                                    if effect == 'Allow':
                                        user_can_list_logs_bucket = True
                                        logger.debug("Allows you to list the logs bucket")
                                    else:
                                        user_cannot_list_logs_bucket = True
                                        num_errors += 1
                                        logger.error("The following DCP bucket policy statement will prevent you from listing the logs bucket:\n{}".format(pp.pformat(statement)))
                        if re.match(resource_re, logs_resource):
                            for action_re in actions_re:
                                if re.match(action_re, 's3:GetObject'):
                                    if effect == 'Allow':
                                        user_can_get_logs = True
                                        logger.debug("Allows you to get the AFI creation logs.")
                                    else:
                                        user_cannot_get_logs = True
                                        num_errors += 1
                                        logger.error("The following logs bucket policy statement will prevent you from getting the AFI creation logs:\n{}".format(pp.pformat(statement)))
    
    # Test user's or role's permissions from IAM
    logger.debug("Checking user's permissions from IAM")
    for statement in user_policy_statements:
        # The principal is implicit because these are policies associated with the user or role
        (principals_re, actions_re, resources_re, effect) = process_policy_statement(statement)
        for resource_re in resources_re:
            if re.match(resource_re, dcp_bucket_resource):
                for action_re in actions_re:
                    if re.match(action_re, 's3:ListBucket'):
                        if effect == 'Allow':
                            user_can_list_dcp_bucket = True
                            logger.debug("Allows you to list the DCP bucket:\n{}".format(pp.pformat(statement)))
                        else:
                            user_cannot_list_dcp_bucket = True
                            num_errors += 1
                            logger.error("The following IAM policy statement will prevent you from listing the DCP bucket:\n{}".format(pp.pformat(statement)))
            if re.match(resource_re, dcp_resource):
                for action_re in actions_re:
                    if re.match(action_re, 's3:PutObject'):
                        if effect == 'Allow':
                            user_can_put_dcp = True
                            logger.debug("Allows you to write the DCP:\n{}".format(pp.pformat(statement)))
                        else:
                            user_cannot_put_dcp = True
                            num_errors += 1
                            logger.error("The following IAM policy statement will prevent you from writing the DCP:\n{}".format(pp.pformat(statement)))
            if re.match(resource_re, logs_bucket_resource):
                for action_re in actions_re:
                    if re.match(action_re, 's3:ListBucket'):
                        if effect == 'Allow':
                            user_can_list_logs_bucket = True
                            logger.debug("Allows you to list the logs bucket:\n{}".format(pp.pformat(statement)))
                        else:
                            user_cannot_list_logs_bucket = True
                            num_errors += 1
                            logger.error("The following IAM policy statement will prevent you from listing the logs bucket:\n{}".format(pp.pformat(statement)))
            if re.match(resource_re, logs_resource):
                for action_re in actions_re:
                    if re.match(action_re, 's3:GetObject'):
                        if effect == 'Allow':
                            user_can_get_logs = True
                            logger.debug("Allows you to get the AFI creation logs:\n{}".format(pp.pformat(statement)))
                        else:
                            user_cannot_get_logs = True
                            num_errors += 1
                            logger.error("The following IAM policy statement will prevent you from getting the AFI creation logs:\n{}".format(pp.pformat(statement)))
    
    extra_dcp_statements = []
    extra_logs_statements = []
    if not aws_can_list_dcp_bucket:
        num_errors += 1
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
                "Resource": "arn:aws:s3:::{dcp_bucket}"
            }}'''.format(aws_account=aws_account, dcp_bucket=args.dcp_bucket)
        logger.error('''AWS can't list the DCP bucket.
        
Add the following statement to the bucket policy for:
{dcp_bucket}
        '''.format(dcp_bucket=args.dcp_bucket) + statement_str)
        extra_dcp_statements.append(statement_str)
        
    if not aws_can_get_dcp:
        num_errors += 1
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
                "Resource": "arn:aws:s3:::{dcp_bucket}/{dcp_key}"
            }}
'''.format(aws_account=aws_account, dcp_bucket=args.dcp_bucket, dcp_key=args.dcp_key)
        logger.error('''AWS can't read the DCP.
        
Add the following statement to the bucket policy for:
{dcp_bucket}
        '''.format(dcp_bucket=args.dcp_bucket) + statement_str)
        statement = json.loads(statement_str)
        extra_dcp_statements.append(statement_str)
        
    if not user_can_list_dcp_bucket:
        num_errors += 1
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
                "Resource": "arn:aws:s3:::{dcp_bucket}"
            }}
'''.format(user_account_arn=user_account_arn, dcp_bucket=args.dcp_bucket)
        logger.error('''User can't list the DCP bucket
        
Add the following statement to the bucket policy for:
{dcp_bucket}
        '''.format(dcp_bucket=args.dcp_bucket) + statement_str)
        extra_dcp_statements.append(statement_str)
        
    if not user_can_put_dcp:
        num_errors += 1
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
                "Resource": "arn:aws:s3:::{dcp_bucket}/{dcp_key}"
            }}
'''.format(user_account_arn=user_account_arn, dcp_bucket=args.dcp_bucket, dcp_key=args.dcp_key)
        logger.error('''User can't write the DCP
        
Add the following statement to the bucket policy for:
{dcp_bucket}
        '''.format(dcp_bucket=args.dcp_bucket) + statement_str)
        extra_dcp_statements.append(statement_str)
        
    if not aws_can_list_logs_bucket and (args.logs_bucket != args.dcp_bucket):
        num_errors += 1
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
'''.format(aws_account=aws_account, logs_bucket=args.logs_bucket)
        logger.error('''AWS can't list the the logs bucket
        
Add the following statement to the bucket policy for:
{logs_bucket}
        '''.format(logs_bucket=args.logs_bucket) + statement_str)
        extra_logs_statements.append(statement_str)
        
    if not aws_can_put_logs:
        num_errors += 1
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
'''.format(aws_account=aws_account, logs_resource=logs_resource)
        logger.error('''AWS can't write the logs
        
Add the following statement to the bucket policy for:
{logs_bucket}
        '''.format(logs_bucket=args.logs_bucket) + statement_str)
        if args.logs_bucket == args.dcp_bucket:
            extra_dcp_statements.append(statement_str)
        else:
            extra_logs_statements.append(statement_str)
        
    if not user_can_get_logs:
        num_errors += 1
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
'''.format(user_account_arn=user_account_arn, logs_resource=logs_resource)
        logger.error('''User can't get logs
        
Add the following statement to the bucket policy for:
{logs_bucket}
        '''.format(logs_bucket=args.logs_bucket) + statement_str)
        if args.logs_bucket == args.dcp_bucket:
            extra_dcp_statements.append(statement_str)
        else:
            extra_logs_statements.append(statement_str)
    
    if num_errors:
        logger.error('''You need to provide AWS (Account ID: {aws_account}) the appropriate [read/write permissions](http://docs.aws.amazon.com/AmazonS3/latest/dev/example-walkthroughs-managing-access-example2.html) to your S3 buckets.

**NOTE**: *The AWS Account ID has changed, please ensure you are using the correct Account ID listed here.*

See $HDK_DIR/cl/examples/README.md'''.format(aws_account=aws_account))

    if len(extra_dcp_statements):
        if dcp_bucket_policy:
            logger.info("Add the following statements to the {} bucket policy:".format(args.dcp_bucket))
            for statement_str in extra_dcp_statements:
                logger.info(statement_str)
        else:
            logger.info("You currently don't have a bucket policy for {}".format(args.dcp_bucket))
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
                "Resource": "arn:aws:s3:::{dcp_bucket}"
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
                "Resource": "arn:aws:s3:::{dcp_bucket}/{dcp_key}"
            }}'''.format(aws_account=aws_account, dcp_bucket=args.dcp_bucket, dcp_key=args.dcp_key)
        if args.logs_bucket == args.dcp_bucket:
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
            }}'''.format(aws_account=aws_account, logs_resource=logs_resource)
        policy_str += '''
        ]
    }'''
        logger.info("The following bucket policy will resolve the problem:\n{}".format(policy_str))
        
    if (args.logs_bucket != args.dcp_bucket) and len(extra_logs_statements):
        if logs_bucket_policy:
            logger.info("Add the following statements to the {} bucket policy:".format(args.logs_bucket))
            for statement_str in extra_logs_statements:
                logger.info(statement_str)
        else:
            logger.info("You currently don't have a bucket policy for {}".format(args.logs_bucket))
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
                "Resource": "arn:aws:s3:::{logs_bucket}"
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
'''.format(aws_account=aws_account, logs_bucket=args.logs_bucket, logs_resource=logs_resource)
            logger.info("The following bucket policy will resolve the problem:\n{}".format(policy_str))

    if num_errors:
        logger.error("Failed")
        sys.exit(2)
    logger.info("Passed")
    sys.exit(0)
