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
#import os
import pprint
import re
import sys

logger = logging.getLogger('logger')

pp = pprint.PrettyPrinter(indent = 4)

aws_account = '365015490807'
aws_account_arn = 'arn:aws:iam::{}:root'.format(aws_account)

if __name__ == '__main__':
    num_errors = 0
    
    parser = argparse.ArgumentParser()
    
    parser.add_argument('--dcp-bucket', action = 'store', required = True, help = 'S3 bucket where DCP is stored')
    parser.add_argument('--dcp-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--logs-bucket', action = 'store', required = True, help = 'S3 bucket where AFI creation logs will be stored')
    parser.add_argument('--logs-key', action = 'store', required = True, help = 'DCP path in S3 bucket')
    parser.add_argument('--debug', action = 'store_true', required = False, help = 'Enable debug messages')
    
    args = parser.parse_args()
    
    dcp_bucket_resource = 'arn:aws:s3:::{}'.format(args.dcp_bucket)
    dcp_resource = 'arn:aws:s3:::{}/{}'.format(args.dcp_bucket, args.dcp_key)
    logs_bucket_resource = 'arn:aws:s3:::{}'.format(args.logs_bucket)
    logs_resource = 'arn:aws:s3:::{}/{}'.format(args.logs_bucket, args.logs_key)
    
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
    except:
        num_errors += 1
        logger.error("Couldn't get the bucket policy for {}.\nEither the bucket doesn't exist or you don't have permission to access the bucket policy.".format(args.dcp_bucket))
        raise
    logger.debug("The S3 bucket policy of {} is:".format(args.dcp_bucket))
    policy = json.loads(response['Policy'])
    logger.debug(pp.pformat(policy))
    
    # Check for required permissions for user and AWS account
    aws_can_list_dcp_bucket = False
    aws_cannot_list_dcp_bucket = False
    aws_can_get_dcp = False
    aws_cannot_get_dcp = False
    aws_can_put_logs = False
    aws_cannot_put_logs = False
    user_can_list_dcp_bucket = False
    user_cannot_list_dcp_bucket = False
    user_can_put_dcp = False
    user_cannot_put_dcp = False
    user_can_get_logs = False
    user_cannot_get_logs = False
    for statement in policy['Statement']:
        principals = statement['Principal']['AWS']
        if not isinstance(principals, list):
            principals = [principals]
        actions = statement['Action']
        if not isinstance(actions, list):
            actions = [ actions ]
        resources = statement['Resource']
        if not isinstance(resources, list):
            resources = [ resources ]
        effect = statement['Effect']
        for principal in principals:
            principal = re.sub(r'\*', '.*', principal)
            if re.match(principal, aws_account_arn):
                logger.debug("Found a policy for AWS F1 account:\n{}".format(pp.pformat(statement)))
                for resource in resources:
                    resource = re.sub(r'\*', '.*', resource)
                    if re.match(resource, dcp_bucket_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:ListBucket'):
                                if effect == 'Allow':
                                    aws_can_list_dcp_bucket = True
                                    logger.debug("Allows AWS to list the DCP bucket")
                                else:
                                    aws_cannot_list_dcp_bucket = True
                                    logger.debug("Prevents AWS from listing the DCP bucket")
                    if re.match(resource, dcp_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:GetObject'):
                                if effect == 'Allow':
                                    aws_can_get_dcp = True
                                    logger.debug("Allows AWS to get the DCP")
                                else:
                                    aws_cannot_get_dcp = True
                                    logger.debug("Prevents AWS from getting the DCP")
                    if re.match(resource, logs_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:PutObject'):
                                if effect == 'Allow':
                                    aws_can_put_logs = True
                                    logger.debug("Allows AWS to write the AFI creation logs")
                                else:
                                    aws_cannot_put_logs = True
                                    logger.debug("Prevents AWS from writing the AFI creation logs")
            if re.match(principal, user_account_arn):
                logger.debug("Found a policy for user account")
                logger.debug(pp.pformat(statement))
                for resource in resources:
                    resource = re.sub(r'\*', '.*', resource)
                    if re.match(resource, dcp_bucket_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:ListBucket'):
                                if effect == 'Allow':
                                    user_can_list_dcp_bucket = True
                                else:
                                    user_cannot_list_dcp_bucket = True
                    if re.match(resource, dcp_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:PutObject'):
                                if effect == 'Allow':
                                    user_can_put_dcp = True
                                else:
                                    user_cannot_put_dcp = True
                    if re.match(resource, logs_resource):
                        for action in actions:
                            action = re.sub(r'\*', '.*', action)
                            if re.match(action, 's3:GetObject'):
                                if effect == 'Allow':
                                    user_can_get_logs = True
                                else:
                                    user_cannot_get_logs = True
    
    # Test user's or role's permissions from IAM
    for statement in user_policy_statements:
        # The principal is implicit because these are policies associated with the user or role
        actions = statement['Action']
        if not isinstance(actions, list):
            actions = [ actions ]
        resources = statement['Resource']
        if not isinstance(resources, list):
            resources = [ resources ]
        effect = statement['Effect']
        for resource in resources:
            resource = re.sub(r'\*', '.*', resource)
            if re.match(resource, dcp_bucket_resource):
                for action in actions:
                    action = re.sub(r'\*', '.*', action)
                    if re.match(action, 's3:ListBucket'):
                        if effect == 'Allow':
                            user_can_list_dcp_bucket = True
                        else:
                            user_cannot_list_dcp_bucket = True
            if re.match(resource, dcp_resource):
                for action in actions:
                    action = re.sub(r'\*', '.*', action)
                    if re.match(action, 's3:PutObject'):
                        if effect == 'Allow':
                            user_can_put_dcp = True
                        else:
                            user_cannot_put_dcp = True
            if re.match(resource, logs_resource):
                for action in actions:
                    action = re.sub(r'\*', '.*', action)
                    if re.match(action, 's3:GetObject'):
                        if effect == 'Allow':
                            user_can_get_logs = True
                        else:
                            user_cannot_get_logs = True
        
    if not aws_can_list_dcp_bucket or aws_cannot_list_dcp_bucket:
        num_errors += 1
        logger.error("AWS can't list the DCP bucket")
    if not aws_can_get_dcp or aws_cannot_get_dcp:
        num_errors += 1
        logger.error("AWS can't read the DCP")
    if not aws_can_put_logs or aws_cannot_put_logs:
        num_errors += 1
        logger.error("AWS can't write logs")
    if not user_can_list_dcp_bucket or user_cannot_list_dcp_bucket:
        num_errors += 1
        logger.error("User can't list the DCP bucket")
    if not user_can_put_dcp or user_cannot_put_dcp:
        num_errors += 1
        logger.error("User can't write the DCP")
    if not user_can_get_logs or user_cannot_get_logs:
        num_errors += 1
        logger.error("User can't get logs")
        
    if num_errors:
        logger.error("Failed")
        sys.exit(2)
    logger.info("Passed")
    sys.exit(0)
