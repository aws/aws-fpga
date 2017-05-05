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
import logging
import sys
import os
from fileprovider import FileProvider

logger = logging.getLogger('logger')

description = '''This script checks all files within the repository for license headers.
It lists out all files that don't comply and exits with an error code 2.
'''

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=description, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--dir', action='store', required=False, default=os.path.abspath(__file__) + "/../../../" ,help='Directory to check for the headers')
    parser.add_argument('--debug', action='store_true', required=False, help='Enable debug messages')

    args = parser.parse_args()

    logging_level = logging.INFO
    if args.debug:
        logging_level = logging.DEBUG

    logging_format = '%(levelname)s: %(message)s'

    fh = logging.StreamHandler()
    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)

    logger.setLevel(logging_level)
    fh.setFormatter(formatter)
    logger.addHandler(fh)

    file_provider = FileProvider(args.dir)

    logger.info("Checking path: " + os.path.abspath(args.dir))
    hdk_file_path_list = file_provider.get_files()

    # Start with a simple string to check
    string_to_check = 'Amazon FPGA Hardware Development Kit'
    files_with_bad_headers = []

    for file_path in hdk_file_path_list:
        f = open(file_path, 'r')
        lines = f.read()
        answer = lines.find(string_to_check)

        if answer == -1:
            files_with_bad_headers.append(file_path)

    if files_with_bad_headers:
        logger.error("Following files didn't have the correct header: ")
        logger.error(files_with_bad_headers)
        sys.exit(2)
    else:
        logger.info("All files seem compliant")
        sys.exit(0)
