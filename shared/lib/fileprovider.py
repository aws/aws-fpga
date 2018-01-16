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

# External Modules
from git import Git
import logging
import os
from os.path import basename, dirname, realpath, relpath
import re
import sys
import traceback

try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source shared/tests/bin/setup_test_env.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class FileProvider(object):
    '''
    Find all files starting at a directory in a git repo.
    '''
    def __init__(self,):
        # All exclude paths will be relative to the repo directory.
        self.repo_dir = aws_fpga_test_utils.get_git_repo_root(dirname(realpath(__file__)))
        self.git = Git(self.repo_dir)

        self.exclude_files = []
        self.exclude_file_regexps = []

        self.exclude_paths = []
        self.exclude_path_regexps = []

    def set_exclude_files(self, files):
        self.exclude_files = files
        self.exclude_file_regexps = []
        for file in files:
            self.exclude_file_regexps.append(re.compile(file))

    def set_exclude_paths(self, paths):
        self.exclude_paths = paths
        self.exclude_path_regexps = []
        for path in paths:
            self.exclude_path_regexps.append(re.compile(path))

    def get_files(self, directory_to_search):
        directory_to_search = os.path.join(self.repo_dir, directory_to_search)
        if not os.path.exists(directory_to_search):
            logger.error("Directory doesn't exist: {}".format(directory_to_search))
            return None

        file_list = []

        for root, dirs, files in os.walk(directory_to_search, topdown=True):
            relative_root = relpath(root, self.repo_dir)

            # Skip excluded paths
            excluded = False
            for exclude_path_re in self.exclude_path_regexps:
                if exclude_path_re.match(relative_root):
                    excluded = True
                    break;
            if excluded:
                logger.debug("Excluded {}".format(relative_root))
                continue
            for dir in dirs:
                relative_dir = relpath(os.path.join(root, dir), self.repo_dir)
                excluded = False
                for exclude_path_re in self.exclude_path_regexps:
                    if exclude_path_re.match(relative_dir):
                        excluded = True
                        break;
                if excluded:
                    logger.debug("Excluded {}".format(relative_dir))
                    dirs.remove(dir)
                    continue

            # Exclude files
            for filename in files:
                relative_filename = os.path.join(relative_root, filename)
                # Ignore files not in the repo
                rval = self.git.ls_files(relative_filename)
                if not rval:
                    logger.debug("Excluded {}".format(relative_filename))
                    continue
                excluded = False
                for exclude_file_re in self.exclude_file_regexps:
                    if exclude_file_re.match(relative_filename):
                        excluded = True
                        break
                if excluded:
                    logger.debug("Excluded {}".format(relative_filename))
                    continue
                file_list.append(relative_filename)

        return file_list
