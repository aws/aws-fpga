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
'''
Pytest module:

Call using ```pytest test_find_sdaccel_examples.py```

See TESTING.md for details.
'''

from __future__ import print_function
import os
from os.path import dirname, realpath
import json
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source shared/bin/setup_test_env.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestFindSDAccelExamples(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    '''
    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)
        return

    def test_find_example_makefiles(self):

        assert os.path.exists(self.xilinx_sdaccel_examples_dir), "The Xilinx SDAccel example dir does not exist: {}".format(self.xilinx_sdaccel_examples_dir)
        assert os.listdir(self.xilinx_sdaccel_examples_dir) != [], "Xilinx SDAccel example submodule not cloned or does not exist"

        xilinx_examples_makefiles = []
        xilinx_sdaccel_example_map = {}

        for root, dirs, files in os.walk(self.xilinx_sdaccel_examples_dir):
            for file in files:
                if file.endswith('Makefile'):
                    makefile_path = root + "/Makefile"

                    # If the Makefile has a docs target, it's not the makefile we want to read
                    if 'docs:' not in open(makefile_path).read():
                        xilinx_examples_makefiles.append(root)

        assert len(xilinx_examples_makefiles) != 0, "Could not find any Xilinx SDAccel example in %s" % self.xilinx_sdaccel_examples_dir

        # Remove the workspace path so that the next node can reference this path directly
        # So we don't face cases like /workspace@3 ..
        xilinx_examples_makefiles = [os.path.relpath(full_path, self.WORKSPACE) for full_path in xilinx_examples_makefiles]

        for example_path in xilinx_examples_makefiles:

            example_test_class = example_path.replace('/', '__').capitalize()

            xilinx_sdaccel_example_map[example_test_class] = example_path

        with open(self.xilinx_sdaccel_examples_list_file, 'w') as outfile:
            json.dump(xilinx_sdaccel_example_map, outfile)

        assert os.path.getsize(self.xilinx_sdaccel_examples_list_file) > 0, "%s is a non zero file. We need to have some data in the file" % self.xilinx_sdaccel_examples_list_file
