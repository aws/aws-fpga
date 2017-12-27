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

Call using ```pytest test_md_links.py```

See TESTING.md for details.
'''

from __future__ import print_function
import os
from os.path import dirname, realpath
import pytest
import sys
import traceback
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh or shared/tests/bin/setup_test_env*.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestMdLinks(AwsFpgaTestBase):
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

    def test_md_links(self):
        cmd = self.test_dir + "/bin/check_md_links.py"
        cmd += " --exclude SDAccel/examples/xilinx"
        # This is a valid link but sometimes it 404s
        cmd += " --ignore-url https://docs.pytest.org/en/latest/"
        (rc, stdout, stderr) = self.run_cmd(cmd, echo=True)
        assert rc == 0
