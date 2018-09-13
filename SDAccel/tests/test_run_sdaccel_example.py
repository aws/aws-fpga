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

Call using ```pytest test_create_afi.py```

See TESTING.md for details.
'''

from __future__ import print_function
import boto3
import os
from os.path import basename, dirname, realpath
import pytest
import re
import sys
import traceback
import json
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source shared/bin/setup_test_env.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestRunSDAccelExample(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    Run the SDAccel example
    '''

    ADD_EXAMPLEPATH = True
    ADD_RTENAME = True
    ADD_XILINX_VERSION = True

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)

        AwsFpgaTestBase.assert_sdk_setup()
        AwsFpgaTestBase.assert_sdaccel_setup()

        return

    def teardown_method(self, test_method):
        aws_fpga_test_utils.remove_xdma_driver()

    def test_run_sdaccel_example(self, examplePath, rteName, xilinxVersion):

        os.chdir(self.get_sdaccel_example_fullpath(examplePath))

        (rc, stdout_lines, stderr_lines) = self.run_cmd("make exe")
        assert rc == 0

        em_run_cmd = self.get_sdaccel_example_run_cmd(examplePath)

        self.get_sdaccel_aws_xclbin_file(examplePath, rteName, xilinxVersion)

        run_cmd = "sudo -E /bin/bash -l -c \"source /opt/Xilinx/SDx/{}.rte.{}/setup.sh && {} \"".format(xilinxVersion, rteName, em_run_cmd)

        logger.info("Running cmd={}".format(run_cmd))
        (rc, stdout_lines, stderr_lines) = self.run_cmd(run_cmd)
        assert rc == 0


