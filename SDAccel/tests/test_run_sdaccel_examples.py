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

Call using ```pytest test_run_sdaccel_examples.py```

See TESTING.md for details.
'''

import os
from os.path import dirname, realpath
import json
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source shared/bin/setup_test_env.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestRunSDAccelExamples(AwsFpgaTestBase):
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
        AwsFpgaTestBase.assert_hdk_setup()
        AwsFpgaTestBase.assert_sdaccel_setup()

        return

    def test_sw_emu(self, examplePath):
        self.runner(examplePath=examplePath, target="sw_emu", check=True)

    def test_hw_emu(self, examplePath):
        self.runner(examplePath=examplePath, target="hw_emu", check=True)

    def test_hw_build(self, examplePath):
        self.runner(examplePath=examplePath, target="hw", check=False)

    def runner(self, examplePath, target, clean=True, check=True):

        full_example_path = self.WORKSPACE + "/" + examplePath
        assert os.path.exists(full_example_path), logger.error("SDAccel Example path={} does not exist".format(examplePath))

        logger.info("SDAccel Example path={}".format(examplePath))
        os.chdir(full_example_path)

        if clean:
            (rc, stdout_lines, stderr_lines) = self.run_cmd("make clean")
            assert rc == 0, "SDAccel build failed while cleaning with rc={}".format(rc)

        check_string = ""
        if check:
            check_string = "check"

        (rc, stdout_lines, stderr_lines) = self.run_cmd("make {0} TARGETS={1} DEVICES={2} all".format(check_string, target, os.environ['AWS_PLATFORM']))
        assert rc == 0, "SDAccel build failed with rc={}".format(rc)

        return
