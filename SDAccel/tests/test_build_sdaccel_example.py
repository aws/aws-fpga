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

Call using ```pytest test_build_sdaccel_examples.py```

See TESTING.md for details.
'''

from __future__ import print_function
import os
from os.path import dirname, realpath, basename
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

class TestBuildSDAccelExample(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

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

    def test_sw_emu(self, examplePath, rteName, xilinxVersion):
        target = "sw_emu"
        self.base_test(examplePath=examplePath, target=target, rteName=rteName, xilinxVersion=xilinxVersion, check=True)

    def test_hw_emu(self, examplePath, rteName, xilinxVersion):
        target = "hw_emu"
        self.base_test(examplePath=examplePath, target=target, rteName=rteName, xilinxVersion=xilinxVersion, check=True)

    def test_hw_build(self, examplePath, rteName, xilinxVersion):
        target = "hw"
        self.base_test(examplePath=examplePath, target=target, rteName=rteName, xilinxVersion=xilinxVersion, check=False)

    def check_build(self, examplePath, target):

        xclbin_path = self.get_sdaccel_xclbin_dir(examplePath)

        logger.info("Checking if SDAccel Example xclbin path={} exists".format(xclbin_path))
        assert os.path.exists(xclbin_path), "SDAccel Example xclbinpath={} does not exist".format(xclbin_path)

        logger.info("Checking that a non zero size xclbin file exists in {}".format(xclbin_path))
        xclbin = self.assert_non_zero_file(os.path.join(xclbin_path, "*.{}.*.xclbin".format(target)))
        logger.info("xclbin: {}".format(xclbin))

        return xclbin

    def base_test(self, examplePath, target, rteName, xilinxVersion, clean=True, check=True):

        full_example_path = self.get_sdaccel_example_fullpath(examplePath=examplePath)
        logger.info("SDAccel Example path={}".format(full_example_path))

        assert os.path.exists(full_example_path), "SDAccel Example path={} does not exist".format(full_example_path)

        os.chdir(full_example_path)

        if clean:
            (rc, stdout_lines, stderr_lines) = self.run_cmd("make clean")
            assert rc == 0, "SDAccel build failed while cleaning with rc={}".format(rc)

        check_string = ""
        if check:
            check_string = "check"

        (rc, stdout_lines, stderr_lines) = self.run_cmd("make {0} TARGETS={1} DEVICES={2} all".format(check_string, target, os.environ['AWS_PLATFORM']))
        assert rc == 0, "SDAccel build failed with rc={}".format(rc)

        # Check for non zero xclbin
        xclbin = self.check_build(examplePath=examplePath, target=target)

        xclbin_key = os.path.join(self.get_sdaccel_example_s3_xclbin_tag(examplePath=examplePath, target=target, rteName=rteName, xilinxVersion=xilinxVersion), basename(xclbin))

        logger.info("Uploading xclbin to {}".format(os.path.join(self.s3_bucket, xclbin_key)))
        self.s3_client().upload_file(xclbin, self.s3_bucket, xclbin_key)

        return
