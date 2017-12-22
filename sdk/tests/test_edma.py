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

from __future__ import print_function
import logging
import os
from os.path import dirname, realpath
import pytest
import subprocess
import sys
import traceback
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source sdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestEdma(AwsFpgaTestBase):
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

        AwsFpgaTestBase.assert_sdk_setup()

        assert AwsFpgaTestBase.running_on_f1_instance(), 'This test must be run on an F1 instance.'
        return

    def test_unittest(self):
        (agfi, afi) = self.get_agfi_from_readme('cl_dram_dma')
        self.fpga_load_local_image(agfi, 0)
        aws_fpga_test_utils.install_edma_driver()
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_unit_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0

    def test_perftest(self):
        (agfi, afi) = self.get_agfi_from_readme('cl_dram_dma')
        self.fpga_load_local_image(agfi, 0)
        aws_fpga_test_utils.install_edma_driver()
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_perf_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0
