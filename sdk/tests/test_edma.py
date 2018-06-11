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

        assert AwsFpgaTestBase.running_on_f1_instance(), "This test must be run on an F1 instance. Running on {}".format(aws_fpga_test_utils.get_instance_type())

        (cls.cl_dram_dma_agfi, cl_dram_dma_afi) = cls.get_agfi_from_readme('cl_dram_dma')

        cls.get_fio_dma_tools()
        return

    def setup_method(self, test_method):
        aws_fpga_test_utils.remove_all_drivers()

    def teardown_method(self, test_method):
        aws_fpga_test_utils.remove_all_drivers()

    def test_unittest(self):
        self.load_msix_workaround(slot=0)
        self.fpga_load_local_image(self.cl_dram_dma_agfi, 0)
        aws_fpga_test_utils.install_edma_driver()
        assert aws_fpga_test_utils.edma_driver_installed() == True
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_unit_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0

    def test_perftest(self):
        self.load_msix_workaround(slot=0)
        self.fpga_load_local_image(self.cl_dram_dma_agfi, 0)
        aws_fpga_test_utils.install_edma_driver()
        assert aws_fpga_test_utils.edma_driver_installed() == True
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_perf_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0

    @pytest.mark.skip(reason="Flaky. We Re-start tests after shell updates.")
    def test_fio_perf(self):
        # Build the driver so the fio script can install it.
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma && make".format(self.WORKSPACE), echo=True)
        assert rc == 0
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/tests/fio_dma_tools && sudo ./edma_perf.sh 1 0 {} {} {}".format(
            self.WORKSPACE, self.msix_agfi, self.cl_dram_dma_agfi, self.WORKSPACE), check=False, echo=True)
        if rc != 0:
            logger.error("FIO EDMA test failed")
            # Create some diagnostic information
            # Debug is problematic for intermittent problems because the instance is terminated when the tests finish.
            self.run_cmd("sudo fpga-describe-local-image-slots", check=False, echo=True)
            for slot in range(self.num_slots):
                self.run_cmd("sudo fpga-describe-local-image -S {} -M".format(slot), check=False, echo=True)
        assert rc == 0
