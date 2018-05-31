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

        for slot in range(AwsFpgaTestBase.num_slots):
            AwsFpgaTestBase.load_msix_workaround(slot)

        cls.setup_fio_tools()

        return

    def setup_method(self, test_method):
        aws_fpga_test_utils.remove_all_drivers()

        for slot in range(AwsFpgaTestBase.num_slots):
            self.fpga_load_local_image(self.cl_dram_dma_agfi, slot)
            assert AwsFpgaTestBase.check_fpga_afi_loaded(self.cl_dram_dma_agfi, slot), "{} not loaded in slot {}".format(self.cl_dram_dma_agfi, slot)

    def teardown_method(self, test_method):
        aws_fpga_test_utils.remove_all_drivers()

        for slot in range(AwsFpgaTestBase.num_slots):
            AwsFpgaTestBase.fpga_clear_local_image(slot)

    @pytest.fixture(params=['poll','interrupt'])
    def driver_mode(self, request):
        return request.param

    def test_unittest(self, driver_mode):
        aws_fpga_test_utils.install_edma_driver(mode=driver_mode)
        assert aws_fpga_test_utils.edma_driver_installed() == True
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_unit_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0

    def test_perftest(self, driver_mode):

        aws_fpga_test_utils.install_edma_driver(mode=driver_mode)
        assert aws_fpga_test_utils.edma_driver_installed() == True
        (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/sdk/linux_kernel_drivers/edma/unit-test && ./run_perf_test.sh".format(self.WORKSPACE), echo=True)
        assert rc == 0

    def test_fio_dma_verify(self, driver_mode):
        aws_fpga_test_utils.install_edma_driver(mode=driver_mode)
        assert aws_fpga_test_utils.edma_driver_installed() == True

        (rc, stdout_lines, stderr_lines) = self.run_cmd("sudo {} {}".format(self.get_fio_tool_run_script(), self.get_fio_verify_script(driver='edma')), echo=True, check=False)
        if rc != 0:
            logger.error("FIO edma verify test failed")
            # Create some diagnostic information
            # Debug is problematic for intermittent problems because the instance is terminated when the tests finish.
            self.run_cmd("sudo fpga-describe-local-image-slots", check=False, echo=True)
            for slot in range(self.num_slots):
                self.run_cmd("sudo fpga-describe-local-image -S {} -M".format(slot), check=False, echo=True)
        assert rc == 0

    @pytest.mark.xfail(reason='These are flaky tests. Might fail, but still need to see what\'s going on')
    def test_fio_write_benchmark(self, driver_mode):
        aws_fpga_test_utils.install_edma_driver(mode=driver_mode)
        assert aws_fpga_test_utils.edma_driver_installed() == True

        (rc, stdout_lines, stderr_lines) = self.run_cmd("sudo {} {}".format(self.get_fio_tool_run_script(), self.get_fio_write_benchmark_script(driver='edma')), echo=True, check=False)
        if rc != 0:
            logger.error("FIO edma write benchmark test failed")
            # Create some diagnostic information
            # Debug is problematic for intermittent problems because the instance is terminated when the tests finish.
            self.run_cmd("sudo fpga-describe-local-image-slots", check=False, echo=True)
            for slot in range(self.num_slots):
                self.run_cmd("sudo fpga-describe-local-image -S {} -M".format(slot), check=False, echo=True)
        assert rc == 0

    @pytest.mark.xfail(reason='These are flaky tests. Might fail, but still need to see what\'s going on')
    def test_fio_read_benchmark(self, driver_mode):
        aws_fpga_test_utils.install_edma_driver(mode=driver_mode)
        assert aws_fpga_test_utils.edma_driver_installed() == True

        (rc, stdout_lines, stderr_lines) = self.run_cmd("sudo {} {}".format(self.get_fio_tool_run_script(), self.get_fio_read_benchmark_script(driver='edma')), echo=True, check=False)
        if rc != 0:
            logger.error("FIO edma read benchmark test failed")
            # Create some diagnostic information
            # Debug is problematic for intermittent problems because the instance is terminated when the tests finish.
            self.run_cmd("sudo fpga-describe-local-image-slots", check=False, echo=True)
            for slot in range(self.num_slots):
                self.run_cmd("sudo fpga-describe-local-image -S {} -M".format(slot), check=False, echo=True)
        assert rc == 0
