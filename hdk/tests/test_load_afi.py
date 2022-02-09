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

Call using ```pytest test_load_afi.py```

See TESTING.md for details.
'''

from __future__ import print_function
import boto3
import os
from os.path import basename, dirname, realpath
import pytest
import re
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

class TestLoadAfi(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    Load AFI created by test_create_afi.py
    '''

    ADD_XILINX_VERSION = True

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)

        AwsFpgaTestBase.assert_sdk_setup()

        assert AwsFpgaTestBase.running_on_f1_instance(), 'This test must be run on an F1 instance. Instance type={}'.format(aws_fpga_test_utils.get_instance_type())

        return

    def setup_method(self, test_method):
        aws_fpga_test_utils.remove_all_drivers()

    def get_agfi(self, cl, xilinxVersion, option_tag):
        '''
        On Jenkins the afi_id_filename will be restored using unstash.
        If not running on Jenkins then get it from S3.
        '''
        afi_id_filename = self.get_cl_afi_id_filename(cl)

        if not os.path.exists(afi_id_filename):
            # Get the file with AFI IDs from S3
            logger.info("{} doesn't exist".format(afi_id_filename))
            afi_id_path = dirname(afi_id_filename)
            if not os.path.exists(afi_id_path):
                os.makedirs(afi_id_path)
            afi_id_key = self.get_cl_s3_afi_tag(cl, option_tag, xilinxVersion)
            logger.info("Fetching from s3://{}/{}".format(self.s3_bucket, afi_id_key))
            self.s3_client().download_file(Bucket=self.s3_bucket, Key=afi_id_key, Filename=afi_id_filename)

        # Read the AFI IDs from the file
        fh = open(afi_id_filename, 'r')
        afi = fh.readline().rstrip()
        agfi = fh.readline().rstrip()
        fh.close()
        logger.info("afi={}".format(afi))
        logger.info("agfi={}".format(agfi))

        return (agfi, afi)

    def base_precompiled_test(self, cl, install_xdma_driver, slots_to_test=[], option_tag='default'):
        (agfi, afi) = self.get_agfi_from_readme(cl)
        self.assert_afi_public(afi)
        self.base_test(cl, agfi, afi, install_xdma_driver, slots_to_test, option_tag)

    def base_fdf_test(self, cl, xilinxVersion, build_strategy='DEFAULT', clock_recipe_a='A0', clock_recipe_b='B0', clock_recipe_c='C0', uram_option='2',
                      install_xdma_driver=False, slots_to_test=[]):
        assert build_strategy in self.DCP_BUILD_STRATEGIES
        assert clock_recipe_a in self.DCP_CLOCK_RECIPES['A']['recipes']
        assert clock_recipe_b in self.DCP_CLOCK_RECIPES['B']['recipes']
        assert clock_recipe_c in self.DCP_CLOCK_RECIPES['C']['recipes']
        assert uram_option in self.DCP_URAM_OPTIONS

        option_tag = "{}_{}_{}_{}_{}".format(clock_recipe_a, clock_recipe_b, clock_recipe_c, uram_option, build_strategy)
        (agfi, afi) = self.get_agfi(cl, xilinxVersion, option_tag)
        self.base_test(cl, agfi, afi, install_xdma_driver, slots_to_test, option_tag)

    def byte_swap(self, value):
        swapped_value = 0;
        for b in range(4):
            swapped_value |= ((value >> (b * 8)) & 0xff) << (8 * (3 - b))
        return swapped_value;

    def load_agfi(self, cl, agfi, afi, slot):
        self.assert_afi_available(afi)

        self.fpga_load_local_image(agfi, slot)

        logger.info("Checking slot {} AFI Load status".format(slot))
        assert self.check_fpga_afi_loaded(agfi, slot), "{} not loaded in slot {}".format(agfi, slot)
        return

    def check_runtime_software(self, cl, slot):
        # Example test = cl_hello_world
        # makefile makes test_hello_world, so removing cl_ from the string
        test_obj_name = cl[3:]

        if cl == 'cl_dram_dma':
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {}".format(
                self.WORKSPACE, cl, test_obj_name, slot), echo=True)
            assert rc == 0, "Runtime example failed."
            logger.info("stdout:\n{}\nstderr:\n{}".format("\n".join(stdout_lines), "\n".join(stderr_lines)))

        elif re.match(r'cl_hello_world', cl):
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {}".format(
                self.WORKSPACE, cl, test_obj_name, slot), echo=True)
            assert rc == 0, "Runtime example failed."
            exp_vdip_switch = '0000-0000-0000-0000'
            act_vdip_switch = self.fpga_get_virtual_dip_switch(slot)
            assert act_vdip_switch == exp_vdip_switch, "Virtual DIP switch miscompare: exp={}, act={}".format(exp_vdip_switch, act_vdip_switch)
            exp_vled = '0000-0000-0000-0000'
            act_vled = self.fpga_get_virtual_led(slot)
            assert act_vled == exp_vled, "Virtual LED miscompare: exp={}, act={}".format(exp_vled, act_vled)

            exp_vdip_switch = '1111-1111-1111-1111'
            self.fpga_set_virtual_dip_switch(exp_vdip_switch, slot)
            act_vdip_switch = self.fpga_get_virtual_dip_switch(slot)
            assert act_vdip_switch == exp_vdip_switch, "Virtual DIP switch miscompare: exp={}, act={}".format(exp_vdip_switch, act_vdip_switch)
            exp_vled = '1010-1101-1101-1110'
            act_vled = self.fpga_get_virtual_led(slot)
            assert act_vdip_switch == exp_vdip_switch, "Virtual DIP switch miscompare: exp={}, act={}".format(exp_vdip_switch, act_vdip_switch)

            # Walk a 1 through all 32 bit positions
            for b in range(32):
                reg_value = 1 << b
                logger.info("Testing with reg_value=0x{:016x}".format(reg_value))
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} 0x{:x}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, reg_value), echo=True)
                assert rc == 0, "Runtime example failed."

                exp_reg_value = self.byte_swap(reg_value)
                exp_vled = "{:016b}".format(reg_value & 0xffff)
                act_vled = self.fpga_get_virtual_led(slot)
                act_vled = re.sub('-', '', act_vled)
                assert act_vled == exp_vled, "Virtual LED miscompare: exp={}, act={}".format(exp_vled, act_vled)
                logger.info("Virtual LED={}".format(act_vled))

        elif re.match(r'cl_uram_example', cl):
            find_pass_re = re.compile(r'^Find OK')
            find_fail_re = re.compile(r'^Find KO')
            del_pass_re = re.compile(r'^Deletion OK')
            add_pass_re = re.compile(r'^The value 0x\S+ has been added to the URAM successfully')

            # Test the commands printed by the test:
            # find FEEDBABE
            # add CAFE4B1D
            # del DEADDEAD
            command = 'find FEEDBABE'
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
            assert rc == 0, "Runtime example failed."
            assert find_fail_re.match(stdout_lines[-2]), "{} didn't fail. stdout:\n{}".format(command, "\n".join(stdout_lines))

            command = 'add CAFE4B1D'
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
            assert rc == 0, "Runtime example failed."
            assert add_pass_re.match(stdout_lines[-2]), "{} didn't pass. stdout:\n{}".format(command, "\n".join(stdout_lines))

            command = 'del DEADDEAD'
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
            assert rc == 0, "Runtime example failed."
            assert not del_pass_re.match(stdout_lines[-2]), "{} didn't fail. stdout:\n{}".format(command, "\n".join(stdout_lines))

            command = 'del CAFE4B1D'
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
            assert rc == 0, "Runtime example failed."
            assert del_pass_re.match(stdout_lines[-2]), "{} didn't pass. stdout:\n{}".format(command, "\n".join(stdout_lines))

            # Test adding, finding, and deleting each value
            values = ['FEEDBABE', 'CAFE4B1D', 'DEADDEAD']
            for value in values:
                command = "find {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert find_fail_re.match(stdout_lines[-2]), "{} didn't fail. stdout:\n{}".format(command, "\n".join(stdout_lines))

                command = "add {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert add_pass_re.match(stdout_lines[-2]), "{} didn't pass. stdout:\n{}".format(command, "\n".join(stdout_lines))

                command = "find {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert find_pass_re.match(stdout_lines[-2]), "{} didn't pass. stdout:\n{}".format(command, "\n".join(stdout_lines))

                command = "del {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert del_pass_re.match(stdout_lines[-2]), "{} didn't pass. stdout:\n{}".format(command, "\n".join(stdout_lines))

                command = "find {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert find_fail_re.match(stdout_lines[-2]), "{} didn't fail. stdout:\n{}".format(command, "\n".join(stdout_lines))

                command = "del {}".format(value)
                (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && sudo ./test_{} --slot {} {}".format(
                    self.WORKSPACE, cl, test_obj_name, slot, command), echo=True)
                assert rc == 0, "Runtime example failed."
                assert find_fail_re.match(stdout_lines[-2]), "{} didn't fail. stdout:\n{}".format(command, "\n".join(stdout_lines))

        elif re.match(r'cl_sde', cl):
            (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && make clean && make all".format(
                self.WORKSPACE, cl), echo=True)
            assert rc == 0, "Runtime example failed."

        else:
            assert False, "Invalid cl: {}".format(cl)

    def base_test(self, cl, agfi, afi, install_xdma_driver, slots_to_test, option_tag):
        if len(slots_to_test):
            # Make sure that the requested slots are valid for this instance type
            for slot in slots_to_test:
                assert slot >= 0 and slot < self.num_slots
        else:
            slots_to_test = range(self.num_slots)

        # Make sure that the test can be built first
        if cl != 'cl_sde':
           logger.info("Building runtime software")
           (rc, stdout_lines, stderr_lines) = self.run_cmd("cd {}/hdk/cl/examples/{}/software/runtime && make -f Makefile SDK_DIR={}/sdk".format(self.WORKSPACE, cl, self.WORKSPACE))
           assert rc == 0, "Runtime software build failed."
        else:
           logger.info("cl_sde runtime test is app. No build needed")

        # Load the AFI onto all available FPGAs
        # This is required for the XDMA driver to correctly install for all slots
        # We do this because otherwise installation on slots 1-7 doesn't seem to work.
        logger.info("Loading the AFI into all slots")
        for slot in slots_to_test:
            self.load_agfi(cl, agfi, afi, slot)

        if install_xdma_driver:
            aws_fpga_test_utils.install_xdma_driver()

        for slot in slots_to_test:
            logger.info("Running runtime software on slot {}".format(slot))
            self.check_runtime_software(cl, slot)

        for slot in slots_to_test:
            self.fpga_clear_local_image(slot)


    def test_precompiled_cl_dram_dma(self, xilinxVersion):
        cl = 'cl_dram_dma'
        self.base_precompiled_test(cl, install_xdma_driver=True)

    def test_precompiled_cl_hello_world(self, xilinxVersion):
        cl = 'cl_hello_world'
        self.base_precompiled_test(cl, install_xdma_driver=False)

    def test_precompiled_cl_sde(self, xilinxVersion):
        cl = 'cl_sde'
        self.base_precompiled_test(cl, install_xdma_driver=False)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_dram_dma(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_dram_dma'
        self.base_fdf_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c, install_xdma_driver=True)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_hello_world(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_hello_world'
        self.base_fdf_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c, install_xdma_driver=False)

    def test_cl_hello_world_vhdl(self, xilinxVersion):
        cl = 'cl_hello_world_vhdl'
        self.base_fdf_test(cl, xilinxVersion, install_xdma_driver=False)

    @pytest.mark.parametrize("uram_option", AwsFpgaTestBase.DCP_URAM_OPTIONS)
    def test_cl_uram_example(self, xilinxVersion, uram_option):
        cl = 'cl_uram_example'
        self.base_fdf_test(cl, xilinxVersion, clock_recipe_a='A0', uram_option=uram_option, install_xdma_driver=False)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_sde(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_sde'
        self.base_fdf_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c, install_xdma_driver=False)
 
