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
Base class for pytest modules

See TESTING.md for details.
'''

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
    from aws_fpga_test_utils import get_git_repo_root
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class AwsFpgaTestBase(object):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    Load AFI created by test_create_afi.py
    '''

    @classmethod
    def setup_class(cls, derived_cls, filename_of_test_class):
        AwsFpgaTestBase.s3_bucket = 'aws-fpga-jenkins-testing'
        AwsFpgaTestBase.__ec2_client = None
        AwsFpgaTestBase.__s3_client = None
        AwsFpgaTestBase.test_dir = dirname(realpath(filename_of_test_class))
        AwsFpgaTestBase.git_repo_dir = get_git_repo_root(dirname(filename_of_test_class))
        AwsFpgaTestBase.WORKSPACE = AwsFpgaTestBase.git_repo_dir

        # SDAccel locations
        # Need to move to either a config file somewhere or a subclass
        AwsFpgaTestBase.xilinx_sdaccel_examples_dir = AwsFpgaTestBase.git_repo_dir + "/SDAccel/examples/xilinx"
        AwsFpgaTestBase.xilinx_sdaccel_examples_list_file = AwsFpgaTestBase.WORKSPACE + "/sdaccel_examples_list.json"

        if 'WORKSPACE' in os.environ:
            assert os.environ['WORKSPACE'] == AwsFpgaTestBase.git_repo_dir, "WORKSPACE incorrect"
        else:
            os.environ['WORKSPACE'] = AwsFpgaTestBase.WORKSPACE
        AwsFpgaTestBase.instance_type = aws_fpga_test_utils.get_instance_type()
        AwsFpgaTestBase.num_slots = aws_fpga_test_utils.get_num_fpga_slots(AwsFpgaTestBase.instance_type)
        return

    @staticmethod
    def ec2_client():
        if not AwsFpgaTestBase.__ec2_client:
            AwsFpgaTestBase.__ec2_client = boto3.client('ec2')
        return AwsFpgaTestBase.__ec2_client

    @staticmethod
    def s3_client():
        if not AwsFpgaTestBase.__s3_client:
            AwsFpgaTestBase.__s3_client = boto3.client('s3')
        return AwsFpgaTestBase.__s3_client

    @staticmethod
    def assert_hdk_setup():
        assert 'AWS_FPGA_REPO_DIR' in os.environ, "AWS_FPGA_REPO_DIR not set. source {}/hdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['AWS_FPGA_REPO_DIR'] == AwsFpgaTestBase.git_repo_dir, "AWS_FPGA_REPO_DIR not set to the repo dir. source {}/hdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert 'HDK_DIR' in os.environ, "HDK_DIR not set. source {}/hdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['HDK_DIR'] == os.path.join(AwsFpgaTestBase.git_repo_dir, 'hdk'), "HDK_DIR incorrect. source {}/hdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)

    @staticmethod
    def assert_sdk_setup():
        assert 'SDK_DIR' in os.environ, "SDK_DIR not set. source {}/sdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['SDK_DIR'] == os.path.join(AwsFpgaTestBase.git_repo_dir, 'sdk'), "SDK_DIR incorrect. source {}/sdk_setup.sh".format(AwsFpgaTestBase.git_repo_dir)

    @staticmethod
    def assert_sdaccel_setup():
        assert 'AWS_FPGA_REPO_DIR' in os.environ, "AWS_FPGA_REPO_DIR not set. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['AWS_FPGA_REPO_DIR'] == AwsFpgaTestBase.git_repo_dir, "AWS_FPGA_REPO_DIR not set to the repo dir. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert 'HDK_DIR' in os.environ, "HDK_DIR not set. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['HDK_DIR'] == os.path.join(AwsFpgaTestBase.git_repo_dir, 'hdk'), "HDK_DIR incorrect. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert 'SDK_DIR' in os.environ, "SDK_DIR not set. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['SDK_DIR'] == os.path.join(AwsFpgaTestBase.git_repo_dir, 'sdk'), "SDK_DIR incorrect. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert 'SDACCEL_DIR' in os.environ, "SDACCEL_DIR not set. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ['SDACCEL_DIR'] == os.path.join(AwsFpgaTestBase.git_repo_dir, 'SDAccel'), "SDACCEL_DIR incorrect. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ.get('AWS_PLATFORM') != 'None', "Environment Var AWS_PLATFORM not set. source {}/sdaccel_setup.sh".format(AwsFpgaTestBase.git_repo_dir)
        assert os.environ.get('XILINX_SDX') != 'None', "Environment Var XILINX_SDX not set. Please check the AMI."

    @staticmethod
    def running_on_f1_instance():
        '''
        Check to see if running on an F1 instance
        '''
        instance_type = aws_fpga_test_utils.get_instance_type()
        return re.match(r'f1\.', instance_type)

    @staticmethod
    def run_cmd(cmd, echo=False, check=True):
        if echo:
            logger.info("Running: {}".format(cmd))
        p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (stdout_data, stderr_data) = p.communicate()
        stdout_lines = stdout_data.split('\n')
        stderr_lines = stderr_data.split('\n')
        if check and p.returncode:
            logger.error("Cmd failed with rc={}\ncmd: {}\nstdout:\n{}\nstderr:\n{}".format(
                p.returncode, cmd, stdout_data, stderr_data))
        return (p.returncode, stdout_lines, stderr_lines)

    @staticmethod
    def run_hdk_cmd(cmd, echo=False, check=True):
        source_hdk_cmd = "source {}/hdk_setup.sh &> /dev/null".format(AwsFpgaTestBase.git_repo_dir)
        cmd = source_hdk_cmd + " && " + cmd
        return AwsFpgaTestBase.run_cmd(cmd, echo, check)

    @staticmethod
    def run_sdk_cmd(cmd, echo=False, check=True):
        source_sdk_cmd = "source {}/sdk_setup.sh &> /dev/null".format(AwsFpgaTestBase.git_repo_dir)
        cmd = source_sdk_cmd + " && " + cmd
        return AwsFpgaTestBase.run_cmd(cmd, echo, check)

    @staticmethod
    def run_sdaccel_cmd(cmd, echo=False, check=True):
        source_sdaccel_cmd = "source {}/sdaccel_setup.sh &> /dev/null".format(AwsFpgaTestBase.git_repo_dir)
        cmd = source_sdaccel_cmd + " && " + cmd
        return AwsFpgaTestBase.run_cmd(cmd, echo, check)

    @staticmethod
    def get_cl_dir(cl):
        return "{}/hdk/cl/examples/{}".format(AwsFpgaTestBase.WORKSPACE, cl)

    @staticmethod
    def get_cl_to_aws_dir(cl):
        return os.path.join(AwsFpgaTestBase.get_cl_dir(cl), 'build/checkpoints/to_aws')

    @staticmethod
    def get_cl_afi_id_filename(cl):
        return os.path.join(AwsFpgaTestBase.get_cl_dir(cl), 'build/create-afi/afi_ids.txt')

    @staticmethod
    def get_cl_scripts_dir(cl):
        return os.path.join(AwsFpgaTestBase.get_cl_dir(cl), 'build/scripts')

    @staticmethod
    def get_cl_s3_dcp_tag(cl, option_tag):
        '''
        @param option_tag: A tag that is unique for each build.
            Required because a CL can be built with different options such as clock recipes.
        '''
        assert option_tag != ''
        return "jenkins/{}/{}/{}/dcp".format(os.environ['BUILD_TAG'], cl, option_tag)

    @staticmethod
    def get_cl_s3_afi_tag(cl, option_tag):
        '''
        @param option_tag: A tag that is unique for each build.
            Required because a CL can be built with different options such as clock recipes.
        '''
        assert option_tag != ''
        return "jenkins/{}/{}/{}/create-afi/afi_ids.txt".format(os.environ['BUILD_TAG'], cl, option_tag)

    @staticmethod
    def assert_afi_available(afi):
        # Check the status of the afi
        logger.info("Checking the status of {}".format(afi))
        afi_state = AwsFpgaTestBase.ec2_client().describe_fpga_images(FpgaImageIds=[afi])['FpgaImages'][0]['State']['Code']
        logger.info("{} state={}".format(afi, afi_state))
        assert afi_state == 'available'

    @staticmethod
    def fpga_clear_local_image(slot):
        logger.info("Clearing FPGA slot {}".format(slot))
        (rc, stdout_lines, stderr_lines) = AwsFpgaTestBase.run_cmd("sudo fpga-clear-local-image  -S {}".format(slot))
        assert rc == 0, "Clearing FPGA slot {} failed.".format(slot)

    @staticmethod
    def fpga_load_local_image(agfi, slot):
        logger.info("Loading {} into slot {}".format(agfi, slot))
        (rc, stdout_lines, stderr_lines) = AwsFpgaTestBase.run_cmd("sudo fpga-load-local-image -S {} -I {}".format(slot, agfi))
        assert rc == 0, "Failed to load {} in slot {}.".format(agfi, slot)

    @staticmethod
    def check_fpga_afi_loaded(agfi, slot):
        fpgaLocalImage = aws_fpga_test_utils.fpga_describe_local_image(slot)
        assert fpgaLocalImage.statusName == 'loaded', "{} FPGA StatusName != loaded: {}".format(agfi, fpgaLocalImage.statusName)
        assert fpgaLocalImage.statusCode == '0', "{} status code != 0: {}".format(agfi, fpgaLocalImage.statusCode)
        assert fpgaLocalImage.errorName == 'ok', "{} FPGA ErrorName != ok: {}".format(agfi, fpgaLocalImage.ErrorName)
        assert fpgaLocalImage.errorCode == '0', "{} ErrorCode != 0: {}".format(agfi, fpgaLocalImage.errorCode)
        assert fpgaLocalImage.agfi == agfi, "Expected {}, actual {}".format(agfi, fpgaLocalImage.agfi)
        return fpgaLocalImage

    @staticmethod
    def fpga_get_virtual_led(slot, remove_dashes=False):
        (rc, stdout_lines, stderr_lines) = AwsFpgaTestBase.run_cmd("sudo fpga-get-virtual-led -S {}".format(slot))
        assert rc == 0, "Failed to get virtual LEDs from slot {}.".format(slot)
        value = stdout_lines[1]
        if remove_dashes:
            value= re.sub('-', '', value)
        return value

    @staticmethod
    def fpga_get_virtual_dip_switch(slot, remove_dashes=False):
        (rc, stdout_lines, stderr_lines) = AwsFpgaTestBase.run_cmd("sudo fpga-get-virtual-dip-switch -S {}".format(slot))
        assert rc == 0, "Failed to get virtual DIP switches from slot {}.".format(slot)
        value = stdout_lines[1]
        if remove_dashes:
            value= re.sub('-', '', value)
        return value

    @staticmethod
    def fpga_set_virtual_dip_switch(value, slot):
        value= re.sub('-', '', value)
        (rc, stdout_lines, stderr_lines) = AwsFpgaTestBase.run_cmd("sudo fpga-set-virtual-dip-switch -S {} -D {}".format(slot, value))
        assert rc == 0, "Failed to set virtual DIP switches in slot {} to {}.".format(slot, value)

