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

Call using ```pytest test_gen_dcp.py```

See TESTING.md for details.
'''

import glob
import os
from os.path import basename, dirname, realpath
import pytest
import subprocess
import sys
import traceback
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestGenDcp(AwsFpgaTestBase):
    '''
    Pytest test class.
    
    NOTE: Cannot have an __init__ method.
    
    Test all example CLs with different strategies and clock recipes.
    '''
    
    @staticmethod
    def setup_class(self):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(self, __file__)
        
        AwsFpgaTestBase.assert_hdk_setup()
        return
    
    def assert_non_zero_file(self, filter):
        filenames = glob.glob(filter)
        assert len(filenames) > 0, "No {} file found in {}".format(filter, os.getcwd())
        assert len(filenames) == 1, "More than 1 {} file found: {}\n{}".format(filter, len(filenames), filenames)
        filename = filenames[0]
        assert os.stat(filename).st_size != 0, "{} is 0 size".format(filename)
        return filename
    
    def check_build(self, cl):
        cl_dir = self.get_cl_dir(cl)
        checkpoints_dir = os.path.join(cl_dir, 'build/checkpoints')
        to_aws_dir = self.get_cl_to_aws_dir(cl)
        scripts_dir = self.get_cl_scripts_dir(cl)
        
        assert os.path.exists(to_aws_dir), "The checkpoints/to_aws directory does not exist: {}".format(to_aws_dir)
        
        logger.info("Checking that a non zero size ltx file exists in {}".format(checkpoints_dir))
        os.chdir(checkpoints_dir)
        ltx_file = os.path.join(checkpoints_dir, self.assert_non_zero_file('*.ltx'))
        logger.info("ltx file: {}".format(ltx_file))
        
        logger.info("Checking that a non zero size manifest file exists in {}".format(to_aws_dir))
        os.chdir(to_aws_dir)
        manifest_file = os.path.join(to_aws_dir, self.assert_non_zero_file('*.manifest.txt'))
        logger.info("manifest file: {}".format(manifest_file))
        
        logger.info("Checking that a non zero size dcp file exists in {}".format(to_aws_dir))
        dcp = os.path.join(to_aws_dir, self.assert_non_zero_file('*.dcp'))
        logger.info("dcp: {}".format(dcp))
        
        logger.info("Checking that a non zero size tar file exists in {}".format(to_aws_dir))
        tarball = os.path.join(to_aws_dir, self.assert_non_zero_file('*.tar'))
        logger.info("tarball: {}".format(tarball))
        
        logger.info("Checking that a dcp exists in the tar file")
        (rc, stdout_lines, stderr_lines) = self.run_cmd("/usr/bin/tar tvf {} \'*.dcp\'".format(tarball))
        assert rc == 0, "Did not find dcp in {}".format(tarball)
        
        logger.info("Checking that a manifest exists in the tar file")
        (rc, stdout_lines, stderr_lines) = self.run_cmd("/usr/bin/tar tvf {} \'*.manifest.txt\'".format(tarball))
        assert rc == 0, "Did not find manifest in {}".format(tarball)
        
        # Use last_log symlink to grab logname
        os.chdir(scripts_dir)
        logger.debug("Looking for last_log in {}".format(scripts_dir))
        assert os.path.exists("last_log"), "Could not find the log file: {}/last_log".format(scripts_dir)
        
        # Check the number of warnings
        (rc, stdout_lines, stderr_lines) = self.run_cmd("grep \"^WARNING\" last_log", check=False)
        if rc == 0:
            num_warnings = len(stdout_lines) - 1 # Last line is a blank line
        else:
            num_warnings = 0
        logger.info("Saw {} warnings in log file".format(num_warnings))
        
        # Compare number of warnings to expected number
        exp_num_warnings = int(open('.warnings', 'r').readline().rstrip())
        logger.info("Expected {} warnings in log file".format(exp_num_warnings))
        assert num_warnings == exp_num_warnings, "Unexpected number of warnings, exp={}, act={}\n{}\n{}".format(
            exp_num_warnings, num_warnings, "\n".join(stdout_lines), "\n".join(stderr_lines))
        
        # Check the number of critical warnings
        (rc, stdout_lines, stderr_lines) = self.run_cmd("grep \"^CRITICAL WARNING\" last_log", check=False)
        if rc == 0:
            num_warnings = len(stdout_lines) - 1
        else:
            num_warnings = 0
        logger.info("Saw {} critical warnings in log file".format(num_warnings))
        
        # Compare number of warnings to expected number
        exp_num_warnings = int(open('.critical_warnings', 'r').readline().rstrip())
        logger.info("Expected {} critical warnings in log file".format(exp_num_warnings))
        assert num_warnings == exp_num_warnings, "Unexpected number of critical warnings, exp={}, act={}".format(
            exp_num_warnings, num_warnings, "\n".join(stdout_lines))
        
        # Check if there are any setup/hold-time violations
        (rc, stdout_lines, stderr_lines) = self.run_cmd("grep \"The design did not meet timing requirements.\" last_log", check=False)
        if rc == 0:
            NUM_TIMING_VIOLATIONS = len(stdout_lines) -1
        else:
            NUM_TIMING_VIOLATIONS = 0
        assert NUM_TIMING_VIOLATIONS == 0, "{} timing violations found.  Design may not be functional:\n{}".format(
            NUM_TIMING_VIOLATIONS, "\n".join(stdout_lines))
        return tarball
        
    def base_test(self, cl, clock_recipe_a='A1', extra_args='', option_tag='default'):
        cl_dir = self.get_cl_dir(cl)
        logger.info("Setting CL_DIR={}".format(cl_dir))
        os.environ['CL_DIR'] = cl_dir
        assert os.path.exists(cl_dir), logger.error("CL_DIR={} does not exist".format(cl_dir))
        
        # Clean up all previous DCP generations
        to_aws_dir = self.get_cl_to_aws_dir(cl)
        os.system("rm -rf {}/*".format(to_aws_dir))
        
        scripts_dir = self.get_cl_scripts_dir(cl)
        logger.info("Scripts dir is {}".format(scripts_dir))
        os.chdir(scripts_dir)
        
        (rc, stdout_lines, stderr_lines) = self.run_cmd("./aws_build_dcp_from_cl.sh -foreground -clock_recipe_a {} {}".format(clock_recipe_a, extra_args))
        assert rc == 0, "DCP build failed."
        logger.info("DCP Generation Finished")
        
        tarball = self.check_build(cl)
        
        # Upload the DCP tarball to S3.
        dcp_key = os.path.join(self.get_cl_s3_dcp_tag(cl, option_tag), basename(tarball))
        self.s3_client().upload_file(tarball, self.s3_bucket, dcp_key)
        
        return
        
    def test_cl_dram_dma(self):
        cl = 'cl_dram_dma'
        self.base_test(cl)
    
    def test_cl_hello_world(self):
        cl = 'cl_hello_world'
        self.base_test(cl)
    
    def test_cl_hello_world_vhdl(self):
        cl = 'cl_hello_world_vhdl'
        self.base_test(cl)
    
    def test_cl_uram_example_uram_option_2(self):
        cl = 'cl_uram_example'
        self.base_test(cl, clock_recipe_a='A2', extra_args='-uram_option 2', option_tag='uram_option_2')
    
    def test_cl_uram_example_uram_option_3(self):
        cl = 'cl_uram_example'
        self.base_test(cl, clock_recipe_a='A2', extra_args='-uram_option 3', option_tag='uram_option_3')
    
    def test_cl_uram_example_uram_option_4(self):
        cl = 'cl_uram_example'
        self.base_test(cl, clock_recipe_a='A2', extra_args='-uram_option 4', option_tag='uram_option_4')
        