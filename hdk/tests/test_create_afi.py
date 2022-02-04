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
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestCreateAfi(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    Create AFI from DCP.
    '''

    ADD_XILINX_VERSION = True

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)
        return

    def get_dcp_tarball(self, cl):
        dcp_dir = "{}/hdk/cl/examples/{}/build/checkpoints/to_aws".format(self.WORKSPACE, cl)
        dcp_tarball = None
        if os.path.exists(dcp_dir):
            for file in os.listdir(dcp_dir):
                if re.match(r'.+\.Developer_CL\.tar', file):
                    dcp_tarball = dcp_dir + '/' + file
                    logger.info("DCP tarball={}".format(dcp_tarball))
                    break
        if not dcp_tarball:
            raise ValueError("No DCP tarball in {}".format(dcp_dir))
        return dcp_tarball

    def base_test(self, cl, xilinxVersion, build_strategy='DEFAULT', clock_recipe_a='A0', clock_recipe_b='B0', clock_recipe_c='C0', uram_option='2'):
        assert build_strategy in self.DCP_BUILD_STRATEGIES
        assert clock_recipe_a in self.DCP_CLOCK_RECIPES['A']['recipes']
        assert clock_recipe_b in self.DCP_CLOCK_RECIPES['B']['recipes']
        assert clock_recipe_c in self.DCP_CLOCK_RECIPES['C']['recipes']
        assert uram_option in self.DCP_URAM_OPTIONS

        # On Jenkins unstash will have already restored the DCP.
        # If not, download from S3 so can debug this test standalone.

        option_tag = "{}_{}_{}_{}_{}".format(clock_recipe_a, clock_recipe_b, clock_recipe_c, uram_option, build_strategy)

        # Get the DCP tarball
        try:
            dcp_tarball = self.get_dcp_tarball(cl)
        except ValueError:
            # DCP should have already been uploaded to S3 by test_gen_dcp.py
            logger.info("Downloading dcp from s3://{}/{}".format(self.s3_bucket, self.get_cl_s3_dcp_tag(cl, option_tag, xilinxVersion)))
            os.system("aws s3 cp s3://{}/{} {} --recursive".format(self.s3_bucket, self.get_cl_s3_dcp_tag(cl, option_tag, xilinxVersion), self.get_cl_to_aws_dir(cl)))
            dcp_tarball = self.get_dcp_tarball(cl)

        # Create the AFI
        dcp_key = os.path.join(self.get_cl_s3_dcp_tag(cl, option_tag, xilinxVersion), basename(dcp_tarball))
        create_afi_response = self.ec2_client().create_fpga_image(InputStorageLocation={'Bucket': self.s3_bucket, 'Key': dcp_key})
        afi = create_afi_response['FpgaImageId']
        agfi = create_afi_response['FpgaImageGlobalId']
        logger.info("afi={}".format(afi))
        logger.info("agfi={}".format(agfi))

        # Write IDs to S3 for use by downstream tests
        id_filename = self.get_cl_afi_id_filename(cl)
        id_filename_dir = dirname(id_filename)
        id_filename_key = self.get_cl_s3_afi_tag(cl, option_tag, xilinxVersion)
        if not os.path.exists(id_filename_dir):
            os.makedirs(id_filename_dir)
        fh = open(id_filename, 'w')
        fh.write("{}\n{}\n".format(afi, agfi))
        fh.close()
        self.s3_client().upload_file(id_filename, self.s3_bucket, id_filename_key)

        # Wait for the AFI to complete
        rc = os.system(self.WORKSPACE + "/shared/bin/scripts/wait_for_afi.py --afi {}".format(afi))
        assert rc == 0

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_dram_dma(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_dram_dma'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_hello_world(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_hello_world'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)

    def test_cl_hello_world_vhdl(self, xilinxVersion):
        cl = 'cl_hello_world_vhdl'
        self.base_test(cl, xilinxVersion)

    @pytest.mark.parametrize("uram_option", AwsFpgaTestBase.DCP_URAM_OPTIONS)
    def test_cl_uram_example(self, xilinxVersion, uram_option):
        cl = 'cl_uram_example'
        self.base_test(cl, xilinxVersion, clock_recipe_a='A0', uram_option=uram_option)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_sde(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_sde'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)

