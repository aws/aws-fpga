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

Call using ```pytest test_drivers.py```

See TESTING.md for details.
'''

import os
from os.path import basename, dirname, realpath
import pytest
import sys
import traceback
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source sdk_setup.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestNonRootAccess(AwsFpgaTestBase):
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

        (cls.cl_hello_world_agfi, cl_hello_world_afi) = cls.get_agfi_from_readme('cl_hello_world')
        return

    def setup_method(self, test_method):

        for slot in range(AwsFpgaTestBase.num_slots):
            self.fpga_load_local_image(self.cl_hello_world_agfi, slot,
                    as_root=False)
            assert AwsFpgaTestBase.check_fpga_afi_loaded(self.cl_hello_world_agfi, slot), "{} not loaded in slot {}".format(self.cl_hello_world_agfi, slot)
        cmd = "cd $WORKSPACE/hdk/cl/examples/cl_hello_world/software/runtime && make "
        assert os.system(cmd) == 0
        logger.info("Compiled hello world")

    def teardown_method(self, test_method):
        for slot in range(AwsFpgaTestBase.num_slots):
            AwsFpgaTestBase.fpga_clear_local_image(slot, as_root=False)

    def test_hello_world_as_non_root_user(self):
        for slot in range(AwsFpgaTestBase.num_slots):
            (rc, out, err) = self.run_cmd("bash -x {}/sdk/tests/non_root_log_into_group.sh {}".format(os.environ['WORKSPACE'], slot))
            logger.info("{}\n{}".format(out, err))
            assert  rc == 0
            AwsFpgaTestBase.fpga_set_virtual_dip_switch("1111111111111111", slot, as_root=False)
            assert  AwsFpgaTestBase.fpga_get_virtual_led(slot, as_root=False) == "1010-1101-1101-1110"
