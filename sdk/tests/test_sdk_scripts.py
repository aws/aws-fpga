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
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestSdkScripts(AwsFpgaTestBase):
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
        return

    @pytest.mark.skip(reason="Not implemented")
    def test_sdk_setup(self):
        logger.info(self)
        assert False
