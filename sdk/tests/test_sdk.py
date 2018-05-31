#! /user/bin/env python2.7

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
import re
import subprocess
import sys
import time
import traceback
import ctypes
from base_sdk import BaseSdkTools

try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source sdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestSDK(BaseSdkTools):
    '''
    Pytest test class.
    
    NOTE: Cannot have an __init__ method.
    
    '''
    def peek_poke_test_slot(self, slot):
        logger.info("peek poke test")
        handle = ctypes.c_int()
        value = ctypes.c_uint32()
        value8 = ctypes.c_uint8()
        bar = 4

        rc = self.mgmt_so.fpga_pci_attach(slot,0,bar,0,ctypes.byref(handle))
        assert rc == 0
        
        rc = self.mgmt_so.fpga_pci_poke(handle,0x0,0xabcd)
        assert rc == 0

        rc = self.mgmt_so.fpga_pci_peek(handle,0x0,ctypes.byref(value))
        assert rc == 0
        assert value.value == 0xabcd

        rc = self.mgmt_so.fpga_pci_poke8(handle,0x1,0x12)
        assert rc == 0

        rc = self.mgmt_so.fpga_pci_peek8(handle,0x1,ctypes.byref(value8))
        assert rc == 0
        assert value8.value == 0x12

        rc = self.mgmt_so.fpga_pci_peek(handle,0x0,ctypes.byref(value))
        assert rc == 0
        assert value.value == 0x12cd
        logger.info('Final peek/poke result: {0}'.format(hex(value.value)))

    def test_peek_poke(self):
        for slot in range(self.num_slots):
            self.fpga_load_local_image(self.cl_dram_dma_agfi, slot)
            self.peek_poke_test_slot(slot)
