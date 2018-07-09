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
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source sdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class BaseSdkTools(AwsFpgaTestBase):
    '''
    Pytest test class.
    
    NOTE: Cannot have an __init__ method.
    
    Test FPGA AFI Management tools described in ../userspace/fpga_mgmt_tools/README.md
    '''

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)

        AwsFpgaTestBase.assert_sdk_setup()

        assert AwsFpgaTestBase.running_on_f1_instance(), 'This test must be run on an F1 instance. Instance type={}'.format(aws_fpga_test_utils.get_instance_type())

        cls.load_mgmt_so()

        (cls.cl_hello_world_agfi, cls.cl_dram_dma_afi) = cls.get_agfi_from_readme('cl_hello_world')
        (cls.cl_dram_dma_agfi, cls.cl_dram_dma_afi) = cls.get_agfi_from_readme('cl_dram_dma')

        cls.shell_version = cls.get_shell_version()

        # Need to preload an AFI or else may be the wrong shell version because of MSIX fix which is run
        # when the instance is created.
        logger.info("Initializing all slots with cl_hello_world AFI")
        for slot in range(cls.num_slots):
            cls.fpga_load_local_image(cls.cl_hello_world_agfi, slot)
        logger.info("PCI devices:\n{}".format("\n".join(cls.list_pci_devices())))

        # Rescanning PCI for each slot
        logger.info("Rescanning each slot to see if PCI devices change")
        for slot in range(cls.num_slots):
            (rc, stdout, stderr) = cls.run_cmd("sudo fpga-describe-local-image -R -S {}".format(slot))
        logger.info("PCI devices:\n{}".format("\n".join(cls.list_pci_devices())))

        cls.set_slot_to_device_mapping()
        return

    @classmethod
    def load_mgmt_so(cls):
        mgmt_so_loc = "{}/sdk/userspace/lib/so/libfpga_mgmt.so".format(AwsFpgaTestBase.WORKSPACE)
        ctypes.cdll.LoadLibrary(mgmt_so_loc)
        # Setup shared object return and argument types
        cls.mgmt_so = ctypes.CDLL(mgmt_so_loc)

        cls.mgmt_so.fpga_pci_attach.restype = ctypes.c_int
        cls.mgmt_so.fpga_pci_attach.argtypes = [ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_uint32,ctypes.POINTER(ctypes.c_int)]

        cls.mgmt_so.fpga_pci_peek.restype = ctypes.c_int
        cls.mgmt_so.fpga_pci_peek.argtypes = [ctypes.c_int,ctypes.c_uint64,ctypes.POINTER(ctypes.c_uint32)]

        cls.mgmt_so.fpga_pci_poke.restype = ctypes.c_int
        cls.mgmt_so.fpga_pci_poke.argtypes = [ctypes.c_int,ctypes.c_uint64,ctypes.c_uint32]
        
        cls.mgmt_so.fpga_pci_peek8.restype = ctypes.c_int
        cls.mgmt_so.fpga_pci_peek8.argtypes = [ctypes.c_int,ctypes.c_uint64,ctypes.POINTER(ctypes.c_uint8)]

        cls.mgmt_so.fpga_pci_poke8.restype = ctypes.c_int
        cls.mgmt_so.fpga_pci_poke8.argtypes = [ctypes.c_int,ctypes.c_uint64,ctypes.c_uint8]
        

    @classmethod
    def set_slot_to_device_mapping(cls):
        cls.slot2device = {}
        cls.slot2mbox_device = {}
        pci_devices = cls.list_pci_devices()
        (rc, stdout, stderr) = cls.run_cmd("sudo fpga-describe-local-image-slots -M")
        assert len(stdout) == cls.num_slots * 2 + 1
        assert len(stderr) == 1
        slot_re = re.compile(r'AFIDEVICE    ([0-7])       0x[0-9a-fA-F]{4}      0x[0-9a-fA-F]{4}      (0000:00:[01][0-9a-fA-F]\.0)')
        device2slot = {}
        mbox_device2slot = {}
        for slot in range(cls.num_slots):
            matches = slot_re.match(stdout[slot * 2])
            assert matches, "Invalid format: {}".format(stdout[slot * 2])
            assert matches.group(1) == str(slot), "slot!={}: {}".format(slot, stdout[slot * 2])
            dbdf = matches.group(2)
            assert dbdf not in device2slot, "device {} already used by slot {}".format(dbdf, device2slot[dbdf])
            assert dbdf not in mbox_device2slot, "device {} already used by slot {} mbox".format(dbdf, device2slot[dbdf])
            device2slot[dbdf] = slot
            cls.slot2device[slot] = dbdf
            logger.info("Slot {} uses PCI device {}".format(slot, dbdf))

            matches = slot_re.match(stdout[slot * 2 + 1])
            assert matches, "Invalid format: {}".format(stdout[slot * 2 + 1])
            assert matches.group(1) == str(slot), "slot!={}: {}".format(slot, stdout[slot * 2 + 1])
            dbdf = matches.group(2)
            assert dbdf not in device2slot, "device {} already used by slot {}".format(dbdf, device2slot[dbdf])
            assert dbdf not in mbox_device2slot, "device {} already used by slot {} mbox".format(dbdf, device2slot[dbdf])
            mbox_device2slot[dbdf] = slot
            cls.slot2mbox_device[slot] = dbdf
            logger.info("Slot {} mbox uses PCI device {}".format(slot, dbdf))

    @staticmethod
    def list_pci_devices():
        (rc, stdout, stderr) = AwsFpgaTestBase.run_cmd("ls -1 /sys/bus/pci/devices")
        pci_devices = stdout[0:-1]
        return pci_devices
