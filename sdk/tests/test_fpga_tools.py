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
try:
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source sdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestFpgaTools(AwsFpgaTestBase):
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

    def test_describe_local_image_slots(self):
        for slot in range(self.num_slots):
            self.fpga_clear_local_image(slot)

        logger.info("PCI devices:\n{}".format("\n".join(self.list_pci_devices())))

        (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image-slots", echo=True)
        assert len(stdout) == self.num_slots + 1
        assert len(stderr) == 1
        for slot in range(self.num_slots):
            assert stdout[slot] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot]), "slot={}".format(slot)

        # Test -H (display headers)
        (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image-slots -H", echo=True)
        assert len(stdout) == self.num_slots * 2 + 1
        assert len(stderr) == 1
        for slot in range(self.num_slots):
            assert stdout[slot * 2] == 'Type  FpgaImageSlot  VendorId    DeviceId    DBDF', "slot={}".format(slot)
            assert stdout[slot * 2 + 1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot]), "slot={}".format(slot)

        # Test -M (Show the mbox physical function in the list of devices.)
        (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image-slots -M", echo=True)
        assert len(stdout) == self.num_slots * 2 + 1
        assert len(stderr) == 1
        for slot in range(self.num_slots):
            assert stdout[slot * 2    ] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot]), "slot={}\n{}".format(slot, "\n".join(stdout))
            assert stdout[slot * 2 + 1] == 'AFIDEVICE    {}       0x1d0f      0x1041      {}'.format(slot, self.slot2mbox_device[slot]), "slot={}\n{}".format(slot, "\n".join(stdout))

        # Test -H and -M (Show the mbox physical function in the list of devices.)
        (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image-slots -H -M", echo=True)
        assert len(stdout) == self.num_slots * 3 + 1
        assert len(stderr) == 1
        for slot in range(self.num_slots):
            assert stdout[slot * 3 + 0] == 'Type  FpgaImageSlot  VendorId    DeviceId    DBDF'
            assert stdout[slot * 3 + 1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot]), "slot={}\n{}".format(slot, "\n".join(stdout))
            assert stdout[slot * 3 + 2] == 'AFIDEVICE    {}       0x1d0f      0x1041      {}'.format(slot, self.slot2mbox_device[slot]), "slot={}\n{}".format(slot, "\n".join(stdout))

    def test_describe_local_image(self):
        for slot in range(self.num_slots):
            self.fpga_clear_local_image(slot)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version), "slot={}\n{}".format(slot, "\n".join(stdout))
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot]), "slot={}\n{}".format(slot, "\n".join(stdout))

            # Test -H
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -H -S {}".format(slot), echo=True)
            assert len(stdout) == 5
            assert len(stderr) == 1
            assert stdout[0] == 'Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion'
            assert stdout[1] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
            assert stdout[2] == 'Type  FpgaImageSlot  VendorId    DeviceId    DBDF'
            assert stdout[3] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot])

            # Test -M (Return FPGA image hardware metrics.)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -M -S {}".format(slot), echo=True)
            assert len(stdout) == 57
            assert len(stderr) == 1
            assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot])
            assert stdout[2] == 'sdacl-slave-timeout=0'
            assert stdout[50] == 'Clock Group C Frequency (Mhz)'
            assert stdout[51] == '0  0  '

            # Test -C (Return FPGA image hardware metrics (clear on read).)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -M -S {}".format(slot), echo=True)
            assert len(stdout) == 57
            assert len(stderr) == 1
            assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot])
            assert stdout[2] == 'sdacl-slave-timeout=0'
            assert stdout[50] == 'Clock Group C Frequency (Mhz)'
            assert stdout[51] == '0  0  '

    def test_load_local_image(self):
        for slot in range(self.num_slots):
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-load-local-image -S {} -I {}".format(slot, self.cl_hello_world_agfi), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == "AFI          {}       {}  loaded            0        ok               0       {}".format(slot, self.cl_hello_world_agfi, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0xf000      {}'.format(slot, self.slot2device[slot])
            self.fpga_clear_local_image(slot)

            # -A
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-load-local-image -S {} -I {} -A".format(slot, self.cl_hello_world_agfi), echo=True)
            assert len(stdout) == 1
            assert len(stderr) == 1
            # Poll for it to be loaded
            while True:
                fpgaLocalImage = aws_fpga_test_utils.fpga_describe_local_image(slot)
                logger.info('status={}'.format(fpgaLocalImage.statusName))
                if fpgaLocalImage.statusName != 'loaded':
                    time.sleep(1)
                    continue
                (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -S {}".format(slot), echo=True)
                assert len(stdout) == 3
                assert len(stderr) == 1
                assert stdout[0] == "AFI          {}       {}  loaded            0        ok               0       {}".format(slot, self.cl_hello_world_agfi, self.shell_version)
                assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0xf000      {}'.format(slot, self.slot2device[slot])
                break
            self.fpga_clear_local_image(slot)

            # -H
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-load-local-image -S {} -I {} -H".format(slot, self.cl_hello_world_agfi), echo=True)
            assert len(stdout) == 5
            assert len(stderr) == 1
            assert stdout[0] == 'Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion'
            assert stdout[1] == "AFI          {}       {}  loaded            0        ok               0       {}".format(slot, self.cl_hello_world_agfi, self.shell_version)
            assert stdout[2] == 'Type  FpgaImageSlot  VendorId    DeviceId    DBDF'
            assert stdout[3] == 'AFIDEVICE    {}       0x1d0f      0xf000      {}'.format(slot, self.slot2device[slot])
            self.fpga_clear_local_image(slot)

            # -F
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-load-local-image -S {} -I {} -F".format(slot, self.cl_hello_world_agfi), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == "AFI          {}       {}  loaded            0        ok               0       {}".format(slot, self.cl_hello_world_agfi, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0xf000      {}'.format(slot, self.slot2device[slot])
            self.fpga_clear_local_image(slot)

    def test_clear_local_image(self):
        for slot in range(self.num_slots):
            # Test clearing already cleared
            self.fpga_clear_local_image(slot)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-clear-local-image -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot])

            # -A (async)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-clear-local-image -S {} -A".format(slot), echo=True)
            assert len(stdout) == 1
            assert len(stderr) == 1

            # Clear again immediately. It should fail because busy
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-clear-local-image -S {} -A".format(slot), echo=True, check=False)
            assert rc != 0
            assert len(stdout) == 2
            assert len(stderr) == 1
            assert stdout[0] == 'Error: (3) busy'

            # Poll for cleared
            while True:
                fpgaLocalImage = aws_fpga_test_utils.fpga_describe_local_image(slot)
                logger.info('status={}'.format(fpgaLocalImage.statusName))
                if fpgaLocalImage.statusName != 'cleared':
                    time.sleep(1)
                    continue
                (rc, stdout, stderr) = self.run_cmd("sudo fpga-describe-local-image -S {}".format(slot), echo=True)
                assert len(stdout) == 3
                assert len(stderr) == 1
                assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
                assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(slot, self.slot2device[slot])
                break

    @pytest.mark.skip(reason="No way to test right now.")
    def test_start_virtual_jtag(self):
        assert False
        # This doesn't return until a ctrl-c is sent to the process.
        for slot in range(self.num_slots):
            # Start it on an empty slot
            self.fpga_clear_local_image(slot)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-start-virtual-jtag -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'AFI          {}       none                    cleared           1        ok               0       {}'.format(slot, self.shell_version)
            assert stdout[1] == 'AFIDEVICE    {}       0x1d0f      0x1042      {}'.format(self.slot2device[slot])

    def test_get_virtual_led(self):
        # This is tested in the cl_hello_world example
        for slot in range(self.num_slots):
            # Start it on an empty slot
            self.fpga_clear_local_image(slot)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-get-virtual-led -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'FPGA slot id {} have the following Virtual LED:'.format(slot)
            assert re.match('[01]{4}-[01]{4}-[01]{4}-[01]{4}', stdout[1])

    def test_virtual_dip_switch(self):
        for slot in range(self.num_slots):
            # Start it on an empty slot
            self.fpga_clear_local_image(slot)
            # Set to a known value
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-set-virtual-dip-switch -S {} -D 0000000000000000".format(slot), echo=True)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-get-virtual-dip-switch -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'FPGA slot id {} has the following Virtual DIP Switches:'.format(slot)
            assert stdout[1] == '0000-0000-0000-0000'

            (rc, stdout, stderr) = self.run_cmd("sudo fpga-set-virtual-dip-switch -S {} -D 1111111111111111".format(slot), echo=True)
            (rc, stdout, stderr) = self.run_cmd("sudo fpga-get-virtual-dip-switch -S {}".format(slot), echo=True)
            assert len(stdout) == 3
            assert len(stderr) == 1
            assert stdout[0] == 'FPGA slot id {} has the following Virtual DIP Switches:'.format(slot)
            assert stdout[1] == '1111-1111-1111-1111'
