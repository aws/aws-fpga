# Copyright 2015-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may
# not use this file except in compliance with the License. A copy of the
# License is located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
import fpga_mgmt
import fpga_pci
import fpga_dma
import os
import logging
from ctypes import *

logger = logging.getLogger(__name__)

class FPGAFuncs(object):
    def __init__(self):
        self.slot = int(os.environ['BSWAPPER_SLOT'], 0)
        self.AFI = os.environ['BSWAPPER_AFI'].encode('utf-8')
        self.register = int(os.environ['BSWAPPER_REG'], 0)
        logger.info("Slot to be loaded: {}\nAFI: {}\nregister: 0x{:x}".format(self.slot, self.AFI, self.register))
        fpga_mgmt.fpga_mgmt_init()

    def get_slot_info(self):
        logger.info("Retrieving slot info (slot={}).".format(self.slot))
        ret = c_int32()
        info = fpga_mgmt.struct_fpga_mgmt_image_info()
        info.slot_id = self.slot
        ret = fpga_mgmt.fpga_mgmt_describe_local_image(info.slot_id, byref(info), c_uint32(0))
        if ret != 0:
            logger.error("Unable to describe current image (returned {})".format(ret))
            raise RuntimeError("Unable to describe current image")
        return info

    def slot_state(self):
        info = self.get_slot_info()
        return fpga_mgmt.c__Ea_FPGA_STATUS_LOADED__enumvalues[info.status]

    def load_afi(self):
        info = self.get_slot_info()
        ret = c_int32()
        logger.info("Current AFI: {}".format(info.ids.afi_id))
        load_opt = fpga_mgmt.union_fpga_mgmt_load_local_image_options()
        fpga_mgmt.fpga_mgmt_init_load_local_image_options(byref(load_opt))
        load_opt._1.slot_id = self.slot
        load_opt._1.afi_id = cast(self.AFI, POINTER(c_char))
        load_opt._1.flags = fpga_mgmt.FPGA_CMD_FORCE_SHELL_RELOAD
        info = fpga_mgmt.struct_fpga_mgmt_image_info()
        # Choosing arbitrary delay and polling intervals - 3000 and 20 msec
        ret =  fpga_mgmt.fpga_mgmt_load_local_image_sync_with_options(byref(load_opt), 3000, 20, byref(info))
        if ret != 0:
            raise RuntimeError("Could not load AFI {}".format(self.AFI))
        logger.info("Loaded AFI: {}".format(info.ids.afi_id))

    def swap_bytes(self, input_data):
        input_data = int(input_data, 0)
        ret = c_int32()
        handle = fpga_pci.pci_bar_handle_t()
        ret = fpga_pci.fpga_pci_attach(0, fpga_pci.FPGA_APP_PF, fpga_pci.APP_PF_BAR0, 0, byref(handle))
        if ret != 0:
            raise RuntimeError("Could not  attach to slot {}".format(self.slot))
        logger.info("input value: 0x{:x}".format(input_data))
        ret = fpga_pci.fpga_pci_poke(handle, self.register, input_data)
        if ret != 0:
            raise RuntimeError("Could not write to slot {}".format(self.slot))
        swapped_val = fpga_pci.uint32_t()
        ret = fpga_pci.fpga_pci_peek(handle, self.register, byref(swapped_val))
        if ret != 0:
            raise RuntimeError("Could not read from slot {}".format(self.slot))
        logger.info("Swapped value: 0x{:x}".format(swapped_val.value))
        return "0x{:x}".format(swapped_val.value)

    def clear_fpga(self):
        logger.info("Clearing AFI on slot {}".format(self.slot))
        ret = c_int32()
        ret = fpga_mgmt.fpga_mgmt_clear_local_image(self.slot)
        if ret != 0:
            raise RuntimeError("Could not clear slot {}".format(self.slot))

    def clean_up(self):
        fpga_mgmt.fpgma_mgmt_close()
