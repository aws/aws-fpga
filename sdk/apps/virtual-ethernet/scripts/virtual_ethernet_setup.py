#!/usr/bin/env python

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
import os
import sys
import platform
import glob
import argparse
import subprocess
import logging

# DPDK make config target
make_tgt = "x86_64-native-linuxapp-gcc"

dpdk_devbind = "./usertools/dpdk-devbind.py"
num_2MB_hugepages = 16384

# Logger
logger = logging.getLogger('logger')

def print_success(dpdk_path):
    print("")
    print("DPDK setup complete!")
    print("A simple loopback test may be run via the following steps:")
    print("  cd %s" % (dpdk_path))
    print("  sudo ./%s/app/testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=3" % (make_tgt))

def check_output(args, stderr=None):
    return subprocess.Popen(args, stdout=subprocess.PIPE,
                            stderr=stderr).communicate()[0]

def cmd_exec(cmd, check_return=True):
    # Execute the cmd, check the return and exit on failures
    ret = os.system(cmd)
    if check_return == True and ret != 0:
        logger.error("cmd='%s' failed with ret=%d, exiting" % (cmd, ret))
        sys.exit(1)

def load_uio():
    distro = platform.linux_distribution()
    if (distro[0] == "Ubuntu"):
        cmd_exec("modprobe uio")
    else:
        cmd_exec("modprobe uio_pci_generic")

def fpga_slot_str2dbdf(fpga_slot_str):
    dbdf = "None"
    found = False
    cmd = "fpga-describe-local-image-slots"
    # Exec the command first to give an error message
    # if the SDK hasn't been installed.
    cmd_exec("%s >/dev/null 2>&1" % (cmd))
    fpga_slots = check_output(cmd).splitlines() 
    for slot_str in fpga_slots:
        if found == True:
            break
        logger.debug("slot_str=%s" % slot_str)
        slot_num = ' '.join(slot_str.split()).split(' ')[1] 
        if slot_num == fpga_slot_str:
            dbdf = ' '.join(slot_str.split()).split(' ')[4] 
            found = True
    return dbdf 

def setup_dpdk(dpdk_path, fpga_slot_str, eni_dbdf, eni_ethdev):
    logger.debug("setup_dpdk: dpdk_path=%s, fpga_slot_str=%s" % (dpdk_path, fpga_slot_str))

    if os.path.exists(dpdk_path) == False:
        logger.error("dpdk_path=%s does not exist." % (dpdk_path))
        logger.error("Please specify a dpdk directory that was installed via virtual-ethernet-install.py, exiting")
        sys.exit(1)

    fpga_dbdf = fpga_slot_str2dbdf(fpga_slot_str)
    if fpga_dbdf == "None":
        logger.error("Could not get DBDF for fpga_slot_str=%s" % fpga_slot_str)
        sys.exit(1)

    # Stash away the current working directory
    cwd = os.getcwd()
    scripts_path = os.path.dirname(os.path.abspath(sys.argv[0]))
    logger.debug("scripts directory path is %s" % (scripts_path))

    # cd to the dpdk_path directory
    os.chdir("%s" % (dpdk_path))

    if os.path.exists(dpdk_devbind) == False:
        logger.error("dpdk_devbind=%s does not exist." % (dpdk_devbind))
        logger.error("Please specify a dpdk directory that was installed via virtual-ethernet-install.py, exiting")
        sys.exit(1)

    # Mount '/mnt/huge', if needed
    if os.path.exists("/mnt/huge") == False:
        cmd_exec("mkdir /mnt/huge")

    cmd_exec("mount -t hugetlbfs nodev /mnt/huge")

    # Configure hugepages
    cmd_exec("echo %d > /sys/kernel/mm/hugepages/hugepages-2048kB/nr_hugepages" % (num_2MB_hugepages))

    # Load distro-specific uio
    load_uio()

    # Remove then load igb_uio.ko
    cmd_exec("rmmod ./%s/kmod/igb_uio.ko >/dev/null 2>&1" % (make_tgt), False)
    cmd_exec("insmod ./%s/kmod/igb_uio.ko" % (make_tgt))

    # Bind the FPGA to to DPDK
    cmd_exec("%s --bind=igb_uio %s" % (dpdk_devbind, fpga_dbdf))

    # Bind the ENI device to to DPDK (optional)
    if eni_dbdf != "None" and eni_ethdev != "None":
        cmd_exec("ifdown %s" % (eni_ethdev))
        cmd_exec("%s --bind=igb_uio %s" % (dpdk_devbind, eni_dbdf))

    # cd back to the original directory
    os.chdir("%s" % (cwd))

    # Print a success message
    print_success(dpdk_path)

def main():
    parser = argparse.ArgumentParser(
        description="Sets up DPDK for SPP PMD use.")
    parser.add_argument('dpdk_path', metavar='DPDK_DIR', type=str,
        help = "specify the full DPDK directory path")
    parser.add_argument('fpga_slot', metavar='FPGA_IMAGE_SLOT', type=str,
        help = "specify the fpga-image-slot.  See fpga-describe-local-image --fpga-image-slot for more info.")
    parser.add_argument('--eni_dbdf', metavar='ENI_DBDF', type=str, default="None",
        help = "specify the ENI DBDF. e.g. see lspci output 0000:00:04.0 Ethernet controller: Device 1d0f:ec20")
    parser.add_argument('--eni_ethdev', metavar='ENI_ETHDEV', type=str, default="None",
        help = "specify the ENI Ethernet device'. e.g. see ifconfig output for eth1")
    parser.add_argument('--debug', action='store_true', required=False,
        help='Enable debug messages')
    args = parser.parse_args()

    logging_level = logging.INFO
    if args.debug:
        logging_level = logging.DEBUG

    logging_format = '%(levelname)s:%(asctime)s: %(message)s'

    logger.setLevel(logging_level)

    fh = logging.StreamHandler()

    fh.setLevel(logging_level)
    formatter = logging.Formatter(logging_format)
    fh.setFormatter(formatter)
    logger.addHandler(fh)

    setup_dpdk(args.dpdk_path, args.fpga_slot, args.eni_dbdf, args.eni_ethdev)

if __name__ == '__main__':
    main()
