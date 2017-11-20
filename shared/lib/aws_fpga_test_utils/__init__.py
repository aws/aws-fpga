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

import git
import logging
import os
import re
import subprocess
import sys
import traceback
import urllib2
try:
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print "error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1])
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__file__)

def get_git_repo_root(path=None):
    if not path:
        path = os.getcwd()
    repo = git.Repo(path, search_parent_directories=True)
    repo_dir = repo.git.rev_parse("--show-toplevel")
    return repo_dir

def remove_edma_driver():
    logger.info("Removing the edma driver")
    os.system('sudo rmmod edma-drv')
    assert os.system('sudo rm -f /lib/modules/`uname -r`/edma-drv.ko') == 0
    assert os.system('sudo rm -f /etc/modules-load.d/edma.conf') == 0

def edma_driver_install_steps():
    logger.info("Running edma driver install steps")
    assert os.system('echo \'edma\' | sudo tee -a /etc/modules-load.d/edma.conf') == 0
    assert os.system('cd $WORKSPACE/sdk/linux_kernel_drivers/edma && \
        make clean && \
        make && \
        sudo cp edma-drv.ko /lib/modules/`uname -r`/ && \
        sudo depmod && \
        sudo modprobe edma-drv') == 0

# Function to install the edma drivers
def install_edma_driver():
    logger.info("Installing the edma drivers")

    # Check if the file exists
    if os.path.exists('/etc/modules-load.d/edma.conf'):
        logger.info("Edma driver is already installed.")
        remove_edma_driver()
    edma_driver_install_steps()

class FpgaLocalImage:
    def __init__(self):
        self.type = None
        self.slot = None
        self.agfi = None
        self.statusName = None
        self.statusCode = None
        self.errorName = None
        self.errorCode = None
        self.shVersion = None
        self.vendorId = None
        self.deviceId = None
        self.dbdf = None
        return
    
    def describe_local_image(self, slot):
        '''
Example output:
$ sudo fpga-describe-local-image -S 0 -R -H
Type  FpgaImageSlot  FpgaImageId             StatusName    StatusCode   ErrorName    ErrorCode   ShVersion
AFI          0       agfi-09c2a21805a8b9257  loaded            0        ok               0       0x0729172b
Type  FpgaImageSlot  VendorId    DeviceId    DBDF
AFIDEVICE    0       0x1d0f      0xf001      0000:00:1d.0
'''
        p = subprocess.Popen(['sudo', 'fpga-describe-local-image', '-S', str(slot), '-R', '-H'], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (stdout_lines, stderr_lines) = p.communicate()
        rc = p.returncode
        if rc:
            raise RuntimeError("fpga-describe-local-image failed with rc={}\nstdout:\n{}\nstderr:{}".format(rc, stdout_lines, stderr_lines))
        stdout_lines = stdout_lines.split('\n')
        (self.type, self.slot, self.agfi, self.statusName, self.statusCode, self.errorName, self.errorCode, self.shVersion) = stdout_lines[1].split()
        (type2, slot2, self.vendorId, self.deviceId, self.dbdf) = stdout_lines[3].split()
        return

def fpga_describe_local_image(slot):
    fpgaLocalImage = FpgaLocalImage()
    fpgaLocalImage.describe_local_image(slot)
    return fpgaLocalImage

def get_instance_id():
    instance_id = urllib2.urlopen('http://169.254.169.254/latest/meta-data/instance-id').read()
    return instance_id

def get_instance_type():
    instance_type = urllib2.urlopen('http://169.254.169.254/latest/meta-data/instance-type').read()
    return instance_type

def get_num_fpga_slots(instance_type):
    if re.match(r'f1\.2xlarge', instance_type):
        return 1
    elif re.match(r'f1\.16xlarge', instance_type):
        return 8
    return 0
