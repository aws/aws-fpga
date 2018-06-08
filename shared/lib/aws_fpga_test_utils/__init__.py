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
import csv
import git
import logging
import os
from os.path import basename, dirname, realpath
import platform
import re
import subprocess
import sys
import traceback
try:
    # For Python 3.0 and later
    from urllib.request import urlopen
except ImportError:
    # Fall back to Python 2's urllib2
    from urllib2 import urlopen
try:
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__file__)

def get_git_repo_root(path=None):
    if not path:
        path = os.getcwd()
    repo = git.Repo(path, search_parent_directories=True)
    repo_dir = repo.git.rev_parse("--show-toplevel")
    return repo_dir

def edma_driver_installed():
    if find_files_in_path('/lib/modules', 'edma-drv.ko'):
        return True
    if os.path.exists('/etc/modules-load.d/edma.conf'):
        return True
    if os.system('/usr/sbin/lsmod | grep edma_drv') == 0:
        return True
    return False

def remove_edma_driver():
    logger.info("Removing the edma driver")
    # This fails if the driver isn't installed
    edma_driver_ko_list = find_files_in_path('/lib/modules', 'edma-drv.ko')
    for edma_ko in edma_driver_ko_list:
        logger.info("Removing {}".format(edma_ko))
        assert os.system("sudo rm -f {}".format(edma_ko)) == 0

    assert os.system('sudo rm -f /etc/modules-load.d/edma.conf') == 0
    os.system('sudo rmmod edma-drv')

def edma_driver_install_steps():
    logger.info("Running edma driver install steps")
    # Check if the file exists
    if edma_driver_installed():
        logger.info("edma driver is already installed.")
        remove_edma_driver()

    assert os.system('cd $WORKSPACE/sdk/linux_kernel_drivers/edma && \
        make clean && \
        make && \
        sudo insmod edma-drv.ko') == 0

# Function to install the edma drivers
def install_edma_driver():
    logger.info("Installing the edma drivers")

    # Check if the file exists
    if edma_driver_installed():
        logger.info("Edma driver is already installed.")
        remove_edma_driver()
    edma_driver_install_steps()

def xdma_driver_installed():
    if find_files_in_path('/lib/modules', 'xdma.ko'):
        return True
    if os.path.exists('/etc/modules-load.d/xdma.conf'):
        return True
    if os.system('/usr/sbin/lsmod | grep xdma') == 0:
        return True
    if os.path.exists('/etc/udev/rules.d/10-xdma.rules'):
        return True
    return False

def remove_xdma_driver():
    logger.info("Removing the xdma driver.")
    # This fails if the driver isn't installed
    os.system('sudo rmmod xdma')

    xdma_driver_ko_list = find_files_in_path('/lib/modules', 'xdma.ko')
    for xdma_ko in xdma_driver_ko_list:
        logger.info("Removing {}".format(xdma_ko))
        assert os.system("sudo rm -f {}".format(xdma_ko)) == 0

    assert os.system('sudo rm -f /etc/modules-load.d/xdma.conf') == 0
    assert os.system('sudo rm -f /etc/udev/rules.d/10-xdma.rules') == 0

def install_xdma_driver():
    logger.info("Installing the xdma driver")

    # Check if the file exists
    if xdma_driver_installed():
        logger.info("xdma driver is already installed.")
        remove_xdma_driver()
    assert os.system('cd $WORKSPACE/sdk/linux_kernel_drivers/xdma && \
        make clean && \
        make && \
        sudo insmod xdma.ko poll_mode=1') == 0

def remove_xocl_driver():
    logger.info("Removing the xocl driver.")
    # This fails if the driver isn't installed
    os.system('sudo rmmod xocl')

    xocl_driver_ko_list = find_files_in_path('/lib/modules', 'xocl.ko')
    for xocl_ko in xocl_driver_ko_list:
        logger.info("Removing {}".format(xocl_ko))
        assert os.system("sudo rm -f {}".format(xocl_ko)) == 0

    assert os.system('sudo rm -f /etc/udev/rules.d/10-xocl.rules') == 0

def remove_all_drivers():
    remove_xdma_driver()
    remove_edma_driver()
    remove_xocl_driver()

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
    instance_id = urlopen('http://169.254.169.254/latest/meta-data/instance-id').read()
    return instance_id

def get_instance_type():
    instance_type = urlopen('http://169.254.169.254/latest/meta-data/instance-type').read()
    return instance_type

def get_num_fpga_slots(instance_type):
    if re.match('f1\.2xlarge', instance_type):
        return 1
    elif re.match('f1\.16xlarge', instance_type):
        return 8
    return 0

def read_clock_recipes():
    '''
    @returns a struct liek the following:
    CLOCK_RECIPES = {
        'A': {
            'clock_names': ['clk_main_a0, clk_extra_a1, ...],
            'recipes': {
                'A0': {
                    'clk_main_a0': '125',
                    'clk_extra_a1': '62.5',
                    ...
                },
                ...
            }
        },
        ...
    }
    '''
    git_repo_dir = get_git_repo_root(dirname(__file__))
    clock_recipes_csv = os.path.join(git_repo_dir, 'hdk/docs/clock_recipes.csv')
    with open(clock_recipes_csv, 'r') as csvfile:
        CLOCK_RECIPES = {}
        csvreader = csv.reader(csvfile)
        for row in csvreader:
            if not row or row[0] == '':
                continue
            matches = re.match('Clock Group (\S)', row[0])
            assert matches, "Invalid format in {}. Expected 'Clock Group \S'\n{}".format(clock_recipes_csv, row[0])
            clock_group = matches.group(1)
            logger.debug(row[0])
            CLOCK_RECIPES[clock_group] = {}
            CLOCK_RECIPES[clock_group]['clock_names'] = []
            CLOCK_RECIPES[clock_group]['recipes'] = {}
            row = next(csvreader)
            assert row[0] == 'Recipe Number', "Invalid format in {}. Expected 'Recipe Number'\n{}".format(clock_recipes_csv, row[0])
            for clock_name in row[1:]:
                if clock_name == '':
                    break;
                CLOCK_RECIPES[clock_group]['clock_names'].append(clock_name)
            logger.debug("  Clock names:\n  {}".format("\n  ".join(CLOCK_RECIPES[clock_group]['clock_names'])))
            while True:
                row = next(csvreader)
                if not row or row[0] == '':
                    break
                recipe_number = row[0]
                CLOCK_RECIPES[clock_group]['recipes'][recipe_number] = {}
                for i in range(len(CLOCK_RECIPES[clock_group]['clock_names'])):
                    clock_name = CLOCK_RECIPES[clock_group]['clock_names'][i]
                    CLOCK_RECIPES[clock_group]['recipes'][recipe_number][clock_name] = row[i + 1]
    return CLOCK_RECIPES

def find_files_in_path(root_folder='/lib/modules', filename='xdma.ko'):
    found_file_list=[]

    for root, dirs, files in os.walk(root_folder):
        for file in files:
            if file == filename:
                 found_file_list.append(os.path.join(root, filename))

    return found_file_list

