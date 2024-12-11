#!/usr/bin/env python3

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
import distro
import glob
import argparse
import logging

dpdk_git = "https://github.com/DPDK/dpdk.git"
dpdk_kmods_git = "git://dpdk.org/dpdk-kmods"

# Use a SHA that is "known good" for SPP testing
dpdk_ver = "v24.03"

# Patch file directories
dpdk_patches_dir = "../patches/spp-dpdk"
dpdk_kmods_patches_dir = "../patches/spp-dpdk-kmods"

# Logger
logger = logging.getLogger('logger')

def print_success(scripts_path, install_path):
    print("")
    print("DPDK installation and build complete!")
    print("A simple loopback test may be run via the following steps:")
    print("  sudo fpga-load-local-image -S 0 -I <SDE loopback CL AGFI>")
    print("  sudo %s/virtual_ethernet_setup.py %s/dpdk 0" % (scripts_path, install_path))
    print("  cd %s/dpdk" % (install_path))
    print("  sudo ./build/app/dpdk-testpmd -l 0-1  -- --port-topology=loop --auto-start --tx-first --stats-period=3")

def cmd_exec(cmd):
    # Execute the cmd, check the return and exit on failures
    ret = os.system(cmd)
    if ret != 0:
        logger.error("cmd='%s' failed with ret=%d, exiting" % (cmd, ret))
        sys.exit(1)

def install_dpdk_dep():
    installed_distro = distro.name()
    if (installed_distro == "Ubuntu"):
        cmd_exec("apt -y install libnuma-dev")
        cmd_exec("apt -y install libpcap-dev")
        cmd_exec("apt -y install meson")
        cmd_exec("apt -y install python3-pyelftools")
    else:
        cmd_exec("yum -y install numactl-devel.x86_64")
        cmd_exec("yum -y install libpcap-devel")
        cmd_exec("yum -y install meson")
        cmd_exec("yum -y install python3-pyelftools")

def install_dpdk(install_path):
    logger.debug("install_dpdk: install_path=%s" % (install_path))

    if os.path.exists(install_path):
        # Allow the user to remove an already existing install_path
        logger.error("install_path=%s allready exists." % (install_path))
        logger.error("Please specify a different directory or remove the existing directory, exiting")
        sys.exit(1)

    # Install DPDK dependencies
    install_dpdk_dep()

    # Stash away the current working directory
    cwd = os.getcwd()
    scripts_path = os.path.dirname(os.path.abspath(sys.argv[0]))
    logger.debug("scripts directory path is %s" % (scripts_path))

    # Make the install_path directory
    cmd_exec("mkdir %s" % (install_path))

    # Construct the path to the dpdk-kmods git patch files
    dpdk_kmods_patches_path = "%s/%s" % (scripts_path, dpdk_kmods_patches_dir)
    logger.info("Patches will be installed from %s" % (dpdk_kmods_patches_path))

    # Read in the patch filenames
    dpdk_kmods_patchfiles = []
    for patchfile in sorted(glob.iglob("%s/000*.patch" % (dpdk_kmods_patches_path))):
        logger.debug("found patchfile=%s" % patchfile)
        dpdk_kmods_patchfiles.append(os.path.abspath(patchfile))

    # Construct the path to the dpdk git patch files
    dpdk_patches_path = "%s/%s" % (scripts_path, dpdk_patches_dir)
    logger.info("Patches will be installed from %s" % (dpdk_patches_path))

    # Read in the patch filenames
    dpdk_patchfiles = []
    for patchfile in sorted(glob.iglob("%s/000*.patch" % (dpdk_patches_path))):
        logger.debug("found patchfile=%s" % patchfile)
        dpdk_patchfiles.append(os.path.abspath(patchfile))

    # cd to the install_path directory
    os.chdir("%s" % (install_path))

    # Clone the DPDK-KMODS repo
    logger.info("Cloning %s into %s" % (dpdk_kmods_git, install_path))
    cmd_exec("git clone %s" % (dpdk_kmods_git))

    # cd to the dpdk-kmods directory
    os.chdir("dpdk-kmods")

    # Apply the patches
    for patchfile in dpdk_kmods_patchfiles:
        logger.info("Applying patch for patchfile=%s" % patchfile)
        cmd_exec("git am %s" % (patchfile))

    # Clone the DPDK repo
    os.chdir("%s" % (install_path))
    logger.info("Cloning %s version of %s into %s" % (dpdk_ver, dpdk_git, install_path))
    cmd_exec("git clone -b %s %s" % (dpdk_ver, dpdk_git))

    # cd to the dpdk directory
    os.chdir("dpdk")

    # Apply the patches
    for patchfile in dpdk_patchfiles:
        logger.info("Applying patch for patchfile=%s" % patchfile)
        cmd_exec("git am %s" % (patchfile))

    cmd_exec("cp -r ../dpdk-kmods/linux ./kernel/")

    # Configure the DPDK build
    cmd_exec("meson -Dexamples=all build")
    cmd_exec("ninja -C build")

    # cd back to the original directory
    os.chdir("%s" % (cwd))

    # Print a success message
    print_success(scripts_path, install_path)

def main():
    parser = argparse.ArgumentParser(
        description="Installs the DPDK (master) and applies DPDK SPP PMD related patches.")
    parser.add_argument('install_path', metavar='INSTALL_DIR', type=str,
        help = "specify the full installation directory path")
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

    install_dpdk(args.install_path)

if __name__ == '__main__':
    main()
