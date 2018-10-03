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
import logging

dpdk_git = "https://github.com/DPDK/dpdk.git"
pktgen_git = "git://dpdk.org/apps/pktgen-dpdk"

# Use a SHA that is "known good" for use with pktgen 
dpdk_sha = "a5dce55556286cc56655320d975c67b0dbe08693"

# Use a SHA that is "known good" for testing
pktgen_sha = "f05efdb91eefd6c2cb59f2eeac839bf7709f9a48"

# dpdk branch name that we'll use
dpdk_branch = "dpdk-ena-061418"

# pktgen branch name that we'll apply patches to
pktgen_branch = "pktgen-dpdk-ena-061418"

# Patch file directory
patches_dir = "../patches/pktgen-dpdk/master"

# DPDK make target
make_tgt = "x86_64-native-linuxapp-gcc"

# Logger
logger = logging.getLogger('logger')

def print_success(scripts_path, install_path):
    print("")
    print("pktgen-dpdk installation and build complete!")
    print("pktgen-dpdk may be setup via the following step:")
    print("  sudo %s/virtual_ethernet_pktgen_setup.py %s --eni_dbdf <ENI_DBDF> --eni_ethdev <ENI_ETHDEV>" % (scripts_path, install_path))

def cmd_exec(cmd):
    # Execute the cmd, check the return and exit on failures
    ret = os.system(cmd)
    if ret != 0:
        logger.error("cmd='%s' failed with ret=%d, exiting" % (cmd, ret))
        sys.exit(1)

def install_dpdk_dep():
    distro = platform.linux_distribution()
    if (distro[0] == "Ubuntu"):
        cmd_exec("apt -y install libnuma-dev")
        cmd_exec("apt -y install libpcap-dev")
    else:
        cmd_exec("yum -y install numactl-devel.x86_64")
        cmd_exec("yum -y install libpcap-devel") 

def install_pktgen_dpdk(install_path):
    logger.debug("install_pktgen_dpdk: install_path=%s" % (install_path))

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

    # Construct the path to the git patch files
    patches_path = "%s/%s" % (scripts_path, patches_dir)
    logger.info("Patches will be installed from %s" % (patches_path))

    # Read in the patch filenames
    patchfiles = []
    for patchfile in sorted(glob.iglob("%s/000*.patch" % (patches_path))):
        logger.debug("found patchfile=%s" % patchfile)
	patchfiles.append(os.path.abspath(patchfile))

    # cd to the install_path directory
    os.chdir("%s" % (install_path))

    # Clone the DPDK repo
    logger.info("Cloning %s into %s" % (dpdk_git, install_path))
    cmd_exec("git clone %s" % (dpdk_git))

    # cd to the dpdk directory 
    os.chdir("dpdk")

    # Checkout the feature branch
    logger.info("Checking out dpdk feature branch %s" % (dpdk_branch))
    cmd_exec("git checkout %s -b %s" % (dpdk_sha, dpdk_branch))

    # Configure and build DPDK 
    cmd_exec("make install T=%s" % (make_tgt))

    # cd to the install_path directory
    os.chdir("%s" % (install_path))

    # Clone the pktgen-dpdk repo
    logger.info("Cloning %s into %s" % (pktgen_git, install_path))
    cmd_exec("git clone %s" % (pktgen_git))

    # cd to the pktgen-dpdk directory 
    os.chdir("pktgen-dpdk")

    # Checkout the feature branch
    logger.info("Checking out pktgen feature branch %s" % (pktgen_branch))
    cmd_exec("git checkout %s -b %s" % (pktgen_sha, pktgen_branch))

    # Check that the patches can be applied
    for patchfile in patchfiles:
        logger.debug("Checking git apply patch for patchfile=%s" % patchfile)
        cmd_exec("git apply --check %s" % (patchfile))

    # Apply the patches
    for patchfile in patchfiles:
        logger.info("Applying patch for patchfile=%s" % patchfile)
        cmd_exec("git am %s" % (patchfile))

    # Build pktgen-dpdk
    cmd_exec("export RTE_SDK=%s/dpdk; export RTE_TARGET=%s; make" % (install_path, make_tgt))

    # cd back to the original directory
    os.chdir("%s" % (cwd))

    # Print a success message
    print_success(scripts_path, install_path)

def main():
    parser = argparse.ArgumentParser(
        description="Installs pktgen-dpdk and applies pktgen related patches for ENA use.")
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

    install_pktgen_dpdk(args.install_path)

if __name__ == '__main__':
    main()
