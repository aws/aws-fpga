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
import platform

dpdk_git = "https://github.com/DPDK/dpdk.git"
pktgen_git = "git://dpdk.org/apps/pktgen-dpdk"
meson_git = "https://github.com/mesonbuild/meson/releases/download/0.59.2/meson-0.59.2.tar.gz"
ninja_git = "https://github.com/ninja-build/ninja/releases/download/v1.10.2/ninja-linux.zip"
meson_file = meson_git[meson_git.rfind('/')+1:]
meson_ver  = meson_file[:meson_file.find('.tar.gz')]

# Use a version that is "known good" for use with pktgen 
dpdk_ver = "v20.08"

# Use a version that is "known good" for testing
pktgen_ver = "pktgen-20.09.0"

# Patch file directory
patches_dir = "../patches/pktgen-dpdk/master"

# DPDK make target
make_tgt = "x86_64-native-linuxapp-gcc"
try:
    if "aarch64" in platform.processor():
        make_tgt = "arm64-armv8a-linuxapp-gcc"
except AttributeError:
    pass

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
        cmd_exec("sudo apt -y install libnuma-dev")
        cmd_exec("sudo apt -y install libpcap-dev")
    else:
        cmd_exec("sudo yum -y install numactl-devel")
        cmd_exec("sudo yum -y install libpcap-devel") 

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
    # Read in the pktgen patch filenames
    patchfiles = []
    for patchfile in sorted(glob.iglob("%s/000*.patch" % (patches_path))):
        logger.debug("found patchfile=%s for pktgen" % patchfile)
	patchfiles.append(os.path.abspath(patchfile))
    # Read in the dpdk patch filenames
    dpdk_patchfiles = []
    for dpdk_patchfile in sorted(glob.iglob("%s/dpdk*.patch" % (patches_path))):
        logger.debug("found patchfile=%s for dpdk" % dpdk_patchfile)
	dpdk_patchfiles.append(os.path.abspath(dpdk_patchfile))
    # cd to the install_path directory
    os.chdir("%s" % (install_path))

    # meson install
    logger.info("download and untar meson")
    cmd_exec("wget %s" % (meson_git))
    cmd_exec("tar -xf %s" %(meson_file))
    cmd_exec("rm %s" %(meson_file))
    # ninja install
    logger.info("download and unzip ninja")
    cmd_exec("wget %s" % (ninja_git))
    cmd_exec("unzip ninja-linux.zip")
    cmd_exec("rm ninja-linux.zip")

    # Clone the DPDK repo
    logger.info("Cloning %s version of %s into %s" % (dpdk_ver, dpdk_git, install_path))
    cmd_exec("git clone -b %s %s" % (dpdk_ver, dpdk_git))

    # cd to the dpdk directory 
    os.chdir("dpdk")
    for dpdk_patchfile in dpdk_patchfiles:
        logger.info("Applying patch for patchfile=%s" % dpdk_patchfile)
        cmd_exec("git apply %s" % (dpdk_patchfile))

    # Configure and build DPDK 
    #cmd_exec("make install T=%s" % (make_tgt))
    cmd_exec("export PATH=$PATH:%s; ../%s/meson.py build -Denable_kmods=true" % (install_path, meson_ver))
    builddir="./build"
    os.chdir("%s" % (builddir))
    cmd_exec("../../ninja")
    cmd_exec("sudo ../../ninja install")
    os.chdir("../")
    #cmd_exec("make install T=x86_64-native-linuxapp-gcc")
    # cd to the install_path directory
    os.chdir("%s" % (install_path))

    # Clone the pktgen-dpdk repo
    logger.info("Cloning %s version of %s into %s" % (pktgen_ver, pktgen_git, install_path))
    cmd_exec("git clone -b %s %s" % (pktgen_ver, pktgen_git))

    # cd to the pktgen-dpdk directory 
    os.chdir("pktgen-dpdk")

    # Check that the patches can be applied
    for patchfile in patchfiles:
        logger.debug("Checking git apply patch for patchfile=%s" % patchfile)
        cmd_exec("git apply --check %s" % (patchfile))

    # Apply the patches
    for patchfile in patchfiles:
        logger.info("Applying patch for patchfile=%s" % patchfile)
        cmd_exec("git apply %s" % (patchfile))

    # Build pktgen-dpdk
    cmd_exec("ln -s %s/%s/meson.py %s/meson" %(install_path, meson_ver, install_path))
    # also set pkg_config_path and ld_lib_path which are expected to /usr/local/lib64 as per
    # https://doc.dpdk.org/guides/prog_guide/build-sdk-meson.html
    cmd_exec("export PKG_CONFIG_PATH=/usr/local/lib64/pkgconfig/; export LD_LIBRARY_PATH=/usr/local/lib64; export PATH=$PATH:%s; export RTE_SDK=%s/dpdk; export RTE_TARGET=%s; make" % (install_path, install_path, make_tgt))

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
