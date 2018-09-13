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
import glob
import argparse
import logging

fio_git = "https://github.com/axboe/fio.git"

# Use a SHA that is "known good" for F1 DMA testing
fio_sha = "e5aaf1e677d1413125ffaf7aae48b1e8f4ce9ebc"

# FIO branch name that we'll apply patches to
fio_branch = "fio-2.21-f1-dma-tools-052118"

# Patch file directory
patches_dir = "../patches/fio-2.21"

# Logger
logger = logging.getLogger('logger')

def print_success(scripts_path, install_path):
    print("")
    print("FIO installation and build complete!")

def cmd_exec(cmd):
    # Execute the cmd, check the return and exit on failures
    ret = os.system(cmd)
    if ret != 0:
        logger.error("cmd='%s' failed with ret=%d, exiting" % (cmd, ret))
        sys.exit(1)

def install_fio(install_path):
    logger.debug("install_fio: install_path=%s" % (install_path))

    if os.path.exists(install_path):
        # Allow the user to remove an already existing install_path
        logger.error("install_path=%s allready exists." % (install_path))
        logger.error("Please specify a different directory or remove the existing directory, exiting")
        sys.exit(1)

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

    # Clone the FIO repo
    logger.info("Cloning %s into %s" % (fio_git, install_path))
    cmd_exec("git clone %s" % (fio_git))

    # cd to the fio directory
    os.chdir("fio")

    # Checkout the feature branch
    logger.info("Checking out feature branch %s" % (fio_branch))
    cmd_exec("git checkout %s -b %s" % (fio_sha, fio_branch))

    # Check that the patches can be applied
    for patchfile in patchfiles:
        logger.debug("Checking git apply patch for patchfile=%s" % patchfile)
        cmd_exec("git apply --check %s" % (patchfile))

    # Apply the patches
    for patchfile in patchfiles:
        logger.info("Applying patch for patchfile=%s" % patchfile)
        cmd_exec("git am %s" % (patchfile))

    # Build FIO
    cmd_exec("make")

    # For convenience, we install a soft-link from the install_path back to the
    # the scripts_path.  We first remove any pre-existing soft-link.
    cmd_exec("rm -f %s/fio" % (scripts_path))
    cmd_exec("ln -s %s/fio/fio %s/fio" % (install_path, scripts_path))

    # cd back to the original directory
    os.chdir("%s" % (cwd))

    # Print a success message
    print_success(scripts_path, install_path)

def main():
    parser = argparse.ArgumentParser(
        description="Installs FIO and applies FIO F1 DMA related patches.")
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

    install_fio(args.install_path)

if __name__ == '__main__':
    main()
