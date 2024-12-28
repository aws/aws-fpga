#!/usr/bin/env python3

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
# =============================================================================


from optparse import OptionParser
import datetime
import subprocess
import os
import sys
import re


TIMESTAMP_LOG_FORMAT = "%Y-%m-%d %H:%M:%S"
TIMESTAMP_FILE_FORMAT = "%Y_%m_%d-%H%M%S"


#############################################################
# Print error message and exit
#############################################################
def print_error(err_msg):
    print(f"ERROR: {err_msg}\n")
    exit(1)


def print_warning(warn_msg):
    print(f"WARNING: {warn_msg}\n")


#############################################################
# Get version file output
#############################################################
def get_file_version(dir, file, version_key):
    version_file = os.path.join(dir, file)
    with open(version_file, 'r') as f:
        for line in f:
            if line.startswith(version_key):
                return line.split('=')[1].strip()
    print_error("Failed to detect the version string")


#############################################################
# Get PCIe IDs
#############################################################
def get_pcie_ids():
    id_file = os.path.join(os.environ['CL_DIR'], "design", "cl_id_defines.vh")
    ids = {}
    if not (os.path.exists(id_file)):
        print_error(f"Cannot find \"cl_id_defines.vh\" file for PCIe ID definitions")

    with open(id_file, 'r') as f:
        for line in f:
            if re.search(r"\s*`define\s*CL_SH_ID0", line):
                ids['pci_device_id']='0x'+line.split()[2].lstrip("32'h").split("_")[0]
                ids['pci_vendor_id']='0x'+line.split()[2].lstrip("32'h").split("_")[1]
            if re.search(r"\s*`define\s*CL_SH_ID1", line):
                ids['pci_subsystem_id']='0x'+line.split()[2].lstrip("32'h").split("_")[0]
                ids['pci_subsystem_vendor_id']='0x'+line.split()[2].lstrip("32'h").split("_")[1]
    return ids


#############################################################
# Get Vivado tool version
#############################################################
def get_cmd_output(cmd):
    cmd_out = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return cmd_out.stdout.decode('utf-8')


def get_vivado_version():
    tool_str = get_cmd_output('vivado -version')
    VERSION_CONVERSION_MAP = {
        "v2023.2.2": "v2023.2"
    }

    for line in tool_str.splitlines():
        if (re.search(r'vivado', line, re.IGNORECASE)):
            version = line.split()[1]

            if version in VERSION_CONVERSION_MAP.keys():
                return VERSION_CONVERSION_MAP[version]
            return version
    print_error("Failed to detect the Vivado version.")


#############################################################
# Generate manifest file for DCP tarball
#############################################################
def generate_manifest_file(tag, tar_dir, manifest):
    manifest_file = tag + ".manifest.txt"
    with open(os.path.join(tar_dir, manifest_file), 'w') as f:
        for key, value in manifest.items():
            f.write(f"{key}={value}\n\n")


#############################################################
# Generate DCP tarball file
#############################################################
def generate_dcp_tarball(cl, tag, clock_recipe_a, clock_recipe_b, clock_recipe_c, clock_recipe_hbm):
    dcp_name = cl + '.' + tag + '.post_route.dcp'
    dcp_violated_name = cl + '.' + tag + '.post_route.VIOLATED.dcp'
    probe_name = tag + '.debug_probes.ltx'
    checkpoints_dir = os.path.join(os.path.join(os.environ['CL_DIR']), "build", "checkpoints")
    dcp_file = os.path.join(checkpoints_dir, dcp_name)
    dcp_violated_file = os.path.join(checkpoints_dir, dcp_violated_name)
    probe_file = os.path.join(checkpoints_dir, probe_name)

    if (os.path.exists('to_aws')):
        now = datetime.datetime.now()
        surfix = now.strftime(TIMESTAMP_FILE_FORMAT)
        os.rename('to_aws', 'to_aws_backup_' + surfix)
        print(f"Save the existing to_aws/ to to_aws_backup_{surfix}/")
    os.mkdir('to_aws')

    if (os.path.exists(dcp_violated_file) or os.path.exists(dcp_file)):
        manifest = get_pcie_ids()
        manifest['manifest_format_version']=2
        if (os.path.exists(dcp_violated_file)):
            print_warning("\nDetected a post-route DCP with timing failure for AFI creation. Design functionalities are NOT guranteed.\n")
            os.system(f"cp {dcp_violated_file} ./to_aws/{tag}.SH_CL_routed.dcp")
            manifest['dcp_hash'] = get_cmd_output(f"sha256sum {dcp_violated_file}").split()[0]
        else:
            os.system(f"cp {dcp_file} ./to_aws/{tag}.SH_CL_routed.dcp")
            manifest['dcp_hash'] = get_cmd_output(f"sha256sum {dcp_file}").split()[0]
            print(get_cmd_output(f"sha256sum {dcp_file}"))
        os.system(f"cp {probe_file} ./to_aws/")
        manifest["shell_version"] = get_file_version(os.environ['HDK_SHELL_DIR'], 'shell_version.txt', os.environ['SHELL_MODE'])
        # The hdk_version is the RELEASE_VERSION in release_version.txt.
        manifest["hdk_version"] = get_file_version(os.environ['AWS_FPGA_REPO_DIR'], 'release_version.txt', 'RELEASE_VERSION')
        manifest["tool_version"] = get_vivado_version()
        manifest['date'] = tag
        manifest['clock_recipe_a'] = clock_recipe_a
        manifest['clock_recipe_b'] = clock_recipe_b
        manifest['clock_recipe_c'] = clock_recipe_c
        manifest['clock_recipe_hbm'] = clock_recipe_hbm
        manifest['dcp_file_name'] = tag + ".SH_CL_routed.dcp"
    else:
        print_error(f"Did not find the post-route DCP file from {os.environ['CL_DIR']}/build/checkpoints/")

    generate_manifest_file(tag, './to_aws', manifest)

    os.system(f"tar -cf {checkpoints_dir}/{tag}.Developer_CL.tar ./to_aws")
    os.system('rm -rf to_aws')

#############################################################
# MAIN
#############################################################
def main():
    parser = OptionParser()
    parser.add_option("-c", "--cl",
                      dest="cl",
                      help="CL module name",
                      default="cl_dram_hbm_dma")

    parser.add_option("-m", "--mode",
                      dest="mode",
                      help="Mode of shell. Supported value is: small_shell. Default to <small_shell>",
                      default="small_shell")

    parser.add_option("-f", "--flow",
                      dest="flow",
                      help="Build flow. Supported values are: SynthCL, ImplCL, BuildAll. Default to <BuildAll>.",
                      default="BuildAll")

    parser.add_option("--aws_clk_gen",
                      action="store_true",
                      help="Set this flag to enable custom clock recipes (only functions with aws_)")

    parser.add_option("--clock_recipe_a",
                      dest="clock_recipe_a",
                      help="Select Clock Recipe for Clock Group A (A0 | A1 | A2)",
                      default="A1")

    parser.add_option("--clock_recipe_b",
                      dest="clock_recipe_b",
                      help="Select Clock Recipe for Clock Group B (B0 | B1 | B2 | B3 | B4 | B5)",
                      default="B2")

    parser.add_option("--clock_recipe_c",
                      dest="clock_recipe_c",
                      help="Select Clock Recipe for Clock Group C (C0 | C1 | C2 | C3)",
                      default="C0")

    parser.add_option("--clock_recipe_hbm",
                      dest="clock_recipe_hbm",
                      help="Select Clock Recipe for Clock Group HBM (H0 | H1 | H2 | H3 | H4 | H5)",
                      default="H2")

    parser.add_option("-p", "--place",
                      dest="place_direct",
                      metavar="DIRECT",
                      default="SSI_SpreadLogic_high",
                      help="Placement directive, refer to Vivado manual for supported values. Default to <SSI_SpreadLogic_high>.")

    parser.add_option("-o", "--phy_opt",
                      dest="phy_opt_direct",
                      metavar="DIRECT",
                      default="AggressiveExplore",
                      help="Physical Optimization directive, refer to Vivado manual for supported values. Default to <AggressiveExplore>.")

    parser.add_option("-r", "--route",
                      dest="route_direct",
                      metavar="DIRECT",
                      default="AggressiveExplore",
                      help="Routing directive, refer to Vivado manual for supported values. Default to <Explore>.")

    parser.add_option("-t", "--tag", dest="build_tag",
                      help="Build tag. Default to <mm_DD_yy-HHMMSS>. \
                            NOTE: Certain build flows might require a existing " +
                           "build tag.")

    (options, args) = parser.parse_args()

    print(f"==================================================")
    print(f"Running CL builds")
    print(f"==================================================")
    for opt, value in options.__dict__.items():
        print("%-16s : %-16s" % (opt, value))
    print(f"==================================================")

    # Check selected build flow
    if (options.flow not in ["SynthCL", "ImplCL", "BuildAll"]):
        print_error(f"Unsupported build flow value: {options.flow}. Build terminated")

    # Check selected shell mode
    if (options.mode not in ["small_shell"]):
        if (options.mode == "xdma_shell"):
            print_warning(f"XDMA shell is not supported at this time. See ERRATA for details.")
        print_error(f"Unsupported mode value: {options.mode}. Build terminated")


    # Check selected clock_recipe_a
    if (options.clock_recipe_a not in ["A0", "A1", "A2"]):
        print_error(f"Unsupported clk_recipe_a: {options.clk_recipe_a}. Build terminated")

    # Check selected clock_recipe_b
    if (options.clock_recipe_b not in ["B0", "B1", "B2", "B3", "B4", "B5"]):
        print_error(f"Unsupported clk_recipe_b: {options.clk_recipe_b}. Build terminated")

    # Check selected clock_recipe_c
    if (options.clock_recipe_c not in ["C0", "C1", "C2", "C3"]):
        print_error(f"Unsupported clk_recipe_c: {options.clk_recipe_c}. Build terminated")

    # Check selected clock_recipe_hbm
    if (options.clock_recipe_hbm not in ["H0", "H1", "H2", "H3", "H4", "H5"]):
        print_error(f"Unsupported clk_recipe_hbm: {options.clk_recipe_b}. Build terminated")

    # Check if CL_DIR is set
    if (os.getenv('CL_DIR') is None):
        print_error(f"$CL_DIR environment variable not set. Please set by running \'export CL_DIR=<path to CL>\'")

    # Check if CL_DIR is in same path as PWD
    if (os.path.realpath(os.environ['CL_DIR']) not in os.path.realpath(os.getcwd())):
        print_error(f"$CL_DIR path is not in current build dir. Expecting $CL_DIR @ $CWD/../../../<CL_NAME>")

    cl_name = os.path.realpath(os.environ['CL_DIR']).split("/")[-1]

    if (options.cl != cl_name):
        print_error(f"{options.cl} does not match CL_DIR env variable. Please provide correct names for --cl and CL_DIR")

    os.environ['CL'] = options.cl
    os.environ['SHELL_MODE'] = options.mode
    os.environ['BUILD_FLOW'] = options.flow

    # Create a timestamp if no user tag is assgined
    if (options.build_tag):
        build_tag = options.build_tag
    else:
        now = datetime.datetime.now()
        build_tag = now.strftime(TIMESTAMP_FILE_FORMAT)
    os.environ['BUILD_TAG'] = build_tag

    # Last check before build in case the user sets clock recipes without the aws_clk_gen IP
    if not options.aws_clk_gen and "clock_recipe" in str(sys.argv):
        print_error("""The aws_clk_gen IP is required for setting custom clock recipes.

            Custom `clock_recipe` arguments were detected, please add `--aws_clk_gen` to continue.""")

    # Run the Vivado job
    cmd = f"vivado -mode batch -source build_all.tcl -log {build_tag}.vivado.log " +\
          f"-tclargs {options.place_direct} {options.phy_opt_direct} {options.route_direct} " +\
          f"{options.clock_recipe_a} {options.clock_recipe_b} {options.clock_recipe_c} {options.clock_recipe_hbm} "

    start_time = datetime.datetime.now()
    print(f"\nAWS FPGA: {start_time.strftime(TIMESTAMP_LOG_FORMAT)} - Build starts\n")

    sys.stdout.flush()
    os.system(cmd)

    if (options.flow == "BuildAll"):
        generate_dcp_tarball(cl_name, build_tag, options.clock_recipe_a, options.clock_recipe_b, options.clock_recipe_c, options.clock_recipe_hbm)

    finish_time = datetime.datetime.now()
    print(f"\nAWS FPGA: {finish_time.strftime(TIMESTAMP_LOG_FORMAT)} - Build completes\n")
    print(f"\nAWS FPGA: Build Time = {finish_time - start_time}. \n")

if __name__ == '__main__':
    main()
