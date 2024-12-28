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

import os
import fileinput
from glob import glob
from argparse import ArgumentParser


XSIM = 'xsim'
VCS = 'vcs'
QUESTA = 'questa'
INCLUDE_SYNTAX = {XSIM: '-include ', VCS: '+incdir+', QUESTA: '+incdir+'}


def main(args) -> None:
    generated_file_list = get_generated_file_list(args.cl_dir, args.simulator)
    update_sim_file_list(args.cl_dir, args.simulator, generated_file_list)


def get_generated_file_list(cl_dir, simulator):
    all_file_objects: list[str] = glob(f'{cl_dir}/design/**', recursive=True)
    all_file_paths = [obj for obj in all_file_objects if os.path.isfile(obj)]
    all_dir_paths = [obj for obj in all_file_objects if os.path.isdir(obj)]

    generated_file_list = ['']
    for dir_path in all_dir_paths:
        generated_file_list.append(INCLUDE_SYNTAX[simulator.lower()] + dir_path.replace(cl_dir, '$CL_DIR'))

    generated_file_list.append('')
    for file_path in all_file_paths:
        if not file_path.endswith('h') and not file_path.endswith('md'):
            generated_file_list.append(file_path.replace(cl_dir, '$CL_DIR'))

    return generated_file_list + ['']


def update_sim_file_list(cl_dir, simulator, generated_file_list):
    IN_GENERATE_BLOCK = False
    sim_file_list_path = f'{cl_dir}/verif/scripts/top.{simulator.lower()}.f'
    for line in fileinput.input(sim_file_list_path, inplace=True):
        if "BEGIN AUTO-GENERATE" in line:
            IN_GENERATE_BLOCK = True
            print(line, end='')
            for generated_line in generated_file_list:
                print(generated_line, end='\n')

        if IN_GENERATE_BLOCK and "END AUTO-GENERATE" in line:
            IN_GENERATE_BLOCK = False

        if not IN_GENERATE_BLOCK:
            print(line, end='')


parser = ArgumentParser(prog="Generate Simulation File List",
                        description="Gerneate a file list in `$CL_DIR/verif/scripts` for a specific simulator")
parser.add_argument('--simulator', dest='simulator', required=True)
parser.add_argument('--cl_dir', dest='cl_dir', required=True)


if __name__ == '__main__':
    args = parser.parse_args()
    main(args)
