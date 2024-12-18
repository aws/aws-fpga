#!/usr/bin/env python3

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

import os
import sys
import shutil
import fileinput
import subprocess
from glob import glob
from argparse import ArgumentParser
from typing import List, Dict, Callable, Union

parser = ArgumentParser(prog="Compile IPs", description="Compile the IPs using Xilinx's compilation scripts")
parser.add_argument('--simulator', dest='simulator', required=True)
parser.add_argument('--complib_dir', dest='complib_dir', required=True)
parser.add_argument('--compile_cl_ip_dir', dest='compile_cl_ip_dir', required=True)
parser.add_argument('--in_progress_file', dest='in_progress_file', required=True)


if __name__ == '__main__':
    args = parser.parse_args()

    print(f"Using Python {sys.version} from '/usr/bin/env python3'")
    is_python3 = sys.version_info >= (3, 0) and sys.version_info < (4, 0)
    is_greater_than_3_8 = sys.version_info >= (3, 8)
    if not (is_python3 and is_greater_than_3_8):
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        raise Exception(f"Python {sys.version} from this system's '/usr/bin/env python3' is not usable. Please review and make sure Python 3.8+ is installed\n")


def run_cmd(cmd: List[str], working_directory: str = os.getcwd(), do_print: bool = False) -> str:
    if working_directory is None:
        working_directory = os.getcwd()
    result = subprocess.run(cmd, stdout=subprocess.PIPE, cwd=working_directory)
    stdout = result.stdout.decode('utf-8').strip()
    if do_print:
        print(stdout)
    return stdout


def get_git_root() -> str:
    git_root_cmd: List[str] = ['git', 'rev-parse', '--show-toplevel']
    return run_cmd(git_root_cmd)


XSIM = 'xsim'
VCS = 'vcs'
QUESTA = 'questa'


class Compiler:
    orig_file_ext: str = '.orig'
    cl_dir: str = os.getenv('CL_DIR')
    default_xilinx_library_name: str = 'xil_defaultlib'
    cl_ip_sim_scripts_dir: str = f'{get_git_root()}/hdk/common/ip/cl_ip/cl_ip.ip_user_files/sim_scripts'
    init_files: Dict[str,str] = {XSIM: 'xsim.ini', VCS: 'synopsys_sim.setup', QUESTA: 'modelsim.ini'}

    def __init__(self, args):
        self.backed_up_files: List[str] = []
        self.in_progress_file: str = args.in_progress_file
        self.simulator: str = args.simulator.lower()
        if not self.simulator in self.init_files.keys():
            self.clean_failure(f"Unknown simulator: {self.simulator}")

        self.complib_dir: str = args.complib_dir
        self.compile_cl_ip_dir: str = args.compile_cl_ip_dir

        self.results_file: str = f'{os.getcwd()}/{self.simulator}_cl_ip_compilation.log'
        self.sim_initfile: str = f'{self.complib_dir}/{self.init_files[self.simulator]}'

    def compile_cl_ips(self) -> None:
        self.add_xil_defaultlib_path_to_initfile()
        xilinx_ip_compile_scripts: List[str] = self.get_all_cl_ip_compilation_script_paths()
        with open(self.results_file, 'w') as f:
            f.write(str(xilinx_ip_compile_scripts))
            for xilinx_ip_path in xilinx_ip_compile_scripts:
                self.compile_ip(xilinx_ip_path, f)

        self.check_for_errors()
        print(f"__PYTHON_INFO__: Moving {self.results_file} to {self.compile_cl_ip_dir}/done")
        shutil.move(self.results_file, f'{self.compile_cl_ip_dir}/done')

    def check_for_errors(self) -> None:
        with open(self.results_file) as output:
            for line in output:
                if "Error" in line and not "Errors: 0" in line:
                    self.clean_failure(f"FOUND COMPILATION ERRORS! See {self.results_file}")

    def add_xil_defaultlib_path_to_initfile(self) -> None:
        lib_path_seperator: str = ':' if self.simulator == VCS else '='
        new_line: str = f'{self.default_xilinx_library_name} {lib_path_seperator} {self.compile_cl_ip_dir}\n'
        line_insertion_map: Dict[str, Dict[str, Union[Callable, List[str]]]] = {
            XSIM:   {'func': self.append_line_to_file, 'args': [self.sim_initfile, new_line, self.default_xilinx_library_name]},
            VCS:    {'func': self.append_line_to_file, 'args': [self.sim_initfile, new_line, self.default_xilinx_library_name]},
            QUESTA: {'func': self.insert_line_above_target, 'args': [self.sim_initfile, '[DefineOptionset]', new_line]}}
        insertion_func: Callable = line_insertion_map[self.simulator]['func']
        insertion_args: List[str] = line_insertion_map[self.simulator]['args']
        insertion_func(*insertion_args)

    def append_line_to_file(self, file_path: str, new_line: str, exception: str) -> None:
        with open(file_path, 'r+') as f:
            for line in f:
                if exception is not None and exception in line:
                    break
            else:
                f.write(new_line)

    def insert_line_above_target(self, file_path: str, target: str, new_line: str) -> None:
        exists: bool = False
        for line in fileinput.input(file_path, inplace=True):
            if self.default_xilinx_library_name in line:
                exists: bool = True
            if not exists and line.startswith(target):
                print(new_line, end='')
            print(line, end='')

    def get_all_cl_ip_compilation_script_paths(self) -> List[str]:
        ip_compile_scripts: List[str] = []
        for ip_name in [ip.name for ip in os.scandir(self.cl_ip_sim_scripts_dir) if ip.is_dir()]:
            ip_sim_dir: str = f'{self.cl_ip_sim_scripts_dir}/{ip_name}/{self.simulator}'
            shell_scripts: List [str] = glob(f'{ip_sim_dir}/*.sh')
            if len(shell_scripts) != 1:
                self.clean_failure(f"Found {shell_scripts} at {ip_sim_dir}")
            ip_compile_scripts.append(shell_scripts[0])
        return ip_compile_scripts

    def compile_ip(self, xilinx_ip_script_path: str, compile_log) -> None:
        ip_script_dir: str = os.path.dirname(xilinx_ip_script_path)
        symlink_dst: str = f'{ip_script_dir}/{self.init_files[self.simulator]}'
        if not os.path.exists(symlink_dst):
            os.symlink(self.sim_initfile, symlink_dst)

        self.prepare_ip_script_for_compilation(ip_script_dir, xilinx_ip_script_path)
        subprocess.check_call([xilinx_ip_script_path, '-lib_map_path', self.complib_dir], cwd=ip_script_dir, stdout=compile_log)
        self.cleanup_compilation_dir(ip_script_dir, symlink_dst)

    def prepare_ip_script_for_compilation(self, dir_path: str, file_path: str) -> None:
        self.backup_file(file_path)
        if self.simulator == QUESTA:
            self.remove_lines(f'{dir_path}/compile.do', line_prefixes_to_remove=['vlib', 'vmap'])

        self.append_line_to_file(file_path, new_line='compile\n', exception=None)
        self.remove_lines(file_path, line_prefixes_to_remove=['run $*'])
        self.replace_hardcoded_xilninx_path(file_path)

    def remove_lines(self, file_path: str, line_prefixes_to_remove: List[str]) -> None:
        self.backup_file(file_path)
        for line in fileinput.input(file_path, inplace=True):
            if not any([line.startswith(prefix) for prefix in line_prefixes_to_remove]):
                print(line, end='')

    def replace_hardcoded_xilninx_path(self, file_path) -> None:
        hardcoded_xilinx_path: str = '/tools/Xilinx/Vivado/2024.1'
        xilinx_path_env_var: str = '$XILINX_VIVADO'
        for line in fileinput.input(file_path, inplace=True):
            if hardcoded_xilinx_path in line:
                line = line.replace(hardcoded_xilinx_path, xilinx_path_env_var)
            print(line, end='')

    def cleanup_compilation_dir(self, ip_script_dir: str, symlink_dst: str) -> None:
        os.remove(symlink_dst)
        self.remove_compile_artifacts(ip_script_dir)
        self.move_backup_files_back()

    def remove_compile_artifacts(self, ip_script_dir: str) -> None:
        artifacts_to_remove = {
            XSIM: ['compile.log', 'xvhdl.log', 'xvhdl.pb', 'xvlog.log', 'xvlog.pb', 'xsim.dir'],
            VCS: ['vhdlan.log', 'vlogan.log'],
            QUESTA: ['compile.log']}

        for artifact_name in artifacts_to_remove[self.simulator]:
            artifact_path: str = f'{ip_script_dir}/{artifact_name}'
            if os.path.exists(artifact_path):
                if os.path.isdir(artifact_path):
                    shutil.rmtree(artifact_path)
                else:
                    os.remove(artifact_path)

    def move_backup_files_back(self) -> None:
        for modified_file_path in self.backed_up_files:
            original_file_path: str = f'{modified_file_path}{self.orig_file_ext}'
            if os.path.exists(original_file_path):
                shutil.move(original_file_path, modified_file_path)

    def backup_file(self, file_path: str) -> None:
        if file_path not in self.backed_up_files:
            self.backed_up_files.append(file_path)
            shutil.copy(file_path, f'{file_path}{self.orig_file_ext}')

    def clean_failure(self, message: str) -> None:
        if os.path.exists(self.in_progress_file):
            os.remove(self.in_progress_file)
        raise Exception(message)



if __name__ == '__main__':
    try:
        compiler = Compiler(args)
        if os.path.exists(compiler.compile_cl_ip_dir):
            shutil.rmtree(compiler.compile_cl_ip_dir)

        os.makedirs(compiler.compile_cl_ip_dir)
        compiler.compile_cl_ips()
    except:
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        raise Exception("The Python script experienced a failure. Please review and make sure Python 3.8+ is installed\n")
