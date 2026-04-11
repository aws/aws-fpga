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
import shutil
import subprocess
import sys
from argparse import ArgumentParser
from collections.abc import Callable
from glob import glob

parser = ArgumentParser(prog="Compile IPs", description="Compile the IPs using Xilinx's compilation scripts")
parser.add_argument("--simulator", dest="simulator", required=True)
parser.add_argument("--complib_dir", dest="complib_dir", required=True)
parser.add_argument("--compile_cl_ip_dir", dest="compile_cl_ip_dir", required=True)
parser.add_argument("--in_progress_file", dest="in_progress_file", required=True)


if __name__ == "__main__":
    args = parser.parse_args()

    print(f"Using Python {sys.version} from '/usr/bin/env python3'")
    is_python3 = sys.version_info >= (3, 0) and sys.version_info < (4, 0)
    is_greater_than_3_8 = sys.version_info >= (3, 8)
    if not (is_python3 and is_greater_than_3_8):
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        raise Exception(
            f"Python {sys.version} from this system's '/usr/bin/env python3' is not usable. "
            "Please review and make sure Python 3.8+ is installed\n"
        )


def get_hdk_common_dir() -> str:
    hdk_common_dir = os.getenv('HDK_COMMON_DIR')
    if hdk_common_dir is None:
        raise Exception("Environment variable HDK_COMMON_DIR not set. Please source hdk_setup.sh\n")
    return os.path.realpath(hdk_common_dir)


XSIM = "xsim"
VCS = "vcs"
QUESTA = "questa"


class Compiler:
    orig_file_ext: str = ".orig"
    cl_dir: str = os.getenv("CL_DIR")
    default_xilinx_library_name: str = "xil_defaultlib"
    cl_ip_sim_scripts_dir: str = f"{get_hdk_common_dir()}/ip/cl_ip/cl_ip.ip_user_files/sim_scripts"
    init_files: dict[str, str] = {XSIM: "xsim.ini", VCS: "synopsys_sim.setup", QUESTA: "modelsim.ini"}

    def __init__(self, args):
        self.backed_up_files: list[str] = []
        self.in_progress_file: str = args.in_progress_file
        self.simulator: str = args.simulator.lower()
        if self.simulator not in self.init_files:
            self.clean_failure(f"Unknown simulator: {self.simulator}")

        self.complib_dir: str = args.complib_dir
        self.compile_cl_ip_dir: str = args.compile_cl_ip_dir

        self.results_file: str = f"{os.getcwd()}/{self.simulator}_cl_ip_compilation.log"
        self.sim_initfile: str = f"{self.complib_dir}/{self.init_files[self.simulator]}"

    def compile_cl_ips(self) -> None:
        self.add_xil_defaultlib_path_to_initfile()
        xilinx_ip_compile_scripts: list[str] = self.get_all_cl_ip_compilation_script_paths()
        with open(self.results_file, "w") as f:
            f.write(str(xilinx_ip_compile_scripts))
            for xilinx_ip_path in xilinx_ip_compile_scripts:
                self.compile_ip(xilinx_ip_path, f)

        self.check_for_errors()
        print(f"__PYTHON_INFO__: Moving {self.results_file} to {self.compile_cl_ip_dir}/done")
        shutil.move(self.results_file, f"{self.compile_cl_ip_dir}/done")

    def check_for_errors(self) -> None:
        with open(self.results_file) as output:
            for line in output:
                if "Error" in line and "Errors: 0" not in line:
                    self.clean_failure(f"FOUND COMPILATION ERRORS! See {self.results_file}")

    def add_xil_defaultlib_path_to_initfile(self) -> None:
        lib_path_seperator: str = ":" if self.simulator == VCS else "="
        xilinx_defaultlib_mapping: str = f"{self.default_xilinx_library_name} {lib_path_seperator} {self.compile_cl_ip_dir}\n"
        line_insertion_map: dict[str, dict[str, Callable | list[str]]] = {
            XSIM: {
                "func": self.append_line_to_file,
                "args": [self.sim_initfile, xilinx_defaultlib_mapping, self.default_xilinx_library_name],
            },
            VCS: {
                "func": self.append_line_to_file,
                "args": [self.sim_initfile, xilinx_defaultlib_mapping, self.default_xilinx_library_name],
            },
            QUESTA: {
                "func": self.insert_line_at_end_of_section,
                "args": [self.sim_initfile, "[Library]", xilinx_defaultlib_mapping],
            },
        }
        insertion_func: Callable = line_insertion_map[self.simulator]["func"]
        insertion_args: list[str] = line_insertion_map[self.simulator]["args"]
        insertion_func(*insertion_args)

    def append_line_to_file(self, file_path: str, xilinx_defaultlib_mapping: str, exception: str) -> None:
        with open(file_path, "r+") as f:
            for line in f:
                if exception is not None and exception in line:
                    break
            else:
                f.write(xilinx_defaultlib_mapping)

    def insert_line_at_end_of_section(self, file_path: str, section_header: str, xilinx_defaultlib_mapping: str) -> None:
        exists, in_section, last_was_lib_entry = False, False, False
        lines = []
        with open(file_path) as f:
            for line in f:
                exists |= self.default_xilinx_library_name in line
                in_section |= line.strip().startswith(section_header)

                is_lib_entry = in_section and "=" in line and not line.strip().startswith(";")
                should_insert = not exists and in_section and last_was_lib_entry and not is_lib_entry
                if should_insert:
                    lines.append(xilinx_defaultlib_mapping)
                    in_section = False

                lines.append(line)
                last_was_lib_entry = is_lib_entry

        with open(file_path, "w") as f:
            f.writelines(lines)

    def get_all_cl_ip_compilation_script_paths(self) -> list[str]:
        ip_compile_scripts: list[str] = []
        for ip_name in [ip.name for ip in os.scandir(self.cl_ip_sim_scripts_dir) if ip.is_dir()]:
            ip_sim_dir: str = f"{self.cl_ip_sim_scripts_dir}/{ip_name}/{self.simulator}"
            shell_scripts: list[str] = glob(f"{ip_sim_dir}/*.sh")
            if len(shell_scripts) != 1:
                self.clean_failure(f"Found {shell_scripts} at {ip_sim_dir}")
            ip_compile_scripts.append(shell_scripts[0])
        return ip_compile_scripts

    def compile_ip(self, xilinx_ip_script_path: str, compile_log) -> None:
        ip_script_dir: str = os.path.dirname(xilinx_ip_script_path)
        symlink_dst: str = f"{ip_script_dir}/{self.init_files[self.simulator]}"

        # check for abnormalities
        print(f"Compiling this cl_ip {xilinx_ip_script_path}")
        assert os.path.exists(self.sim_initfile), f"FATAL missing init file {self.sim_initfile}"
        artifacts_dirs_exist = os.path.exists(f"{self.compile_cl_ip_dir}/_info") or os.path.exists(f"{self.compile_cl_ip_dir}/_vmake")
        if self.simulator == QUESTA and not artifacts_dirs_exist:
            print(f"WARNING no lib, running vlib {self.compile_cl_ip_dir}")
            subprocess.check_call(["vlib", self.compile_cl_ip_dir], cwd=ip_script_dir, stdout=compile_log)

        if not os.path.exists(symlink_dst):
            os.symlink(self.sim_initfile, symlink_dst)
        self.prepare_ip_script_for_compilation(ip_script_dir, xilinx_ip_script_path)
        print(f"Doing {xilinx_ip_script_path} -lib_map_path {self.complib_dir}")
        subprocess.check_call([xilinx_ip_script_path, "-lib_map_path", self.complib_dir], cwd=ip_script_dir, stdout=compile_log)
        self.cleanup_compilation_dir(ip_script_dir, symlink_dst)

    def prepare_ip_script_for_compilation(self, dir_path: str, file_path: str) -> None:
        self.backup_file(file_path)
        if self.simulator == QUESTA:
            self.remove_lines(f"{dir_path}/compile.do", line_prefixes_to_remove=["vlib", "vmap"])

        self.append_line_to_file(file_path, xilinx_defaultlib_mapping="compile\n", exception=None)
        self.remove_lines(file_path, line_prefixes_to_remove=["run $*"])
        self.replace_hardcoded_xilninx_path(file_path)

    def remove_lines(self, file_path: str, line_prefixes_to_remove: list[str]) -> None:
        self.backup_file(file_path)
        lines = []
        with open(file_path) as f:
            for line in f:
                if not any(line.startswith(prefix) for prefix in line_prefixes_to_remove):
                    lines.append(line)
        with open(file_path, "w") as f:
            f.writelines(lines)

    def replace_hardcoded_xilninx_path(self, file_path) -> None:
        hardcoded_xilinx_path: str = "/tools/Xilinx/Vivado/2024.1"
        xilinx_path_env_var: str = "$XILINX_VIVADO"
        lines = []
        with open(file_path) as f:
            for line in f:
                if hardcoded_xilinx_path in line:
                    line = line.replace(hardcoded_xilinx_path, xilinx_path_env_var)
                lines.append(line)
        with open(file_path, "w") as f:
            f.writelines(lines)

    def cleanup_compilation_dir(self, ip_script_dir: str, symlink_dst: str) -> None:
        os.remove(symlink_dst)
        self.remove_compile_artifacts(ip_script_dir)
        self.move_backup_files_back()

    def remove_compile_artifacts(self, ip_script_dir: str) -> None:
        artifacts_to_remove = {
            XSIM: ["compile.log", "xvhdl.log", "xvhdl.pb", "xvlog.log", "xvlog.pb", "xsim.dir"],
            VCS: ["vhdlan.log", "vlogan.log"],
            QUESTA: ["compile.log"],
        }

        for artifact_name in artifacts_to_remove[self.simulator]:
            artifact_path: str = f"{ip_script_dir}/{artifact_name}"
            if os.path.exists(artifact_path):
                if os.path.isdir(artifact_path):
                    shutil.rmtree(artifact_path)
                else:
                    os.remove(artifact_path)

    def move_backup_files_back(self) -> None:
        for modified_file_path in self.backed_up_files:
            original_file_path: str = f"{modified_file_path}{self.orig_file_ext}"
            if os.path.exists(original_file_path):
                shutil.move(original_file_path, modified_file_path)

    def backup_file(self, file_path: str) -> None:
        if file_path not in self.backed_up_files:
            self.backed_up_files.append(file_path)
            shutil.copy(file_path, f"{file_path}{self.orig_file_ext}")

    def clean_failure(self, message: str) -> None:
        if os.path.exists(self.in_progress_file):
            os.remove(self.in_progress_file)
        raise Exception(message)


if __name__ == "__main__":
    try:
        compiler = Compiler(args)
        if os.path.exists(compiler.compile_cl_ip_dir):
            shutil.rmtree(compiler.compile_cl_ip_dir)

        os.makedirs(compiler.compile_cl_ip_dir)
        compiler.compile_cl_ips()
    except Exception as e:
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        raise Exception("The Python script experienced a failure. Please review and make sure Python 3.8+ is installed\n") from e
