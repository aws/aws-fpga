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


from __future__ import annotations

import os
import re
import shlex
import shutil
import subprocess
import sys
from argparse import ArgumentParser
from collections import deque
from collections.abc import Callable
from glob import glob

parser = ArgumentParser(prog="Compile IPs", description="Compile the IPs using Xilinx's compilation scripts")
parser.add_argument("--simulator", dest="simulator", required=True)
parser.add_argument("--complib_dir", dest="complib_dir", required=True)
parser.add_argument("--compile_cl_ip_dir", dest="compile_cl_ip_dir", required=True)
parser.add_argument("--in_progress_file", dest="in_progress_file", required=True)
parser.add_argument("--common_library", dest="common_libraries", action="append", default=[])


class CompileError(RuntimeError):
    pass


def check_python_version(in_progress_file: str) -> None:
    print(f"Using Python {sys.version} from '/usr/bin/env python3'")
    if sys.version_info < (3, 10):  # noqa: UP036
        if os.path.exists(in_progress_file):
            os.remove(in_progress_file)
        raise Exception(
            f"Python {sys.version} from this system's '/usr/bin/env python3' is not usable. "
            "Please review and make sure Python 3.10+ is installed\n"
        )


if __name__ == "__main__":
    args = parser.parse_args()
    check_python_version(args.in_progress_file)


XSIM = "xsim"
VCS = "vcs"
QUESTA = "questa"

LIBRARY_MAPPING_PATH = re.compile(r"^\s*[A-Za-z][A-Za-z0-9_]*\s*[:=]\s*(\S+)")


def maps_into(line: str, directory: str) -> bool:
    match = LIBRARY_MAPPING_PATH.match(line)
    return bool(match) and os.path.dirname(match.group(1)) == directory


class Compiler:
    orig_file_ext: str = ".orig"
    cl_dir: str = os.getenv("CL_DIR")
    default_xilinx_library_name: str = "xil_defaultlib"
    init_files: dict[str, str] = {XSIM: "xsim.ini", VCS: "synopsys_sim.setup", QUESTA: "modelsim.ini"}

    def __init__(self, args):
        self.backed_up_files: list[str] = []
        self.in_progress_file: str = args.in_progress_file
        self.simulator: str = args.simulator.lower()
        if self.simulator not in self.init_files:
            self.clean_failure(f"Unknown simulator: {self.simulator}")

        self.hdk_common_dir: str = os.getenv("HDK_COMMON_DIR")
        if not self.hdk_common_dir:
            self.clean_failure("HDK_COMMON_DIR is not set. Please source hdk_setup.sh before compiling CL IPs.")

        self.complib_dir: str = args.complib_dir
        self.compile_cl_ip_dir: str = args.compile_cl_ip_dir
        self.common_libraries: list[str] = args.common_libraries

        self.cl_ip_sim_scripts_dir: str = f"{self.hdk_common_dir}/ip/cl_ip/cl_ip.ip_user_files/sim_scripts"
        self.results_file: str = f"{self.compile_cl_ip_dir}/cl_ip_compilation.log"
        self.sim_initfile: str = f"{self.complib_dir}/{self.init_files[self.simulator]}"

    def compile_cl_ips(self) -> None:
        xilinx_ip_compile_scripts: list[str] = self.get_all_cl_ip_compilation_script_paths()
        self.add_library_paths_to_initfile(xilinx_ip_compile_scripts)
        ip_logs: dict[str, str] = {}
        with open(self.results_file, "w") as f:
            f.write("CL IP compilation logs:\n")
            for xilinx_ip_path in xilinx_ip_compile_scripts:
                ip_name, ip_log = self.compile_ip(xilinx_ip_path)
                ip_logs[ip_name] = ip_log
                f.write(f"{ip_name}: {ip_log}\n")

        self.check_for_errors(ip_logs)
        print(f"__PYTHON_INFO__: Moving {self.results_file} to {self.compile_cl_ip_dir}/done")
        shutil.move(self.results_file, f"{self.compile_cl_ip_dir}/done")

    def check_for_errors(self, ip_logs: dict[str, str]) -> None:
        errors = []
        for ip_name, ip_log in ip_logs.items():
            with open(ip_log, errors="replace") as output:
                for line in output:
                    if re.search(r"\berrors?\b", line, re.IGNORECASE) and not re.search(r"\berrors:\s*0\b", line, re.IGNORECASE):
                        errors.append((ip_name, ip_log, line.strip()))
                        break
        if errors:
            summary = "\n\n".join(
                f"IP: {ip_name}\nreported error: {line}\nfull log: {ip_log}\nlast 80 log lines:\n{self.get_log_tail(ip_log)}"
                for ip_name, ip_log, line in errors
            )
            self.clean_failure(f"=== CL IP COMPILATION REPORTED ERRORS ===\n{summary}")

    def add_library_paths_to_initfile(self, xilinx_ip_compile_scripts: list[str]) -> None:
        library_paths = {self.default_xilinx_library_name: f"{self.compile_cl_ip_dir}/{self.default_xilinx_library_name}"}
        if self.simulator != XSIM:
            required_libraries = set(self.common_libraries)
            required_libraries.update(self.get_generated_script_libraries(xilinx_ip_compile_scripts))
            library_paths.update(
                {
                    library: f"{self.compile_cl_ip_dir}/{library}"
                    for library in required_libraries
                    if library != self.default_xilinx_library_name
                }
            )

        self.remove_library_mapping(self.default_xilinx_library_name)
        # This run deletes and recreates every library under compile_cl_ip_dir, so their old mappings are stale.
        self.remove_library_mappings_into(self.compile_cl_ip_dir)
        mapped_libraries = self.get_mapped_libraries()
        missing_library_paths = {library: path for library, path in library_paths.items() if library not in mapped_libraries}
        for path in missing_library_paths.values():
            if self.simulator == QUESTA:
                command = ["vlib", path]
                try:
                    subprocess.check_call(command)
                except subprocess.CalledProcessError as error:
                    self.clean_failure(
                        "Unable to create Questa simulation library.\n"
                        f"command: {shlex.join(command)}\n"
                        f"library path: {path}\n"
                        f"exit code: {error.returncode}"
                    )
            else:
                os.makedirs(path, exist_ok=True)

        lib_path_separator: str = ":" if self.simulator == VCS else "="
        library_mappings = "".join(f"{library} {lib_path_separator} {path}\n" for library, path in sorted(missing_library_paths.items()))
        if not library_mappings:
            return

        line_insertion_map: dict[str, dict[str, Callable | list[str]]] = {
            XSIM: {
                "func": self.append_line_to_file,
                "args": [self.sim_initfile, library_mappings, None],
            },
            VCS: {
                "func": self.append_line_to_file,
                "args": [self.sim_initfile, library_mappings, None],
            },
            QUESTA: {
                "func": self.insert_line_at_end_of_section,
                "args": [self.sim_initfile, "[Library]", library_mappings],
            },
        }
        insertion_func: Callable = line_insertion_map[self.simulator]["func"]
        insertion_args: list[str] = line_insertion_map[self.simulator]["args"]
        insertion_func(*insertion_args)

    def get_generated_script_libraries(self, xilinx_ip_compile_scripts: list[str]) -> set[str]:
        work_option = re.compile(r"^\s*(?:vlogan|vhdlan|vlog|vcom)\b.*?\s-work\s+([A-Za-z0-9_]+)")
        libraries = set()
        for script_path in xilinx_ip_compile_scripts:
            compile_path = script_path if self.simulator == VCS else f"{os.path.dirname(script_path)}/compile.do"
            with open(compile_path) as compile_file:
                for line in compile_file:
                    match = work_option.match(line)
                    if match:
                        libraries.add(match.group(1))
        return libraries

    def get_mapped_libraries(self) -> set[str]:
        library_mapping = re.compile(r"^\s*([A-Za-z][A-Za-z0-9_]*)\s*[:=]")
        mapped_libraries = set()
        with open(self.sim_initfile) as init_file:
            for line in init_file:
                match = library_mapping.match(line)
                if match:
                    mapped_libraries.add(match.group(1))
        return mapped_libraries

    def remove_library_mapping(self, library: str) -> None:
        library_mapping = re.compile(rf"^\s*{re.escape(library)}\s*[:=]")
        with open(self.sim_initfile) as init_file:
            lines = [line for line in init_file if not library_mapping.match(line)]
        with open(self.sim_initfile, "w") as init_file:
            init_file.writelines(lines)

    def remove_library_mappings_into(self, directory: str) -> None:
        with open(self.sim_initfile) as init_file:
            lines = [line for line in init_file if not maps_into(line, directory)]
        with open(self.sim_initfile, "w") as init_file:
            init_file.writelines(lines)

    def append_line_to_file(self, file_path: str, xilinx_defaultlib_mapping: str, exception: str) -> None:
        with open(file_path, "r+") as f:
            for line in f:
                if exception is not None and exception in line:
                    break
            else:
                f.write(xilinx_defaultlib_mapping)

    def insert_line_at_end_of_section(self, file_path: str, section_header: str, xilinx_defaultlib_mapping: str) -> None:
        in_section, last_was_lib_entry = False, False
        lines = []
        with open(file_path) as f:
            for line in f:
                in_section |= line.strip().startswith(section_header)

                is_lib_entry = in_section and "=" in line and not line.strip().startswith(";")
                should_insert = in_section and last_was_lib_entry and not is_lib_entry
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
                self.clean_failure(
                    "Expected exactly one CL IP compilation script.\n"
                    f"IP: {ip_name}\n"
                    f"simulator: {self.simulator}\n"
                    f"expected pattern: {ip_sim_dir}/*.sh\n"
                    f"found: {shell_scripts}"
                )
            ip_compile_scripts.append(shell_scripts[0])
        return ip_compile_scripts

    @staticmethod
    def get_log_tail(log_path: str, line_count: int = 80) -> str:
        try:
            with open(log_path, errors="replace") as log_file:
                return "".join(deque(log_file, maxlen=line_count)).strip()
        except OSError as error:
            return f"Could not read log: {error}"

    def compilation_failure_message(
        self,
        ip_name: str,
        command: list[str],
        working_directory: str,
        log_path: str,
        returncode: int | None = None,
        cause: Exception | None = None,
    ) -> str:
        lines = [
            "=== CL IP COMPILATION FAILED ===",
            f"simulator: {self.simulator}",
            f"IP: {ip_name}",
            f"command: {shlex.join(command)}",
            f"working directory: {working_directory}",
        ]
        if returncode is not None:
            lines.append(f"exit code: {returncode}")
        if cause is not None:
            lines.append(f"cause: {cause}")
        lines.extend([f"full log: {log_path}", f"last 80 log lines:\n{self.get_log_tail(log_path)}"])
        return "\n".join(lines)

    def compile_ip(self, xilinx_ip_script_path: str) -> tuple[str, str]:
        ip_script_dir: str = os.path.dirname(xilinx_ip_script_path)
        symlink_dst: str = f"{ip_script_dir}/{self.init_files[self.simulator]}"
        ip_name = os.path.basename(os.path.dirname(ip_script_dir))
        log_dir = f"{self.compile_cl_ip_dir}/logs"
        os.makedirs(log_dir, exist_ok=True)
        ip_log = f"{log_dir}/{ip_name}.log"
        command = [xilinx_ip_script_path, "-lib_map_path", self.complib_dir]
        created_symlink = False

        try:
            print(f"Compiling CL IP '{ip_name}'; log: {ip_log}")
            if not os.path.exists(self.sim_initfile):
                self.clean_failure(f"Missing simulator initialization file.\nsimulator: {self.simulator}\ninit file: {self.sim_initfile}")

            if not os.path.exists(symlink_dst):
                os.symlink(self.sim_initfile, symlink_dst)
                created_symlink = True
            self.prepare_ip_script_for_compilation(ip_script_dir, xilinx_ip_script_path)
            with open(ip_log, "w") as compile_log:
                compile_log.write(f"IP: {ip_name}\n")
                compile_log.write(f"command: {shlex.join(command)}\n")
                compile_log.write(f"working directory: {ip_script_dir}\n\n")
                result = subprocess.run(
                    command,
                    cwd=ip_script_dir,
                    stdout=compile_log,
                    stderr=subprocess.STDOUT,
                    check=False,
                )
            if result.returncode:
                self.clean_failure(
                    self.compilation_failure_message(
                        ip_name,
                        command,
                        ip_script_dir,
                        ip_log,
                        returncode=result.returncode,
                    )
                )
            return ip_name, ip_log
        except CompileError:
            raise
        except Exception as error:
            self.clean_failure(self.compilation_failure_message(ip_name, command, ip_script_dir, ip_log, cause=error))
        finally:
            self.cleanup_compilation_dir(ip_script_dir, symlink_dst, created_symlink)

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

    def cleanup_compilation_dir(self, ip_script_dir: str, symlink_dst: str, created_symlink: bool) -> None:
        if created_symlink and os.path.lexists(symlink_dst):
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
        self.backed_up_files = []

    def backup_file(self, file_path: str) -> None:
        if file_path not in self.backed_up_files:
            self.backed_up_files.append(file_path)
            shutil.copy(file_path, f"{file_path}{self.orig_file_ext}")

    def clean_failure(self, message: str) -> None:
        if os.path.exists(self.in_progress_file):
            os.remove(self.in_progress_file)
        raise CompileError(message)


if __name__ == "__main__":
    try:
        compiler = Compiler(args)
        if os.path.exists(compiler.compile_cl_ip_dir):
            shutil.rmtree(compiler.compile_cl_ip_dir)

        os.makedirs(compiler.compile_cl_ip_dir)
        compiler.compile_cl_ips()
    except CompileError as error:
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        print(error, file=sys.stderr)
        raise SystemExit(1) from None
    except Exception:
        if os.path.exists(args.in_progress_file):
            os.remove(args.in_progress_file)
        print("=== CL IP COMPILATION FAILED ===\nUnexpected error before compilation completed.", file=sys.stderr)
        raise
