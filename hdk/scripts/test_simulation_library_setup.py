#!/usr/bin/env python3

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import patch

from hdk.common.verif.scripts.compile_cl_ips import CompileError, Compiler, check_python_version, maps_into


class TestSimulationLibrarySetup(unittest.TestCase):
    def setUp(self):
        # Compiler() refuses to build without it; the tests below never read the path back.
        hdk_common_dir = patch.dict(os.environ, {"HDK_COMMON_DIR": "/unused/hdk/common"})
        hdk_common_dir.start()
        self.addCleanup(hdk_common_dir.stop)

    def test_compile_cl_ips_maps_only_missing_required_libraries(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            complib_dir = root / "complib"
            complib_dir.mkdir()
            init_file = complib_dir / "synopsys_sim.setup"
            init_file.write_text("xil_defaultlib : /precompiled/xil_defaultlib\nxpm : /precompiled/xpm\n")

            compile_script = root / "compile.sh"
            compile_script.write_text(
                "\n".join(
                    [
                        "vlogan -work xpm source.sv",
                        "vlogan -work axi_register_slice_v2_1_36 source.sv",
                        "vlogan -work xil_defaultlib source.sv",
                    ]
                )
            )
            compile_cl_ip_dir = root / "compiled_cl_ips"
            compiler = Compiler(
                Namespace(
                    simulator="vcs",
                    complib_dir=str(complib_dir),
                    compile_cl_ip_dir=str(compile_cl_ip_dir),
                    in_progress_file=str(root / "in_progress"),
                    common_libraries=["hbm_v1_0_18", "xpm"],
                )
            )

            compiler.add_library_paths_to_initfile([str(compile_script)])

            mappings = init_file.read_text()
            self.assertEqual(mappings.count("xpm :"), 1)
            self.assertEqual(mappings.count("xil_defaultlib :"), 1)
            self.assertNotIn("/precompiled/xil_defaultlib", mappings)
            self.assertIn(
                f"axi_register_slice_v2_1_36 : {compile_cl_ip_dir}/axi_register_slice_v2_1_36",
                mappings,
            )
            self.assertIn(f"hbm_v1_0_18 : {compile_cl_ip_dir}/hbm_v1_0_18", mappings)
            self.assertIn(f"xil_defaultlib : {compile_cl_ip_dir}/xil_defaultlib", mappings)
            self.assertTrue((compile_cl_ip_dir / "axi_register_slice_v2_1_36").is_dir())
            self.assertTrue((compile_cl_ip_dir / "hbm_v1_0_18").is_dir())
            self.assertTrue((compile_cl_ip_dir / "xil_defaultlib").is_dir())
            self.assertFalse((compile_cl_ip_dir / "xpm").exists())

    def test_compile_cl_ips_initializes_questa_libraries(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            complib_dir = root / "complib"
            complib_dir.mkdir()
            init_file = complib_dir / "modelsim.ini"
            init_file.write_text("[Library]\nxil_defaultlib = /precompiled/xil_defaultlib\nxpm = /precompiled/xpm\n\n[vcom]\n")

            script_dir = root / "sim_script"
            script_dir.mkdir()
            compile_script = script_dir / "compile.sh"
            compile_script.touch()
            (script_dir / "compile.do").write_text("vlog -work axi_register_slice_v2_1_36 source.sv\n")
            compile_cl_ip_dir = root / "compiled_cl_ips"
            compiler = Compiler(
                Namespace(
                    simulator="questa",
                    complib_dir=str(complib_dir),
                    compile_cl_ip_dir=str(compile_cl_ip_dir),
                    in_progress_file=str(root / "in_progress"),
                    common_libraries=[],
                )
            )

            with patch("hdk.common.verif.scripts.compile_cl_ips.subprocess.check_call") as check_call:
                compiler.add_library_paths_to_initfile([str(compile_script)])

            mappings = init_file.read_text()
            self.assertEqual(mappings.count("xpm ="), 1)
            self.assertEqual(mappings.count("xil_defaultlib ="), 1)
            self.assertNotIn("/precompiled/xil_defaultlib", mappings)
            self.assertIn(
                f"axi_register_slice_v2_1_36 = {compile_cl_ip_dir}/axi_register_slice_v2_1_36",
                mappings,
            )
            self.assertIn(f"xil_defaultlib = {compile_cl_ip_dir}/xil_defaultlib", mappings)
            self.assertEqual(check_call.call_count, 2)
            check_call.assert_any_call(["vlib", f"{compile_cl_ip_dir}/axi_register_slice_v2_1_36"])
            check_call.assert_any_call(["vlib", f"{compile_cl_ip_dir}/xil_defaultlib"])

    def test_maps_into_matches_a_library_directly_under_the_directory(self):
        self.assertTrue(maps_into("axi_register_slice_v2_1_36 : /ips/axi_register_slice_v2_1_36\n", "/ips"))

    def test_maps_into_ignores_a_library_outside_the_directory(self):
        self.assertFalse(maps_into("xpm = /complib/xpm\n", "/ips"))

    def test_compile_cl_ips_recreates_its_libraries_after_the_directory_is_deleted(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            complib_dir = root / "complib"
            complib_dir.mkdir()
            init_file = complib_dir / "synopsys_sim.setup"
            init_file.write_text("xpm : /precompiled/xpm\n")
            compile_script = root / "compile.sh"
            compile_script.write_text("vlogan -work axi_register_slice_v2_1_36 source.sv\n")
            compile_cl_ip_dir = root / "compiled_cl_ips"
            compiler = Compiler(
                Namespace(
                    simulator="vcs",
                    complib_dir=str(complib_dir),
                    compile_cl_ip_dir=str(compile_cl_ip_dir),
                    in_progress_file=str(root / "in_progress"),
                    common_libraries=[],
                )
            )

            compiler.add_library_paths_to_initfile([str(compile_script)])
            # A rerun, such as make recompile_cl_ips, deletes the directory but keeps the complib init file.
            shutil.rmtree(compile_cl_ip_dir)
            compiler.add_library_paths_to_initfile([str(compile_script)])

            self.assertTrue((compile_cl_ip_dir / "axi_register_slice_v2_1_36").is_dir())
            self.assertEqual(init_file.read_text().count("axi_register_slice_v2_1_36 :"), 1)

    def test_simlib_compile_includes_ip_libraries_and_cleans_failed_state(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            repo_root = Path(__file__).resolve().parents[2]
            common_dir = root / "common"
            (common_dir / "ip/cl_ip").mkdir(parents=True)
            (common_dir / "ip/cl_ip/common_liblists.mk").touch()
            scripts_dir = common_dir / "verif/tb/scripts"
            scripts_dir.mkdir(parents=True)
            (scripts_dir / "Makefile.vcs.inc").touch()

            makefile = root / "Makefile"
            makefile.write_text(
                "\n".join(
                    [
                        f"HDK_COMMON_DIR := {common_dir}",
                        f"SIM_ROOT := {root / 'sim'}",
                        "VCS := 1",
                        f"include {repo_root / 'hdk/common/verif/tb/scripts/Makefile.common.inc'}",
                        "",
                    ]
                )
            )

            captured_tcl = root / "create_libs.tcl"
            vivado_calls = root / "vivado_calls"
            fake_bin = root / "bin"
            fake_bin.mkdir()
            fake_vivado = fake_bin / "vivado"
            fake_vivado.write_text('#!/bin/sh\nprintf x >> "$VIVADO_CALLS"\ncp create_libs.tcl "$CAPTURED_TCL"\nexit 37\n')
            fake_vivado.chmod(0o755)

            env = os.environ.copy()
            env["PATH"] = f"{fake_bin}:{env['PATH']}"
            env["CAPTURED_TCL"] = str(captured_tcl)
            env["VIVADO_CALLS"] = str(vivado_calls)
            compile_cl_ip_dir = common_dir / "verif/ip_simulation_libraries/vcs_compiled_cl_ips"
            make_command = [
                "make",
                "--no-print-directory",
                "-j2",
                "-f",
                str(makefile),
                str(compile_cl_ip_dir),
            ]
            results = [
                subprocess.run(
                    make_command,
                    capture_output=True,
                    env=env,
                    text=True,
                    timeout=10,
                    check=False,
                )
                for _ in range(2)
            ]

            for result in results:
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("Simulation library compilation is in progress", result.stderr)
            self.assertEqual(vivado_calls.read_text(), "xx")
            tcl = captured_tcl.read_text()
            self.assertIn("-library all", tcl)
            self.assertNotIn("-no_ip_compile", tcl)
            self.assertIn("-family virtexuplus", tcl)
            self.assertNotIn("-family all", tcl)
            self.assertNotIn("open_project", tcl)
            ip_sim_dir = common_dir / "verif/ip_simulation_libraries"
            self.assertFalse((ip_sim_dir / "vcs_complib").exists())
            self.assertFalse((ip_sim_dir / "vcs_complib_dir_in_progress").exists())
            self.assertFalse((ip_sim_dir / "vcs_compile_cl_ips_dir_in_progress").exists())
            self.assertFalse((root / "sim/create_libs.tcl").exists())

    def test_compile_cl_ips_preserves_failure_cause(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            in_progress_file = root / "in_progress"
            in_progress_file.touch()
            compile_script = Path(__file__).resolve().parents[1] / "common/verif/scripts/compile_cl_ips.py"

            result = subprocess.run(
                [
                    sys.executable,
                    str(compile_script),
                    "--simulator",
                    "invalid",
                    "--complib_dir",
                    str(root / "complib"),
                    "--compile_cl_ip_dir",
                    str(root / "compiled_cl_ips"),
                    "--in_progress_file",
                    str(in_progress_file),
                ],
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unknown simulator: invalid", result.stderr)
            self.assertNotIn("Python script experienced a failure", result.stderr)
            self.assertFalse(in_progress_file.exists())

    def test_compile_cl_ips_detects_plural_error_summary(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            in_progress_file = root / "in_progress"
            in_progress_file.touch()
            ip_log = root / "broken_ip.log"
            ip_log.write_text("Errors: 3, Warnings: 0\n")
            compiler = Compiler(
                Namespace(
                    simulator="vcs",
                    complib_dir=str(root / "complib"),
                    compile_cl_ip_dir=str(root / "compiled_cl_ips"),
                    in_progress_file=str(in_progress_file),
                    common_libraries=[],
                )
            )

            with self.assertRaisesRegex(CompileError, "Errors: 3"):
                compiler.check_for_errors({"broken_ip": str(ip_log)})

            self.assertFalse(in_progress_file.exists())

    def test_compile_cl_ips_requires_hdk_common_dir(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            in_progress_file = root / "in_progress"
            in_progress_file.touch()
            environment = {name: value for name, value in os.environ.items() if name != "HDK_COMMON_DIR"}

            with (
                patch.dict(os.environ, environment, clear=True),
                self.assertRaisesRegex(CompileError, "HDK_COMMON_DIR is not set"),
            ):
                Compiler(
                    Namespace(
                        simulator="vcs",
                        complib_dir=str(root / "complib"),
                        compile_cl_ip_dir=str(root / "compiled_cl_ips"),
                        in_progress_file=str(in_progress_file),
                        common_libraries=[],
                    )
                )

            self.assertFalse(in_progress_file.exists())

    def test_unsupported_python_removes_in_progress_file(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            in_progress_file = Path(temp_dir) / "in_progress"
            in_progress_file.touch()

            with (
                patch("hdk.common.verif.scripts.compile_cl_ips.sys.version_info", (3, 9)),
                self.assertRaisesRegex(Exception, "Python 3.10\\+"),
            ):
                check_python_version(str(in_progress_file))

            self.assertFalse(in_progress_file.exists())

    def test_compile_cl_ips_failed_ip_reports_log_and_restores_workspace(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            complib_dir = root / "complib"
            complib_dir.mkdir()
            (complib_dir / "synopsys_sim.setup").write_text("xil_defaultlib : /precompiled/xil_defaultlib\n")
            in_progress_file = root / "in_progress"
            in_progress_file.touch()

            ip_dir = root / "hdk/common/ip/cl_ip/cl_ip.ip_user_files/sim_scripts/broken_ip/vcs"
            ip_dir.mkdir(parents=True)
            compile_script = ip_dir / "compile.sh"
            original_script = (
                "#!/bin/sh\n"
                "printf '%s\\n' 'FAKE_IP_DIAGNOSTIC: missing broken_ip dependency'\n"
                "printf '%s\\n' 'temporary vlogan output' > vlogan.log\n"
                "printf '%s\\n' 'temporary vhdlan output' > vhdlan.log\n"
                "exit 37\n"
            )
            compile_script.write_text(original_script)
            compile_script.chmod(0o755)

            compile_cl_ip_dir = root / "compiled_cl_ips"
            compile_script_path = Path(__file__).resolve().parents[1] / "common/verif/scripts/compile_cl_ips.py"
            result = subprocess.run(
                [
                    sys.executable,
                    str(compile_script_path),
                    "--simulator",
                    "vcs",
                    "--complib_dir",
                    str(complib_dir),
                    "--compile_cl_ip_dir",
                    str(compile_cl_ip_dir),
                    "--in_progress_file",
                    str(in_progress_file),
                ],
                capture_output=True,
                cwd=root,
                env={**os.environ, "HDK_COMMON_DIR": str(root / "hdk/common")},
                text=True,
                check=False,
            )

            per_ip_log = compile_cl_ip_dir / "logs/broken_ip.log"
            output = result.stdout + result.stderr
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("=== CL IP COMPILATION FAILED ===", output)
            self.assertIn("IP: broken_ip", output)
            self.assertIn("exit code: 37", output)
            self.assertIn(str(per_ip_log), output)
            self.assertIn("FAKE_IP_DIAGNOSTIC: missing broken_ip dependency", output)
            self.assertTrue(per_ip_log.exists())
            self.assertIn("FAKE_IP_DIAGNOSTIC: missing broken_ip dependency", per_ip_log.read_text())
            self.assertFalse(in_progress_file.exists())
            self.assertFalse((ip_dir / "synopsys_sim.setup").exists())
            self.assertEqual(compile_script.read_text(), original_script)
            self.assertFalse((ip_dir / "compile.sh.orig").exists())
            self.assertFalse((ip_dir / "vlogan.log").exists())
            self.assertFalse((ip_dir / "vhdlan.log").exists())


if __name__ == "__main__":
    unittest.main()
