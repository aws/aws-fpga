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


import shutil
from argparse import ArgumentParser
from pathlib import Path


CL_TEMPLATE = "CL_TEMPLATE"
SCRIPT_DIR = Path(__file__).resolve().parent
CL_TEMPLATE_DIR = SCRIPT_DIR / CL_TEMPLATE


def replace_template_text(root_dir: Path, new_cl_name: str) -> None:
    for path in root_dir.rglob("*"):
        if not path.is_file():
            continue

        try:
            contents = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue

        updated_contents = contents.replace(CL_TEMPLATE, new_cl_name)
        if updated_contents != contents:
            path.write_text(updated_contents, encoding="utf-8")


def rename_template_paths(root_dir: Path, new_cl_name: str) -> None:
    paths_to_rename = sorted(
        (path for path in root_dir.rglob(f"*{CL_TEMPLATE}*")),
        key=lambda path: (len(path.parts), str(path)),
        reverse=True,
    )

    for path in paths_to_rename:
        path.rename(path.with_name(path.name.replace(CL_TEMPLATE, new_cl_name)))


def create_new_cl_example(new_cl_name: str, output_dir: Path) -> Path:
    if not CL_TEMPLATE_DIR.is_dir():
        raise FileNotFoundError(f"CL template directory not found: {CL_TEMPLATE_DIR}")

    if not output_dir.is_dir():
        raise NotADirectoryError(f"Output directory does not exist: {output_dir}")

    new_cl_dir = output_dir / new_cl_name
    shutil.copytree(CL_TEMPLATE_DIR, new_cl_dir)

    replace_template_text(new_cl_dir, new_cl_name)
    rename_template_paths(new_cl_dir, new_cl_name)

    return new_cl_dir


def parse_args():
    parser = ArgumentParser(
        prog="Generate a new CL example",
        description="Create a new CL example with all the basic files",
    )
    parser.add_argument("--new_cl_name", dest="new_cl_name", required=True)
    parser.add_argument(
        "--dir",
        dest="output_dir",
        default=Path.cwd(),
        type=Path,
        help="Directory where the new CL example will be created. Defaults to the current working directory.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    create_new_cl_example(args.new_cl_name, args.output_dir.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
