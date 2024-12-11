#!/usr/bin/env python3


import os
import shutil
import subprocess
from glob import glob
from argparse import ArgumentParser


def run_cmd(cmd: list, working_directory: str = os.getcwd(), do_print: bool = False) -> str:
    if working_directory is None:
        working_directory = os.getcwd()
    result = subprocess.run(cmd, stdout=subprocess.PIPE, cwd=working_directory)
    stdout = result.stdout.decode('utf-8').strip()
    if do_print:
        print(stdout)
    return stdout


def get_git_root() -> str:
    git_root_cmd: list[str] = ['git', 'rev-parse', '--show-toplevel']
    return run_cmd(git_root_cmd)


CL_TEMPLATE = "CL_TEMPLATE"
CL_EXAMPLE_DIR = f"{get_git_root()}/hdk/cl/examples"


def create_new_cl_example(new_cl_name):
    new_cl_dir = f"{CL_EXAMPLE_DIR}/{new_cl_name}"
    shutil.copytree(f"{CL_EXAMPLE_DIR}/{CL_TEMPLATE}", new_cl_dir)

    text_replacement_command = f'grep -rl {CL_TEMPLATE} {new_cl_dir} | xargs sed -i "s/{CL_TEMPLATE}/{new_cl_name}/g"'
    os.system(text_replacement_command)

    # Move directories first to avoid invalid paths for files
    cl_template_dirs = [f for f in glob(f"{new_cl_dir}/**/*{CL_TEMPLATE}*", recursive=True) if os.path.isdir(f)]
    for cl_template_dir in cl_template_dirs:
        shutil.move(cl_template_dir, cl_template_dir.replace(CL_TEMPLATE, new_cl_name))

    cl_template_files = glob(f"{new_cl_dir}/**/*{CL_TEMPLATE}*", recursive=True)
    for cl_template_file in cl_template_files:
        shutil.move(cl_template_file, cl_template_file.replace(CL_TEMPLATE, new_cl_name))


parser = ArgumentParser(prog="Generate a new CL example", description="Create a new CL example with all the basic files")
parser.add_argument('--new_cl_name', dest='new_cl_name', required=True)


if __name__ == '__main__':
    args = parser.parse_args()

    create_new_cl_example(args.new_cl_name)
