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

from collections import defaultdict
import os
import glob
import re
import requests
import signal
import subprocess
import sys
from termcolor import colored
from time import sleep
from typing import Dict, List, Match
import argparse

def get_repo_root_dir() -> str:
    repo_root_dir = subprocess.run("git rev-parse --show-toplevel".split(), capture_output=True, cwd=os.path.dirname(__file__), check=True).stdout.decode("utf-8").strip()
    return repo_root_dir


def get_link_to_self_html(rst_f: str) -> str:
    repo_root_dir = get_repo_root_dir()
    rst_to_html = rst_f.replace(".rst", ".html")
    rst_to_html = rst_to_html.replace("docs-rtd/source/", "")
    rst_to_html = rst_to_html.replace(f"{repo_root_dir}", ".")
    return rst_to_html


def construct_relative_link(rst_f: str, link_body: str) -> str:
    # Start by going to the location of the file that contains the relative link
    os.chdir(os.path.dirname(rst_f))

    # Follow the relative link
    back_pos = link_body.find("../")
    while back_pos != -1:
        os.chdir("..")
        link_body = link_body[:back_pos] + link_body[back_pos + 3:]
        back_pos = link_body.find("../")

    # Obtain the specified file path that current directory is relative to
    start = os.getcwd().replace(get_repo_root_dir(), "").replace("/docs-rtd/source/", "")

    # Reassemble the link relative to the repo root
    start = f"{start}/{link_body.replace('../', '').replace('./', '')}"
    if start[-1] == "/":
        start = start[:-1]
    return start


def perform_request(link_body: str, rst_f: str, preamble: str) -> int:
    default_request = "http://localhost:3000"
    is_external_link = link_body.startswith("http")
    is_internal_section_link = link_body.startswith("#")
    link_is_broken = False
    session = requests.Session()
    try:
        if is_external_link:
            response = session.head(
                link_body,
                timeout=15,
                headers={"User-Agent": "Mozilla/5.0"},
                allow_redirects=True,
                verify=True
            )
        elif is_internal_section_link:
            link_to_self = get_link_to_self_html(rst_f)
            internal_link = f"{link_to_self}{link_body}"
            response = session.head(f"{default_request}/{internal_link}", timeout=1)
        elif "html" in link_body:
            response = session.head(f"{default_request}/{link_body}")
            if response.status_code != 200:
                relative_link = construct_relative_link(rst_f, link_body)
                response = session.head(f"{default_request}/{relative_link}")
        else:
            file_or_directory_link = f"{default_request}/{link_body}"
            response = session.head(file_or_directory_link, timeout=1)

        link_is_broken = response.status_code != 200
        status = "ERROR" if link_is_broken else "OK"
        color = "red" if link_is_broken else "green"
        print(preamble + ": " + colored(f"{status}, {response.status_code}", color))
        return int(link_is_broken)
    except Exception as e:
        link_is_broken = True
        print(preamble + ": " + colored("ERROR, Request exception thrown", "red"))
        print(e)
        return int(link_is_broken)
    finally:
        session.close()

def navigate_to_rtd_build_html_dir() -> None:
    repo_root_dir = get_repo_root_dir()
    rtd_build_html_dir = "docs-rtd/build/html"
    os.chdir(f"{repo_root_dir}/{rtd_build_html_dir}")


def check_links(files_links_dict: Dict[str, List[List[str]]]) -> None:
    navigate_to_rtd_build_html_dir()
    link_server = subprocess.Popen(
        [sys.executable, "-m", "http.server", "3000"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    sleep(1)

    total_links_in_error = 0
    try:
        for rst_f, link_info in files_links_dict.items():
            print(f"Now testing links from: {rst_f}")
            for link in link_info:
                link_text = link[0]
                link_body = link[1]
                skip_link = any([
                    "mailto" in link_body,
                    "|" in link_body
                ])
                if skip_link:
                    continue
                preamble = f"\t{link_text}, {link_body}"
                total_links_in_error += perform_request(link_body, rst_f, preamble)
            print()
    finally:
        link_server.send_signal(signal.SIGTERM)
        print("Shutting down http server")
        print(f"Total Links in Error: {total_links_in_error}")
        link_server.wait()


def get_link_text_and_link(link_match: Match[str]) -> List[str]:
    link_text = "".join([f"{word} " if word != "|" else "" for word in link_match.group(1).split()]).strip()
    link_body = "".join([word if word != "|" else "" for word in link_match.group(2).split()])
    link_text_link_body = [link_text, link_body]
    return link_text_link_body


def process_file(rst_f: str, files_links_dict: Dict[str, List[List[str]]]) -> None:
    # Link looks like `Text that you would click on <actual/link>`__
    # Emphasized text is ``text``, so we don't want to be tricked by this.
    ignore_double_backtick = r"(?<!`)"
    back_tick_that_starts_link = r"`"
    gets_link_text = r"([^`<]*)"
    gets_actual_link = r"<([^>]+)>`__"
    link_pattern_regex = r''.join([
        ignore_double_backtick,
        back_tick_that_starts_link,
        gets_link_text,
        gets_actual_link
    ])
    compiled_link_pattern = re.compile(link_pattern_regex, re.DOTALL)

    file_contents = ""
    with open(rst_f, "r", encoding="utf-8") as f:
        file_contents = f.read()

    for link_match in compiled_link_pattern.finditer(file_contents):
        files_links_dict[rst_f].append(
            get_link_text_and_link(link_match)
        )


def get_links_from_files(rst_files: List[str]) -> Dict[str, List[List[str]]]:
    files_links_dict: Dict[str, List[List[str]]] = defaultdict(list)
    for rst_f in rst_files:
        process_file(rst_f, files_links_dict)
    return files_links_dict


def navigate_to_rtd_sources_dir() -> None:
    repo_root_dir = get_repo_root_dir()
    rtd_sources_dir = "docs-rtd/source"
    os.chdir(f"{repo_root_dir}/{rtd_sources_dir}")


def gather_file_names(files_to_check: List[str]) -> List[str]:
    navigate_to_rtd_sources_dir()
    rst_file_ext = ".rst"
    rst_files = glob.glob(os.getcwd() + f"/**/*{rst_file_ext}", recursive=True)
    if not files_to_check:
        return rst_files
    return [rst_file for rst_file in rst_files for f in files_to_check if f in rst_file]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('-f', nargs='+', required=False, default="")
    args = vars(p.parse_args())['f']
    rst_files = gather_file_names(args)
    files_links_dict = get_links_from_files(rst_files)
    check_links(files_links_dict)

if __name__ == "__main__":
    main()