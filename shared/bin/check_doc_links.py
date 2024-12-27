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

from codecs import strict_errors
from collections import defaultdict
from email.policy import default
import os
import pathlib
import glob
import re
import requests
import signal
import subprocess
import sys
from termcolor import colored
from time import sleep
from typing import Dict, List, Match

def get_repo_root_dir() -> str:
    repo_root_dir = subprocess.run("git rev-parse --show-toplevel".split(), capture_output=True, cwd=os.path.dirname(__file__), check=True).stdout.decode("utf-8").strip()
    return repo_root_dir


def get_link_to_self_html(rst_f: str) -> str:
    repo_root_dir = get_repo_root_dir()
    rst_to_html = rst_f.replace(".rst", ".html")
    rst_to_html = rst_to_html.replace("docs-rtd/source/", "")
    rst_to_html = rst_to_html.replace(f"{repo_root_dir}", ".")
    return rst_to_html


def perform_request(link_body: str, rst_f: str, preamble: str) -> int:
    default_request = "http://localhost:3000"
    is_external_link = link_body.startswith("http")
    is_internal_section_link = link_body.startswith("#")
    try:
        if is_external_link:
            response = requests.get(
                link_body,
                timeout=2,
                headers={"User-Agent": "Mozilla/5.0"},
                allow_redirects=True
            )
        elif is_internal_section_link:
            link_to_self = get_link_to_self_html(rst_f)
            internal_link = f"{link_to_self}{link_body}"
            response = requests.head(f"{default_request}/{internal_link}")
        else:
            file_or_directory_link = f"{default_request}/{link_body}"
            response = requests.head(file_or_directory_link)

        return_code = response.status_code
        if return_code != 200:
            raise requests.RequestException(response)
        print(preamble + colored(f" OK, {return_code}", "green"))
        return 0
    except requests.RequestException as re:
        return_code = 404
        print(preamble + colored(f"ERROR, {return_code}", "red"))
        return 1


def navigate_to_rtd_build_html_dir() -> None:
    repo_root_dir = get_repo_root_dir()
    rtd_build_html_dir = "docs-rtd/build/html"
    os.chdir(f"{repo_root_dir}/{rtd_build_html_dir}")


def check_links(files_links_dict: Dict[str, List[List[str]]]) -> None:
    navigate_to_rtd_build_html_dir()
    print(os.getcwd())
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
                preamble = f"\t{link_text}, {link_body}: "
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


def gather_file_names() -> List[str]:
    navigate_to_rtd_sources_dir()
    rst_file_ext = ".rst"
    rst_files = glob.glob(os.getcwd() + f"/**/*{rst_file_ext}", recursive=True)
    return rst_files


def main():
    rst_files = gather_file_names()
    files_links_dict = get_links_from_files(rst_files)
    check_links(files_links_dict)

if __name__ == "__main__":
    main()