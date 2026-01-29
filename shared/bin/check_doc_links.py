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

import argparse
import glob
import logging
import os
import re
import signal
import subprocess
import sys
from collections import defaultdict
from enum import IntEnum
from time import sleep
from typing import Dict, List, Match, Set
from urllib.parse import unquote

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

SUCCESS = 200
NOT_FOUND = 404
LOCAL_HOST = "http://localhost:3000"
REPO_ROOT_DIR = (
    subprocess.run(
        "git rev-parse --show-toplevel".split(),
        capture_output=True,
        cwd=os.path.dirname(__file__),
        check=True,
    )
    .stdout.decode("utf-8")
    .strip()
)


class ResultEnum(IntEnum):
    OK = 0
    ERROR = 1
    EXCEPTION = 2


class InternalLinkType(IntEnum):
    SAME_PAGE = 1
    OTHER_PAGE = 2


def display_links_dict(in_dict: Dict[str, Dict[str, str]], logger: logging.Logger) -> None:
    logger.info("")
    for rst_f, links_dict in in_dict.items():
        logger.info(f"{rst_f}:")
        for link_text, link_body in links_dict.items():
            logger.info(f"\t{link_text} {link_body}")
        logger.info("")


def check_section_exists_in_html(link: str, response: requests.Response) -> int:
    _, fragment = link.split("#", 1)
    fragment = unquote(fragment)  # Handle URL-encoded fragments

    # Works when the RST tag matches the section name
    # This can't always be accommodated, because there cannot be two identical tags across any two RST documents.
    # IE Getting started in both HDK README and SDK README
    # Can't both be .. _getting-started:
    # One should be .. _getting-started-hdk: and the other .. _getting-started-sdk:
    section_id_pattern = f'section id="{fragment}"'
    span_id_pattern = f'span id="{fragment}"'
    header_id_pattern = f'h2 id="{fragment}"'

    content = response.text
    found_internal_section = any(
        [pattern in content for pattern in [section_id_pattern, span_id_pattern, header_id_pattern]]
    )
    if response.status_code == SUCCESS and found_internal_section:
        return SUCCESS
    else:
        return NOT_FOUND


def perform_github_line_check(link: str, response: requests.Response) -> int:
    # Extract line numbers from URL
    line_match = re.search(r"#L(\d+)(?:-L?(\d+))?$", link)
    if not line_match:
        return SUCCESS

    start_line = int(line_match.group(1))
    # If group(2) exists, it's a range. Otherwise, end_line = start_line
    end_line = int(line_match.group(2)) if line_match.group(2) else start_line

    page_text = response.text.splitlines()
    total_lines = len(page_text)

    if 1 <= start_line <= end_line <= total_lines:
        return SUCCESS
    else:
        return NOT_FOUND
    return SUCCESS


def validate_section_exists(link: str, response: requests.Response) -> int:
    # GitHub line number links are different from other page section links:
    if "github.com" in link:
        return perform_github_line_check(link, response)
    return check_section_exists_in_html(link, response)


def get_link_to_self_html(rst_f: str, link_body: str, internal_link_type: InternalLinkType) -> str:
    if internal_link_type == InternalLinkType.SAME_PAGE:
        rst_to_html = rst_f.replace(".rst", ".html")  # Recontextualize to html
        rst_to_html = rst_to_html.replace(
            "docs-rtd/source/", ""
        )  # Lop this off because we want nothing but the path that follows
        rst_to_html = rst_to_html.replace(REPO_ROOT_DIR, "")  # Get rid of the full path as well
        rst_to_html = rst_to_html.replace(
            "./", ""
        )  # Get rid of any leading ./. Not that it causes problems, it's just confusing to look at in the output

        # Drop leading double //s. Not that they cause issues, they're just confusing to look at in the output
        if rst_to_html[0] == "/":
            rst_to_html = rst_to_html[1:]
        return f"{LOCAL_HOST}/{rst_to_html}{link_body}"
    else:
        filename_only = rst_f.split("/")[-1]
        relative_to_docs_rtd = rst_f.replace(REPO_ROOT_DIR, "")
        relative_to_docs_dir = relative_to_docs_rtd.replace("docs-rtd/source", "")
        final_relative_link = relative_to_docs_dir.replace(filename_only, "")
        revised_link = f"{final_relative_link}/{link_body}"
        web_server_internal_link = revised_link.replace("///", "/").replace("//", "/")
        if web_server_internal_link[0] == "/":
            web_server_internal_link = web_server_internal_link[1:]
        web_server_internal_link = f"{LOCAL_HOST}/{web_server_internal_link}"
        return web_server_internal_link


def construct_relative_link(rst_f: str, link_body: str) -> str:
    # Start by going to the location of the file that contains the relative link
    os.chdir(os.path.dirname(rst_f))

    # Follow the relative link
    back_pos = link_body.find("../")
    while back_pos != -1:
        os.chdir("..")
        link_body = link_body[:back_pos] + link_body[back_pos + 3 :]
        back_pos = link_body.find("../")

    # Obtain the specified file path that current directory is relative to
    start = os.getcwd().replace(REPO_ROOT_DIR, "").replace("/docs-rtd/source/", "")

    # Reassemble the link relative to the repo root
    start = f"{start}/{link_body.replace('../', '').replace('./', '')}"
    if start[-1] == "/":
        start = start[:-1]
    return start


def do_generic_html_request(rst_f: str, link_body: str, session: requests.Session) -> requests.Response:
    response = session.head(f"{LOCAL_HOST}/{link_body}")
    if response.status_code != SUCCESS:
        relative_link = construct_relative_link(rst_f, link_body)
        response = session.head(f"{LOCAL_HOST}/{relative_link}")
    return response


def do_other_page_section_request(rst_f: str, link_body: str, session: requests.Session) -> requests.Response:
    web_server_internal_link = get_link_to_self_html(rst_f, link_body, InternalLinkType.OTHER_PAGE)
    response = session.get(
        web_server_internal_link,
        timeout=3,
        headers={"User-Agent": "Mozilla/5.0"},
        allow_redirects=True,
        verify=True,
    )
    response.status_code = validate_section_exists(web_server_internal_link, response)
    return response


def do_same_page_link_request(rst_f: str, link_body: str, session: requests.Session) -> requests.Response:
    web_server_internal_link = get_link_to_self_html(rst_f, link_body, InternalLinkType.SAME_PAGE)
    response = session.get(web_server_internal_link, timeout=1)
    response.status_code = validate_section_exists(web_server_internal_link, response)
    return response


def do_external_link_request(link_body: str, session: requests.Session) -> requests.Response:
    response = session.get(
        link_body,
        timeout=3,
        headers={
            "User-Agent": "Mozilla/5.0",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.5",
        },
        allow_redirects=True,
        verify=True,
    )
    if "#" in link_body:
        response.status_code = validate_section_exists(link_body, response)
    return response


def gather_link_exceptions(exceptions_file_path: str) -> Set[str]:
    exceptions_set: Set[str] = set()
    if exceptions_file_path:
        with open(exceptions_file_path, "r") as give_pass:
            contents = give_pass.readlines()
            exceptions_set = {str(line.split(": ")[0]).strip() for line in contents}
    return exceptions_set


def perform_request(
    link_body: str,
    rst_f: str,
    preamble: str,
    exceptions_set: Set[str],
    logger: logging.Logger,
) -> int:
    is_external_link = link_body.startswith("http")
    is_same_page_section_link = link_body.startswith("#")
    is_other_page_section_link = "http" not in link_body and "#" in link_body
    link_is_broken = False

    session = requests.Session()
    retry_strategy = Retry(
        total=6,
        backoff_factor=2,
        status_forcelist=[429, 500, 502, 503, 504],
    )
    adapter = HTTPAdapter(max_retries=retry_strategy)
    session.mount("http://", adapter)
    session.mount("https://", adapter)

    link_is_broken = False
    status = "ERROR"
    response: requests.Response = requests.Response()

    if link_body in exceptions_set:
        logger.info(preamble + ": " + "OK, Exception Granted")
        return ResultEnum.EXCEPTION

    try:
        if is_external_link:
            response = do_external_link_request(link_body, session)

        elif is_same_page_section_link:
            response = do_same_page_link_request(rst_f, link_body, session)

        elif is_other_page_section_link:
            response = do_other_page_section_request(rst_f, link_body, session)

        elif "html" in link_body:
            response = do_generic_html_request(rst_f, link_body, session)

        else:
            file_or_directory_link = f"{LOCAL_HOST}/{link_body}"
            response = session.head(file_or_directory_link, timeout=1)

        link_is_broken = response.status_code != SUCCESS
        status = "ERROR" if link_is_broken else "OK"
        if status == "OK":
            logger.info(preamble + ": " + f"{status}, {response.status_code}")
        else:
            logger.error(preamble + ": " + f"{status}, {response.status_code}")
    except Exception as _:
        link_is_broken = True
        logger.error(preamble + ": " + "ERROR, Request exception thrown")
    finally:
        session.close()
        return ResultEnum(link_is_broken)


def navigate_to_rtd_build_html_dir() -> None:
    rtd_build_html_dir = "docs-rtd/build/html"
    os.chdir(f"{REPO_ROOT_DIR}/{rtd_build_html_dir}")


def check_links(
    files_links_dict: Dict[str, List[List[str]]],
    exceptions_file_path: str,
    logger: logging.Logger,
) -> None:
    navigate_to_rtd_build_html_dir()
    link_server = subprocess.Popen(
        [sys.executable, "-m", "http.server", "3000"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    sleep(1)

    total_links_in_error = 0
    errored_links: Dict[str, Dict[str, str]] = defaultdict(dict)

    exceptions_granted = 0
    links_granted_exceptions: Dict[str, Dict[str, str]] = defaultdict(dict)

    exceptions_set: Set[str] = set()
    if exceptions_file_path:
        exceptions_set = gather_link_exceptions(exceptions_file_path)
    logger.info(exceptions_set)

    try:
        for rst_f, link_info in files_links_dict.items():
            logger.info(f"Now testing links from: {rst_f}")
            for link in link_info:
                link_text = link[0]
                link_body = link[1]
                skip_link = any(["mailto" in link_body, "|" in link_body])
                if skip_link:
                    continue
                preamble = f"\t{link_text}, {link_body}"
                result = perform_request(link_body, rst_f, preamble, exceptions_set, logger)
                if result == ResultEnum.EXCEPTION:
                    exceptions_granted += 1
                    links_granted_exceptions[rst_f][link_text] = link_body
                elif result == ResultEnum.ERROR:
                    total_links_in_error += 1
                    errored_links[rst_f][link_text] = link_body
                else:
                    continue
            logger.info("")
    finally:
        link_server.send_signal(signal.SIGTERM)
        logger.info("Shutting down http server")
        logger.info(f"Total Exceptions Granted: {exceptions_granted}")
        display_links_dict(links_granted_exceptions, logger)
        logger.info(f"Total Links in Error: {total_links_in_error}")
        display_links_dict(errored_links, logger)
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
    link_pattern_regex = r"".join(
        [
            ignore_double_backtick,
            back_tick_that_starts_link,
            gets_link_text,
            gets_actual_link,
        ]
    )
    compiled_link_pattern = re.compile(link_pattern_regex, re.DOTALL)

    file_contents = ""
    with open(rst_f, "r", encoding="utf-8") as f:
        file_contents = f.read()

    for link_match in compiled_link_pattern.finditer(file_contents):
        files_links_dict[rst_f].append(get_link_text_and_link(link_match))


def get_links_from_files(rst_files: List[str]) -> Dict[str, List[List[str]]]:
    files_links_dict: Dict[str, List[List[str]]] = defaultdict(list)
    for rst_f in rst_files:
        process_file(rst_f, files_links_dict)
    return files_links_dict


def navigate_to_rtd_sources_dir() -> None:
    rtd_sources_dir = "docs-rtd/source"
    os.chdir(f"{REPO_ROOT_DIR}/{rtd_sources_dir}")


def gather_file_names(files_to_check: List[str]) -> List[str]:
    navigate_to_rtd_sources_dir()
    rst_file_ext = ".rst"
    rst_files = glob.glob(os.getcwd() + f"/**/*{rst_file_ext}", recursive=True)
    if not files_to_check:
        return rst_files
    return [rst_file for rst_file in rst_files for f in files_to_check if f in rst_file]


def configure_logger(worker_name: str) -> logging.Logger:
    worker_id: str = worker_name
    worker_id = f"worker_{worker_id}"
    logger = logging.getLogger(worker_id)
    if not logger.handlers:
        logger.setLevel(logging.INFO)

        logs_dir_name = "links_logs"
        os.makedirs(name=logs_dir_name, exist_ok=True)

        fh = logging.FileHandler(f"{logs_dir_name}/{worker_id}.log", mode="w")
        formatter = logging.Formatter("%(asctime)s - %(levelname)s - %(message)s")
        fh.setFormatter(formatter)
        logger.addHandler(fh)

    return logger


def main():
    p = argparse.ArgumentParser()
    p.add_argument("-e", "--exceptions_file_path", type=str, required=False, default="")
    p.add_argument("-f", "--check_file_paths", nargs="+", required=False, default="")
    p.add_argument("-w", "--worker_name", type=str, required=False, default="links_logger")
    args: argparse.Namespace = p.parse_args()
    logger = configure_logger(args.worker_name)
    if args.exceptions_file_path:
        logger.info(f"Exceptions path: {args.exceptions_file_path}")
    rst_files = gather_file_names(args.check_file_paths)
    files_links_dict = get_links_from_files(rst_files)
    check_links(files_links_dict, args.exceptions_file_path, logger)


if __name__ == "__main__":
    main()
