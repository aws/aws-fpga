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
import atexit
import logging
import os
import re
import signal
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import unquote, urljoin

import requests
import urllib3
import urllib3.util
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

logging.basicConfig(level=logging.INFO, format="%(message)s", handlers=[logging.StreamHandler(sys.stdout)])
logger = logging.getLogger(__name__)

# Suppress SSL warnings for better output
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Constants
SUCCESS = 200
NOT_FOUND = 404
LOCAL_HOST = "http://localhost:3000"
REQUEST_TIMEOUT = 10  # Increased timeout but with better handling
MAX_RETRIES = 1
BACKOFF_FACTOR = 1
ERROR = "ERROR"
EXCEPTION = "EXCEPTION"


class ResultEnum(IntEnum):
    """Enumeration for link check results."""

    OK = 0
    ERROR = 1
    EXCEPTION = 2


class LinkListEnum(IntEnum):
    ERROR = 0
    EXCEPTION = 1


class NoFilesToCheckError(Exception):
    pass


class WebServerNotStartedError(Exception):
    pass


@dataclass
class ResponseInfo:
    succeeded: bool = False
    status_code: int = 0
    msg: str = ""


class LinkChecker:
    def __init__(self, exceptions_file: Optional[str] = None, worker_name: str = "links_logger"):
        self.rtd_source_dir: Path = Path(f"{self._get_repo_root()}/docs-rtd/source")
        self.rtd_build_dir: Path = Path(f"{self._get_repo_root()}/docs-rtd/build/html")
        self.exceptions: set[str] = self._load_exceptions(exceptions_file) if exceptions_file else set()
        self.session: requests.Session = self._create_session()
        self.server_process: Optional[subprocess.Popen] = None

        self.total_checked = 0
        self.total_ok = 0
        self.total_errors = 0
        self.total_exceptions = 0
        self.error_links: Dict[str, List[Tuple[str, str]]] = defaultdict(list)
        self.exception_links: Dict[str, List[Tuple[str, str]]] = defaultdict(list)

        # Register cleanup
        atexit.register(self._cleanup)

    def _get_repo_root(self) -> str:
        try:
            result = subprocess.run(
                ["git", "rev-parse", "--show-toplevel"],
                capture_output=True,
                text=True,
                cwd=os.path.dirname(__file__),
                timeout=5,
                check=True,
            )
            return result.stdout.strip()
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            current_dir = Path(__file__).parent.parent.parent
            return str(current_dir.resolve())

    def _load_exceptions(self, exceptions_file: str) -> Set[str]:
        exceptions = set()
        try:
            with open(exceptions_file, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        # Extract URL from "URL: filepath" format
                        # Split on the last ": " to handle URLs with colons (https://)
                        if ": " in line:
                            url = line.rsplit(": ", 1)[0].strip()
                            if url:
                                exceptions.add(url)
            logger.info(f"Loaded {len(exceptions)} link exceptions")
        except FileNotFoundError:
            logger.exception(f"Exceptions file not found: {exceptions_file}")
            raise
        except Exception as e:
            logger.exception(f"Error loading exceptions: {e}")
            raise

        return exceptions

    def _create_session(self) -> requests.Session:
        session = requests.Session()
        retry_strategy = Retry(
            total=MAX_RETRIES,
            backoff_factor=BACKOFF_FACTOR,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["HEAD", "GET", "OPTIONS"],
        )

        adapter = HTTPAdapter(max_retries=retry_strategy, pool_connections=10, pool_maxsize=10)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.headers.update(
            {
                "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate",
                "Connection": "keep-alive",
            }
        )
        return session

    def _cleanup(self):
        if self.session:
            self.session.close()
        self._stop_server()

    def find_rst_files(self, file_patterns: List[str]) -> List[str]:
        if not self.rtd_source_dir.exists():
            raise FileNotFoundError(f"Documentation source directory not found: {self.rtd_source_dir}")

        rst_file_paths = [str(f) for f in list(self.rtd_source_dir.glob("**/*.rst"))]
        if file_patterns:
            filtered_files = []
            for pattern in file_patterns:
                filtered_files.extend([f for f in rst_file_paths if pattern in f])
            rst_file_paths = list(set(filtered_files))  # Remove duplicates

        logger.info(f"Found {len(rst_file_paths)} RST files to check")
        return rst_file_paths

    def extract_links_from_file(self, rst_file: str) -> List[Tuple[str, str]]:
        content = None
        try:
            with open(rst_file, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            logger.exception(f"Error reading file {rst_file}: {e}")
            raise

        # Regex pattern to match RST links: `link text <url>`__
        # Avoiding double backticks to prevent matching code blocks
        pattern = r"(?<!`)`([^`<]*)<([^>]+)>`__"

        links: list[tuple[str, str]] = []
        for match in re.finditer(pattern, content, re.DOTALL):
            link_text = match.group(1).strip()
            link_url = match.group(2).strip()
            if any(skip in link_url for skip in ["mailto:", "|"]):
                continue
            links.append((link_text, link_url))
        return links

    def _start_local_server(self) -> None:
        if not self.rtd_build_dir.exists():
            raise FileNotFoundError(
                f"Build directory not found: {self.rtd_build_dir}! "
                "Please build the documentation first with 'make html' in docs-rtd/"
            )

        try:
            self.server_process = subprocess.Popen(
                [sys.executable, "-m", "http.server", "3000"],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                preexec_fn=os.setsid,  # Create new process group
                cwd=self.rtd_build_dir,
            )
            time.sleep(2)
            try:
                response = self.session.get(LOCAL_HOST, timeout=5)
                if response.status_code == 200:
                    logger.info("Local HTTP server started successfully")
                else:
                    logger.error(f"Server responded with status {response.status_code}")
            except Exception as e:
                logger.exception(f"Server not responding: {e}")
                raise WebServerNotStartedError("Local web server did not respond! Cannot check RTD doc links!")
        except Exception as e:
            logger.exception(f"Failed to start server: {e}")
            raise WebServerNotStartedError("Failed to start local web server! Cannot check RTD doc links!")

    def _stop_server(self) -> None:
        if self.server_process:
            try:
                os.killpg(os.getpgid(self.server_process.pid), signal.SIGTERM)
                self.server_process.wait(timeout=5)
                logger.info("Local HTTP server stopped")
            except (OSError, subprocess.TimeoutExpired):
                try:
                    os.killpg(os.getpgid(self.server_process.pid), signal.SIGKILL)
                    self.server_process.wait(timeout=2)
                except Exception:
                    pass

    def _check_external_link(self, url: str) -> ResponseInfo:
        try:
            # For URLs with anchors, we need the content to validate the anchor
            # so use GET request directly
            response = None
            if "#" in url:
                response = self.session.get(url, timeout=REQUEST_TIMEOUT, allow_redirects=True)
            else:
                # Use HEAD request first for efficiency
                response = self.session.head(url, timeout=REQUEST_TIMEOUT, allow_redirects=True)

                # Some servers don't support HEAD, try GET if HEAD fails
                if response.status_code in [405, 501]:
                    response = self.session.get(url, timeout=REQUEST_TIMEOUT, allow_redirects=True)

            if "#" in url and response.status_code == 200:
                return self._check_anchor_in_response(url, response)
            return ResponseInfo(response.status_code == 200, response.status_code, "")
        except Exception as e:
            return ResponseInfo(
                False, 0, f"Exception: {e.__class__.__name__} occurred during external link check: {str(e)}"
            )

    def _check_internal_link(self, rst_file: str, link_url: str) -> ResponseInfo:
        try:
            if "#" in link_url:
                return self._check_anchor_link(rst_file, link_url)
            else:
                return self._check_internal_file_link(rst_file, link_url)

        except Exception as e:
            return ResponseInfo(
                False, 0, f"Exception: {e.__class__.__name__} occurred during internal link check: {str(e)}"
            )

    def _check_anchor_link(self, rst_file: str, link_url: str) -> ResponseInfo:
        SAME_PAGE_ANCHOR = "same-page anchor"
        OTHER_PAGE_ANCHOR = "other-page anchor"

        full_url, link_type = "", ""
        if link_url.startswith("#"):
            full_url = self._rst_path_to_html_url(rst_file) + link_url
            link_type = SAME_PAGE_ANCHOR
        else:
            full_url = self._resolve_relative_link(rst_file, link_url)
            link_type = OTHER_PAGE_ANCHOR

        try:
            response = self.session.get(full_url, timeout=REQUEST_TIMEOUT)
            if response.status_code == 200:
                return self._check_anchor_in_response(full_url, response)
            return ResponseInfo(
                False, response.status_code, f"Page not found when attemptiong to check anchor link: {full_url}!"
            )
        except Exception as e:
            return ResponseInfo(
                False, 0, f"Exception {e.__class__.__name__} occurred when checking {link_type}: {str(e)}"
            )

    def _check_internal_file_link(self, rst_file: str, link_url: str) -> ResponseInfo:
        full_url = self._resolve_relative_link(rst_file, link_url)

        try:
            response = self.session.head(full_url, timeout=REQUEST_TIMEOUT)
            return ResponseInfo(response.status_code == 200, response.status_code, "")
        except Exception as e:
            return ResponseInfo(
                False, 0, f"Exception {e.__class__.__name__} occurred when checking for internal file: {str(e)}"
            )

    def _rst_path_to_html_url(self, rst_file: str) -> str:
        rel_path = Path(rst_file).relative_to(self.rtd_source_dir)
        html_path = rel_path.with_suffix(".html")
        return f"{LOCAL_HOST}/{html_path}"

    def _resolve_relative_link(self, rst_file: str, link_url: str) -> str:
        relative_rst_file_path = Path(rst_file).relative_to(self.rtd_source_dir)
        rst_file_dir_depth = len(relative_rst_file_path.parent.parts)
        link_url_levels_up = len([part for part in Path(link_url).parts if part == ".."])
        if link_url_levels_up > rst_file_dir_depth:
            raise RuntimeError(f"Link: {link_url} tries to escape root dir!")

        base_url = self._rst_path_to_html_url(rst_file)
        return urljoin(base_url, link_url)

    def _check_anchor_in_response(self, url: str, response: requests.Response) -> ResponseInfo:
        _, fragment = url.split("#", 1)
        fragment = unquote(fragment)

        if urllib3.util.parse_url(url).host == "github.com":
            return self._check_github_line_numbers(fragment, response)

        # Check for HTML anchors/sections
        content = response.text.lower()
        fragment_lower = fragment.lower()

        # Common patterns for anchors in HTML - only look for actual anchor definitions
        patterns = [
            f'id="{fragment_lower}"',
            f"id='{fragment_lower}'",
            f'name="{fragment_lower}"',
            f"name='{fragment_lower}'",
            # Pattern for when fragment appears in content (like headings)
            fragment_lower.replace("-", " ").replace("_", " "),
        ]

        anchor_found = any(pattern in content for pattern in patterns)
        if anchor_found:
            return ResponseInfo(True, response.status_code, "")
        return ResponseInfo(False, 404, f"Anchor '{fragment}' not found in link: {url}")

    def _check_github_line_numbers(self, fragment: str, response: requests.Response) -> ResponseInfo:
        line_match = re.search(r"L(\d+)(?:-L?(\d+))?$", fragment)
        if not line_match:
            return ResponseInfo(True, response.status_code, "")  # Not a line number link

        start_line = int(line_match.group(1))
        end_line = int(line_match.group(2)) if line_match.group(2) else start_line
        total_lines = len(response.text.splitlines())

        valid_response = 1 <= start_line <= end_line <= total_lines
        if valid_response:
            return ResponseInfo(True, response.status_code, "")
        return ResponseInfo(False, 404, f"Line range {start_line}-{end_line} not valid (file has {total_lines} lines)")

    def _format_display_text(self, text: str, max_length: int = 150) -> str:
        if not text.strip():
            return "[empty link text]"

        # Normalize whitespace - replace newlines, tabs, and multiple spaces with single spaces
        normalized_text = re.sub(r"\s+", " ", text.strip())
        return normalized_text if len(normalized_text) <= max_length else (normalized_text[: max_length - 3] + "...")

    def _format_display_url(self, url: str, max_length: int = 150) -> str:
        if len(url) <= max_length:
            return url
        prefix_len = max_length // 2 - 2
        suffix_len = max_length - prefix_len - 3
        return url[:prefix_len] + "..." + url[-suffix_len:]

    def check_link(self, rst_file: str, link_text: str, link_url: str) -> ResultEnum:
        self.total_checked += 1
        display_text = self._format_display_text(link_text)

        if link_url in self.exceptions:
            self.total_exceptions += 1
            self.exception_links[rst_file].append((link_text, link_url))
            logger.warning(f"  ⚠️ EXCEPTION  | {display_text}")
            logger.warning(f"               | {link_url}")
            return ResultEnum.EXCEPTION

        resp_info: ResponseInfo
        if link_url.startswith(("http://", "https://")):
            resp_info = self._check_external_link(link_url)
        else:
            resp_info = self._check_internal_link(rst_file, link_url)

        if resp_info.succeeded:
            self.total_ok += 1
            logger.info(f"  ✅ OK ({resp_info.status_code:3d}) | {display_text}")
            logger.info(f"               | {link_url}")
            return ResultEnum.OK

        self.total_errors += 1
        self.error_links[rst_file].append((link_text, link_url))
        error_detail = f" - {resp_info.msg}" if resp_info.msg else ""
        logger.error(f"  ❌ ERROR ({resp_info.status_code:3d}) | {display_text}")
        logger.error(f"                   | {link_url}{error_detail}")
        return ResultEnum.ERROR

    def check_files(self, rst_files: List[str]) -> None:
        if not rst_files:
            raise NoFilesToCheckError("No RST files to check!")

        self._start_local_server()

        logger.info(f"Checking links in {len(rst_files)} files...")
        for rst_file in rst_files:
            logger.info(f"\nChecking file: {rst_file}")
            links = self.extract_links_from_file(rst_file)
            if not links:
                logger.warning("  No links found")
                continue
            logger.info(f"  Found {len(links)} links")
            for link_text, link_url in links:
                self.check_link(rst_file, link_text, link_url)

    def _print_error_or_exception_links(
        self, to_print: Dict[str, List[Tuple[str, str]]], list_enum: LinkListEnum
    ) -> None:
        logger.error(f"\n{'-' * 80}")
        logger.error(f"DETAILS for ({self.total_errors} {ERROR} links):")
        logger.error(f"{'-' * 80}")
        for rst_file, links in to_print.items():
            short_file = Path(rst_file).relative_to(self.rtd_source_dir)
            logger.error(f"\n📄 {short_file}:")
            for link_text, link_url in links:
                display_text = self._format_display_text(link_text, 50)
                logger.error(f"   ❌ {display_text}")
                logger.error(f"     {link_url}")

    def print_summary(self) -> None:
        logger.info("\n" + "=" * 80)
        logger.info("LINK CHECK SUMMARY")
        logger.info("=" * 80)
        logger.info(f"Total links checked: {self.total_checked:4d}")
        logger.info(f"✅ Valid links:       {self.total_ok:4d}")
        logger.info(f"❌ Broken links:      {self.total_errors:4d}")
        logger.info(f"⚠️ Exception links:   {self.total_exceptions:4d}")
        if self.error_links:
            self._print_error_or_exception_links(self.error_links, LinkListEnum.ERROR)


def main():
    parser = argparse.ArgumentParser(
        description="RST files link checker", formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("-e", "--exceptions_file_path", type=str, help="Path to file containing link exceptions")
    parser.add_argument("-f", "--check_file_paths", nargs="+", help="Specific file patterns to check (optional)")
    parser.add_argument(
        "-w",
        "--worker_name",
        type=str,
        default="links_logger",
        help="Name for the worker/logger (default: links_logger)",
    )

    args = parser.parse_args()
    checker = LinkChecker(exceptions_file=args.exceptions_file_path, worker_name=args.worker_name)

    rst_files = checker.find_rst_files(args.check_file_paths)
    assert rst_files, "No RST files found to check!"

    checker.check_files(rst_files)
    checker.print_summary()
    assert checker.total_errors == 0, "Broken links found!"


if __name__ == "__main__":
    main()
