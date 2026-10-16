#!/usr/bin/env python3

# =============================================================================
# Amazon FPGA Hardware Development Kit
#
# Copyright 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

"""Validate relative links and image paths in the repo's markdown files.

The RST link checker only sees generated files under docs-rtd/source, and the md->rst sync
recomputes image path prefixes from the destination RST's depth. A wrong `../` count in a
markdown file is therefore invisible to both: the docs site renders correctly while GitHub,
which resolves the markdown literally, shows a broken image. This checker reads the markdown
sources directly so those paths are validated where they're actually authored.

External (http/https) links are out of scope here; check_doc_links.py covers those via the
generated RST.
"""

import argparse
import logging
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

logging.basicConfig(level=logging.INFO, format="%(message)s", handlers=[logging.StreamHandler(sys.stdout)])
logger = logging.getLogger(__name__)

# Links we never resolve on disk: external targets, same-page anchors, and templated paths.
SKIP_PREFIXES = ("http://", "https://", "mailto:", "ftp://", "#")
SKIP_SUBSTRINGS = ("${", "{{", "<")

LINK_PATTERNS = (
    # Markdown image and inline link: ![alt](path) / [text](path)
    re.compile(r"!?\[[^\]]*\]\(\s*([^)\s]+)"),
    # Raw HTML kept in markdown for tables the RST converter can't express
    re.compile(r"<img[^>]+src=[\"']([^\"']+)[\"']", re.IGNORECASE),
    re.compile(r"<a[^>]+href=[\"']([^\"']+)[\"']", re.IGNORECASE),
)

ESCAPES_ROOT = "escapes the repo root"
MISSING = "target does not exist"


@dataclass
class BrokenLink:
    md_file: Path
    link: str
    reason: str


def get_repo_root(timeout: int = 5) -> Path:
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(__file__),
        timeout=timeout,
        check=True,
    )
    return Path(result.stdout.strip())


class MarkdownLinkChecker:
    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.broken_links: list[BrokenLink] = []
        self.total_checked = 0

    def find_md_files(self) -> list[Path]:
        """List tracked markdown files, so generated and vendored trees are excluded for free."""
        result = subprocess.run(
            ["git", "ls-files", "*.md"],
            capture_output=True,
            text=True,
            cwd=self.repo_root,
            check=True,
        )
        md_files = [self.repo_root / line for line in result.stdout.splitlines() if line]
        logger.info(f"Found {len(md_files)} markdown files to check")
        return md_files

    def extract_links(self, md_file: Path) -> list[str]:
        content = md_file.read_text(encoding="utf-8", errors="ignore")

        links: list[str] = []
        for pattern in LINK_PATTERNS:
            for match in pattern.finditer(content):
                link = match.group(1).strip()
                if link.startswith(SKIP_PREFIXES) or any(skip in link for skip in SKIP_SUBSTRINGS):
                    continue
                links.append(link)
        return links

    def check_link(self, md_file: Path, link: str) -> BrokenLink | None:
        self.total_checked += 1

        # Strip the anchor; anchor validity inside markdown isn't checked here
        path_part = link.split("#")[0]
        if not path_part:
            return None

        target = self.repo_root / path_part.lstrip("/") if path_part.startswith("/") else md_file.parent / path_part
        target = Path(os.path.normpath(target))

        try:
            target.relative_to(self.repo_root)
        except ValueError:
            return BrokenLink(md_file, link, ESCAPES_ROOT)

        if not target.exists():
            return BrokenLink(md_file, link, MISSING)
        return None

    def check_files(self, md_files: list[Path]) -> None:
        for md_file in md_files:
            for link in self.extract_links(md_file):
                broken = self.check_link(md_file, link)
                if broken:
                    self.broken_links.append(broken)

    def print_summary(self) -> None:
        logger.info("\n" + "=" * 80)
        logger.info("MARKDOWN LINK CHECK SUMMARY")
        logger.info("=" * 80)
        logger.info(f"Total relative links checked: {self.total_checked:4d}")
        logger.info(f"❌ Broken links:              {len(self.broken_links):4d}")

        if not self.broken_links:
            return

        logger.error(f"\n{'-' * 80}")
        logger.error("DETAILS:")
        logger.error(f"{'-' * 80}")
        for broken in self.broken_links:
            logger.error(f"\n📄 {broken.md_file.relative_to(self.repo_root)}:")
            logger.error(f"   ❌ {broken.link}")
            logger.error(f"      {broken.reason}")


def main():
    parser = argparse.ArgumentParser(description="Markdown relative link and image path checker")
    parser.add_argument("-r", "--repo_root", type=Path, default=None, help="Repo root to scan (default: git toplevel)")
    args = parser.parse_args()

    checker = MarkdownLinkChecker(args.repo_root or get_repo_root())

    md_files = checker.find_md_files()
    assert md_files, "No markdown files found to check!"

    checker.check_files(md_files)
    checker.print_summary()
    assert not checker.broken_links, "Broken links found!"
    logger.info("NO ISSUES DETECTED!")


if __name__ == "__main__":
    main()
