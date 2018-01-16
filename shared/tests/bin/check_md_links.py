#!/usr/bin/env python2.7

# Amazon FPGA Hardware Development Kit
#
# Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

# This script looks for broken hyperlinks in all markdown files (*.md) in the repository.
# It returns 0 if it didn't find any broken or non-zero if it found broken links.
#
# Specifics:
# Run at the top of the aws-fpga* repository you cloned.
# The algorithm is:
#  1) find all *.md files in the repo
#  2) For each md file:
#     - Render the markdown to xhtml5
#     - Scan the html for links and anchors save them in lists
#  3) Check all of the links:
#     - If it is an http link then use urllib2 to try to open the link.
#       Exception: Doesn't test links to the AWS forum because that requires a login to access
#     - Check each link to other markdown files to make sure that the file exists
#       and that if an anchor is specified in the link that the anchor exists.
#     - Print out the details of each broken link or missing anchor.
#  4) Display summary of results
#  5) return non-zero if there are broken links.
#

from __future__ import print_function
import argparse
import git
from HTMLParser import HTMLParser
import io
import logging
import markdown
import os
import os.path
from os.path import dirname, realpath
import re
import sys
try:
    # For Python 3.0 and later
    from urllib.request import urlopen
except ImportError:
    # Fall back to Python 2's urllib2
    from urllib2 import urlopen, urlparse
try:
    import aws_fpga_test_utils
    import aws_fpga_utils
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class HtmlAnchorParser(HTMLParser):
    '''
    Class for parsing html to extract links and anchors.

    It handles the start of each tag it finds and parses the tag type and its atrributes.
    A link is an "a" tag with an "href" attribute.
    An anchor is any tag with an 'id' or 'name' attribute.

    It saves the links in an array and it saves the anchors in a dict so that it is easy
    and efficient to check to see if an anchor exists.
    '''
    def __init__(self):
        HTMLParser.__init__(self)
        self.anchors = {}
        self.links = []
        return

    def handle_starttag(self, tag, attrs):
        # logger.info("started {}".format(tag))
        if tag == 'a':
            for attr in attrs:
                if attr[0] == 'href':
                    # logger.info('link: {}'.format(attr[1]))
                    self.links.append(attr[1])
        for attr in attrs:
            if attr[0] in ['id', 'name']:
                # logger.info("{} attr: {}".format(tag, attr))
                self.anchors[attr[1]] = 1
        return

def check_link(url):
    '''
    Checks a link whose URL starts with 'http'.

    Ignores links that start with:
    * https://forums.aws.amazon.com
    because you have to be signed in to the forum for the link to be valid.

    Uses urllib2 to parse the URL and check that it is valid.

    @returns True if the link is valid, False otherwise.
    '''
    logger.debug("Checking {}".format(url))
    if re.match(r'https://forums\.aws\.amazon\.com/', url):
        return True
    try:
        if not urlparse.urlparse(url).netloc:
            return False

        website = urlopen(url)
        html = website.read()

        if website.code != 200:
            return False
    except Exception, e:
        logger.exception("")
        return False
    return True

def contains_link(path):
    parent_dir = dirname(path)
    if parent_dir == path:
        return False
    if os.path.islink(path):
        logger.debug("Found link: {}".format(path))
        return True
    return contains_link(parent_dir)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--exclude', action='store', nargs='*', default=[], help="Paths to ignore")
    parser.add_argument('--ignore-url', action='store', nargs='*', default=[], help="URLs to ignore. Will ignore all URLs starting with this prefix.")
    parser.add_argument('--debug', action='store_true', default=False, help="Enable debug messages")
    args = parser.parse_args()
    if args.debug:
        logger.setLevel(logging.DEBUG)

    # Make sure running at root of repo
    repo_dir = aws_fpga_test_utils.get_git_repo_root(dirname(__file__))
    os.chdir(repo_dir)

    num_links = 0  # total number of links we've found in .md files
    num_broken = 0  # total number of links which are broken

    if args.exclude:
        logger.info("Ignoring {} paths:\n  {}".format(len(args.exclude), "  \n".join(args.exclude)))
    if args.ignore_url:
        logger.info("Ignoring {} urls:\n  {}".format(len(args.ignore_url), "  \n".join(args.ignore_url)))

    # Get a list of markdown files
    logger.debug("Getting list of .md files")
    md_files = []
    topdir = '.'
    for root, dirs, files in os.walk(topdir):
        for name in files:
            if name.lower().endswith('.md'):
                path = os.path.join(root, name)
                path = os.path.relpath(path)
                exclude = False
                for exclude_path in args.exclude:
                    if re.match(exclude_path, path):
                        exclude = True
                        break
                if exclude:
                    logger.warning("Ignoring {}".format(path))
                    continue
                md_files.append(path)
    logger.debug ("Found {} .md files".format(len(md_files)))

    # Render the markdown files to xhtml5 and parse the HTML for links and anchors
    md_info = {}
    for md_file in md_files:
        md_info[md_file] = {}
        logger.debug("Rendering {} to html".format(md_file))
        md_info[md_file]['html'] = markdown.markdown(io.open(md_file, 'r', encoding='utf-8').read(), extensions=['markdown.extensions.toc'], output='xhtml5')
        html_parser = HtmlAnchorParser()
        logger.debug("  Parsing out anchors and links")
        html_parser.feed(md_info[md_file]['html'])
        md_info[md_file]['anchors'] = html_parser.anchors
        md_info[md_file]['links'] = html_parser.links
        num_links += len(html_parser.links)

    # Check links
    for md_file in md_files:
        logger.debug("Checking {}".format(md_file))
        for link in md_info[md_file]['links']:
            if re.match('http', link):
                ignore = False
                for url in args.ignore_url:
                    if link.startswith(url):
                        ignore = True
                        logger.warning("In {} ignoring {}".format(md_file, link))
                        break
                if ignore:
                    continue
                # Check using urllib2
                if not check_link(link):
                    logger.error("Broken link in {}: {}".format(md_file, link))
                    num_broken += 1
            else:
                # File reference
                # Split out the anchor in the file, if it exists.
                matches = re.search(r'^(.*)#(.+)$', link)
                if matches:
                    link_only = matches.group(1)
                    anchor = matches.group(2)
                else:
                    link_only = link
                    anchor = None
                file_exists = True
                if len(link_only):
                    # Link points to a different file
                    md_file_dir = dirname(md_file)
                    link_path = os.path.join(md_file_dir, link_only)
                    # github doesn't resolve paths that contain symbolic links
                    if contains_link(link_path):
                        logger.error("Broken link in {}: {}".format(md_file, link))
                        logger.error("  Link contains a symbolic link.")
                        num_broken += 1
                    link_path = os.path.relpath(link_path)
                    if not os.path.exists(link_path):
                        logger.error("Broken link in {}: {}".format(md_file, link))
                        logger.error("  File doesn't exist: {}".format(link_path))
                        file_exists = False
                        num_broken += 1
                else:
                    # Links is an anchor only that points to the same file.
                    link_path = md_file
                if file_exists and anchor:
                    # If there is an anchor check to make sure it is valid
                    if not link_path in md_info:
                        logger.error("Broken link in {}: {}".format(md_file, link))
                        logger.error("  No anchors found for {}".format(link_path))
                        num_broken += 1
                    elif not anchor in md_info[link_path]['anchors']:
                        logger.error("Broken link in {}: {}".format(md_file, link))
                        logger.error("    Anchor missing in {}".format(link_path))
                        num_broken += 1

    logger.info("NUM doc files (.md)   : {}".format(len(md_files)))
    logger.info("NUM links in doc files: {}".format(num_links))
    logger.info("NUM brokenlinks       : {}".format(num_broken))

    # if no broken links, return code is 0. Else it's the number of broken links.
    sys.exit(num_broken)
