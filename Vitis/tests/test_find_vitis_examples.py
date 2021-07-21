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
'''
Pytest module:

Call using ```pytest test_find_vitis_examples.py```

See TESTING.md for details.
'''

from __future__ import print_function
import os
from os.path import dirname, realpath
import json
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source shared/bin/setup_test_env.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)

class TestFindVitisExamples(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    '''
    ADD_XILINX_VERSION = True

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)
        return

    def test_find_example_makefiles(self, xilinxVersion):

        assert os.path.exists(self.xilinx_vitis_examples_dir), "The Xilinx Vitis example dir does not exist: {}".format(self.xilinx_vitis_examples_dir)
        assert os.listdir(self.xilinx_vitis_examples_dir) != [], "Xilinx Vitis example submodule not cloned or does not exist"

        xilinx_examples_makefiles = []
        xilinx_vitis_example_map = {}

        for root, dirs, files in os.walk(self.xilinx_vitis_examples_dir):
            ignore = False

            if os.path.exists(root + "/description.json") and os.path.exists(root + "/Makefile"):
                with open(root + "/description.json", "r") as description_file:
                    description = json.load(description_file)

                    if "containers" in description:
                        if len(description["containers"]) > 1:
                            ignore = True
                            logger.info("Ignoring {} as >1 containers found in description.json.".format(root))
                    else:
                        ignore = True
                        logger.info("Ignoring {} as no containers found in description.json.".format(root))
                        continue

                    if "ndevice" in description:
                        if "aws" in description["ndevice"]:
                            ignore = True
                            logger.info("Ignoring {} as F1 device found in ndevice.".format(root))
                            continue

                    if "platform_blacklist" in description:
                        if "aws" in description["platform_blacklist"]:
                            ignore = True
                            logger.info("Ignoring {} as F1 device found in ndevice.".format(root))
                            continue
            else:
                ignore = True
                logger.warn("Ignoring: {} as no Makefile/description.json exist".format(root))

            if not ignore:
                xilinx_examples_makefiles.append(root)
                logger.info("Adding: " + root)

        assert len(xilinx_examples_makefiles) != 0, "Could not find any Xilinx Vitis example in %s" % self.xilinx_vitis_examples_dir

        # Remove the workspace path so that the next node can reference this path directly
        # So we don't face cases like /workspace@3 ..
        xilinx_examples_makefiles = [os.path.relpath(full_path, self.WORKSPACE) for full_path in xilinx_examples_makefiles]

        for example_path in xilinx_examples_makefiles:

            example_test_class = example_path.replace('/', '__').capitalize()

            xilinx_vitis_example_map[example_test_class] = example_path

        with open(self.xilinx_vitis_examples_list_file, 'w') as outfile:
            json.dump(xilinx_vitis_example_map, outfile)

        # Also write the archive file
        with open(self.xilinx_vitis_examples_list_file + "." + xilinxVersion, 'w') as archive_file:
            json.dump(xilinx_vitis_example_map, archive_file)

        assert os.path.getsize(self.xilinx_vitis_examples_list_file) > 0, "%s is a non zero file. We need to have some data in the file" % self.xilinx_vitis_examples_list_file
