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
pytest configuration
'''

import pytest

def pytest_addoption(parser):
    parser.addoption("--examplePath", action="store", required=False, type=str,
        help="Path to the Xilinx Example to test")

def pytest_generate_tests(metafunc):
    if metafunc.module.__name__ == 'test_run_sdaccel_examples' :
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("examplePath = " + metafunc.config.getoption('examplePath'))
        metafunc.parametrize("examplePath", [metafunc.config.getoption('examplePath')])
