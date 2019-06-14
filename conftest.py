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
    parser.addoption("--batch", action="store", required=False, type=str,
        help="batch option for internal simulations", default=0)
    parser.addoption("--simulator", action="store", required=False, type=str,
        help="Simulator tool requested for this test", default="vivado")
    parser.addoption("--examplePath", action="store", required=False, type=str,
        help="Path to the Xilinx Example to test", default="SDAccel/examples/xilinx/getting_started/host/helloworld_ocl")
    parser.addoption("--rteName", action="store", required=False, type=str,
        help="RTE Name", default="dyn")
    parser.addoption("--xilinxVersion", action="store", required=False, type=str,
        help="Xilinx Version. For eg: 2017.4, 2018.2, 2018.3 etc", default="2018.3")


def pytest_generate_tests(metafunc):

    if metafunc.cls.ADD_BATCH:
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("Batch = " + metafunc.config.getoption('batch'))
        metafunc.parametrize("batch", [metafunc.config.getoption('batch')])

    if metafunc.cls.ADD_SIMULATOR:
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("Simulator = " + metafunc.config.getoption('simulator'))
        metafunc.parametrize("simulator", [metafunc.config.getoption('simulator')])

    if metafunc.cls.ADD_EXAMPLEPATH:
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("examplePath = " + metafunc.config.getoption('examplePath'))
        metafunc.parametrize("examplePath", [metafunc.config.getoption('examplePath')])

    if metafunc.cls.ADD_RTENAME:
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("rteName = " + metafunc.config.getoption('rteName'))
        metafunc.parametrize("rteName", [metafunc.config.getoption('rteName')])

    if metafunc.cls.ADD_XILINX_VERSION:
        print("Configuring parameters of {}::{}".format(metafunc.module.__name__, metafunc.function.__name__))
        print("xilinxVersion = " + metafunc.config.getoption('xilinxVersion'))
        metafunc.parametrize("xilinxVersion", [metafunc.config.getoption('xilinxVersion')])
