#!/usr/bin/env python

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

import unittest
import xmlrunner
import subprocess
import os
import logging
import sys

logging.basicConfig(
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)-5.5s]  %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)])

logger = logging.getLogger("run_tests")


class SimulationTestCases(unittest.TestCase):

    WORKSPACE      = "None"
    RUN_SIM_SCRIPT = "None"

    @classmethod
    def setUpClass(cls):
        if cls.WORKSPACE == "None":
            assert False, "Workspace not set correctly"
        if cls.RUN_SIM_SCRIPT == "None":
            assert False, "run_sim.sh script path not set correctly"

    def run_sim(self, test_dir="", test_name="", test_type=""):

        # Error on defaults
        if not(test_dir and test_name and test_type):
            self.fail("Please enter non empty test_dir, test_name and test_type when calling run_sim")

        command_line = [self.RUN_SIM_SCRIPT, '--test-name', test_name, '--test-dir', test_dir, '--test-type', test_type]

        logger.debug("Calling: " + subprocess.list2cmdline(command_line))

        try:
            output = subprocess.check_output(
                command_line,
                cwd=os.path.dirname(self.RUN_SIM_SCRIPT),
                stderr=subprocess.STDOUT
            )
            logger.info(output)

        except subprocess.CalledProcessError as e:
            self.fail(e.output)
        except OSError as o:
            self.fail(o.strerror)

    # cl_dram_dma sv

    def test_cl_dram_dma__dram_dma__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__ddr__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__clk_recipe__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_clk_recipe'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__int__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_int'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__peek_poke__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__peek_poke_pcis_axsize__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_pcis_axsize'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__ddr_peek_poke__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr_peek_poke'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    # cl_dram_dma c
    @unittest.skip("Skip till the test is fixed. Fix is planned.")
    def test_cl_dram_dma__dram_dma__c(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    # cl_hello_world sv

    def test_cl_hello_world__hello_world__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    # cl_test_gl_cntr sv

    def test_cl_hello_world__gl_cntr__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_gl_cntr'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    # cl_hello_world vhdl

    def test_cl_hello_world__hello_world__vhdl(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world_vhdl/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'vhdl'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    # cl_hello_world c

    def test_cl_hello_world__hello_world__c(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)


if __name__ == '__main__':

    try:
        workspace = os.environ["WORKSPACE"]
    except KeyError:
        logger.error("Please set the environment variable WORKSPACE")
        sys.exit(1)

    if not os.listdir(workspace):
        logger.error("Workspace seems to be empty. Please clone the git repository correctly.")
        sys.exit(1)

    SimulationTestCases.WORKSPACE = workspace
    SimulationTestCases.RUN_SIM_SCRIPT = os.path.dirname(os.path.realpath(__file__)) + "/run_sim.sh"

    unittest.main(
        testRunner=xmlrunner.XMLTestRunner(output='test-reports'),
        # these make sure that some options that are not applicable
        # remain hidden from the help menu.
        failfast=False, buffer=False, catchbreak=False)
