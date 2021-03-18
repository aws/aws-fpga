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

from __future__ import print_function
import logging
import os
from os.path import dirname, realpath
import pytest
import subprocess
import sys
import traceback
import re
try:
    import aws_fpga_utils
    import aws_fpga_test_utils
    from aws_fpga_test_utils.AwsFpgaTestBase import AwsFpgaTestBase
except ImportError as e:
    traceback.print_tb(sys.exc_info()[2])
    print("error: {}\nMake sure to source hdk_setup.sh".format(sys.exc_info()[1]))
    sys.exit(1)

logger = aws_fpga_utils.get_logger(__name__)


class TestSims(AwsFpgaTestBase):
    """
    Pytest test class.

    NOTE: Cannot have an __init__ method.
    """

    ADD_SIMULATOR = True
    ADD_BATCH = True

    @classmethod
    def setup_class(cls):
        """
        Do any setup required for tests.
        """
        AwsFpgaTestBase.setup_class(cls, __file__)

        AwsFpgaTestBase.assert_hdk_setup()

        cls.RUN_SIM_SCRIPT = dirname(realpath(__file__)) + "/run_sim.sh"
        assert os.path.exists(cls.RUN_SIM_SCRIPT)

        cls.set_simulation_error_signatures()
        cls.set_simulation_pass_signatures()

        return

    @classmethod
    def set_simulation_error_signatures(cls):
        """
        Adding compiled errors
        """

        cls.failure_messages = [
            r'.*\*{0,3}\s*ERROR\s*\*{0,3}',
            r'.*\*{0,3}\s*TEST[\s_-]{0,2}FAILED\s*\*{0,3}.*',
            r'.*Detected\s*[1-9]\d*\s*error[s]?.*'
        ]
        cls.compiled_failure_messages = []

        for failure_message in cls.failure_messages:
            cls.compiled_failure_messages.append(re.compile(failure_message))

    @classmethod
    def set_simulation_pass_signatures(cls):
        """
        Adding compiled pass signatures
        """

        cls.pass_messages = [
            r'.*[\*\!]{0,3}\s*TEST[\s_-]{0,2}PASSED\s*[\*\!]{0,3}.*',
        ]
        cls.compiled_pass_messages = []

        for pass_message in cls.pass_messages:
            cls.compiled_pass_messages.append(re.compile(pass_message))

    @classmethod
    def parse_simulation_output(cls, test_name, test_type, test_stdout, test_stderr):
        """
        Parse stdout and stderr and see if the test had any fail signatures
        Also check if Test Passed. a no Test passed signature is
        """

        failure_messages = []
        pass_messages = []

        # Check failures
        for stdout_line in test_stdout:
            for fail_regex in cls.compiled_failure_messages:
                if fail_regex.match(stdout_line):
                    failure_messages.append(stdout_line)

        # Check passes
        for stdout_line in test_stdout:
            for pass_regex in cls.compiled_pass_messages:
                if pass_regex.match(stdout_line):
                    pass_messages.append(stdout_line)

        return_dict = {
            "passes": pass_messages,
            "fails": failure_messages
        }

        return return_dict

    def run_sim(self, test_dir="", test_name="", test_type="", simulator="", batch=""):

        vivado_version = os.environ.get('VIVADO_TOOL_VERSION', 'unknown')

        # Error on defaults
        if not(test_dir and test_name and test_type):
            self.fail("Please enter non empty test_dir, test_name and test_type when calling run_sim")

        command_line = [self.RUN_SIM_SCRIPT,
                        '--test-name', test_name,
                        '--test-dir', test_dir,
                        '--test-type', test_type,
                        '--simulator', simulator,
                        '--batch', batch,
                        '--vivado-version', vivado_version
                        ]

        (rc, stdout_lines, stderr_lines) = self.run_cmd(" ".join(command_line))


        # write simulation output
        if simulator == "vivado":
            simulator_version = "{}_{}".format(simulator, vivado_version)
        else:
            simulator_version = simulator

        stdout_file_name = "{}/{}_{}_{}.stdout.sim.log".format(test_dir, test_name, test_type, simulator_version)
        with open(stdout_file_name, 'w') as f:
            for item in stdout_lines:
                f.write("%s\n" % item)

        # Only write if there is something to write
        if stderr_lines:
            stderr_file_name = "{}/{}_{}_{}.stderr.sim.log".format(test_dir, test_name, test_type, simulator_version)
            with open(stderr_file_name, 'w') as f:
                for item in stderr_lines:
                    f.write("%s\n" % item)

        # Check exit code
        assert rc == 0, "Sim failed. Received Non-Zero return code"

        return_dict = self.parse_simulation_output(test_name=test_name,
                                                   test_type=test_type,
                                                   test_stdout=stdout_lines,
                                                   test_stderr=stderr_lines)

        # Check for fail signatures
        assert [] == return_dict["fails"], "Found failures {}".format(return_dict["fails"])

        # Check for pass signatures. We need at least one to make the test as a pass
        assert [] != return_dict["passes"], "Found no matching pass statements"

    # cl_dram_dma sv

    def test_cl_dram_dma__dram_dma__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_axi_mstr__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_axi_mstr'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_rnd__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_rnd'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_rnd__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_rnd'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_rnd__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_rnd'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_rnd__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_rnd'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_4k_crossing__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_4k_crossing'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_single_beat_4k__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_single_beat_4k'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_single_beat_4k__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_single_beat_4k'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_single_beat_4k__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_single_beat_4k'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_single_beat_4k__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_single_beat_4k'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcis_concurrent__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcis_concurrent'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcis_concurrent__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcis_concurrent'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcis_concurrent__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcis_concurrent'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcis_concurrent__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcis_concurrent'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__host_pcim__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_host_pcim'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcim_concurrent__sv(self, simulator, batch):
        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcim_concurrent'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcim_concurrent__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcim_concurrent'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)
    def test_cl_dram_dma__dma_pcim_concurrent__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcim_concurrent'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_pcim_concurrent__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcim_concurrent'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_sda_concurrent__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_sda_concurrent'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_sda_concurrent__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_sda_concurrent'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dma_sda_concurrent__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_sda_concurrent'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)
    def test_cl_dram_dma__dma_sda_concurrent__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_sda_concurrent'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__ddr__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__clk_recipe__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_clk_recipe'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__int__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_int'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_wc__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_wc'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_wc__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_wc'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_wc__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_wc'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_wc__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_wc'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_len__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_len'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_len__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_len'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_len__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_len'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_len__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_len'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_pcis_axsize__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_pcis_axsize'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_pcis_axsize__sv_fast(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_pcis_axsize'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_pcis_axsize__sv_fast_ecc_direct(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_pcis_axsize'
        test_type = 'sv_fast_ecc_direct'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__peek_poke_pcis_axsize__sv_fast_ecc_rnd(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_pcis_axsize'
        test_type = 'sv_fast_ecc_rnd'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__ddr_peek_poke__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr_peek_poke'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__ddr_peek_bdr_walking_ones__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr_peek_bdr_walking_ones'
        test_type = 'sv_ddr_bkdr'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_dram_bdr_row_col_combo__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_dram_bdr_row_col_combo'
        test_type = 'sv_ddr_bkdr'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_mem_model_bdr_wr__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_mem_model_bdr_wr'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_mem_model_bdr_rd__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_mem_model_bdr_rd'
        test_type = 'sv_fast'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__axi_mstr_multi_rw__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_axi_mstr_multi_rw'
        test_type = 'sv'

    def test_cl_dram_dma__bar1__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_bar1'
        test_type = 'sv'

    def test_cl_dram_dma__dram_dma_allgn_addr_4k__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_allgn_addr_4k'
        test_type = 'sv'

    def test_ddr_peek_bdr_walking_ones__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_ddr_peek_bdr_walking_ones'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_uram_example c

    def test_cl_uram_example__uram_example__c(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_uram_example/verif/scripts'
        test_name = 'test_uram_example'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_dram_dma c

    def test_cl_dram_dma__sda__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_sda'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    def test_cl_dram_dma__dram_dma_hwsw_cosim__c(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_hwsw_cosim'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_hello_world sv

    def test_cl_hello_world__hello_world__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_test_gl_cntr sv

    def test_cl_hello_world__gl_cntr__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_gl_cntr'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_hello_world vhdl

    def test_cl_vhdl_hello_world__hello_world__vhdl(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world_vhdl/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'vhdl'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_hello_world c

    def test_cl_hello_world__hello_world__c(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_hello_world/verif/scripts'
        test_name = 'test_hello_world'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_sde_c2h sv

    def test_cl_sde__test_simple_c2h__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_sde/verif/scripts'
        test_name = 'test_simple_c2h'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)

    # cl_sde_h2c sv

    def test_cl_sde__test_simple_h2c__sv(self, simulator, batch):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_sde/verif/scripts'
        test_name = 'test_simple_h2c'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type, simulator=simulator, batch=batch)
