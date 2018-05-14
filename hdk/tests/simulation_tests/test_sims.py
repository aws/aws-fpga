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
    '''
    Pytest test class.
    
    NOTE: Cannot have an __init__ method.
    '''

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)

        AwsFpgaTestBase.assert_hdk_setup()

        cls.RUN_SIM_SCRIPT = dirname(realpath(__file__)) + "/run_sim.sh"
        assert os.path.exists(cls.RUN_SIM_SCRIPT)
        return

    def run_sim(self, test_dir="", test_name="", test_type=""):

        # Error on defaults
        if not(test_dir and test_name and test_type):
            self.fail("Please enter non empty test_dir, test_name and test_type when calling run_sim")

        command_line = [self.RUN_SIM_SCRIPT, '--test-name', test_name, '--test-dir', test_dir, '--test-type', test_type]

        (rc, stdout_lines, stderr_lines) = self.run_cmd(" ".join(command_line))
        assert rc == 0, "Sim failed"

    # cl_dram_dma sv

    def test_cl_dram_dma__dram_dma__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)
    
    def test_cl_dram_dma__dram_dma_axi_mstr__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_axi_mstr'
        test_type = 'sv'
        
        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dram_dma_rnd__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_rnd'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dram_dma_4k_crossing__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_4k_crossing'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dram_dma_single_beat_4k__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_single_beat_4k'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dma_pcis_concurrent__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcis_concurrent'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dma_pcim_concurrent__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_pcim_concurrent'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dma_sda_concurrent__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dma_sda_concurrent'
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

    def test_cl_dram_dma__peek_poke_wc__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_wc'

    def test_cl_dram_dma__peek_poke_len__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_peek_poke_len'
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

    # cl_uram_example c

    def test_cl_uram_example__uram_example__c(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_uram_example/verif/scripts'
        test_name = 'test_uram_example'
        test_type = 'c'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)    
    
    # cl_dram_dma c

    def test_cl_dram_dma__sda__sv(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_sda'
        test_type = 'sv'

        self.run_sim(test_dir=test_dir, test_name=test_name, test_type=test_type)

    def test_cl_dram_dma__dram_dma_hwsw_cosim__c(self):

        test_dir = self.WORKSPACE + '/hdk/cl/examples/cl_dram_dma/verif/scripts'
        test_name = 'test_dram_dma_hwsw_cosim'
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
