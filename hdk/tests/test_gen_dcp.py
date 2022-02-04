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

Call using ```pytest test_gen_dcp.py```

See TESTING.md for details.
'''

from __future__ import print_function
import glob
import os
from os.path import basename, dirname, realpath
import pytest
import re
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


class TestGenDcp(AwsFpgaTestBase):
    '''
    Pytest test class.

    NOTE: Cannot have an __init__ method.

    Test all example CLs with different strategies and clock recipes.
    '''

    ADD_XILINX_VERSION = True

    @classmethod
    def setup_class(cls):
        '''
        Do any setup required for tests.
        '''
        AwsFpgaTestBase.setup_class(cls, __file__)
        AwsFpgaTestBase.assert_hdk_setup()

        cls.set_allowed_warnings()
        return

    @classmethod
    def set_allowed_warnings(cls):

        cls.allowed_warnings = (
            (('.*',), r'^WARNING: \[Constraints 18-838\] Failed to create SRL placer macro for cell SH/SH/MGT_TOP.*'),
            (('.*',), r'^WARNING: \[Shape Builder 18-838\] Failed to create SRL placer macro for cell WRAPPER_INST/SH/SH/MGT_TOP.*'),
            (('.*',), r'^WARNING: \[Common 17-576\] \'fanout_opt\' is deprecated.*'),
            (('.*',), r'^CRITICAL WARNING: \[Place 30-823\] Failed to process clock nets that should have matching clock routes\. Reason: Found incompatible user defined or fixed clock roots for related clocks \'CL/SH_DDR/ddr_cores\.DDR4'),
            (('.*',), r'^CRITICAL WARNING: \[Constraints 18-850\] Failed to place register with ASYNC_REG property shape that starts with register SH/SH/MGT_TOP/SH_ILA_0/inst/ila_core_inst/u_ila_reset_ctrl/asyncrounous_transfer\.arm_in_transfer_inst/dout_reg0_reg\. '),
            (('.*',), r'^CRITICAL WARNING: \[Constraints 18-850\] Failed to place register with ASYNC_REG property shape that starts with register SH/SH/MGT_TOP/SH_ILA_0/inst/ila_core_inst/capture_qual_ctrl_2_reg\[0\]\. '),
            (('.*',), r'^CRITICAL WARNING: \[Constraints 18-850\] Failed to place register with ASYNC_REG property shape that starts with register SH/SH/MGT_TOP/SH_ILA_0/inst/ila_core_inst/en_adv_trigger_2_reg\. '),
            (('.*',), r'^CRITICAL WARNING: \[Shape Builder 18-850\] Failed to place register with ASYNC_REG property shape that starts with register WRAPPER_INST/SH/SH/MGT_TOP.*'),
            (('.*',), r'^CRITICAL WARNING: \[Vivado 12-1433\] Expecting a non-empty list of cells to be added to the pblock\.  Please verify the correctness of the <cells> argument. \[/home/centos/src/project_data/workspace/test_develop_manual/hdk/cl/examples/cl_dram_dma/build/constraints/cl_pnr_user\.xdc:15'),
            (('.*',), r'^CRITICAL WARNING: \[filemgmt 20-1741\] File \'axi_register_slice_v2_1_vl_rfs.v\'.*'),
            (('.*',), r'^CRITICAL WARNING: \[filemgmt 20-1741\] File \'blk_mem_gen_v8_3_vhsyn_rfs.vhd\'.*'),
            (('.*',), r'^CRITICAL WARNING: \[filemgmt 20-1741\] File \'fifo_generator_v13_1_vhsyn_rfs.vhd\'.*'),
            (('.*',), r'^CRITICAL WARNING: \[Opt 31-430\].*'),
            (('.*',), r'WARNING: \[Vivado 12-3731\].*'),
            (('.*',), r'WARNING: \[Constraints 18-619\] A clock with name \'CLK_300M_DIMM._DP\'.*'),
            (('.*',), r'WARNING: \[Constraints 18-5648\] .*'),
            (('.*',), r'WARNING: \[Constraints 18-4434\] Global Clock Buffer \'static_sh.*'),
            (('.*',), r'WARNING: \[Vivado_Tcl 4-391\] The following IPs are missing output products for Implementation target. These output products could be required for synthesis, please generate the output products using the generate_target or synth_ip command before running synth_design.*'),
            (('.*',), r'WARNING: \[DRC RPBF-3\] IO port buffering.*'),
            (('.*',), r'WARNING: \[Place 46-14\] The placer has determined that this design is highly congested and may have difficulty routing. Run report_design_analysis -congestion for a detailed report\.'),
            (('.*',), r'WARNING: \[BD 41-1661\] .*'),
            (('.*',), r'WARNING: \[Vivado 12-584\] No ports matched \'tck\''),
            (('.*',), r'WARNING: \[Vivado 12-830\] No fanout objects found for'),
            (('.*',), r'WARNING: \[Place 30-640\] Place Check.*'),
            (('.*',), r'WARNING: \[BD 41-2180\] Resetting the memory initialization file.*'),
            (('.*',), r'WARNING: \[Synth 8-689\] .*'),
            (('.*',), r'WARNING: \[Synth 8-6896\] .*'),
            (('.*',), r'WARNING: \[Synth 8-7023\] .*'),
            (('.*',), r'CRITICAL WARNING: \[DRC HDPR-113\] Check for INOUT ports in RP: Reconfigurable module WRAPPER_INST/SH contains an INOUT port named .*'),
            (('.*',), r'WARNING: \[Synth 8-7071\] .*'),
            (('.*',), r'WARNING: \[Synth 8-7129\] .*'),
            (('.*',), r'WARNING: \[Route 35-3387\] .*'),
            (('.*',), r'WARNING: \[Synth 8-6779\] .*'),
            (('.*',), r'WARNING: \[Synth 8-7080\] .*'),
            (('cl_sde_*',), r'WARNING: \[Vivado 12-180\] No cells matched .*'),
            (('cl_sde_*',), r'WARNING: \[Vivado 12-1008\] No clocks found for command.*'),
            (('cl_sde_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] .*'),
            (('cl_sde_*',), r'^CRITICAL WARNING: \[Constraints 18-952\] .*'),
            (('cl_sde_*',), r'^CRITICAL WARNING: \[Vivado 12-1039\] .*'),
            (('cl_sde_*',), r'^CRITICAL WARNING: \[Vivado 12-1433\] .*'),
            (('cl_sde.*',), r'WARNING: \[Synth 8-6057\] Memory.*'),
            (('cl_dram_dma_A1_B2_C0_2_(CONGESTION|BASIC)',), r'^CRITICAL WARNING: \[Route 35-39\] The design did not meet timing requirements'),
            (('cl_dram_dma_A1_B2_C0_2_(CONGESTION|TIMING)',), r'WARNING: \[Vivado 12-180\] No cells matched \'CL/CL_DMA_PCIS_SLV/CL_TST_DDR_B/CL_TST/sync_rst_n_reg\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_microblaze_I_0\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_rst_0_0\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_ilmb_0\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_dlmb_0\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_iomodule_0_0\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ddr4_core_microblaze_mcs\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ddr4_core\''),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'axi_clock_converter_0\''),
            (('cl_dram_dma_*',), r'WARNING: \[Synth 8-6104\] Input port \'size\' has an internal driver .*'),
            (('cl_dram_dma_*',), r'WARNING: \[Synth 8-6104\] Input port \'value\' has an internal driver .*'),
            (('cl_dram_dma_*',), r'WARNING: \[Vivado 12-180\] No cells matched .*'),
            (('cl_dram_dma_*',), r'WARNING: \[Vivado 12-1008\] No clocks found for command.*'),
            (('.*',), r'WARNING: \[Memdata 28-146\] Could not find a netlist instance for the specified SCOPED_TO_REF value of: ddr4_core'),
            (('.*',), r'WARNING: \[Memdata 28-146\] Could not find a netlist instance for the specified SCOPED_TO_REF value of: bd_bf3f'),
            (('cl_dram_dma_*',), r'WARNING: \[Place 46-14\] The placer has determined'),
            (('cl_dram_dma_*',), r'WARNING: \[Synth 8-5856\]*'),
            (('cl_dram_dma_*',), r'WARNING: \[Physopt 32-894\].*'),
            (('cl_dram_dma_*',), r'CRITICAL WARNING: \[Vivado 12-1433\] Expecting a non-empty list of cells to be added to the pblock.*'),
            (('cl_hello_world_vhdl_A.*',), r'WARNING: \[Memdata 28-146\] Could not find a netlist instance for the specified SCOPED_TO_REF value of: ddr4_core'),
            (('cl_hello_world_vhdl_A.*',), r'WARNING: \[Memdata 28-146\] Could not find a netlist instance for the specified SCOPED_TO_REF value of: bd_bf3f'),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_microblaze_I_0\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_rst_0_0\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_ilmb_0\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_dlmb_0\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'bd_bf3f_iomodule_0_0\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ddr4_core_microblaze_mcs\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ddr4_core\''),
            (('cl_hello_world_vhdl_A.*',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'axi_clock_converter_0\''),
            (('cl_uram_example_A._B._C._[2-4]',), r'WARNING: \[Designutils 20-262\] Invalid BRAM Mode CASC\. Setting it to the default mode RAMB18\.'),
            (('cl_uram_example.*',), r'WARNING: \[xilinx\.com:ip:blk_mem_gen:8\.[3-4]-1\] /blk_mem_gen_\d Block Memory Generator IP is configured to use UltraRAM, but UltraRAM does not support Memory Initialization.*'),
            (('cl_uram_example_A._B._C._[2-4]',), r'WARNING: \[Synth 8-2507\] parameter declaration becomes local in flop_ccf with formal parameter declaration list'),
            (('cl_uram_example_A._B._C._[2-4]',), r'WARNING: \[Synth 8-5790\] Small sized RAM gen_wr_a\.gen_word_narrow\.mem_reg will be implemented using URAM because of explicit ram_style = \"ultra\" attribute'),
            (('cl_uram_example.*',), r'WARNING: \[Synth 8-6057\] Memory.*'),
            (('cl_uram_example.*',), r'WARNING: \[Vivado 12-180\] No cells matched .*'),
            (('cl_uram_example_A._B._C._[2-4]',), r'WARNING: \[Vivado 12-180\] No cells matched \'CL/vled_q_reg\*\'\.'),
            (('cl_uram_example_A._B._C._[2-4]',), r'WARNING: \[Vivado 12-1421\] No ChipScope debug cores matched \'\''),
            (('cl_uram_example_A._B._C._[2-4]',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ila_0\''),
            (('cl_uram_example_A._B._C._[2-4]',), r'CRITICAL WARNING: \[Designutils 20-1280\] Could not find module \'ila_vio_counter\''),
            (('cl_uram_example_A._B._C._[2-4]',), r'CRITICAL WARNING: \[Designutils 20-1281\] Could not find module \'vio_0\''),
        )

        cls.allowed_warnings_regexps = []
        for allowed_warning_spec in cls.allowed_warnings:
            option_tag_regexps = []
            for option_tag in allowed_warning_spec[0]:
                option_tag_regexps.append(re.compile(option_tag))
            cls.allowed_warnings_regexps.append((option_tag_regexps, re.compile(allowed_warning_spec[1])))

        cls.allowed_timing_violations = [
            re.compile(r'cl_dram_dma_A1_B2_C0_2_(CONGESTION|BASIC)'),
        ]

    def filter_warnings(self, cl, option_tag, warnings):
        option_tag = cl + "_" + option_tag
        # Get reg_exps that match the option tag
        filters = []
        for allowed_warnings_regexp_spec in self.allowed_warnings_regexps:
            for option_tag_regexp in allowed_warnings_regexp_spec[0]:
                if option_tag_regexp.match(option_tag):
                    filters.append(allowed_warnings_regexp_spec[1])
        if len(filters) == 0:
            return warnings
        filtered_warnings = []
        for warning in warnings:
            matched = False
            for filter in filters:
                if filter.match(warning):
                    matched = True
                    break
            if not matched:
                filtered_warnings.append(warning)
        return filtered_warnings

    def allow_timing_violations(self, cl, option_tag):
        option_tag = cl + "_" + option_tag
        for reg_exp in self.allowed_timing_violations:
            if reg_exp.match(option_tag):
                return True
        return False

    def assert_non_zero_file(self, filter):
        filenames = glob.glob(filter)
        assert len(filenames) > 0, "No {} file found in {}".format(filter, os.getcwd())
        assert len(filenames) == 1, "More than 1 {} file found: {}\n{}".format(filter, len(filenames),
                                                                               "\n".join(filenames))
        filename = filenames[0]
        assert os.stat(filename).st_size != 0, "{} is 0 size".format(filename)
        return filename

    def check_build(self, cl, clock_recipes, option_tag):
        cl_dir = self.get_cl_dir(cl)
        checkpoints_dir = os.path.join(cl_dir, 'build/checkpoints')
        to_aws_dir = self.get_cl_to_aws_dir(cl)
        scripts_dir = self.get_cl_scripts_dir(cl)
        reports_dir = os.path.join(cl_dir, 'build/reports')

        assert os.path.exists(to_aws_dir), "The checkpoints/to_aws directory does not exist: {}".format(to_aws_dir)

        logger.info("Checking that a non zero size ltx file exists in {}".format(checkpoints_dir))

        ltx_file = self.assert_non_zero_file(os.path.join(checkpoints_dir, '*.ltx'))
        logger.info("ltx file: {}".format(ltx_file))

        logger.info("Checking that a non zero size manifest file exists in {}".format(to_aws_dir))
        manifest_file = self.assert_non_zero_file(os.path.join(to_aws_dir, '*.manifest.txt'))
        logger.info("manifest file: {}".format(manifest_file))

        logger.info("Checking that a non zero size dcp file exists in {}".format(to_aws_dir))
        dcp = self.assert_non_zero_file(os.path.join(to_aws_dir, '*.dcp'))
        logger.info("dcp: {}".format(dcp))

        logger.info("Checking that a non zero size tar file exists in {}".format(to_aws_dir))
        tarball = self.assert_non_zero_file(os.path.join(to_aws_dir, '*.tar'))
        logger.info("tarball: {}".format(tarball))

        logger.info("Checking that a dcp exists in the tar file")
        (rc, stdout_lines, stderr_lines) = self.run_cmd("/usr/bin/tar tvf {} \'*.dcp\'".format(tarball))
        assert rc == 0, "Did not find dcp in {}".format(tarball)

        logger.info("Checking that a manifest exists in the tar file")
        (rc, stdout_lines, stderr_lines) = self.run_cmd("/usr/bin/tar tvf {} \'*.manifest.txt\'".format(tarball))
        assert rc == 0, "Did not find manifest in {}".format(tarball)

        # Use last_log symlink to grab logname
        logger.debug("Looking for last_log in {}".format(scripts_dir))

        assert os.path.exists("last_log"), "Could not find the log file: {}/last_log".format(scripts_dir)

        # Check the number of warnings
        (rc, stdout_lines, stderr_lines) = self.run_cmd("grep \"^WARNING\" last_log", check=False)
        if rc == 0:
            warnings = stdout_lines[:-1]  # Last line is a blank line
        else:
            warnings = []
        num_warnings = len(warnings)
        logger.info("Saw {} warnings in log file".format(num_warnings))
        filtered_warnings = self.filter_warnings(cl, option_tag, warnings)
        num_warnings = len(filtered_warnings)
        logger.info("Saw {} filtered warnings in log file:\n{}".format(num_warnings, "\n".join(filtered_warnings)))
        # Check the number of critical warnings
        (rc, stdout_lines, stderr_lines) = self.run_cmd("grep \"^CRITICAL WARNING\" last_log", check=False)
        if rc == 0:
            critical_warnings = stdout_lines[:-1]  # Last line is a blank line
        else:
            critical_warnings = []
        num_critical_warnings = len(critical_warnings)
        logger.info("Saw {} critical warnings in log file".format(num_critical_warnings))
        filtered_critical_warnings = self.filter_warnings(cl, option_tag, critical_warnings)
        num_critical_warnings = len(filtered_critical_warnings)
        logger.info("Saw {} filtered critical warnings in log file:\n{}".format(num_critical_warnings,
                                                                                "\n".join(filtered_critical_warnings)))

        assert not (num_warnings or num_critical_warnings), "Unexpected warnings"
        # Check if there are any setup/hold-time violations
        (rc, stdout_lines, stderr_lines) = self.run_cmd(
            "grep \"The design did not meet timing requirements.\" last_log", check=False)
        if rc == 0:
            NUM_TIMING_VIOLATIONS = len(stdout_lines) - 1
        else:
            NUM_TIMING_VIOLATIONS = 0
        logger.info("{} timing violations".format(NUM_TIMING_VIOLATIONS))
        if self.allow_timing_violations(cl, option_tag):
            logger.info("Timing violations ignored for this configuration")
            NUM_TIMING_VIOLATIONS = 0
        assert NUM_TIMING_VIOLATIONS == 0, "{} timing violations found.  Design may not be functional:\n{}".format(
            NUM_TIMING_VIOLATIONS, "\n".join(stdout_lines))

        # Check clock recipes
        timing_report = self.assert_non_zero_file(os.path.join(reports_dir, '*.SH_CL_final_timing_summary.rpt'))
        logger.info("Checking clock frequencies in {}".format(timing_report))
        for clock_group in sorted(clock_recipes):
            recipe = clock_recipes[clock_group]
            for clock_name in self.DCP_CLOCK_RECIPES[clock_group]['clock_names']:
                (rc, stdout_lines, stderr_lines) = self.run_cmd("grep -m 1 {} {}".format(clock_name, timing_report))
                assert rc == 0, "Couldn't find {} in {}".format(clock_name, timing_report)
                fields = stdout_lines[0].split()
                act_freq = float(fields[4])
                exp_freq = float(self.DCP_CLOCK_RECIPES[clock_group]['recipes'][recipe][clock_name])
                assert act_freq == exp_freq, "{} frequency miscompare: act={} exp={}\n{}".format(clock_name, act_freq,
                                                                                                 exp_freq,
                                                                                                 stdout_lines[0])
                logger.info("{} : {}".format(clock_name, act_freq))

        return tarball

    def base_test(self, cl, xilinxVersion, build_strategy='DEFAULT', clock_recipe_a='A0', clock_recipe_b='B0',
                  clock_recipe_c='C0', uram_option='2'):
        assert build_strategy in self.DCP_BUILD_STRATEGIES
        assert clock_recipe_a in self.DCP_CLOCK_RECIPES['A']['recipes']
        assert clock_recipe_b in self.DCP_CLOCK_RECIPES['B']['recipes']
        assert clock_recipe_c in self.DCP_CLOCK_RECIPES['C']['recipes']
        assert uram_option in self.DCP_URAM_OPTIONS
        cl_dir = self.get_cl_dir(cl)
        logger.info("Setting CL_DIR={}".format(cl_dir))
        os.environ['CL_DIR'] = cl_dir
        assert os.path.exists(cl_dir), logger.error("CL_DIR={} does not exist".format(cl_dir))

        # Clean up all previous DCP generations
        cl_dir = self.get_cl_dir(cl)
        checkpoints_dir = os.path.join(cl_dir, 'build/checkpoints')
        to_aws_dir = self.get_cl_to_aws_dir(cl)
        scripts_dir = self.get_cl_scripts_dir(cl)
        reports_dir = os.path.join(cl_dir, 'build/reports')
        os.system("rm -rf {}/*".format(to_aws_dir))
        os.system("rm -f {}/*".format(checkpoints_dir))
        os.system("rm -rf {}/*".format(reports_dir))
        os.system("rm -f {}/*.log".format(scripts_dir))

        logger.info("Scripts dir is {}".format(scripts_dir))
        cwd = os.getcwd()
        os.chdir(scripts_dir)

        option_tag = "{}_{}_{}_{}_{}".format(clock_recipe_a, clock_recipe_b, clock_recipe_c, uram_option,
                                             build_strategy)
        (rc, stdout_lines, stderr_lines) = self.run_cmd(
            "./aws_build_dcp_from_cl.sh -foreground -strategy {} -clock_recipe_a {} -clock_recipe_b {} -clock_recipe_c {} -uram_option {}".format(
                build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c, uram_option))
        assert rc == 0, "DCP build failed."
        logger.info("DCP Generation Finished")

        tarball = self.check_build(cl, {'A': clock_recipe_a, 'B': clock_recipe_b, 'C': clock_recipe_c}, option_tag)

        # Upload the DCP tarball to S3.
        dcp_key = os.path.join(self.get_cl_s3_dcp_tag(cl, option_tag, xilinxVersion), basename(tarball))
        self.s3_client().upload_file(tarball, self.s3_bucket, dcp_key)

        return

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_dram_dma(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_dram_dma'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_hello_world(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_hello_world'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)

    def test_cl_hello_world_vhdl(self, xilinxVersion):
        cl = 'cl_hello_world_vhdl'
        self.base_test(cl, xilinxVersion)

    @pytest.mark.parametrize("uram_option", AwsFpgaTestBase.DCP_URAM_OPTIONS)
    def test_cl_uram_example(self, xilinxVersion, uram_option):
        cl = 'cl_uram_example'
        logger.info("uram_option={}".format(uram_option))
        self.base_test(cl, xilinxVersion, clock_recipe_a='A0', uram_option=uram_option)

    @pytest.mark.parametrize("build_strategy", AwsFpgaTestBase.DCP_BUILD_STRATEGIES)
    @pytest.mark.parametrize("clock_recipe_c", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['C']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_b", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['B']['recipes'].keys()))
    @pytest.mark.parametrize("clock_recipe_a", sorted(AwsFpgaTestBase.DCP_CLOCK_RECIPES['A']['recipes'].keys()))
    def test_cl_sde(self, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c):
        cl = 'cl_sde'
        self.base_test(cl, xilinxVersion, build_strategy, clock_recipe_a, clock_recipe_b, clock_recipe_c)
