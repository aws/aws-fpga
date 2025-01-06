CL_MEM_PERF Example Simulation
==============================

Table of Contents
-----------------

- `CL_MEM_PERF Example Simulation <#cl_mem_perf-example-simulation>`__

  - `Table of Contents <#table-of-contents>`__
  - `Overview <#overview>`__
  - `Dump Waves <#dump-waves>`__
  - `System Verilog Tests <#system-verliog-tests>`__

    - `test_aws_clk_gen_recipe.sv (VCS and QUESTA only) <#test_aws_clk_gen_recipesv-vcs-and-questa-only-mem>`__
    - `test_clk_recipe.sv <#test_clk_recipesv-mem>`__
    - `test_ddr_peek_poke.sv <#test_ddr_peek_pokesv-mem>`__
    - `test_ddr.sv <#test_ddrsv-mem>`__
    - `test_hbm.sv <#test_hbmsv-mem>`__
    - `test_hbm_perf32.sv <#test_hbm_perf32sv-mem>`__
    - `test_hbm_perf_kernel_cfg.sv <#test_hbm_perf_kernel_cfgsv-mem>`__
    - `test_hbm_perf_random.sv <#test_hbm_perf_randomsv-mem>`__
    - `test_dram_dma.sv <#test_dram_dmasv-mem>`__
    - `test_dram_dma_rnd.sv <#test_dram_dma_rndsv-mem>`__
    - `test_dma_pcim_concurrent.sv <#test_dma_pcim_concurrentsv-mem>`__
    - `test_dma_pcis_concurrent.sv <#test_dma_pcis_concurrentsv-mem>`__
    - `test_dma_sda_concurrent.sv <#test_dma_sda_concurrentsv-mem>`__
    - `test_dram_dma_4k_crossing.sv <#test_dram_dma_4k_crossingsv-mem>`__
    - `test_dram_dma_allgn_addr_4k.sv <#test_dram_dma_allgn_addr_4ksv-mem>`__
    - `test_dram_dma_single_beat_4k.sv <#test_dram_dma_single_beat_4ksv-mem>`__
    - `test_dram_dma_axi_mstr.sv <#test_dram_dma_axi_mstrsv-mem>`__
    - `test_int.sv <#test_intsv-mem>`__
    - `test_peek_poke.sv <#test_peek_pokesv-mem>`__
    - `test_peek_poke_wc.sv <#test_peek_poke_wcsv-mem>`__
    - `test_peek_poke_len.sv <#test_peek_poke_lensv-mem>`__
    - `test_peek_poke_rnd_lengths.sv <#test_peek_poke_rnd_lengthssv-mem>`__
    - `test_peek_poke_pcis_axsize.sv <#test_peek_poke_pcis_axsizesv-mem>`__
    - `test_ddr_peek_bdr_walking_ones <#test_ddr_peek_bdr_walking_ones-mem>`__
    - `test_sda.sv <#test_sdasv-mem>`__
    - `test_null.sv <#test_nullsv-mem>`__

  - `AXI_MEMORY_MODEL Mode
    Simulations <#axi_memory_model-mode-simulations>`__

    - `test_dram_dma_mem_model_bdr_wr <#test_dram_dma_mem_model_bdr_wr>`__
    - `test_dram_dma_mem_model_bdr_rd <#test_dram_dma_mem_model_bdr_rd>`__

  - `DDR Backdoor Loading <#ddr-backdoor-loading>`__

  - `HW/SW Co-Simulation Test <#hwsw-co-simulation-test>`__

Overview
--------

This readme provides information about the simulation environment for
the ``cl_mem_perf`` example. For more details about overall HDK
simulation environment and CL bringup in simulation please refer to `RTL
Simulation Guide for HDK Design
Flow <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html>`__.

The SystemVerilog (SV) simulation can be run from the
``$CL_DIR/verif/scripts/`` directory with all supported simulators (HBM
simulation using VCS & QUESTA is strongly recommended). You can run
tests by calling the make target for that test located in
``$CL_DIR/verif/scripts/Makefile.tests``:

.. code:: bash

   make test_ddr # Runs with XSIM by default
   make test_ddr VCS=1
   make test_ddr QUESTA=1

   make test_hbm # Runs with VCS by default

Alternatively, you can run each test by setting ``TEST=\<Test Name\>``
followed by the environment variables required to run that test.

.. code:: bash

   make TEST=test_dram_dma # Runs with XSIM by default
   make TEST=test_dram_dma VCS=1
   make TEST=test_dram_dma QUESTA=1

   # To Run simulations with a 64 GB DDR DIMM # With user-controlled auto-precharge mode
   make TEST=test_dram_dma USE_AP_64GB_DDR_DIMM=1

   # To Run Simulations in AXI_MEMORY_MODEL mode
   make TEST=test_dram_dma AXI_MEMORY_MODEL=1 # Runs with XSIM by default in AXI_MEMORY_MODEL mode
   make TEST=test_dram_dma AXI_MEMORY_MODEL=1 VCS=1
   make TEST=test_dram_dma AXI_MEMORY_MODEL=1 QUESTA=1

   # To Run DDR backdoor loading tests
   make TEST=test_ddr_peek_bdr_walking_ones # Runs with XSIM by default
   make TEST=test_ddr_peek_bdr_walking_ones VCS=1
   make TEST=test_ddr_peek_bdr_walking_ones QUESTA=1

   # Backdoor loading test list. Description can be found in the sections below.
   test_dram_dma_mem_model_bdr_rd
   test_dram_dma_mem_model_bdr_wr
   test_ddr_peek_bdr_walking_ones

**NOTE**: Please refer to
`Supported_DDR_Modes <./../../../../docs/Supported_DDR_Modes.html>`__
for details on supported DDR configurations.

The HW/SW co-simulation tests can be run from the ``verif/scripts/``
directory with all supported simulators:

.. code:: bash

   make C_TEST=test_dram_dma_hwsw_cosim # Runs with XSIM by default
   make C_TEST=test_dram_dma_hwsw_cosim VCS=1
   make C_TEST=test_dram_dma_hwsw_cosim QUESTA=1

   # To Run in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR.
   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 (Runs with XSIM by default)
   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 VCS=1
   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 QUESTA=1

Note that the appropriate simulators must be installed.

Dump Waves
----------

For information about how to dump waves with XSIM or VCS, please refer
to
`debugging-custom-logic-using-the-aws-hdk <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html#debugging-custom-logic-using-the-aws-hdk>`__

System Verilog Tests
--------------------

The SystemVerilog tests are located at ``verif/tests/``. Most tests
include ``base_test_utils.svh`` which includes common signals and tasks
used across tests. Please refer to this file for the DPI-C tasks used.
Information about each test can be found below.

.. _test_aws_clk_gen_recipesv-vcs-and-questa-only-mem:

test_aws_clk_gen_recipe.sv (VCS and QUESTA only)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs valid clock recipes to the CL and verifies the
corresponding clock frequencies.

.. _test_clk_recipesv-mem:

test_clk_recipe.sv
~~~~~~~~~~~~~~~~~~

This test programs valid clock recipes defined within and verifies the
corresponding clock frequencies.

.. _test_ddr_peek_pokesv-mem:

test_ddr_peek_poke.sv
~~~~~~~~~~~~~~~~~~~~~

This does a walking ones test through the DDR address range. Also checks
if any of the bits are stuck at '0'.

.. _test_ddrsv-mem:

test_ddr.sv
~~~~~~~~~~~

This test programs the CL_TST (ATG) to generate traffic to access all
four DDR channels.

.. _test_hbmsv-mem:

test_hbm.sv
~~~~~~~~~~~

This test programs the CL_TST (ATG) to generate traffic to access both
HBM stacks.

.. _test_hbm_perf32sv-mem:

test_hbm_perf32.sv
~~~~~~~~~~~~~~~~~~

This test programs the HBM performance kernel to run all 32 channels for
maximum bandwidth. The kernel collects timer and bandwidth statistics
and stores them in registers. At the end of the test, the performance is
calculated and printed in the ``sim.log``.

.. _test_hbm_perf_kernel_cfgsv-mem:

test_hbm_perf_kernel_cfg.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test exercises each register in the HBM performance kernel
configuration space.

.. _test_hbm_perf_randomsv-mem:

test_hbm_perf_random.sv
~~~~~~~~~~~~~~~~~~~~~~~

This test executes the same flow as ``test_hbm_perf32.sv`` except with a
random axi length and a random number of channels.

.. _test_dram_dmasv-mem:

test_dram_dma.sv
~~~~~~~~~~~~~~~~

Basic H2C and C2H DMA test through all 4 DDR channels and 2 HBM stacks.

.. _test_dram_dma_rndsv-mem:

test_dram_dma_rnd.sv
~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers with random lengths.

.. _test_dma_pcim_concurrentsv-mem:

test_dma_pcim_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and PCIM traffic to run concurrently and
verifies that there are no errors on both DMA and PCIM interfaces.

.. _test_dma_pcis_concurrentsv-mem:

test_dma_pcis_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and PCIS traffic to run concurrently and
verifies that there are no errors on both DMA and PCIS interfaces.

.. _test_dma_sda_concurrentsv-mem:

test_dma_sda_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and SDA traffic to run concurrently and
verifies that there are no errors on both DMA and SDA interfaces.

.. _test_dram_dma_4k_crossingsv-mem:

test_dram_dma_4k_crossing.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers that will cross a 4k boundary. All
transfers are of same length with different destination addresses.

.. _test_dram_dma_allgn_addr_4ksv-mem:

test_dram_dma_allgn_addr_4k.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers that will cross a 4k boundary. All
transfers are of different length with different destination addresses.

.. _test_dram_dma_single_beat_4ksv-mem:

test_dram_dma_single_beat_4k.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs single beat DMA transfers that will cross a 4k
boundary.

.. _test_dram_dma_axi_mstrsv-mem:

test_dram_dma_axi_mstr.sv
~~~~~~~~~~~~~~~~~~~~~~~~~

This test configures the cl_dram_dma_axi_mstr.sv module to send and
receive traffic from the DDR in the CL design.

.. _test_intsv-mem:

test_int.sv
~~~~~~~~~~~

This test programs enables interrupts in CL and verifies them.

.. _test_peek_pokesv-mem:

test_peek_poke.sv
~~~~~~~~~~~~~~~~~

This test programs ATG in CL to do 128 byte PCIM reads and writes.

.. _test_peek_poke_wcsv-mem:

test_peek_poke_wc.sv
~~~~~~~~~~~~~~~~~~~~

This test performs pcis write combine operations and reads back the
data.

.. _test_peek_poke_lensv-mem:

test_peek_poke_len.sv
~~~~~~~~~~~~~~~~~~~~~

This test programs tester block to do PCIM reads and writes with
incremental lengths.

.. _test_peek_poke_rnd_lengthssv-mem:

test_peek_poke_rnd_lengths.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs tester block to do PCIM reads and writes with random
lengths within valid range.

.. _test_peek_poke_pcis_axsizesv-mem:

test_peek_poke_pcis_axsize.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test does PCIS peek and poke with different sizes. Although shell
model allows different size transfers on PCIS interface, Shell only
supports transfer of size 6 on PCIS interface.

test_ddr_peek_bdr_walking_ones
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

DDR test which uses backdoor loading to populate DDR memory. The test
writes data(walking ones) for different addresses. The test backdoor
loads DDR memory and reads through frontdoor and checks that the data
matches.

.. _test_sdasv-mem:

test_sda.sv
~~~~~~~~~~~

This test does transfers to different addresses on SDA AXIL interface.

.. _test_nullsv-mem:

test_null.sv
~~~~~~~~~~~~

test_null is not an actual test. This is a base SystemVerilog file
needed for HW/SW co-simulation


AXI_MEMORY_MODEL Mode Simulations
---------------------------------

AXI_MEMORY_MODEL mode can be used for better simulation performance.
AXI_MEMORY_MODEL mode enables a test to run with AXI memory models
instead of DDR memory. The documentation can be found in AXI memory
model section at `RTL simulation
guide <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html>`__.
Any test that accesses DDR memory can be run in AXI_MEMORY_MODEL mode.
Below are some example tests for ECC and backdoor loading support
features of AXI memory model.

test_dram_dma_mem_model_bdr_wr
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test backdoor writes AXI memory model, reads through frontdoor and
checks that the data matches.

test_dram_dma_mem_model_bdr_rd
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test backdoor reads AXI memory model, writes through frontdoor and
checks that the data matches.

DDR Backdoor Loading
--------------------

The description of DDR backdoor loading can be found in DDR backdoor loading
support section at `RTL simulation
guide <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html>`__

HW/SW Co-Simulation Test
------------------------

The software test with HW/SW co-simulation support
`test_dram_dma_hwsw_cosim.c <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf/software/runtime/test_dram_dma_hwsw_cosim.c>`__
can be found at ``software/runtime/``. For Information about how HW/SW
co-simulation support can be added to a software test please refer to
"Code changes to enable HW/SW co-simulation" section in `RTL simulation
guide <../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.html>`__
