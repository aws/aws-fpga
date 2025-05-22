CL_DRAM_HBM_DMA Example Simulation
==================================

Table of Contents
-----------------

  - `Overview <#overview>`__
  - `Dump Waves <#dump-waves-dma>`__
  - `SystemVerilog Tests <#system-verilog-tests>`__

    - `test_clk_recipe.sv <#test-clk-recipesv>`__
    - `test_ddr_peek_poke.sv <#test-ddr-peek-pokesv>`__
    - `test_ddr.sv <#test-ddrsv>`__
    - `test_hbm.sv <#test-hbmsv>`__
    - `test_dram_dma.sv <#test-dram-dmasv>`__
    - `test_dram_dma_rnd.sv <#test-dram-dma-rndsv>`__
    - `test_dma_pcim_concurrent.sv <#test-dma-pcim-concurrentsv>`__
    - `test_dma_pcis_concurrent.sv <#test-dma-pcis-concurrentsv>`__
    - `test_dma_sda_concurrent.sv <#test-dma-sda-concurrentsv>`__
    - `test_dram_dma_4k_crossing.sv <#test-dram-dma-4k-crossingsv>`__
    - `test_dram_dma_allgn_addr-4k.sv <#test-dram-dma-allgn-addr-4ksv>`__
    - `test_dram_dma_single_beat-4k.sv <#test-dram-dma-single-beat-4ksv>`__
    - `test_dram_dma_axi_mstr.sv <#test-dram-dma-axi-mstrsv>`__
    - `test_int.sv <#test-intsv>`__
    - `test_peek_poke.sv <#test-peek-pokesv>`__
    - `test_peek_poke_wc.sv <#test-peek-poke-wcsv>`__
    - `test_peek_poke_len.sv <#test-peek-poke-lensv>`__
    - `test_peek_poke_rnd_lengths.sv <#test-peek-poke-rnd-lengthssv>`__
    - `test_peek_poke_pcis_axsize.sv <#test-peek-poke-pcis-axsizesv>`__
    - `test_ddr_peek_bdr_walking_ones <#test-ddr-peek-bdr-walking-ones>`__
    - `test_sda.sv <#test-sdasv>`__
    - `test_null.sv <#test-nullsv>`__

  - `AXI-MEMORY-MODEL Mode Simulations <#axi-memory-model-mode-simulations-dma>`__

    - `test-dram-dma-mem-model-bdr-wr <#test-dram-dma-mem-model-bdr-wr-dma>`__
    - `test-dram-dma-mem-model-bdr-rd <#test-dram-dma-mem-model-bdr-rd-dma>`__

  - `DDR Backdoor Loading <#ddr-backdoor-loading-dma>`__
  - `HW/SW Co-Simulation Test <#hw-sw-co-simulation-test>`__

.. _overview:

Overview
--------

This readme provides information about the simulation environment for
the ``cl_dram_hbm_dma`` example. For more details about overall HDK
simulation environment and CL bringup in simulation please refer to the
`RTL Simulation Guide for HDK Design
Flow <../../../../docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__

SystemVerilog (SV) simulations can be run from the
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

   # To Run simulations with a 64 GB DDR DIMM (with user-controlled auto-precharge mode)
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
`Supported-DDR-Modes <./../../../../docs/Supported-DDR-Modes.html>`__
for details on supported DDR configurations.

The HW/SW co-simulation tests can be run from the ``verif/scripts/``
directory with all supported simulators:

.. code:: bash

   make C_TEST=test_dram_dma_hwsw_cosim # Runs with XSIM by default
   make C_TEST=test_dram_dma_hwsw_cosim VCS=1
   make C_TEST=test_dram_dma_hwsw_cosim QUESTA=1

   # To Run in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR.

   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 # Runs with XSIM by default
   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 VCS=1
   make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 QUESTA=1

Note that the appropriate simulators must be installed.

.. _dump-waves-dma:

Dump Waves
----------

For information about how to dump waves with XSIM or VCS, please refer
to
`debugging-custom-logic-using-the-aws-hdk <../../../../docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__

.. _system-verilog-tests:

SystemVerliog Tests
-------------------

The SystemVerilog test cases are located at ``verif/tests/``. Most tests
include ``base_test_utils.svh`` which includes common signals and tasks
used across tests. Please refer to this file for the DPI-C tasks used.
Information about each test can be found below.

.. _test-clk-recipesv:

test_clk_recipe.sv
~~~~~~~~~~~~~~~~~~

This test programs valid clock recipes defined within and verifies the
corresponding clock frequencies.

.. _test-ddr-peek-pokesv:

test_ddr_peek_poke.sv
~~~~~~~~~~~~~~~~~~~~~

This does a walking ones test through the DDR address range. Also checks
if any of the bits are stuck at '0'.

.. _test-ddrsv:

test_ddr.sv
~~~~~~~~~~~

This test programs the CL_TST (ATG) to generate traffic to access all
four DDR channels.

.. _test-hbmsv:

test_hbm.sv
~~~~~~~~~~~

This test programs the CL_TST (ATG) to generate traffic to access both
HBM stacks.

.. _test-dram-dmasv:

test_dram_dma.sv
~~~~~~~~~~~~~~~~

Basic H2C and C2H DMA test through all 4 DDR channels and 2 HBM stacks.

.. _test-dram-dma-rndsv:

test_dram_dma_rnd.sv
~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers with random lengths.

.. _test-dma-pcim-concurrentsv:

test_dma_pcim_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and PCIM traffic to run concurrently and
verifies that there are no errors on both DMA and PCIM interfaces.

.. _test-dma-pcis-concurrentsv:

test_dma_pcis_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and PCIS traffic to run concurrently and
verifies that there are no errors on both DMA and PCIS interfaces.

.. _test-dma-sda-concurrentsv:

test_dma_sda_concurrent.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs both the DMA and SDA traffic to run concurrently and
verifies that there are no errors on both DMA and SDA interfaces.

.. _test-dram-dma-4k-crossingsv:

test_dram_dma_4k_crossing.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers that will cross a 4k boundary. All
transfers are of same length with different destination addresses.

.. _test-dram-dma-allgn-addr-4ksv:

test_dram_dma_allgn_addr_4k.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs DMA transfers that will cross a 4k boundary. All
transfers are of different length with different destination addresses.

.. _test-dram-dma-single-beat-4ksv:

test_dram_dma_single_beat_4k.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs single beat DMA transfers that will cross a 4k
boundary.

.. _test-dram-dma-axi-mstrsv:

test_dram_dma_axi_mstr.sv
~~~~~~~~~~~~~~~~~~~~~~~~~

This test configures the cl_dram_dma_axi_mstr.sv module to send and
receive traffic from the DDR in the CL design.

.. _test-intsv:

test_int.sv
~~~~~~~~~~~

This test programs enables interrupts in CL and verifies them.

.. _test-peek-pokesv:

test_peek_poke.sv
~~~~~~~~~~~~~~~~~

This test programs ATG in CL to do 128 byte PCIM reads and writes.

.. _test-peek-poke-wcsv:

test_peek_poke_wc.sv
~~~~~~~~~~~~~~~~~~~~

This test performs pcis write combine operations and reads back the
data.

.. _test-peek-poke-lensv:

test_peek_poke_len.sv
~~~~~~~~~~~~~~~~~~~~~

This test programs tester block to do PCIM reads and writes with
incremental lengths.

.. _test-peek-poke-rnd-lengthssv:

test_peek_poke_rnd_lengths.sv
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test programs tester block to do PCIM reads and writes with random
lengths within valid range.

.. _test-peek-poke-pcis-axsizesv:

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

.. _test-sdasv:

test_sda.sv
~~~~~~~~~~~

This test does transfers to different addresses on SDA AXIL interface.

.. _test-nullsv:

test_null.sv
~~~~~~~~~~~~

test_null is not an actual test. This is a base SV file needed for HW/SW
co-simulation

.. _axi-memory-model-mode-simulations-dma:

AXI_MEMORY_MODEL Mode Simulations
---------------------------------

AXI_MEMORY_MODEL mode can be used for better simulation performance.
AXI_MEMORY_MODEL mode enables a test to run with AXI memory models
instead of DDR memory. The documentation can be found in AXI memory
model section at `RTL simulation
guide <../../../../docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__.
Any test that accesses DDR memory can be run in AXI_MEMORY_MODEL mode.
Below are some example tests for ECC and backdoor loading support
features of AXI memory model.

.. _test-dram-dma-mem-model-bdr-wr-dma:

test_dram_dma_mem_model_bdr_wr
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test backdoor writes AXI memory model, reads through frontdoor and
checks that the data matches.

.. _test-dram-dma-mem-model-bdr-rd-dma:

test_dram_dma_mem_model_bdr_rd
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This test backdoor reads AXI memory model, writes through frontdoor and
checks that the data matches.

.. _ddr-backdoor-loading-dma:

DDR Backdoor Loading
--------------------

The description of DDR backdoor loading can be found in DDR backdoor loading
support section at `RTL simulation
guide <../../../../docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__.

.. _hw-sw-co-simulation-test:

HW/SW Co-Simulation Test
------------------------

The software test with HW/SW co-simulation support
`test_dram_dma_hwsw_cosim.c <https://github.com/aws/aws-fpga/tree/f2/hdk/cl/examples/cl_mem_perf/software/runtime/test_dram_dma_hwsw_cosim.c>`__
can be found at ``software/runtime/``. For Information about how HW/SW
co-simulation support can be added to a software test please refer to
"Code changes to enable HW/SW co-simulation" section in `RTL simulation
guide <../../../../docs/RTL-Simulation-Guide-for-HDK-Design-Flow.html>`__.

`Back to HDK README <../../../../README.html>`__
