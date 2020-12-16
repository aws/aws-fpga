This readme provides information about the simulation environment for the cl_dram_dma example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# DRAM DMA CL example simulation

The system verilog simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make TEST=test_ddr_peek_poke (Runs with XSIM by default)
    $ make TEST=test_ddr_peek_poke VCS=1
    $ make TEST=test_ddr_peek_poke QUESTA=1
    $ make TEST=test_ddr_peek_poke IES=1

    //To Run Simulations in AXI_MEMORY_MODEL mode

    $ make TEST=test_ddr AXI_MEMORY_MODEL=1 (Runs with XSIM by default in AXI_MEMORY_MODEL mode)
    $ make TEST=test_ddr AXI_MEMORY_MODEL=1 VCS=1
    $ make TEST=test_ddr AXI_MEMORY_MODEL=1 QUESTA=1
    $ make TEST=test_ddr AXI_MEMORY_MODEL=1 IES=1

    //To Run DDR backdoor loading tests
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 (Runs with XSIM by default)
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 VCS=1
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 QUESTA=1
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 IES=1

    //Backdoor loading test list. Description can be found in the sections below.
    test_ddr_peek_bdr_walking_ones

```

The HW/SW co-simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make C_TEST=test_dram_dma_hwsw_cosim (Runs with XSIM by default)
    $ make C_TEST=test_dram_dma_hwsw_cosim VCS=1
    $ make C_TEST=test_dram_dma_hwsw_cosim QUESTA=1
    $ make C_TEST=test_dram_dma_hwsw_cosim IES=1

    //To Run in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR.

    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 (Runs with XSIM by default)
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 VCS=1
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 QUESTA=1
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 IES=1

```

Note that the appropriate simulators must be installed.

# Dump Waves

For information about how to dump waves with XSIM, please refer to [debugging-custom-logic-using-the-aws-hdk](../../../../docs/RTL_Simulating_CL_Designs.md#debugging-custom-logic-using-the-aws-hdk)

# System Verliog Tests

The system verilog tests are located at [verif/tests](tests). Information about each test can be found below.

## test_clk_recipe.sv
This test programs valid clock recipes defined in and verifies the corresponding clock frequencies.

## test_ddr_peek_poke.sv
This does a walking ones test through the DDR address range. Also checks if any of the bits are stuck at '0'.

## test_ddr.sv
This test programs ATG to generate traffic to access all three DDRs in CL and one DDR in SH.

## test_int.sv
This test programs enables interrupts in CL and verifies them.

## test_peek_poke.sv
This test programs ATG in CL to do 128 byte PCIM reads and writes.

## test_peek_poke_len.sv
This test programs tester block to do PCIM reads and writes with incremental lengths.

## test_peek_poke_rnd_lengths.sv
This test programs tester block to do PCIM reads and writes with random lengths within valid range.

## test_peek_poke_pcis_axsize.sv
This test does PCIS peek and poke with different sizes. Although shell model allows different size transfers on PCIS interface, Shell only supports transfer of size 6 on PCIS interface.

# _AXI_MEMORY_MODEL mode simulations_
AXI_MEMORY_MODEL mode can be used for better simulation perfornmance. AXI_MEMORY_MODEL mode enables a test to run with AXI memory models instead of DDR memory. The documentation can be found in AXI memory model section at [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md). Any test that accesses DDR memory can be run in AXI_MEMORY_MODEL mode. Below are some example tests for ECC and backdoor loading support features of AXI memory model.

# _DDR backdoor loading_
The tests below use backdoor loading to populate DDR memory. The description of DDR backdoor loading can be found in DDR backdoor loading support section at [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

## test_ddr_peek_bdr_walking_ones
DDR test which uses backdoor loading to populate DDR memory. The test writes data(walking ones) for different addresses. The test backdoor loads DDR memory and reads through frontdoor and checks that the data matches.

## test_sda.sv
This test does transfers to different addresses on SDA AXIL interface.

## test_null.sv
test_null is not an actual test. This is a base system verilog file needed for HW/SW co-simulation

# HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_dram_dma_hwsw_cosim.c](../software/runtime/test_dram_dma_hwsw_cosim.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)
