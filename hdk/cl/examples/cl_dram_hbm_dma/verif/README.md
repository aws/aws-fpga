This readme provides information about the simulation environment for the cl_dram_hbm_dma example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to the [RTL Simulation Guide for HDK Design Flow](../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md)

# DRAM HBM DMA CL example simulation

The system verilog simulation tests can be run from the [$CL_DIR/verif/scripts](./scripts) directory with all supported simulators (HBM is only supported in VCS & QUESTA). You can run tests by calling the make target for that test located in [$CL_DIR/verif/scripts/Makefile.tests](./scripts/Makefile.tests):

```bash
make test_ddr # Runs with XSIM by default
make test_ddr VCS=1
make test_ddr QUESTA=1

make test_hbm # Runs with VCS by default
```

Alternatively, you can run each test by setting TEST=<test name> followed by the environment variables required to run that test.

**NOTE: CL_DRAM_HBM_DMA does not currently have a datapath to all 64 GB of DDR. Only the first 32GB is accessible.**


```bash
make TEST=test_dram_dma # Runs with XSIM by default
make TEST=test_dram_dma VCS=1
make TEST=test_dram_dma QUESTA=1

# To Run simulations with a 32 GB DDR DIMM (without user-controlled auto-precharge mode)
make TEST=test_dram_dma USE_32GB_DDR_DIMM=1

# To Run simulations with a 32 GB DDR DIMM (with user-controlled auto-precharge mode)
make TEST=test_dram_dma USE_AP_32GB_DDR_DIMM=1

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
```

**NOTE**: Please refer to [Supported_DDR_Modes.md](./../../../../docs/Supported_DDR_Modes.md) for details on supported DDR configurations.

The HW/SW co-simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```bash
make C_TEST=test_dram_dma_hwsw_cosim # Runs with XSIM by default
make C_TEST=test_dram_dma_hwsw_cosim VCS=1
make C_TEST=test_dram_dma_hwsw_cosim QUESTA=1

# To Run in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR.

make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 # Runs with XSIM by default
make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 VCS=1
make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 QUESTA=1
```

Note that the appropriate simulators must be installed.

## Dump Waves

For information about how to dump waves with XSIM or VCS, please refer to [debugging-custom-logic-using-the-aws-hdk](../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md#)

## System Verliog Tests

The system verilog tests are located at [verif/tests](tests). Most tests include `base_test_utils.svh` which includes common signals and tasks used across tests. Please refer to this file for the DPI-C tasks used. Information about each test can be found below.

### test_clk_recipe.sv
This test programs valid clock recipes defined within and verifies the corresponding clock frequencies.

### test_ddr_peek_poke.sv
This does a walking ones test through the DDR address range. Also checks if any of the bits are stuck at '0'.

### test_ddr.sv
This test programs the CL_TST (ATG) to generate traffic to access all four DDR channels.

### test_hbm.sv
This test programs the CL_TST (ATG) to generate traffic to access both HBM stacks.

### test_dram_dma.sv
Basic H2C and C2H DMA test through all 4 DDR channels and 2 HBM stacks.

### test_dram_dma_rnd.sv
This test programs DMA transfers with random lengths.

### test_dma_pcim_concurrent.sv
This test programs both the DMA and PCIM traffic to run concurrently and verifies that there are no errors on both DMA and PCIM interfaces.

### test_dma_pcis_concurrent.sv
This test programs both the DMA and PCIS traffic to run concurrently and verifies that there are no errors on both DMA and PCIS interfaces.

### test_dma_sda_concurrent.sv
This test programs both the DMA and SDA traffic to run concurrently and verifies that there are no errors on both DMA and SDA interfaces.

### test_dram_dma_4k_crossing.sv
This test programs DMA transfers that will cross a 4k boundary. All transfers are of same length with different destination addresses.

### test_dram_dma_allgn_addr_4k.sv
This test programs DMA transfers that will cross a 4k boundary. All transfers are of different length with different destination addresses.

### test_dram_dma_single_beat_4k.sv
This test programs single beat DMA transfers that will cross a 4k boundary.

### test_dram_dma_axi_mstr.sv
This test configures the cl_dram_dma_axi_mstr.sv module to send and receive traffic from the DDR in the CL design.

### test_int.sv
This test programs enables interrupts in CL and verifies them.

### test_peek_poke.sv
This test programs ATG in CL to do 128 byte PCIM reads and writes.

### test_peek_poke_wc.sv
This test performs pcis write combine operations and reads back the data.

### test_peek_poke_len.sv
This test programs tester block to do PCIM reads and writes with incremental lengths.

### test_peek_poke_rnd_lengths.sv
This test programs tester block to do PCIM reads and writes with random lengths within valid range.

### test_peek_poke_pcis_axsize.sv
This test does PCIS peek and poke with different sizes. Although shell model allows different size transfers on PCIS interface, Shell only supports transfer of size 6 on PCIS interface.

## _AXI_MEMORY_MODEL mode simulations_
AXI_MEMORY_MODEL mode can be used for better simulation perfornmance. AXI_MEMORY_MODEL mode enables a test to run with AXI memory models instead of DDR memory. The documentation can be found in AXI memory model section at [RTL simulation guide](../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md). Any test that accesses DDR memory can be run in AXI_MEMORY_MODEL mode. Below are some example tests for ECC and backdoor loading support features of AXI memory model.

### test_dram_dma_mem_model_bdr_wr
This test backdoor writes AXI memory model, reads through frontdoor and checks that the data matches.

### test_dram_dma_mem_model_bdr_rd
This test backdoor reads AXI memory model, writes through frontdoor and checks that the data matches.

## _DDR backdoor loading_
The tests below use backdoor loading to populate DDR memory. The description of DDR backdoor loading can be found in DDR backdoor loading support section at [RTL simulation guide](../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md).

### test_ddr_peek_bdr_walking_ones
DDR test which uses backdoor loading to populate DDR memory. The test writes data(walking ones) for different addresses. The test backdoor loads DDR memory and reads through frontdoor and checks that the data matches.

### test_sda.sv
This test does transfers to different addresses on SDA AXIL interface.

### test_null.sv
test_null is not an actual test. This is a base system verilog file needed for HW/SW co-simulation

## HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_dram_dma_hwsw_cosim.c](../software/runtime/test_dram_dma_hwsw_cosim.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL simulation guide](../../../../docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md).

## Regressions

A regression with full coverage can be run with the following commands

```bash
make regression <SIMULATOR>=1
make regression AXI_MEMORY_MODEL=1 <SIMULATOR>=1
make regression ECC_DIRECT=1 <SIMULATOR>=1
make regression ECC_RAND=1 <SIMULATOR>=1
make regression DDR_BKDR=1 <SIMULATOR>=1
make regression AXI_MEMORY_MODEL=1 ECC_DIRECT=1 <SIMULATOR>=1
make regression AXI_MEMORY_MODEL=1 ECC_RAND=1 <SIMULATOR>=1
```
