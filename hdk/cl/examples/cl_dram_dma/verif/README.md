This readme provides information about the simulation environment for the cl_dram_dma example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# DRAM DMA CL example simulation

The system verilog simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make TEST=test_dram_dma (Runs with XSIM by default)
    $ make TEST=test_dram_dma VCS=1
    $ make TEST=test_dram_dma QUESTA=1
    $ make TEST=test_dram_dma IES=1
```

The HW/SW co-simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make C_TEST=test_dram_dma_hwsw_cosim (Runs with XSIM by default)
    $ make C_TEST=test_dram_dma_hwsw_cosim VCS=1
    $ make C_TEST=test_dram_dma_hwsw_cosim QUESTA=1
    $ make C_TEST=test_dram_dma_hwsw_cosim IES=1
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

## test_dram_dma.sv
Basic H2C and C2H DMA test.

## test_dram_dma_rnd.sv
This test programs DMA transfers with random lengths.

## test_dma_pcim_concurrent.sv
This test programs both the DMA and PCIM traffic to run concurrently and verifies that there are no errors on both DMA and PCIM interfaces.

## test_dma_pcis_concurrent.sv
This test programs both the DMA and PCIS traffic to run concurrently and verifies that there are no errors on both DMA and PCIS interfaces.

## test_dma_sda_concurrent.sv
This test programs both the DMA and SDA traffic to run concurrently and verifies that there are no errors on both DMA and SDA interfaces.

## test_dram_dma_4k_crossing.sv
This test programs DMA transfers that will cross a 4k boundary. All transfers are of same length with different destination addresses.

## test_dram_dma_allgn_addr_4k.sv
This test programs DMA transfers that will cross a 4k boundary. All transfers are of different length with different destination addresses.

## test_dram_dma_single_beat_4k.sv
This test programs single beat DMA transfers that will cross a 4k boundary.

## test_dram_dma_axi_mstr.sv
This test programs dual master mode and programs the two masters to access different DDRs.

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

## test_sda.sv
This test does transfers to different addresses on SDA AXIL interface.

## test_null.sv
test_null is not an actual test. This is a base system verilog file needed for HW/SW co-simulation

# HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_dram_dma_hwsw_cosim.c](../software/runtime/test_dram_dma_hwsw_cosim.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# Using IPI to run simulations in cl_dram_dma example

Xilinx IPI can also be used to simulate cl_dram_dma. For information about how to use IPI to simulate cl_dram_dma example, please refer to [IPI_GUI_cl_dram_dma_example](../../cl_dram_dma_hlx/README.md)




