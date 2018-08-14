This readme provides information about the simulation environment for the cl_dram_dma example. For more details about overall HDK simulation environment and CL bringup in simulation please refer to [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# DRAM DMA CL example simulation

The system verilog simulation tests can be run from the [verif/scripts](scripts) directory with all supported simulators:

```
    $ make TEST=test_dram_dma (Runs with XSIM by default)
    $ make TEST=test_dram_dma VCS=1
    $ make TEST=test_dram_dma QUESTA=1
    $ make TEST=test_dram_dma IES=1
    
    //To Run Simulations in AXI_MEMORY_MODEL mode
    
    $ make TEST=test_dram_dma AXI_MEMORY_MODEL=1 (Runs with XSIM by default in AXI_MEMORY_MODEL mode)
    $ make TEST=test_dram_dma AXI_MEMORY_MODEL=1 VCS=1 
    $ make TEST=test_dram_dma AXI_MEMORY_MODEL=1 QUESTA=1 
    $ make TEST=test_dram_dma AXI_MEMORY_MODEL=1 IES=1
    
    //To Run Simulations in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR(ECC enabled).
    
    //Direct ECC error injection:
    //Injects ECC errors for read transactions with addresses in the range ECC_ADDR_LO to ECC_ADDR_HI
    
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 (Runs with XSIM by default)
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 VCS=1 
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 QUESTA=1
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 IES=1
    
    //Random ECC error injection:
    //Injects random ECC errors for read transactions for any address range. RND_ECC_WEIGHT is the percentage of time ECC should be injected    
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 (Runs with XSIM by default)
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 VCS=1 
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 QUESTA=1
    $ make TEST=test_dram_dma_ecc_direct AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 IES=1 
     
    //To Run DDR backdoor loading tests
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 (Runs with XSIM by default)
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 VCS=1
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 QUESTA=1
    $ make TEST=test_ddr_peek_bdr_walking_ones DDR_BKDR=1 IES=1
    
    //Backdoor loading test list. Description can be found in the sections below.    
    test_dram_dma_dram_bdr_wr  
    test_dram_dma_dram_bdr_walking_ones
    test_dram_dma_dram_bdr_row_col_combo
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
    
    //To Run Simulations in AXI_MEMORY_MODEL mode with AXI memory models instead of DDR(ECC enabled).
    
    //Direct ECC error injection:
    //Injects ECC errors for read transactions with addresses in the range ECC_ADDR_LO to ECC_ADDR_HI
    
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 (Runs with XSIM by default)
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 VCS=1 
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 QUESTA=1
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_DIRECT=1 ECC_ADDR_HI=100 ECC_ADDR_LO=0 IES=1
    
    //Random ECC error injection:
    //Injects random ECC errors for read transactions for any address range. RND_ECC_WEIGHT is the percentage of time ECC should be injected.
    
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 (Runs with XSIM by default)
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 VCS=1 
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 QUESTA=1
    $ make C_TEST=test_dram_dma_hwsw_cosim AXI_MEMORY_MODEL=1 ECC_RAND=1 RND_ECC_WEIGHT=100 IES=1 
    
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

# _AXI_MEMORY_MODEL mode simulations_
AXI_MEMORY_MODEL mode can be used for better simulation perfornmance. AXI_MEMORY_MODEL mode enables a test to run with AXI memory models instead of DDR memory. The documentation can be found in AXI memory model section at [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md). Any test that accesses DDR memory can be run in AXI_MEMORY_MODEL mode. Below are some example tests for ECC and backdoor loading support features of AXI memory model.

## test_dram_dma_mem_model_bdr_wr
This test backdoor writes AXI memory model, reads through frontdoor and checks that the data matches.

## test_dram_dma_mem_model_bdr_rd
This test backdoor reads AXI memory model, writes through frontdoor and checks that the data matches.

## test_dram_dma_ecc_direct
This test does backdoor write, injects ECC erors in AXI memory model within a address range and checks that the correct number of ECC errors are injected. The model keeps a count of the slave errors when ECC is injected and that count is used in the test to check the ECC functionality of the AXI memory model.

## test_dram_dma_ecc_random
This test does backdoor write, injects random ECC errors in AXI memory model and checks that the correct number of ECC errors are injected by looking at the random ECC error injection weight.

# _DDR backdoor loading_
The tests below use backdoor loading to populate DDR memory. The description of DDR backdoor loading can be found in DDR backdoor loading support section at [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

## test_ddr_peek_bdr_walking_ones
DDR test which uses backdoor loading to populate DDR memory. The test writes data(walking ones) for different addresses. The test backdoor loads DDR memory and reads through frontdoor and checks that the data matches.

## test_dram_dma_dram_bdr_wr    
DMA test backdoor loads one address in DRAM memory and reads through frontdoor. 

## test_dram_dma_dram_bdr_row_col_combo
DMA test which covers all row column combinations in each memory model.

## test_sda.sv
This test does transfers to different addresses on SDA AXIL interface.

## test_null.sv
test_null is not an actual test. This is a base system verilog file needed for HW/SW co-simulation

# HW/SW co-simulation Test

The software test with HW/SW co-simulation support [test_dram_dma_hwsw_cosim.c](../software/runtime/test_dram_dma_hwsw_cosim.c) can be found at [software/runtime](../software/runtime). For Information about how HW/SW co-simulation support can be added to a software test please refer to "Code changes to enable HW/SW co-simulation" section in [RTL_Simulating_CL_Designs](../../../../docs/RTL_Simulating_CL_Designs.md)

# Using IPI to run simulations in cl_dram_dma example

Xilinx IPI can also be used to simulate cl_dram_dma. For information about how to use IPI to simulate cl_dram_dma example, please refer to [IPI_GUI_cl_dram_dma_example](../../cl_dram_dma_hlx/README.md)




