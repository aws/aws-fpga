# CL_DRAM_DMA CustomLogic Example

## Table of Content

1. [Overview](#overview)
2. [Functional Description of the example RTL](#functionalDescription)
3. [Runtime Software](#runtmieSoftware)


<a name="overview"></a>
# Overview  

The CL_DRAM_DMA example demonstrate the use and connectivity for many of the Shell/CL interface and functionality, including:

1) [Register Access over ocl_ and bar1_ AXI-Lite interfaces]  
2) [Mapping of the external four DRAM channel to instance memory via PCIe AppPF BAR4, and the 512-bit pcis_dma_ AXI4 bus]
3) [Virtual JTAG and Xilinx Integrated Logic Analyzer cores]
4) [User-defined interrupts]

### System diagram  

[TBD - visio to be added]

  
  
  
<a name="functionalDescription"></a>
# Functional Description

### DRAM Interfaces

All four DRAM channels are used.... (TBD - how to instiate DRAM, should we set the DDR_A_PRESENT etc ?)

The DRAM space is 64GiB, and is mapped to the pcis_dma AXI4 bus.

### pcis_dma AXI4 bus

sh_cl_pcis_dma_ exposes a address windows of 128GiB matching AppPF BAR4.

This memory space is mapped to the 64GiB DRAM space (the upper half of the 128GiB will just wrap around to the lower half). An [internal fabric] (TBD LINK) will interleave inbound addresses according to TBD.


### ocl_ AXI-Lite

The sh_cl_ocl_ AXI-Lite bus is connected to [cl_ocl_slv.sv](https://github.com/aws/aws-fpga/blob/develop_xdma/hdk/cl/examples/cl_dram_dma/design/cl_ocl_slv.sv) module, and is used for register access to the Automatic Test Generator (ATG) etc.

The valid address map is found [here](./TBD).

Any access invalid address with return TBD


### bar1_ AXI-Lite

The sh_cl_bar1_ AXI-Lite bus is connected to [TBD] module[Add link], which provides 1KiB of scratch RAM.

Address bits [9:0] will be used to access the location of the RAM, but the upper bits of the address are ignored.


### sda_ AXI-Lite

The sh_cl_sda_ AXI-Lite bus is connected to [TBD] module[Add link], which provides 1KiB of scratch RAM.

Address bits [9:0] will be used to access the location of the RAM, but the upper bits of the address are ignored.


### pcim_ AXI4

The cl_sh_pcim_  AXI4 TBD.


### FPGA to FPGA communication over PCIe

This example does not use FPGA to FPGA PCIe communication

### FPGA to FPGA communication over Ring

This example does not use FPGA to FPGA Ring


### Virtual JTAG

A [TBD] ILA cores are integrated, one to monitoring the sh_cl_pcis_dma\* bus and the other to monitor the signals on DDR_A.
VIO is not used.

### Clocks

CL_DRAM_DMA uses the main `clk_main_a0`.  It's frequency is set in the cl_clk under `build/constraints/cl_clocks.xdc`.

`clk_xtra_a1` is used by the virtual JTAG

### Reset

flr_reset is ignored in this design
  
  
  


<a name="runtimeSoftware"></a>
# Runtime Software

