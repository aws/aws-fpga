# CL_DRAM_DMA CustomLogic Example

## Table of Content

1. [Overview](#overview)
2. [Functional Description of the example RTL](#functionalDescription)
3. [Runtime Software](#runtmieSoftware)


<a name="overview"></a>
# Overview  

The CL_DRAM_DMA example demonstrates the use and connectivity for many of the Shell/CL interfaces and functionality, including:


1) Register Access over ocl\_ AXI-Lite interfaces

2) Mapping of the external four DRAM channel to instance memory via PCIe AppPF BAR4, and the 512-bit pcis_dma_ AXI4 bus

3) Virtual JTAG and Xilinx Integrated Logic Analyzer cores

4) User-defined interrupts

5) pcim_ AXI4 traffic for host memory accesses from CL



### System diagram  

[Diagram](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_dram_dma.jpg)

  
<a name="functionalDescription"></a>
# Functional Description

### DRAM Interfaces


All four DRAM channels are used.


The DRAM space is 64GiB, and is mapped to the pcis_dma AXI4 bus.

### pcis_dma AXI4 bus

sh_cl_pcis_dma_ exposes a address windows of 128GiB matching AppPF BAR4.


This memory space is mapped to the 64GiB DRAM space (the upper half of the 128GiB will just wrap around to the lower half). An [axi_crossbar_0](https://github.com/aws/aws-fpga/blob/prelease/hdk/common/shell_v02221781/design/ip/cl_axi_interconnect/hdl/cl_axi_interconnect.v) will interleave inbound addresses according to DDR_A (base_addr=0x0_0000_00000, range=16GB), DDR_B(base_addr=0x4_0000_0000, range=16GB), DDR_C(base_addr=0x8_0000_0000, range=16GB), DDR_D(base_addr=0xC_0000_0000, range=16GB).


### ocl_ AXI-Lite


The sh_cl_ocl\_ AXI-Lite bus is connected to [cl_ocl_slv.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_ocl_slv.sv) module, and is used for register access to the Automatic Test Generator (ATG) etc.


Any access invalid address with return 32'hdeadbeef


### sda_ AXI-Lite

The sh_cl_sda\_ AXI-Lite bus is connected to [cl_sda_slv.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_sda_slv.sv) module, which provides 1KiB of scratch RAM.


Address bits [9:0] will be used to access the location of the RAM, but the upper bits of the address are ignored.


### pcim_ AXI4


The cl_sh_pcim\_  AXI4 bus is driven by Automatic Test Generator (ATG) and connected to [cl_pcim_mstr.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_pcim_mstr.sv). It can be used to read/write from the host memory. 

### irq/ack
[cl_int_slv.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_int_slv.sv) provides an example for generating the IRQ requests and checks if ACK has been received.

### FPGA to FPGA communication over PCIe

This example does not use FPGA to FPGA PCIe communication

### FPGA to FPGA communication over Ring

This example does not use FPGA to FPGA Ring


### Virtual JTAG

2 ILA cores are integrated, one to monitoring the sh_cl_dma\_pcis bus and the other to monitor the AXI4 signals on DDR_A. An example usage is provided in [cl_ila.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_ila.sv).
An example usage for Xilinx VIO is provided in [cl_vio.sv](https://github.com/aws/aws-fpga/blob/prelease/hdk/cl/examples/cl_dram_dma/design/cl_vio.sv)


### Clocks

CL_DRAM_DMA uses the main `clk_main_a0`.  It's frequency is set in the cl_clk under `build/constraints/cl_clocks.xdc`.

`clk_xtra_a1` is used by the Virtual JTAG

### Reset

flr_reset is ignored in this design
  
  
  


<a name="runtmieSoftware"></a>
# Runtime Software

