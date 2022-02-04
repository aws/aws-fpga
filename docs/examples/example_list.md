## Example Applications List

| Accelerator Application | Example | Development Environment | Description |
| --------|---------|---------|-------|
| Custom hardware | [cl\_hello\_world](../../hdk/cl/examples/cl_hello_world) | HDK - RTL (Verilog) | Simple [getting started example](../../hdk/README.md) with minimal hardware |
| Custom hardware | [cl\_dram\_dma](../../hdk/cl/examples/cl_dram_dma) | HDK - RTL (Verilog) | Demonstrates CL connectivity to the F1 shell and connectivity to/from all DDRs |
| Custom hardware | [IP integration example using a GUI - cl\_dram\_dma\_hlx](../../hdk/cl/examples/cl_dram_dma_hlx) | HLx - Verilog  | Demonstrates CL connectivity to the F1 shell and connectivity to/from DRAM using the Vivado IP Integrator GUI |
| Custom hardware | [Virtual Ethernet Application](../../sdk/apps/virtual-ethernet) | [Streaming Data Engine](../../hdk/cl/examples/cl_sde) | The Virtual Ethernet framework facilitates streaming Ethernet frames from a network interface (or any source) into the FPGA for processing and back out to some destination. Possible use cases for this include deep packet inspection, software defined networking, stream encryption or compression, and more. |
| Custom hardware | [Pipelined Workload Applications - cl\_dram\_dma\_data\_retention](../../hdk/docs/data_retention.md)| [HDK](../../hdk/cl/examples/cl_dram_dma/software/runtime/test_dram_dma_retention.c) [SDAccel](../../SDAccel/examples/aws/data_retention) | Demonstrates how to preserve data in DRAMs while swapping out accelerators. Applications that use a temporal accelerator pipeline can take advantage of this feature to reduce latency between FPGA image swaps  |
| High Level Synthesis | [Digital Up-Converter - cl\_hls\_dds\_hlx](../../hdk/cl/examples/cl_hls_dds_hlx) | HLx - C-to-RTL  | Demonstrates an example application written in C that is synthesized to RTL (Verilog) |
| Custom Hardware with Software Defined Acceleration | [RTL Kernels](https://github.com/Xilinx/Vitis_Accel_Examples/tree/master/rtl_kernels) | Vitis - RTL (Verilog) + C/C++/OpenCL  | These examples demonstrate developing new hardware designs (RTL) in a Software Defined workflow|
## Application Notes 

App Note | Description |
|---------|---------|
| [Using PCIe Peer-2-Peer connectivity](https://github.com/awslabs/aws-fpga-app-notes/tree/master/Using-PCIe-Peer2Peer) | This app note shows how to use PCIe P2P connectivity on F1.16XL instances |
| [Using PCIM Port](https://github.com/awslabs/aws-fpga-app-notes/tree/master/Using-PCIM-Port) | This app note shows how to use the PCIM AXI port to transfer data between card and host memory |
| [Using PCIe User Interrupts](https://github.com/awslabs/aws-fpga-app-notes/tree/master/Using-PCIe-Interrupts) | This app note describes the basic kernel calls needed for a developer to write a custom interrupt service routine (ISR) and provides an example that demonstrates those calls |
| [Using PCIe Write Combining](https://github.com/awslabs/aws-fpga-app-notes/tree/master/Using-PCIe-Write-Combining) | This app note describes when to use write combining and how to take advantage of write combining in software for a F1 accelerator |

## Workshops

* [ReInvent:19 Workshop](https://github.com/awslabs/aws-fpga-app-notes/tree/master/reInvent19_Developer_Workshop)
* [ReInvent:18 Workshop](https://github.com/awslabs/aws-fpga-app-notes/tree/master/reInvent18_Developer_Workshop)
