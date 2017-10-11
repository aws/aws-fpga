# CL Example list

|                  | [CL_HELLO_WORLD](./cl_hello_world)<br>[CL_HELLO_WORLD_VHDL](./cl_hello_world_vhdl)<br>[CL_HELLO_WORLD_HLX](./cl_hello_world_hlx)  | [CL_DRAM_DMA ](./cl_dram_dma)<br>[CL_DRAM_DMA_HLX](./cl_dram_dma_hlx)    | [CL_URAM_EXAMPLE](./cl_uram_example)    |
|:-----------------|:---------------:|:---------------:|:---------------:|
|_***CL RTL Features***_|  |  |  |
| DRAM  	         |     Not used  	 | Channel A,B,C,D  |     Not used  	 |
| Register access (AXI-L)  | ocl_    | ocl_ , sda_ | ocl_    |
| Bulk transfer: Instance to CL (AXI)  | Not Used    | dma_pcis 	| Not Used    |
| Bulk transfer: CL to Instance (AXI)  | Not Used    | pcim |  Not Used    |	
| FPGA Direct: CL to CL over PCIe  | Not Used    | Not Used 	| Not Used    |
| FPGA Ring        |   	 Not used  	 |    Not Used   	 | Not Used    |
| Virt. LED      	    |   	 Used  	 | Not Used | Not Used    |
| Virt. DIP Sw     |   	 Used  	 | Not Used  | Not Used    |
| [Virt. JTAG](../../docs/Virtual_JTAG_XVC.md)          |   	Used     | Used 	| Used 	|
| Clocks used |    1 clock   |  2 clocks |    1 clock   |
| PCI Vendor ID	|   	0x1D0F (Amazon)  	|  0x1D0F (Amazon)   	|   	0x1D0F (Amazon)  	|
| PCI Device ID	| 0xF000  	| 0xF001  	| 0xF000  	|
| PCI FLR support | Not Used | Not Used | Not Used |
|_***Software***_|  |  |  |
| [fpga_pci lib](../../../sdk/userspace/include/fpga_pci.h)	|   	Used  	|  Used 	|   	Used  	|
| [fpga_mgmt lib](../../../sdk/userspace/include/fpga_mgmt.h)	|   	Used  	|  Used 	|   	Used  	|
| [edma kernel driver](../../../sdk/linux_kernel_drivers/edma/README.md)	|   	Not used  	|  Used 	|   	Not used  	|
| read()/write() using bulk transfer	|   	Not used  	|  Used 	|   	Not used  	|
| [poll() for user events](../../../sdk/linux_kernel_drivers/edma/user_defined_interrupts_README.md) 	|   	Not used  	|  Used 	|   	Not used  	|
