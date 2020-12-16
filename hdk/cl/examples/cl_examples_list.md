# CL Example list

# CL Example list

|                  | [CL_HELLO_WORLD](./cl_hello_world) | [CL_DRAM_DMA ](./cl_dram_dma)  | [CL_SDE](./cl_sde)    |
|:-----------------|:---------------:|:---------------:|:---------------:|
|_***CL RTL Features***_|  |  |  |
| DRAM  	         |     Not used  	 | Channel A,B,C,D  |     Not used  	 |
| Register access (AXI-L)  | ocl_    | ocl_ , sda_ | ocl_    |
| Bulk transfer: Instance to CL (AXI)  | Not Used    | dma_pcis 	| pcis    |
| Bulk transfer: CL to Instance (AXI)  | Not Used    | pcim |   pcim    |	
| FPGA Direct: CL to CL over PCIe  | Not Used    | Not Used 	| Not Used    |
| FPGA Ring        |   	 Not used  	 |    Not Used   	 | Not Used    |
| Virt. LED      	    |   	 Used  	 | Not Used | Not Used    |
| Virt. DIP Sw     |   	 Used  	 | Not Used  | Not Used    |
| [Virt. JTAG](../../docs/Virtual_JTAG_XVC.md)          |   	Used     | Used 	| Used 	|
| Clocks used |    1 clock   |  2 clocks |    1 clock   |
| PCI Vendor ID	|   	0x1D0F (Amazon)  	|  0x1D0F (Amazon)   	|   	0x1D0F (Amazon)  	|
| PCI Device ID	| 0xF000  	| 0xF001  	| 0xF002  	|
| PCI FLR support | Not Used | Not Used | Not Used |
