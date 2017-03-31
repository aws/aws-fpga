# CL Example list

|                  | [CL_HELLO_WORLD](./cl_hello_world)  | [CL_DRAM_DMA ](./cl_dram_dma)    |
|:-----------------|:---------------:|:---------------:|
|_***CL RTL Features***_|  |  |
| DRAM  	         |     Not used  	 | Channel A,B,C,D  |
| Register access (AXI-L)  | ocl_    | ocl_ , sda_ |
| Bulk transfer: Instance to CL (AXI)  | Not Used    | pcis_dma 	|
| Bulk transfer: CL to Instance (AXI)  | Not Used    | pcim | 	
| FPGA Direct: CL to CL over PCIe  | Not Used    | Not Used 	|
| FPGA Ring        |   	 Not used  	 |    Not Used   	 |
| Virt. LED      	    |   	 Used  	 | Not Used |
| Virt. DIP Sw     |   	 Used  	 | Not Used  |
| [Virt. JTAG](../../docs/Virtual_JTAG_XVC.md)          |   	Not used     | Used 	|
| Clocks used |    1 clock   |  2 clocks |
| PCI Vendor ID	|   	0x1D0F (Amazon)  	|  0x1D0F (Amazon)   	|
| PCI Device ID	| 0xF000  	| 0xF001  	|
| PCI FLR support | Not Used | Not Used |
|_***Software***_|  |  |
| [fpga_pci lib](../../../sdk/userspace/include/fpga_pci.h)	|   	Used  	|  Used 	|
| [fpga_mgmt lib](../../../sdk/userspace/include/fpga_mgmt.h)	|   	Used  	|  Used 	|
| [edma kernel driver](../../../sdk/linux_kernel_drivers/edma/README.md)	|   	Not used  	|  Used 	|
| read()/write() using bulk transfer	|   	Not used  	|  Used 	|
| [poll() for user events](../../../sdk/linux_kernel_drivers/edma/user_defined_interrupts.md) 	|   	Not used  	|  Used 	|
