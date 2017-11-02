# AWS FPGA PCIe Memory Map

FPGAs are PCIe-attached to an AWS EC2 instance, where each FPGA Slot presents a single FPGA with two PCIe Physical Functions (PFs), each with multiple PCIe Base Address Registers (BARs) as defined in [AWS Shell Specification](./AWS_Shell_Interface_Specification.md).

This document describes the actual size and attributes of each of the BARs, with some examples on how can they be mapped in a real life application.

Even though all these PCIe BARs are mapped to the EC2 Instance memory-mapped I/O (MMIO) space, they need to be mapped to Linux kernel or userspace application before accessing them. Please refer to the [Software Programmer's View](./Programmer_View.md) on how the various software pieces can interact with the FPGA PCIe Memory.

## Memory map per Slot
```
--- FPGA Slot X  
  |----- AppPF  
  |   |------- BAR0  
  |   |         * 32-bit BAR, non-prefetchable
  |   |         * 32MiB (0 to 0x1FF-FFFF)
  |   |         * Maps to OCL AXI-L of the CL
  |   |         * Typically used for CL application registers or OpenCL kernels  
  |   |------- BAR1
  |   |         * 32-bit BAR, non-prefetchable
  |   |         * 2MiB (0 to 0x1F-FFFF)
  |   |         * Maps to BAR1 AXI-L of the CL
  |   |         * Typically used for CL application registers 
  |   |------- BAR2
  |   |         * 64-bit BAR, prefetchable
  |   |         * 64KiB (0 to 0xFFFF)
  |   |         * NOT exposed to CL, used by internal DMA inside the Shell
  |   |------- BAR4
  |             * 64-bit BAR, prefetchable
  |             * 128GiB (0 to 0x1F-FFFF-FFFF)
  |             * First 127GiB are exposed to CL, via pcis_dma AXI bus
  |             * The upper 1GiB is reserved for future use
  |
  |
  |----- MgmtPF  
     |------- BAR0  
     |         * 64-bit BAR, prefetchable
     |         * 16KiB (0 to 0x3FFF)
     |         * Maps to internal functions used by the FPGA management tools
     |         * Not mapped to CL
     |------- BAR2
     |         * 64-bit BAR, prefetchable
     |         * 16KiB (0 to 0x3FFF)
     |         * Maps to internal functions used by the FPGA management tools
     |         * Not mapped to CL
     |------- BAR4
               * 64-bit BAR, prefetchable
               * 4MiB (0 to 0x3FFFFF)
               * Maps to CL through SDA AXI-L
               * Could be used by Developer applications, or if using the AWS Runtime Environment (like SDAccel case), it will be used for performance monitoring.
```
