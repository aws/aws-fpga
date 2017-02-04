# AWS FPGA PCIe Memory Map

FPGA are PCIe-attached to AWS EC2 instance, which each FPGA Slot presenting single FPGA with two PCIe Physical Functional, each with multiple BAR (PCIe Base Address Register), matching [AWS Shell Specification](./AWS_Shell_Interface_Spec.md)

This document present the actual size and attribute of each one of the BARs, with some examples how they would be mapped in a real life application.

Though that all these PCIe BARs are mapped to the EC2 Instance memory-mapped I/O (mmio) space, they need to be mapped to Linux kernel or userspace application before accessing them. Please refer to the [Software Programmer's View](./Programmers_View.md) on how the various software pieces could interact with the FPGA PCIe Memory.

## Memory map
```
--- FPGA Slot X  
  |----- AppPF  
     |------- BAR0  
     |         * 32-bit BAR
     |         * 0 to 0xFFFFF
     |         * Maps to OCL AXI-L of the CL
     |         * Typically used for CL application registers or OpenCL kernels  
     |------- BAR1
```
