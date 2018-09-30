# SDE Hardware Guide

## Table of Contents:

* [Overview](#Overview)

* [Feature List](#FeatureList)

* [Architecture](#Architecture)

* [Designing with the SDE](#DesignCLwSDE)

   * [IOs](#IOs)

   * [PF and Address Range](#PF_AddressRange)

   * [Design parameters](#DesignParam)

   * [Implementation - Maximum Clock Frequency](#MaxClockFreq)

   * [Implementation - Resource Utilization](#ResourceUtil)

* [Example Design](#ExampleDesign)

* [FAQ](#FAQ)


<a name="Overview"></a>
## Overview

The Streaming Data Engine (SDE) provides high-performance packet streaming connectivity between the Custom Logic (CL) and the host application. The SDE provides a streaming interface to the CL and uses the shell's PCIM AXI4 interface to move packets between the CL and the host application. The SDE is a parametrizable, soft IP block that is intended to be instanciated within the CL. Each instance of the SDE provides two AXI streaming compliant interfaces viz. one Card-to-Host (C2H) and one Host-to-Card (H2C) channel.

<a name="FeatureList"></a>
## Feature List
1. High Performance PPS for C2H and H2C.
2. 12GB/s Bandwidth per channel for C2H and H2C (4KB packet at 250MHz).
3. AXI Stream compliant on the CL facing side.
4. AXI Stream supports parametrizable data widths 64, 128, 256 and 512 bits (Current version supports 512 bits only).
5. AXI4 complaint on the shell facing side.
6. AXI4 supports parametrizable data widths 64, 128, 256 and 512 bits (Current version supports 512 bits only).
7. User bits on the RX and TX streaming interfaces.
8. Multiple descriptor types (Normal and Compact).
9. Multiple descriptors per packet.
10. Write-back for credits and metadata.
11. Multiple write-back metadata types (Normal and compact)
12. One instance of the streaming data engine can be configured at compile-time to provide the following channel combinations  
* One full-duplex streaming channel (one C2H and one H2C). 
* One Streaming C2H Channel only (No H2C Channel)
* One Streaming H2C Channel only (No C2H Channel)
If more channels or other channel combinations are required, the SDE should be instanced multiple times and the AXI fabric (Crossbar/Interconnect) should be instanced to combine the PCIM and PCIS interfaces of individual SDE instances.

<a name="Architecture"></a>
## Architecture

![alt tag](../images/SDE_Block_Diagram.jpg)

The SDE uses shell s PCIM AXI4 interface to move packets between the AXI Streaming interface and the host. It implements a store and forward mechanism. For C2H, the packets received from the AXI Streaming interface is stored in the C2H packet buffer and are then transmitted on the PCIM AXI4 interface. For H2C, the packets received from the PCIM AXI4 interface are stored in the H2C packet buffer and are then transmitted on the AXI Streaming interface. 

SDE uses descriptors to perform the data movement and the bit-fields of the descriptors are defined to contain all required information for data transfer like buffer physical addresses, length etc. To achieve minimum latency, the SDE implements a descriptor RAM that can be written by software using the PCIS interface utilizing write-combine using  PF0-BAR4. The SDE implements a credit based mechanism to allow the software to track the descriptor utilization. 

In order to minimize latency and reduce the complexity of the software/driver, all the information that is polled by the driver/software (for example, descriptor credits, small packet credits, write-back ring write pointer, etc...) is stored in a contiguous host memory range. The SDE is architected to update these variables together by writing to the physical memory location using the PCIM interface.

<a name="DesignCLwSDE"></a>
## Designing with the SDE

<a name="IOs"></a>
### IOs
* PCIM AXI4 Master Interface: SDE uses this interface to write data to the host. 
* PCIS AXI4 Slave Interface: Software uses this interface to write descriptors and configuration data to the SDE. 
* H2C AXI Stream Master Interface: SDE uses this interface to transmit H2C packets to the CL.
* C2H AXI Stream Slave Interface: SDE uses this interface to receive C2H packets from the CL.
* Clocks and Reset: SDE uses a single clock and a single synchronous active-low reset. 

<a name="PF_AddressRange"></a>
### PF and Address Range
SDE implements a 16KB address space on the PCIS interface and therefore can be accessed using the PF0-BAR4. SDE uses the lower 16 bits of the address bus of the PCIS interface.

<a name="DesignParam"></a>
### Design parameters
The SDE can be parameterized when the SDE is instanced in the CL. Some of the important parameters are (The full list of parameters is available in the SDE Micro-architecture Specification) - 
* C2H_ONLY: Disable SDE H2C logic (Can be set to 1 if only the C2H channel is required).
* H2C_ONLY: Disable SDE C2H logic (Can be set to 1 if only the C2H channel is required).
* C2H_DESC_TYPE & H2C_DESC_TYPE: Descriptor Type (0 - Regular, 1 - Compact) for C2H and H2C respectively.
* C2H_DESC_RAM_DEPTH & H2C_DESC_RAM_DEPTH: Descriptor RAM depth. The maximum number of descriptors for C2H and H2C respectively.
* C2H_BUF_DEPTH & H2C_BUF_DEPTH: Buffer RAM depth. 

<a name="MaxClockFreq"></a>
### Implementation - Maximum Clock Frequency
The SDE can be implemented at a maximum frequency of 250MHz

<a name="ResourceUtil"></a>
### Implementation - Resource Utilization
The resource utilization for the SDE implemented at 250MHz when using 64 descriptor RAM depth and 32KB buffers for C2H and H2C each. 

| Total LUTs | Logic LUTs | LUTRAMs | SRLs |  FFs  | RAMB36 | RAMB18 | URAM | DSP48 Blocks| 
|------------|------------|---------|------|-------|--------|--------|------|-------------|
| 37056      | 36568      | 488     | 0    | 23282 | 16     | 3      | 0    | 0           |


<a name="ExampleDesign"></a>

## Example Design
AWS provides an example CL called CL_SDE. CL_SDE instances the SDE and some utility and test blocks to demonstrate the functionality of the SDE. See [CL_SDE](../../../../hdk/cl/examples/cl_sde/) for details.

<a name="FAQ"></a>

## FAQ

### Q: What is the maximum number of full duplex channels per instance of SDE?
One instance of SDE will provide one full duplex channel (one C2H and one H2C). 

### Q: My application does not need C2H. I only need H2C. How can this be done?
Design parameters C2H_ONLY and H2C_ONLY can be used to get what is required and avoid unwanted logic. For example, if only C2H is required, C2H_ONLY should be 1 so that H2C logic is avoided. 

### Q. My application needs more than one full duplex channel. How can this be achieved? 
With the current version of the SDE, if more than 1 full duplex channel is needed, multiple SDEs have to be instanced and AXI crossbars have to be used to connect the PCIS and PCIM buses to/from the corresponding SDEs. Similarly, if more than 1 C2H or more than 1 H2C channel is required, multiple SDEs have to be used.

### Q. Is there a maximum number of SDEs that can be instanced in a CL?
There is no theoritecal maximum. There is a practical limitation based on the number of resources in the CL. 

### Q. What kind of software/Driver is required to use the SDE. 
A userspace or kernel poll-mode driver is required to use the SDE.

### Q. Does AWS have any example Driver/Application? 
AWS provides DPDK based Virtual Ethernet application described [here](./Virtual_Ethernet_Application_Guide.md).

### Q. Does SDE supports interrupts?
Interrupts are not supported by the SDE.

### Q. My application needs more descriptors in the SDE? How can I achieve this? 
Parameters C2H_DESC_RAM_DEPTH and H2C_DESC_RAM_DEPTH can be used to increase the number of descriptors that can be stored in the SDE. Note that this will increase BRAM usage in the SDE. 

### Q. How can I change the size of the H2C and C2H buffers? 
Parameters C2H_BUF_DEPTH and H2C_BUF_DEPTH can be used to change the size of the main packet buffers for C2H and H2C respectively. 

### Q. What is the guideline for choosing buffer sizes?
The H2C buffer should be sized according to the bandwidth requirements. Having a very small H2C buffer will cause the SDE to reduce the effective number of outstanding PCIM reads leading to host DRAM latencies getting manifested on the H2C AXI-S interface, leading to reduced H2C bandwidth. AWS has observed that 32KB buffer is sufficient to maximize H2C throughput assuming average DRAM latency of 2us and PCI-E BW of 16GB/s. 
The C2H buffer should be sized according to CL resource availability and latency requirements. Assuming 4KB PCIM writes, AWS recommends at least a size of 16KB C2H buffer to maximize C2H BW. 

### Q. My application needs more than / less than 64 user bits. How can this be achieved? 
In the current version of the SDE, User bit width cannot be changed. Therefore, parameters C2H_USER_BIT_WIDTH and H2C_USER_BIT_WIDTH should not be changed. If more user bits are required, they will have to be embedded in the payload of the packet (For example, preamble or appended at the end of the packet). 

### Q. Can I use write-combine to write multiple descriptors per clock? 
Traditional Write-combine, explained [here](https://github.com/awslabs/aws-fpga-app-notes/tree/master/Using-PCIe-Write-Combining), routinely causes the CPU to generate out of order writes to the descriptor address range. SDE does not support out of order writes to the descriptor range. Therefore, x86 intrinsic load/store instructions should be used to write descriptors in order. 

### Q. What is the maximum throughput of the SDE? 
The maximum throughput for H2C is 12 GB/s and the maximum throughput for C2h is 12.4 GB/s. 

### Q. What is the minimum packet size required for maximum throughput? 
4KB is the minimum packet size required for maximum throughput.

### Q. My application uses PCIS and PCIM interfaces for other purposes in the CL. Can I still use the SDE? 
Yes, the SDE can still be used. However, appropriate AXI Crossbars/Fabric needs to be used in the CL in order to provide connectivity for PCIS and PCIM buses to the SDE. Additionally, address and ARID/AWIDs should be appropriately configured/parametrized in the software and the SDE respectively.

### Q. My accelerator/CL cannot transmit/receive data at 512bits per clock. Can SDE transmit/receive less than 512 bits per clock on the H2C/C2H Streaming Interfaces? 
The current version of the SDE can only transmit/receive data at 512 bits per clock. The CL developer can use Xilinx AXI-S width converters to achieve width conversion from any bit width to 512 bits. 

### Q. What is the guideline for choosing between Regular and Compact Descriptor/Metadata types?
Regular Descriptor/Metadata will provide 64 bits for host address and also provide 64 bits for User bits. Compact Descriptor/Metadata will provide only 48 bits for host address and does not provide any user bits. Using the compact type will save PCIS bandwidth for descriptor writes, save PCIM bandwidth for Metadata writes and save BRAM space in the SDE. 
Therefore, the compact type should be chosen when user bits are not required and also to maximize bandwidth usage for packet data and to save BRAM utilization in the CL.

### Q. How many clocks and resets does the SDE use?
The SDE uses only one clock. The SDE uses only one reset that is synchronized to the aforementioned clock.

### Q. Can the SDE be implemented at a clock frequency greater than 250MHz?
AWS only supports SDE implemented at a maximum of 250MHz. 

### Q. Should the SDE be constrained to a single SLR? 
AWS recommends that the all the logic in the SDE be constrained to a single SLR. Additionally, AWS recommends adding pipelining on the PCIM and PCIS interfaces from the shell leading up to the SDE.



