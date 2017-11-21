# Hello World CL Example


## :exclamation:  NOTE: If this is your first time using F1, you should read [How To Create an Amazon FPGA Image (AFI) From One of The CL Examples: Step-by-Step Guide](./../README.md) first!!

## Table of Contents

1. [Overview](#overview)
2. [Functional Description](#description)
3. [Hello World Example Metadata](#metadata)


<a name="overview"></a>
## Overview

This simple *hello_world* example builds a Custom Logic (CL) that will enable the instance to "peek" and "poke" registers in the Custom Logic (CL).
These registers will be in the memory space behind AppPF BAR0, which is the ocl\_cl\_ AXI-lite bus on the Shell to CL interface.

This example demonstrate a basic use-case of the Virtual LED and Virtual DIP switches.

All of the unused interfaces between AWS Shell and the CL are tied to fixed values, and it is recommended that the developer use similar values for every unused interface in the developer's CL.


<a name="description"></a>
## Functional Description

The cl_hello_world example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and the use of the Virtual LED and DIP switches. The cl_hello_world example implements two registers in the FPGA AppPF BAR0 memory space connected to the OCL AXI-L interface. The two registers are:

1. Hello World Register (offset 0x500)
2. Virtual LED Register (offset 0x504)

Please refer to the [FPGA PCIe memory space overview](../../../docs/AWS_Fpga_Pcie_Memory_Map.md)

The Hello World Register is a 32-bit read/write register. However, in order to demonstrate that the register is being accessed correctly, the read data returned for the register will be byte swapped.

The Virtual LED register is a 16-bit read-only register that shadows the lower 16 bits of the Hello World Register such that it will hold the same value as bits 15:0 of the Hello World Register.

The cl_hello_world design utilizes the Virtual LED and DIP switch interface which consistes of two signals described in the [cl_ports.vh] (./../../../common/shell_stable/design/interfaces/cl_ports.vh) file:


```
   input[15:0] sh_cl_status_vdip,               //Virtual DIP switches.  Controlled through FPGA management PF and tools.
   output logic[15:0] cl_sh_status_vled,        //Virtual LEDs, monitored through FPGA management PF and tools
```

In this example the Virtual LED Register is used to drive the Virtual LED signal, cl_sh_status_vled. In addition, the Virtual DIP switch, sh_cl_status_vdip, is used to gate the Virtual LED Register value sent to the Virtual LEDs. So, for example, if the sh_cl_status_vdip is set to 16'h00FF, then only the lower 8 bits of the Virtual LED Register will be signaled on the Virtual LED signal cl_sh_status_vled. 

While running on F1, the developer can use the FPGA tools `fpga-get-virtual-led` to read the LED values on the CL-to-Shell interface.  While `fpga-set-virtual-dip-switch` tool is used to set the DIP switch values on the Shell-to-CL interface.

  
### Unused interfaces

The Hello World example does not use most of AWS Shell interface, hence the unused signals are tied off.
At the end of `cl_hello_world.sv` file, there is a specific `include` command for an interface-specific `.inc` file, to handle the tie-off\'s for every unused interface.


<a name="metadata"></a>
## Hello World Example Metadata

The following table displays information about the CL that is required to register it as an AFI with AWS.
Alternatively, you can directly use a pre-generated AFI for this CL.


| Key   | Value     |
|-----------|------|
| Shell Version | 0x071417d3 |
| PCI Device ID | 0xF000 |
| PCI Vendor ID | 0x1D0F (Amazon) |
| PCI Subsystem ID | 0x1D51 |
| PCI Subsystem Vendor ID | 0xFEDD |
| Pre-generated AFI ID | afi-0853bcceeda387d03 |
| Pre-generated AGFI ID | agfi-0f4478c5ca0b1dbaf |

