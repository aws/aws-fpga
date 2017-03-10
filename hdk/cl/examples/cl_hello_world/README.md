# Hello World CL Example

## Table of Contents

1. [Overview] (#overview)
2. [Functional Description] (#description)
3. [Hello World Example Metadata] (#metadata)

## Overview
This simple *hello_world* example builds a Custom Logic (CL) that will enable the instance to "peek" and "poke" registers in the OpenCL (OCL) memory space of the CL inside the FPGA.

Please read here for [general instructions to build the CL, register an AFI, and start using it on an F1 instance](./../README.md).

## <a name="description"> Functional Description

The cl_hello_world example demonstrates basic Shell-to-CL connectivity, memory-mapped register instantiations and the use of the Virtual LED and DIP switches. The cl_hello_world example implements two registers in the PCIe PF0 BAR0 memory space connected to the OCL AXI-L interface. The two registers are:

1. Hello World Register (offset 0x500)
2. Virtual LED Register (offset 0x504)

The Hello World Register is a 32-bit read/write register. However, in order to demonstrate that the register is being accessed correctly, the read data returned for the register will be byte swapped.

The Virtual LED register is a 16-bit read-only register that shadows the lower 16 bits of the Hello World Register such that it will hold the same value as bits 15:0 of the Hello World Register.

The cl_hello_world design utilizes the Virtual LED and DIP switch interface which consistes of two signals described in the [cl_ports.vh] (./../../../common/shell_v02221781/design/interfaces/cl_ports.vh) file:

```
   input[15:0] sh_cl_status_vdip,               //Virtual DIP switches.  Controlled through FPGA management PF and tools.
   output logic[15:0] cl_sh_status_vled,        //Virtual LEDs, monitored through FPGA management PF and tools
```

In this example the Virtual LED Register is used to drive the Virtual LED signal, cl_sh_status_vled. In addition, the Virtual DIP switch, sh_cl_status_vdip, is used to gate the Virtual LED Register value sent to the Virtual LEDs. So, for example, if the sh_cl_status_vdip is set to 16'h00FF, then only the lower 8 bits of the Virtual LED Register will be signaled on the Virtual LED signal cl_sh_status_vled. 

## <a name="metadata"> Hello World Example Metadata

The following table displays information about the CL that is required to register it as an AFI with AWS.
Alternatively, you can directly use a pre-generated AFI for this CL which you can associate to an instance or AMI.

| Key   | Value     |
|-----------|------|
| FPGA Image Architecture | xvu9p |
| Shell Version | 0x02221781 |
| PCI Device ID | 0xF000 |
| PCI Vendor ID | 0x1D0F (Amazon) |
| PCI Subsystem ID | 0x1D51 |
| PCI Subsystem Vendor ID | 0xFEDD |
| Pre-generated AFI ID | afi-TBD |
| Pre-generated AGFI ID | agfi-TBD |

