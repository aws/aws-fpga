
Revision History
================

  ---------------------------------------------------------
  Revision   Date         Content
  ---------- ------------ ---------------------------------
  0.14       11/28/2016   -   Initial HDK release version
                          
                          
  ---------------------------------------------------------

Overview
========

The AWS FPGA instance provides FPGA acceleration capability to AWS
compute instances. Each FPGA is divided into two partitions:

-   Shell (SH) – AWS platform logic responsible for taking care of the
    FPGA external peripherals, PCIe, and Interrupts.

-   Customer Logic (CL) – Custom acceleration logic created by an FPGA
    Developer

At the end of the development process, the Shell and CL will become an
Amazon FPGA Image (AFI)

This document specifies the hardware interface and functional behavior
between the Shell and the CL.

While there are multiple versions and multiple generations of the
FPGA-accelerated EC2 instances, the rest of this document focuses on the
Shell design for xvu9p architecture used in EC2 F1 instance.

For full details of the available FPGA enabled instances please refer
to:

> <http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/FPGA.html> \[TBD -
> subject to change\]

Architecture and version
------------------------

This specification applies to the Xilinx Virtex Ultrascale Plus
platform, referred to in AWS APIs and the HDK release as
FpgaImageArchitecture=xvu9p.

The Shell is tagged with a revision number. Note while AWS tries to keep
the revision constant, sometimes it is necessary to update the revision
due to discovered issues or added functionality. The HDK release
includes the latest Shell version.

New shell versions require updated CL implementation.

Convention
----------

**CL –** Customer’s Logic: the Logic to be provided by the developer and
integrated with the Shell.

**DW –** Doubleword: referring to 4-byte (32-bit) data size

**AXI –** ARM Advanced eXtensible Interface.

**AXI Stream –** ARM Advanced eXtensible Stream Interface

**M –** Typically refers to the Master side of an AXI bus

**S –** Typical refers to the Slave side of AXI bus

CL (for xvu9p architecture as in EC F1 instances)
=================================================

The F1 FPGA platform includes the following interfaces available to the
CL:

-   One x16 PCIe Gen 3 Interface

-   Four DDR4 RDIMM interfaces (with ECC)

CL/Shell Interfaces (AXI-4)
---------------------------

All interfaces except the inter-FPGA links use the AXI-4 protocol. The
AXI-4 interfaces in the Shell have the following restrictions:

-   AxSIZE – All transfers must be the entire width of the bus. While
    byte-enables bitmap are supported, it must adhere to the interface
    protocol (i.e. PCIe contiguous byte enables on all transfers larger
    than 64-bits)

-   AxBURST – Only INCR burst is supported.

-   AxLOCK – Lock is not supported.

-   AxCACHE – Memory type is not supported.

-   AxPROT – Protection type is not supported

-   AxQOS – Quality of Service is not supported

-   AxREGION – Region identifier is not supported

### Interfaces implemented in CL

Some of the interfaces are implemented in the CL rather than the HL. For
those interfaces, the designs are provided by AWS and instantiated in
the CL. Note this is due to physical constraints.

There are four DDR interfaces labeled A, B, C, and D. Interfaces A, B,
and D are in the CL and interface C is implemented in the CL. A design
block (sh\_ddr.sv) instantiates the three DDR interfaces in the CL (A,
B, D).

For interfaces that are implemented in the CL, the AXI-4 (or AXI-Stream)
interfaces do not connect into the SH, but connect locally inside the CL
to the AWS provided blocks. There are also statistics interfaces that
must be connected from SH to the interface blocks.

Clocking/Reset
--------------

A single 250MHz clock, and associated asynchronous reset is provided to
the CL. All Shell interfaces are synchronous to the 250MHz clock. The CL
can derive clocks off of the 250MHz clock using the Xilinx Mixed Mode
Clock Manager (MMCM) to create clocks of other frequencies/phases. The
reset signal combines the board reset and PCIe reset conditions. Please
refer to the Xilinx documentation (ug974) for more information.

### Function Level Reset

FLR is supported for the User Physical Function using a separate FLR
interface:

-   sh\_cl\_flr\_assert – Level signal that is asserted when FLR has
    been requested

-   cl\_sh\_flr\_done – Asserted for a single clock to acknowledge
    the FLR. This must be asserted in response to sh\_cl\_flr\_assert.
    Note due to pipeline delays it is possible sh\_cl\_flr\_assert is
    asserted for some number of clocks after cl\_sh\_flr\_done.

PCIe Endpoint Presentation to Instance
--------------------------------------

There are two PCIe physical functions (PFs) presented to the F1
instance:

-   FPGA Management PF –This PF allows for management of the FPGA using
    the FPGA Management Tools, including tracking FPGA state and loading
    CL images onto the FPGA.

-   User PF – Customer’s PF for Customer specific logic (CL)

### Management PF

The management PF is a separate PF from the CL PF. Details are provided
for reference for understanding the PCIe mapping from an F1 instance.
This interface is strictly for AWS FPGA Management Tools. No support
exists for the CL code to interface with the Management PF. The
Management PF exposes:

a)  Amazon’s specific and fixed PCIe VendorID and DeviceID

b)  Two BARs with 4KB size

c)  Single MSI-X interrupt

d)  No BusMaster support

e)  A range of 32-bit addressable registers

The Management PF is persistent throughput the life of the instance, and
it will not be reset or cleared (even during the AFI attach/detach
process).

### User PF

The User PF exposes the following:

a)  PCIe BAR0 as a 64-bit prefetchable BAR sized as 128MB (*note the BAR
    size is subject to change, goal is 64GB, but will be no smaller
    than 128MB)*. This BAR may be used to map the entire
    External/Internal memory space to the instance address space if
    desired, through mmap() type calls.

b)  PCIe BAR2 as a 64-bit prefetchable BAR sized as 4KB for the MSI-X
    interrupt tables

c)  FLR capability that will reset the CL

d)  BusMaster capability to allow CL to master transactions towards the
    instance memory

The Developer can write a drivers for the User PF or can leverage the
reference driver provided in the HDK (driver included in Amazon Linux).

PCIe Interface between Shell and CL
-----------------------------------

The PCIe interface between the Shell and CL is accessed over two AXI-4
interfaces:

### AXI-4 for inbound PCIe transactions (Shell is master, CL is slave) 

This AXI-4 bus is for PCIe transactions mastered by the Instance and
targeting User PF BAR0.

It is a 512-bit wide AXI-4 interface that supports 32-bit transactions
only.

A read or write request on this AXI-4 bus that is not acknowledged by
the CL within a certain time window, will be internally terminated by
the Shell. If the time-out error happens on a read, the Shell will
return 0xDEADBEEF data back to the instance. This error is reported to
the Management functions.

Note in future revisions this interface will support larger burst sizes
(up to the Maximum Payload Size).

### AXI-4 for outbound PCIe transactions (CL is master, Shell is slave) 

This is a 512-bit wide AXI-4 Interface for the CL to master cycles to
the PCIe bus. This is used, for example, to DMA data to/from instance
memory.

The following PCIe interface configuration parameters are provided from
the Shell to the CL, and the CL logic must respect these maximum limits:

-   sh\_cl\_cfg\_max\_payload\[1:0\] – PCIe max payload size:

    -   2’b00 – 128 Byte

    -   2’b01 – 256 Byte (Most probable value)

    -   2’b10 – 512 Byte

    -   2’b11 – Reserved

-   sh\_cl\_cfg\_max\_read\_req\[2:0\]

    -   3’b000 – 128 Byte

    -   3’b001 – 256 Byte

    -   3’b010 – 512 Byte (Most probable value)

    -   3’b011 – 1024 Byte

    -   3’b100 – 2048 Byte

    -   3’b101 – 4096 Byte

The PCIe CL to Shell AXI-4 interfaces implement “user” bits on the
address channels (AxUSER\[18:0\]).

-   AxUSER\[10:0\] – DW length of the request. This is 1-based (0-zero
    DW, 1-one DW, 2-two DW, etc…)

-   AxUSER\[14:11\] – First Byte enable for the Request

-   AxUSER\[18:15\] – Last Byte enable for the Request

PCIe AXI-4 interface restrictions:

-   Transfers must not violate PCIe byte enable rules (see byte
    enables below)

-   Transfers must not cross a 4Kbyte Address boundary
    (PCIe restriction)

-   Transfers must not violate Max Payload Size

-   Read requests must not violate Max Read Request Size

-   A read request transaction must not be issued using the same ARID
    (AXI4 Read ID), if that ARID is already outstanding. *The Shell does
    not force ordering between individual read transactions*.

-   The PCIe interface supports 4-bit ARID (16 outstanding read
    transactions maximum). Note PCIe extended tag is not supported on
    the PCIe interface.

-   The address on the AXI-4 interface must reflect the correct byte
    address of the transfer. The Shell does not support using a 64B
    aligned address, and using STRB to signal the actual starting DW.

-   The first/last byte enables are determined from the AxUSER bits, but
    for writes the WSTRB signal must be correct and reflect the
    appropriate valid bytes.

### Byte Enable Rules

All PCIe transactions must adhere to the PCIe Byte Enable rules (see PCI
Express Base specification). Rules are summarized below:

-   All transactions larger than two DW must have contiguous byte
    enables

-   Transactions that are less than two DW may have non-contiguous byte
    enables

### AXI4 Error handling 

Transaction on AXI4 interface will be terminated and reported as SLVERR
on the RRESP/BRESP signals and will not passed to the instance in the
following cases:

-   PCIe BME (BusMaster Enable) is not set in the PCIe configuration
    space

-   Illegal transaction address (Addressing memory space that’s not
    supported by the instance)

-   Transaction crossing 4KB boundaries

-   Illegal byte-masking

-   Illegal length

-   Illegal ARID (ARID is already been used for an outstanding
    read transaction)

### Interrupts (Future)

Interrupts are not supported in the current version of the Shell. Future
versions of the Shell will have support for at least 16 interrupt
sources.

DDR-4 Interface
---------------

Each DDR-4 interface is accessed over an AXI-4 interface:

-   AXI-4 (CL Master) – 512-bit AXI-4 interface to read/write DDR

There is a single status signal that he DDR is trained and ready for
access. The addressing uses ROW/COLUMN/BANK mapping of AXI address to
DDR Row/Col/Bank. The Read and Write channels are serviced with round
robin priority (equal priority).

The DDR-4 interface uses the Xilinx DDR-4 controller. The AXI-4
interface adheres to the Xilinx specification. User bits are added to
the read data channel to signal ECC errors with the read data.

In the current version of the CL, the DDR interfaces are not optional
and have to be instanced in order to successfully place and route the
CL. In future versions, the CL will be able to choose the number of DDR
controllers (A/B/D). If the DDR interfaces are not used, the AXI-4
interfaces of the sh\_ddr.sv should be tied-off.

### DDR Preservation (Future)

In future Shell versions a DDR preservation feature will be implemented.
This feature allows the DDR state to be preserved when dynamically
changing CL logic. The current Shell version will not guarantee
preservation of DDR contents if the CL logic is re-loaded.

Miscellaneous signals
---------------------

There are some miscellaneous generic signals between Shell and CL.

### PCIe IDs

There are some signals that must have the PCIe IDs of the CL. A
Developer’s specific PCIe VendorID, DeviceID, SystemID and SubsystemID
are registered through aws ec2 fpgaImageCreate command to reserve the
PCIe IDs of the CL for mapping of the device into an F1 instance when
the AFI is loaded.

-   cl\_sh\_id0

    -   \[15:0\] – Vendor ID

    -   \[31:16\] – Device ID

-   cl\_sh\_id1

    -   \[15:0\] – Subsystem Vendor ID

    -   \[31:16\] – Subsystem Device ID

### General control/status

The functionality of these signals is TBD.

-   cl\_sh\_status0\[31:0\] – CL to Shell status

-   cl\_sh\_status1\[31:0\] – CL to Shell status

-   sh\_cl\_ctl0\[31:0\] – Shell to CL control information

-   sh\_cl\_ctl1\[31:0\] – Shell to CL control information

-   sh\_cl\_pwr\_state\[1:0\] – This is the power state of the FPGA. 0x0

    -   0x0 – Power is normal

    -   0x1 – Power level 1

    -   0x2 – Power level 2

    -   0x3 – Power is critical and FPGA is subject to shutting off
        clocks or powering down
