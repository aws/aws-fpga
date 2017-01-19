
## Revision History

2016/11/28   -   Initial public release with HDK release version

2016/12/06   -   Added capability to remove DDR controllers in the CL through parameters in `sh_ddr.sv`
                          
                          

# Overview

With F1, each FPGA is divided into two partitions:

-   Shell (SH) – AWS platform logic responsible for taking care of the FPGA external peripherals, PCIe, DRAM, and Interrupts.

-   Customer Logic (CL) – Custom acceleration logic created by an FPGA Developer

At the end of the development process, combining the Shell and CL creates an Amazon FPGA Image (AFI)

This document specifies the hardware interface and functional behavior between the SH and the CL; specifically the Shell design for xvu9p architecture used in EC2 F1 instance.

Full details of the available FPGA enabled instances are [here](https://aws.amazon.com/ec2/instance-types/f1/)

## Architecture and Version

This specification applies to  Xilinx Virtex Ultrascale Plus platform, referred to in AWS APIs and the HDK release as `FpgaImageArchitecture=xvu9p`.

The Shell is tagged with a revision number. Note while AWS tries to keep the revision constant, sometimes it is necessary to update the revision due to discovered issues or added functionality. The HDK release includes the latest Shell version under `/hdk/common/shell_latest`

New shell versions will require updated CL implementation and regenerating the AFI.

## Conventions


**CL –** Custom’s Logic: the Logic to be provided by the developer and integrated with AWS Shell.

**DW –** Doubleword: referring to 4-byte (32-bit) data size.

**AXI-4** ARM Advanced eXtensible Interface.

**AXI-4 Stream –** ARM Advanced eXtensible Stream Interface.

**M –** Typically refers to the Master side of an AXI bus.

**S –** Typical refers to the Slave side of AXI bus.

# Shell Interfaces (for xvu9p architecture as in EC F1 instances)


The F1 FPGA platform includes the following interfaces available to the
CL:

-   One x16 PCI Express 3.0 Interface.

-   Four DDR4 RDIMM interfaces, each interface is 72-bit wide including ECC.


## CL/Shell Interfaces (AXI-4)


All interfaces except the inter-FPGA links uses the AXI-4 protocol. The AXI-4 interfaces in the Shell have the following restrictions:

-   AxSIZE – All transfers must be at the entire width of the bus. While byte-enables bitmap are supported, it must adhere to the interface protocol (i.e. PCIe contiguous byte enables on all transfers larger than 64-bits).

-   AxBURST – Only INCR burst is supported.

-   AxLOCK – Lock is not supported.

-   AxCACHE – Memory type is not supported.

-   AxPROT – Protection type is not supported.

-   AxQOS – Quality of Service is not supported.

-   AxREGION – Region identifier is not supported.


![alt tag](./images/AWS_Shell_CL_overview.jpg)

### External Memory Interfaces implemented in CL

Some of the DRAM interface controllers are implemented in the CL rather than the Shell for optimized resource utilization of the FPGA (Allowing higher utilization for the CL place and route region to maximize usuable FPGA resources). For those interfaces, the designs and the constrains are provided by AWS and must be instantiated in the CL (by including the `sh_ddr.sv`). 

There are four DRAM interfaces labeled A, B, C, and D. Interfaces A, B, and D are in the CL while interface C is implemented in the Shell. A design block (sh_ddr.sv) instantiates the three DRAM interfaces in the CL (A, B, D).

For DRAM interface controllers that are implemented in the CL, the AXI-4 interfaces do not connect into the Shell, but connect locally inside the CL to the AWS provided blocks. There are also statistics interfaces that must be connected from Shell to the DRAM interface controller modules.

All CL's **must** instantiate sh_ddr.sv, regardless of the number of DDR's that should be implemented.  There are three parameters (all default to '1') that define which DDR controllers are implemented:
  * DDR_A_PRESENT
  * DDR_B_PRESENT
  * DDR_D_PRESENT
  
These parameters are used to control which DDR controllers are impemented in the CL design.  An example instantiation:
 ```   
    sh_ddr #(.DDR_A_PRESENT(1),
           .DDR_B_PRESENT(1),
           .DDR_D_PRESENT(0))
           SH_DDR (
              .clk(clk),
              ...
 ```   
 

**NOTE:** *There is no performance or frequency difference between the four DRAM controllers regardless whether they resides in the CL or the Shell logic*


### Clocking/Reset

A single 250MHz clock, and associated asynchronous reset is provided to the CL. All Shell interfaces are synchronous to the 250MHz clock. The CL can derive clocks off of the 250MHz clock.

+The Xilinx Mixed Mode Clock Manager (MMCM) IP can be used to generate slower clocks off of the 250MHz clock.

![alt tag](./images/Dividing_clocks_inside_CL.jpg)

The reset signal combines the board reset and PCIe reset conditions. Please refer to the [Xilinx documentation (ug974)](https://www.xilinx.com/support/documentation/sw_manuals/xilinx2014_1/ug974-vivado-ultrascale-libraries.pdf) for more information.

### Function Level Reset (FLR)

FLR is supported for the application Physical Function using a separate FLR interface:

-   sh_cl_flr_assert – Level signal that is asserted when FLR has
    been requested

-   cl_sh_flr_done – Asserted for a single clock to acknowledge
    the FLR. This must be asserted in response to sh_cl_flr_assert.
    Note due to pipeline delays it is possible sh_cl_flr_assert is
    asserted for some number of clocks after cl_sh_flr_done.


## PCIe Endpoint Presentation to Instance

There are two PCIe Physical Functions (PFs) presented to the F1 instance:

-   Management PF – This PF is used for management of the FPGA using the [FPGA Management Tools](../../sdk/management/fpga_image_tools/README.md), including monitoring FPGA metrics and AFI managment actions.

-   Application PF (AppPF)– The AppPF is used for  CL specific functionality.


### Management PF

The management PF details are provided for reference to help understanding the PCIe mapping from an F1 instance. This interface is strictly used for AWS FPGA Management Tools, and does not support any interface with the CL code. 

The Management PF exposes:

a)  Amazon’s specific and fixed PCIe VendorID (0x1D05) and DeviceID.

b)  Two BARs with 4KB size.

c)  Single MSI-X interrupt.

d)  No BusMaster support.

e)  A range of 32-bit addressable registers.

The Management PF is persistent throughout the lifetime of the instance, and it will not be reset or cleared (even during the AFI Load/Clear process).

### Application PF (AppPF)

The Application PF exposes:

a)  PCIe BAR0 as a 64-bit prefetchable BAR sized as 128MB (*note the BAR size is subject to change, goal is 64GB, but will be no smaller
    than 128MB)*. This BAR may be used to map the entire External/Internal memory space to the instance address space if desired, through `mmap()` type calls.

b)  PCIe BAR2 as a 64-bit prefetchable BAR sized as 4KB for the MSI-X interrupt tables.

c)  FLR capability that will reset the CL.

d)  BusMaster capability to allow the CL to master transactions towards the instance memory.
    
e)  CL’s specific PCIe VendorID, DeviceID, VendorSystemID and SubsystemID as registered through `aws ec2 fpgaImageCreate`

The Developer can write drivers for the AppPF or can leverage the reference driver provided in the SDK.


### CL Interface to PCIe Interface via Shell 

The PCIe interface connecting the FPGA to the instance is in the Shell, and the CL can access it through two AXI-4 interfaces:

#### AXI-4 for Inbound PCIe Transactions (Shell is Master, CL is Slave) 

This AXI-4 bus is used for PCIe transactions mastered by the instance and targeting AppPF BAR0.

It is a 512-bit wide AXI-4 interface that supports 32-bit transactions only. *Future revisions this interface will support larger burst sizes (up to the Maximum Payload Size)*.

A read or write request on this AXI-4 bus that is not acknowledged by the CL within a certain time window, will be internally terminated by the Shell [*May not be supported in early releases*]. If the time-out error happens on a read, the Shell will return `0xDEADBEEF` data back to the instance. This error is reported through the Management PF and could be retrieved by the AFI Management Tools metric.

#### AXI-4 for Outbound PCIe Transactions (CL is Master, Shell is Slave) 

This is a 512-bit wide AXI-4 interface for the CL to master cycles to the PCIe bus. This can be used, for example, to DMA data to/from instance memory.

The following PCIe interface configuration parameters are provided from the Shell to the CL, and the CL logic must respect these maximum limits:

-   sh_cl_cfg_max_payload[1:0] – PCIe max payload size:
    -   2’b00 – 128 Byte
    -   2’b01 – 256 Byte (Most probable value)
    -   2’b10 – 512 Byte
    -   2’b11 – Reserved

-   sh_cl_cfg_max_read_req[2:0]
    -   3’b000 – 128 Byte
    -   3’b001 – 256 Byte
    -   3’b010 – 512 Byte (Most probable value)
    -   3’b011 – 1024 Byte
    -   3’b100 – 2048 Byte
    -   3’b101 – 4096 Byte

The PCIe CL to Shell AXI-4 interfaces **MUST** implement “USER” bits on the address channels (`AxUSER[18:0]`).

-   AxUSER[10:0] – DW length of the request. This is 1-based (0: zero DW, 1: one DW, 2: two DW, etc…).
-   AxUSER[14:11] – First DW's Byte enable for the Request.
-   AxUSER[18:15] – Last DW's Byte enable for the Request.

##### Outbound PCIe AXI-4 Interface Restrictions:

-   Transfers must not violate PCIe byte enable rules (see byte enable rules below).
-   Transfers must not cross a 4Kbyte address boundary (a PCIe restriction).
-   Transfers must not violate Max Payload Size.
-   Read requests must not violate Max Read Request Size.
-   A read request transaction must not be issued using the same AXI4 Read ID(ARID), if that ARID is already outstanding. **NOTE:** *The Shell does not enforce ordering between individual read transactions and read response could be in arbiterary order*.
-   The PCIe interface supports 5-bit ARID (32 outstanding read transactions maximum), as PCIe extended tag is not supported on the PCIe interface.
-   The address on the AXI-4 interface must reflect the correct byte address of the transfer. The Shell does not support using a 64-bit
    aligned address, and using STRB to signal the actual starting DW.
-   The first/last byte enables are determined from the AxUSER bits. In addition, for writesm the WSTRB signal must be correct and reflect the appropriate valid bytes on the WDATA bus even if it was provided on AxUSER. 

##### Byte Enable Rules

All PCIe transactions must adhere to the PCIe Byte Enable rules (see PCI Express Base specification). Rules are summarized below:

-   All transactions larger than two DW must have contiguous byte enables.
-   Transactions that are less than two DW may have non-contiguous byte enables.

### AXI4 Error Handling 

Transactions on AXI4 interface will be terminated and reported as SLVERR on the RRESP/BRESP signals and will not be passed to the instance in the following cases:

-   PCIe BusMaster Enable (BME) is not set in the PCIe configuration space.

-   Illegal transaction address; i.e. addressing memory space that isn't supported by the instance.

-   Transaction crossing 4KB boundaries violating PCIe specifications.

-   Illegal byte-masking.

-   Illegal length.

-   Illegal ARID; i.e ARID is already been used for an outstanding read transaction.

**NOTE** Pre-GA versions of the Shell and the FPGA Magagement tools may not have some of these checks and associated metrics exposed to the developers.

### Interrupts (Future)

Interrupts are not supported in the current version of the Shell. Future
versions of the Shell will have support for at least 16 interrupt
sources.

## DDR4 DRAM Interface

Each DRAM interface is accessed via an AXI-4 interface:

-   AXI-4 (CL Master and DRAM controller is slave) – 512-bit AXI-4 interface to read/write DDR.

There is a single status signal that the DRAM interface is trained and ready for access. The addressing uses ROW/COLUMN/BANK mapping of AXI address to DRAM Row/Col/BankGroup. The Read and Write channels are serviced with round-robin arbitration (i.e. equal priority).

The DRAM interface uses Xilinx DDR-4 Interface controller. The AXI-4 interface adheres to the Xilinx specification. User bits are added to the read data channel to signal ECC errors with the read data.

**NOTE:** even if no DDR4 controllers are desired in the CL, the `sh_ddr.sv` block must be instantiated in the CL (parameters are used to remove DDR controllers).  If the `sh_ddr.sv` module is not instantiated the design will have build errors.

### DRAM Content Preservation between AFI Loads (Future)

In future Shell versions a DRAM content preservation feature will be implemented. This feature allows the DDR state to be preserved when dynamically changing CL logic. The current Shell version will not guarantee preservation of DRAM contents if the CL logic is re-loaded.

#### Miscellaneous signals

There are some miscellaneous generic signals between the Shell and CL.

### PCIe IDs

Some signals must include the PCIe IDs of the CL. A Developer’s specific PCIe VendorID, DeviceID, SubsystemVendorID and SubsystemID are registered through `aws ec2 fpgaImageCreate` command to reserve the PCIe IDs of the CL for mapping of the device into an F1 instance when the AFI is loaded.

-   cl_sh_id0

    -   [15:0] – Vendor ID

    -   [31:16] – Device ID

-   cl_sh_id1

    -   [15:0] – Subsystem Vendor ID

    -  [31:16] – Subsystem ID

### General Control/Status

The functionality of these signals is TBD.

-   cl_sh_status0[31:0] – Placeholder for generic CL to Shell status.

-   cl_sh_status1[31:0] – Placeholder for generic CL to Shell status.

-   sh_cl_ctl0[31:0] – Placeholder for generic Shell to CL control information.

-   sh_cl_ctl1[31:0] – Placeholder for generic Shell to CL control information.

-   sh_cl_pwr_state[1:0] – This is the power state of the FPGA. 

    -   0x0 – Power is normal

    -   0x1 – Power level 1

    -   0x2 – Power level 2

    -   0x3 – Power is critical and FPGA may be shutting off clocks or powering down
