# AWS Shell Interface Specification

## Revision History

2016/11/28   -   Initial public release with HDK release version

2016/12/06   -   Added capability to remove DDR controllers in the CL through parameters in `sh_ddr.sv`

2017/02/02   -   Major updates for Feb/2017 Shell, that includes interrupts, wider and more buses,  DMA, Emulated LED and other. (Please refer to [Release Notes](../../RELEASE_NOTES.md) for details)
                          
  
# Table of Content:

1. [Overview](#overview)

2. [EC2 Instance view of FPGA PCIe](#pciPresentation)

3. [Clocks and Reset](#ClocksNReset)

4. [Shell/CL Interfaces](#ShellInterface)

  4.1 [Interrupts](#interrupts)
  
  4.2 [DDR4 DRAM Interfaces](#ddr)
  
  4.3 [Miscellanous Interfaces (vLED, vDIP)](#misc)
  
  

# Overview<a name="overview"></a>

With F1, each FPGA is divided into two partitions:

-   Shell (SH) – AWS platform logic responsible for taking care of the FPGA external peripherals, PCIe, DRAM, and Interrupts.

-   Customer Logic (CL) – Custom acceleration logic created by an FPGA Developer.

At the end of the development process, combining the Shell and CL creates an Amazon FPGA Image (AFI)

This document specifies the hardware interface and functional behavior between the SH and the CL; specifically the Shell design for xvu9p architecture used in EC2 F1 instance.

Full details of the available FPGA enabled instances are [here](https://aws.amazon.com/ec2/instance-types/f1/)
  
  
## Architecture and Version

This specification applies to  Xilinx Virtex Ultrascale Plus platform available on EC2 F1, each update of the Shell 
 is tagged with a revision number. Note while AWS tries to keep the revision constant, sometimes it is necessary to update the revision due to discovered issues or added functionality. The HDK release includes the latest Shell version under `/hdk/common/shell_latest`

New shell versions will require updated CL implementation and regenerating the AFI.
  
  
## Conventions
  
**CL –** Custom’s Logic: the Logic to be provided by the developer and integrated with AWS Shell.

**DW –** Doubleword: referring to 4-byte (32-bit) data size.

**AXI-4** ARM Advanced eXtensible Interface.

**AXI-4 Stream –** ARM Advanced eXtensible Stream Interface.

**M –** Typically refers to the Master side of an AXI bus.

**S –** Typical refers to the Slave side of AXI bus.  
  
  

# Shell Interfaces<a name="ShellInterfaces"></a>


The F1 FPGA platform includes the following interfaces available to the
CL:

-   One x16 PCI Express 3.0 Interface.

-   Four DDR4 RDIMM interfaces, each interface is 72-bit wide including ECC.


## CL/Shell AXI Interfaces (AXI-4 and AXI-Lite)

All interfaces except the inter-FPGA links use the AXI-4 or AXI-Lite protocol.  The AXI-L buses are for register access use cases, and can run off lower speed control interfaces that use the AXI-Lite protocol. 

For bulk data transfer, wide AXI-4 buses are used. AXI-4 on the CL/Shell interfaces have the following restrictions:

-   AxSIZE – All transfers must be at the entire width of the bus. While byte-enables bitmap are supported, it must adhere to the interface protocol (i.e. PCIe contiguous byte enables on all transfers larger than 64-bits).

-   AxBURST – Only INCR burst is supported.

-   AxLOCK – Lock is not supported.

-   AxCACHE – Memory type is not supported.

-   AxPROT – Protection type is not supported.

-   AxQOS – Quality of Service is not supported.

-   AxREGION – Region identifier is not supported.


![alt tag](./images/AWS_Shell_CL_overview.jpg)

## External Memory Interfaces implemented in CL

Some of the DRAM interface controllers are implemented in the CL rather than the Shell for optimized resource utilization of the FPGA (Allowing higher utilization for the CL place and route region to maximize usable FPGA resources). For those interfaces, the designs and the constraints are provided by AWS and must be instantiated in the CL (by instantiating `sh_ddr.sv` in the CL design). 

There are four DRAM interfaces labeled A, B, C, and D. Interfaces A, B, and D are in the CL while interface C is implemented in the Shell. A design block (sh_ddr.sv) instantiates the three DRAM interfaces in the CL (A, B, D).

For DRAM interface controllers that are implemented in the CL, the AXI-4 interfaces do not connect into the Shell, but connect locally inside the CL to the AWS provided blocks. There are also statistics interfaces that must be connected from Shell to the DRAM interface controller modules.  **WARNING** if the stats interface is not hooked up, the DDR controllers will not function.

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

# FPGA PCIe Presentation to EC2 Instance<a name="pciPresentation"></a>

There are two PCIe Physical Functions (PFs) presented to the F1 instance:

-   Management PF – This PF is used for management of the FPGA using the [FPGA Management Tools](../../sdk/management/fpga_image_tools/README.md), [FPGA Management Library](./TBD), and various control functions like Emulated LED, Emulated DipSwitch, [Virtual JTAG], and including monitoring FPGA metrics and performing AFI management actions.

-   Application PF (AppPF)– The AppPF is used for CL specific functionality.

The [Software Programmers' View](./Programmers_View.md) provides the intended software programmer's view and associated software modules and libraries around the two before mentioned PFs. 

Please refer to [PCI Address map](AWS_Fpga_Pcie_Memory_Map.md) for a more detailed view of the address map.

## Management PF (MgmtPF)

The Management PF details are provided for reference to help understanding the PCIe mapping from an F1 instance. This interface is strictly used for [AWS FPGA Management Tools/Library](./TBD), and [AWS Runtime HAL](./TBD), and does not support any interface with the CL code. 

The Management PF exposes:

a)  Amazon’s specific and fixed PCIe VendorID (0x1D05) and DeviceID.

b)  Three BARs:

      - BAR0 - 16KiB
      - BAR2 - 16KiB
      - BAR4 - 4MiB  

c)  No BusMaster support.

d)  A range of 32-bit addressable registers.

The Management PF is persistent throughout the lifetime of the instance, and it will not be reset or cleared (even during the AFI Load/Clear process).  


## Application PF (AppPF)

The Application PF exposes:

a)  PCIe BAR0 as a 32-bit non-prefetchable BAR sized as 32MiB.  This BAR maps to the the OCL AXI-Lite interface.

b)  PCIe BAR1 as a 32-bit non-prefetchable BAR sized as 2MiB.  This BAR maps to the the BAR1 AXI-Lite interface.

c)  PCIe BAR2 as a 64-bit prefetchable BAR sized as 64KiB. This BAR is not CL visible.  This BAR maps to the MSI-X tables and XDMA (if enabled).

d)  PCIe BAR4 as a 64-bit prefetchable BAR sized as 128GiB. This BAR may be used to map the entire External/Internal memory space to the instance address space if desired, through `mmap()` type calls or use `fpga_pci_lib` APIs.

c)  FLR capability that will reset the CL.

d)  BusMaster capability to allow the CL to master transactions towards the instance memory.
    
e)  CL’s specific PCIe VendorID, DeviceID, VendorSystemID and SubsystemID as registered through `aws ec2 fpgaImageCreate`

The Developer can write drivers for the AppPF or can leverage the reference driver provided in the SDK.


# Clocks and Reset<a name="ClocksNReset"></a>

## Clocks

There are multiple clocks provided by the Shell to the CL, grouped in 3 groups marked \_a, \_b and \_c suffix: 

   - clk_main_a0
   - clk_extra_a1
   - clk_extra_a2
   - clk_extra_a3

   - clk_extra_b0
   - clk_extra_b1

   - clk_extra_c0
   - clk_extra_c1

**clk_main_a0** is the main clock and used, since all interfaces between CL and SH are clocked with clk_main_a0.

The clocks within each group are generated from a common VCO/PLL, which restrict what combinations of frequencies are allowed within a group.

The maximum frequency on clk_main_a0 is 250MHz.

** *Note: The Developer must NOT assume any phase alignment between clock sources* **
** *Note: The Developer must NOT assume frequency lock or alignment between clocks from different groups, even if they are set for same frequencies * **  


### Defining Clock frequencies by Developer

There Developer can select among a set of available frequencies, provided in the table below. The target frequencies must defined in the [AFI Manifest](./AFI_Manifest.md), which would be included in the tar file passed to `aws ec2 create-fpga-image` AFI registration API.

 .  **FIXME NEED TO PUT TABLE OF FREQUENCIES**

### Default Clock Frequency setting if a clock group is missing from the AFI Manifest

   clk_main_a0:   125MHz
   clk_extra_a1:  125MHz
   clk_extra_a2:  375MHz
   clk_extra_a3:  500MHz

   clk_extra_b0:  250MHz
   clk_extra_b1:  125MHz

   clk_extra_c0:  300MHz
   clk_extra_c1:  400MHz


## Reset

The shell provides an active_low reset signal synchronous to clk_main_a0: rst_main_n.  This is an active low reset signal, and combines the board reset and PCIe link-level reset conditions.

### PCIe Function Level Reset (FLR)

PCIe FLR is supported for the Application Physical Function (PF) using a separate FLR signal:

-   sh_cl_flr_assert – Active-high Level signal that is asserted when FLR has been requested

-   cl_sh_flr_done – Asserted (active-high) for a single clock to acknowledge the FLR. This must be asserted in response to sh_cl_flr_assert. Note due to pipeline delays it is possible sh_cl_flr_assert is asserted for some number of clocks after cl_sh_flr_done. 


# Interfaces between Shell and CL

## CL Interface to PCIe Interface via Shell  

The PCIe interface connecting the FPGA to the instance is in the Shell, and the CL can access it through two AXI-4 interfaces:
  
  
### AXI-4 for Inbound PCIe Transactions (Shell is Master, CL is Slave, 512-bit) -- DMA_PCIS interface 

This AXI-4 bus is used for PCIe transactions mastered by the instance and targeting AppPF BAR4.

It is a 512-bit wide AXI-4 interface. 

A read or write request on this AXI-4 bus that is not acknowledged by the CL within a certain time window, will be internally terminated by the Shell. If the time-out error happens on a read, the Shell will return `0xDEADBEEF` data back to the instance. This error is reported through the Management PF and could be retrieved by the AFI Management Tools metric.

If DMA is enabled this interface also has DMA traffic targeting the CL.

### AXI-4 for Outbound PCIe Transactions (CL is Master, Shell is Slave, 512-bit)  -- PCIM interface

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
-   The address on the AXI-4 interface must reflect the correct byte address of the transfer. The Shell does not support using a 64-bit
    aligned address, and using STRB to signal the actual starting DW.
-   The first/last byte enables are determined from the AxUSER bits. In addition, for writesm the WSTRB signal must be correct and reflect the appropriate valid bytes on the WDATA bus even if it was provided on AxUSER. 

##### Byte Enable Rules

All PCIe transactions must adhere to the PCIe Byte Enable rules (see PCI Express Base specification). Rules are summarized below:

-   All transactions larger than two DW must have contiguous byte enables.
-   Transactions that are less than two DW may have non-contiguous byte enables.

#### AXI4 Error Handling for CL outbound transactions 

Transactions on AXI4 interface will be terminated and reported as SLVERR on the RRESP/BRESP signals and will not be passed to the instance in the following cases:

-   PCIe BusMaster Enable (BME) is not set in the PCIe configuration space.

-   Illegal transaction address; i.e. addressing memory space that isn't supported by the instance.

-   Transaction crossing 4KB boundaries violating PCIe specifications.

-   Illegal byte-masking.

-   Illegal length.

-   Illegal ARID; i.e ARID is already been used for an outstanding read transaction.

**NOTE** Pre-GA versions of the Shell and the FPGA Management tools may not have some of these checks and associated metrics exposed to the developers.


## AXI-Lite interfaces for register access -- (SDA, OCL, BAR1)

There are three AXI-L master interfaces (Shell is master) that can be used for register access interfaces.  Each interface is sourced from a different PCIe PF/BAR.  Breaking this info multiple interfaces allows for different software entities to have a control interface into the CL:

-   SDA AXI-L: Associated with MgmtPF, BAR4.  If the developer is using AWS OpenCL runtime Lib (As in SDAccel case), this interface will be used for performance monitors etc.
-   OCL AXI-L: Associated with AppPF, BAR0. If the developer is using AWS OpenCL runtime lib(As in SDAccel case), this interface will be used for openCL Kernel access
-   BAR1 AXI-L: Associated with AppPF, BAR1.

Please refer to [PCI Address map](AWS_Fpga_Pcie_Memory_Map.md) for a more detailed view of the address map.


## Interrupts <a name="interrupts"></a>

16 user interrupt source are supported.  There is mapping logic that maps the user interrupts to MSI-X vectors.  Mapping registers int he DMA controller map the 16 user interrupt sources to MSI-X vectors.  

There are two sets of signals to generate interrupts:

-   cl_sh_apppf_irq_req[15:0] (from CL to SH)
-   sh_cl_apppf_irq_ack[15:0] (from SH to CL)

The CL asserts (active high) cl_sh_apppf_irq_req[x], and holds it asserted until the SH responds with sh_cl_apppf_irq_ack[x].


## DDR4 DRAM Interface<a name="ddr"></a>

Each DRAM interface is accessed via an AXI-4 interface:

-   AXI-4 (CL Master and DRAM controller is slave) – 512-bit AXI-4 interface to read/write DDR.

There is a single status signal that the DRAM interface is trained and ready for access. The addressing uses ROW/COLUMN/BANK mapping of AXI address to DRAM Row/Col/BankGroup. The Read and Write channels are serviced with round-robin arbitration (i.e. equal priority).

The DRAM interface uses Xilinx DDR-4 Interface controller. The AXI-4 interface adheres to the Xilinx specification. User bits are added to the read data channel to signal ECC errors with the read data.

**NOTE:** even if no DDR4 controllers are desired in the CL, the `sh_ddr.sv` block must be instantiated in the CL (parameters are used to remove DDR controllers).  If the `sh_ddr.sv` module is not instantiated the design will have build errors.
  
  
### DRAM Content Preservation between AFI Loads (Future)
  
  
In future Shell versions a DRAM content preservation feature will be implemented. This feature allows the DDR state to be preserved when dynamically changing CL logic. The current Shell version will not guarantee preservation of DRAM contents if the CL logic is re-loaded.
  
  
## Miscellaneous signals<a name="misc"></a>

There are some miscellaneous generic signals between the Shell and CL.

### PCIe IDs

Some signals must include the PCIe IDs of the CL. A Developer’s specific PCIe VendorID, DeviceID, SubsystemVendorID and SubsystemID are registered through `aws ec2 fpgaImageCreate` command to reserve the PCIe IDs of the CL for mapping of the device into an F1 instance when the AFI is loaded.  These signals should not be reset with any asynchronous reset (must be constant, or driven from flops that are not reset)

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

### Virtual LED/DIP

There are virtual LED/DIP switches that can be used to control/monitor CL logic.  There are 16 LEDs and 16 DIP Switches.  Registers exposed to the Management PF are used to control/monitor the LED/DIP Switches.

vLED - There are 16 virtual LEDs that can be driven from the CL logic to the SH (cl_sh_status_vled[15:0]).  The value of these signals can be read by S/W in the Instance.  An API is also provided through AWS Management Software.

vDIP - There are 16 virtual DIP switches that drive from the SH to the CL logic (sh_cl_status_vdip[15:0]).  These can be used to control logic in the CL.  The value of these signals can be written/read by S/W in the instance.  An API is also provided through AWS Management Software.

### DMA

There is an integrated DMA controller inside the Shell.  The DMA controller can perform efficient bulk data moves between the Instance and the CL logic.  Please refer to TBD for more information on the integrated DMA controller.


