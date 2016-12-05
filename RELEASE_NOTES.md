
# AWS EC2 FPGA HDK+SDK Release notes

# Release 1.0.0

## Content

This is first public release for AWS EC2 FPGA Development Kit. The kit comes with HDK(Hardware Development Kit) and SDK(Software Development Kit). Below is the list of features included in this  release. More details about these features can be found in ![AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)

*   AWS EC2 FPGA platform feature list:
    *    Xilinx UltraScale+ VU9P
    *    Interfaces available for Custom Logic(CL):
          *    One x16 PCIe Gen 3 Interface
          *    Four DDR4 RDIMM interfaces (with ECC)
               *    AXI4 protocol support on all interfaces
    *  	250 MHz base clock and asynchronous reset provided to Custom Logic(CL)
    *    PCIE endpoint presentation to Custom Logic(CL)
         *    Management PF (physical function)
         *    Application PF
         *    FLR interface for Application PF
    *    PCIE interface between Shell(SH) and Custom Logic(CL).
         *    SH to CL inbound AXI4 interface.
         *    CL to SH outbound AXI4 interface.
         *    512 bit bus that supports 32-bit transactions on inbound and outbound transactions
         *    Maximum payload size set by the Shell
         *    Maximum read request size set by the Shell
         *    AXI4 error handling
         *    Proprietary AxUSER bits implemented on address channels: please refer to ![AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)        

## Implementation Restrictions

*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
    *    All PCIe transactions must adhere to the PCIe Exress base spec.
    *    4Kbyte Address boundary for all transactions(PCIe restriction).
    *    Multiple outstanding outbound PCIe Read transactions with same ID not supported.
    *    PCIE extended tag not supported, so read-request is limited to 32 outstanding.
    *    Address must match DoubleWord(DW) address of the transaction.
    *    WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
    *    Only Increment burst type is supported.
    *    AXI lock, memory type, protection type, Quality of service and Region identifier are not supported.

## Unsupported Features (Planned for future releases)

* DMA Engine is not included with the current version of the Shell
* Interrupts are not supported
* Build flow limited to RTL/Verilog source files
* HLS and OpenCL build flow not included in this HDK release
* ChipScope
* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over the 400Gbps Ring for F1.16xl
* Customizable PCIe DeviceID/VendorID
* Capability to remove some of the DRAM interface controllers from the CL
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence RTL simulations tools
* Synopsys RTL simulations tools
* Xilinx SDAccel development environment
* Additional metric counters for FPGA management tools

## Supported Tools and Environment

* The HDK and SDK are designed for **Linux** environment and has not been tested on other platforms.
* First install of AWS FPGA SDK requires having gcc installed in the instance server. If that's not available, try `sudo yum update && sudo yum group install "Development Tools"`
* The HDK build step requires having Xilinx's Vivado tool and Vivado License Management running
* Vivado License need to support VU9p ES1 FPGA
* Vivado License need to support encryption
* This release tested and validated with Vivado 2016.3
* Vivado XSIM RTL simulator supported by the HDK
* MentorGraphic's Questa RTL simulator supported by the HDK (but requires a purchase of separate license from MentorGraphics)

## License Requirements

The HDK and SDK in the development kit have different licenses. SDK is licensed under open source Apache license and HDK is licensed under Amazon Software License. Please refer to [HDK License](./hdk/LICENSE.txt) and [SDK License](./sdk/LICENSE.txt).

## What's new

This section will include any new features added in the future releases.

## Bug Fixes

This section will include any bug fixes in the future releases. Please use [HDK Bug](https://github.com/aws/aws-fpga/issues/16) and [SDK Bug](https://github.com/aws/aws-fpga/issues/17) to file bugs for HDK and SDK respectively and use [HDK Feature](https://github.com/aws/aws-fpga/issues/18) and [SDK Feature](https://github.com/aws/aws-fpga/issues/19) to file feature requests for HDK and SDK respectively. For any other general purpose requests, please use [F1 FPGA general support](https://github.com/aws/aws-fpga/issues/20).

## Known Issues

This section will include any known issues in the future releases.


