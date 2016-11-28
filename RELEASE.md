
#**AWS EC2 FPGA Development Kit r1.0.0**

##**_Overview_**:

This is an initial release for AWS EC2 FPGA Development Kit. 

*   This initial release AWS EC2 FPGA platform comes with the features below:

    *    Interfaces available for Customer Logic(CL):
          *    One x16 PCIe Gen 3 Interface.
          *    Four DDR4 RDIMM interfaces (with ECC).
               *    AXI4 protocol support on all interfaces.
    *  	 250 MHz clock and asynchronous reset provided to Customer Logic(CL).
    *    PCIE endpoint presentation to Customer Logic(CL).
         *    FPGA management physical function
         *    User physical function
         *    FLR interface for User physical function
    *    PCIE interface between Shell(SH) and Customer Logic(CL).
         *    SH to CL inbound AXI4 interface.
         *    CL to SH outbound AXI4 interface.
         *    512 bit bus that supports 32-bit transactions on inbound and outbound transactions.
         *    128, 256 and 512 byte max payload size support.
         *    128, 256, 512, 1024, 2048 and 4096 max read request size support.
         *    AXI4 error handling.
         *    Upto 48 vectors of MSIX interface support.
         *    AxUSER bits implemented on address channels. 

##**_Implementation Restrictions_**:

*    All PCIE AXI4 interfaces between Customer Logic(CL) and Shell(SH) must adhere to following restrictions:

     *     All PCIe transactions must adhere to the PCIe Byte Enable rules (see PCI Express Base specification).
     *     Transfers must not cross a 4Kbyte Address boundary (PCIe restriction).
     *     Transfers must not violate Max Payload Size.
     *     Read requests must not violate Max Read Request Size.
     *     Multiple outstanding Read transactions with same ID not supported.
     *     Only 5-bit ARID is supported(32 outstanding read transactions).
     *     PCIE extended tag not supported.
     *     Address must reflect the correct DW address of the transfer.
     *     WSTRB(write strobe) must be correct and reflect the appropriate valid bytes for writes. 

##**_License Requirements_**:

This section will include license requirements.

##**_What's new_**?

This section will include any new features added in the future releases.

##**_Bug Fixes_**:

This section will include any bug fixes in the future releases.

##**_Known Issues_**:
This section will include known issues.


