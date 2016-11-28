
#**AWS EC2 FPGA Development Kit r1.0.0**

##**_Overview_**:

This is an initial release for AWS EC2 FPGA Development Kit. The kit comes with HDK(hardware development kit) and SDK(software development kit). Below is the list of features included in this initial release. More details about these features can be found in the customer logic spec located at the link below (link to be included once the final spec is ready). 

*   AWS EC2 FPGA platform feature list:

    *    VU9P architecture support.
    *    Interfaces available for Customer Logic(CL):
          *    One x16 PCIe Gen 3 Interface.
          *    Four DDR4 RDIMM interfaces (with ECC).
               *    AXI4 protocol support on all interfaces.
    *  	250 MHz base clock and asynchronous reset provided to Customer Logic(CL).
    *    PCIE endpoint presentation to Customer Logic(CL).
         *    FPGA management physical function.
         *    User physical function.
         *    FLR interface for User physical function.
    *    PCIE interface between Shell(SH) and Customer Logic(CL).
         *    SH to CL inbound AXI4 interface.
         *    CL to SH outbound AXI4 interface.
         *    512 bit bus that supports 32-bit transactions on inbound and outbound transactions.
         *    128, 256 and 512 byte maximum payload size support.
         *    128, 256, 512, 1024, 2048 and 4096 maximum read request size support.
         *    AXI4 error handling.
         *    AxUSER bits implemented on address channels. 
    *    DDR interface for DOM0 stats.         

##**_Implementation Restrictions_**:

*    All PCIE AXI4 interfaces between Customer Logic(CL) and Shell(SH) must adhere to following restrictions:

    *    All PCIe transactions must adhere to the PCIe Exress base spec.
    *    4Kbyte Address boundary for all transactions(PCIe restriction).
    *    Multiple outstanding Read transactions with same ID not supported.
    *    Only 16 outstanding read transactions supported.
    *    PCIE extended tag not supported.
    *    Address must reflect the correct address of the transaction.
    *    WSTRB(write strobe) must reflect the appropriate valid bytes for writes. 

##**_License Requirements_**:

The HDK and SDK in the development kit have different licenses. SDK is licensed under open source Apache license and HDK is licensed under Amazon Software License. Please refer to LICENSE.txt in aws/aws-fpga/sdk and aws/aws-fpga/hdk sections for more information.

##**_What's new_**?

This section will include any new features added in the future releases.

##**_Bug Fixes_**:

This section will include any bug fixes in the future releases.

##**_Known Issues_**:

This initial release will have following limitations.

*    No HMC memory interface support for Customer Logic(CL).
*    No FPGA to FPGA serial link support.
*    No MSIX interrupt support in Shell(SH).

