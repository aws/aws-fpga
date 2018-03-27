
# AWS EC2 FPGA HDK+SDK Errata


## Release 1.3.X
### Implementation Restrictions
*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
    *    All PCIe transactions must adhere to the PCIe Express base spec
    *    4Kbyte Address boundary for all transactions(PCIe restriction)
    *    Multiple outstanding outbound PCIe Read transactions with same ID not supported
    *    PCIE extended tag not supported, so read-request is limited to 32 outstanding
    *    Address must match DoubleWord(DW) address of the transaction
    *    WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
    *    Only Increment burst type is supported
    *    AXI lock, memory type, protection type, Quality of service and Region identifier are not supported
    *    Transactions from the Shell to CL must complete within the timeout period to avoid transaction termination by the Shell
    *    DMA transactions from the Shell to CL must complete within the timeout period to avoid transaction termination and invalid data returned for the DMA transaction

## Unsupported Features (Planned for future releases)
* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over the 400Gbps Ring for F1.16xl
* Aurora and Reliable Aurora modules for the FPGA-to-FPGA 
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence Xcelium simulations tools
* PCIM and DMA-PCIS AXI-4 interfaces do not support AxSIZE other than 3'b110 (64B)

## Known Bugs/Issues
* F1 CL designs using the v1.3 Shell must treat all clocks within the same group as asynchronous.  For example:  If using clk_main_a1, clk_extra_a1, clk_extra_a2, and clk_extra_a3 they need to be asynchronous.  See [AWS Shell Interface Specification](./hdk/docs/AWS_Shell_Interface_Specification.md)
* The API fpga-load-local-image, has a bug in the error messaging which does not indicate a PCI ID mismatch occurred.  The PCI ID’s listed in the AFI manifest when an AFI is submitted to the CreateFpgaImage api (Vendor ID, Device ID, SubSystem ID, or SubSystem Vendor ID) should match the actual values in the submitted DCP. If there is a mismatch between the manifest IDs and the actual device ID, calling fpga-load-local-image on the AFI should report back load-failed (error 7), with a sub-error indicating there is a device ID mismatch. However, fpga-load-local-image does not report the sub-error, leaving no description as to why the load has failed.  Until this issue has been fixed, if you experience an AFI load-failed when loading the AFI,  double check the device IDs in the submitted manifest match the device IDs in the DCP.

