
# AWS EC2 FPGA HDK+SDK Errata


## Preview 1.3.0 - Features that are not supported in preview.  These features will see additional updates.
* create-fpga-image 
* fpga-load-local-image 
* Improvements to URAM utilization 
* IP Integrator flow
* SDAccel


## Release 1.3.0 
### Implementation Restrictions
*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
    *    All PCIe transactions must adhere to the PCIe Exress base spec
    *    4Kbyte Address boundary for all transactions(PCIe restriction)
    *    Multiple outstanding outbound PCIe Read transactions with same ID not supported
    *    PCIE extended tag not supported, so read-request is limited to 32 outstanding
    *    Address must match DoubleWord(DW) address of the transaction
    *    WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
    *    Only Increment burst type is supported
    *    AXI lock, memory type, protection type, Quality of service and Region identifier are not supported

## Unsupported Features (Planned for future releases)
* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over the 400Gbps Ring for F1.16xl
* Aurora and Reliabile Aurora modules for the FPGA-to-FPGA 
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence RTL simulations tools
* All AXI-4 interfaces (PCIM, DDR4) do not support AxSIZE other than 0b110 (64B)

## Known Bugs/Issues


