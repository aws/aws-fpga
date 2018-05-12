
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
* Questa 10.6b simulations tools have not been tested.  Xilinx 2017.4 tools only support Questa 10.6b.   
* PCIM and DMA-PCIS AXI-4 interfaces do not support AxSIZE other than 3'b110 (64B)

## Known Bugs/Issues

* AXI-L Interface ordering - The v071417d3 shell has an issues that impacts transaction ordering on the AXI-L interfaces (BAR1, OCL, SDA) only.  The Shell should preserve PCIe ordering rules on these interfaces, but there is an issue where a read request may pass a previous write request.  The shell terminates a write when the data is transferred on the W channel (WVALID/WREADY) rather than wait for the response on the B channel.  A CL workaround for this issue is to backpressure reads (deassert ARREADY) when there are any writes pending.
* Linux kernel 3.10.0-862.2.3.el7.x86_64.  By default, the AWS Developer AMI GUI setup script updates the kernel version. We have provided a patch to prevent kernel updates during GUI setup. Instead of running the setup_gui.sh as documented/included within the developer AMI, please use the patched script as shown below:
$curl https://s3.amazonaws.com/aws-fpga-developer-ami/1.4.0/Scripts/setup_gui.sh -o /home/centos/src/scripts/setup_gui.sh
$/home/centos/src/scripts/setup_gui.sh
 
