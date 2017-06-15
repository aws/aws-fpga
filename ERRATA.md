
# AWS EC2 FPGA HDK+SDK Errata

Any items in this release marked as WIP (Work-in-progress) or NA (Not avaiable yet) are not currently supported by the 1.2.0 release.

## Integrated DMA in Beta Release. AWS Shell now includes DMA capabilities on behalf of the CL
* The DMA bus toward the CL is multiplexed over sh_cl_dma_pcis AXI4 interface so the same address space can be accessed via DMA or directly via PCIe AppPF BAR4 
* DMA usage is covered in the new [CL_DRAM_DMA example](./hdk/cl/examples/cl_dram_dma) RTL verification/simulation and Software 
* A corresponding AWS Elastic DMA ([EDMA](./sdk/linux_kernel_drivers/edma)) driver is provided.
* [EDMA Installation Readme](./sdk/linux_kernel_drivers/edma/edma_install.md) provides installation and usage guidlines
* The initial release supports a single queue in each direction
* DMA support is in Beta stage with a known issue for DMA READ transactions that cross 4K address boundaries.  See [Kernel_Drivers_README](./sdk/linux_kernel_drivers/edma/README.md) for more information on restrictions for this releas

## Implementation Restrictions

*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
    *    All PCIe transactions must adhere to the PCIe Exress base spec
    *    4Kbyte Address boundary for all transactions(PCIe restriction)
    *    Multiple outstanding outbound PCIe Read transactions with same ID not supported
    *    PCIE extended tag not supported, so read-request is limited to 32 outstanding
    *    Address must match DoubleWord(DW) address of the transaction
    *    WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
    *    Only Increment burst type is supported
    *    AXI lock, memory type, protection type, Quality of service and Region identifier are not supported
*    PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) must follow the AMBA AXI4 protocol specification.  
    *    Prior to running on F1 instance, it is highly recommended that developers run logic simulations with the ARM or Xilinx AXI4 protocol checker  


## Unsupported Features (Planned for future releases)

* PCI-M AXI interface is not supported in this release.
* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over the 400Gbps Ring for F1.16xl
* Aurora and Reliabile Aurora modules for the FPGA-to-FPGA 
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence RTL simulations tools
* All AXI-4 interfaces (PCIM, DDR4) do not support AxSIZE other than 0b110 (64B)

## Known Bugs/Issues

* The PCI-M AXI interface is not supported in this release.  
    * The interface is included in cl_ports.vh and required in a CL design, but not enabled for functional use

* The integrated DMA function is in Beta stage.  Known issues: 
    * DMA READ addresses crossing 4K page boundaries.  The failure can be triggered by READ transfers that start on an address other than 4K aligned AND cross the 4K page boundary.  READ transfers that do not cross the 4K boundary OR transfers that start at the beginning of a 4K page and greater than 4K size are not susceptible to the error.  WRITE transfers are not affected by this issue Developers should use 4K aligned address boundaries on any READ transfer that can cross a 4K boundary to avoid the issue. 
    * Transfer sizes of 8KB or less are supported with the integrated DMA engine for this revision of the Shell.  Integrated DMA with large transfer sizes (16KB or greater) can cause timeouts between the Shell and CL if the Shell can’t respond with all data before the timeout.  Please see documentation on how to [detect a timeout has occured](./hdk/docs/HOWTO_detect_shell_timeout.md)



