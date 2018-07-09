# AWS EC2 FPGA Shell Errata (04261818)

## Implementation Restrictions
* PCIE AXI4 interfaces between Custom Logic(CL) and Shell(SH) have following restrictions:
  * All PCIe transactions must adhere to the PCIe Express base spec
  * 4Kbyte Address boundary for all transactions(PCIe restriction)
  * Multiple outstanding outbound PCIe Read transactions with same ID not supported
  * PCIE extended tag not supported, so read-request is limited to 32 outstanding
  * Address must match DoubleWord(DW) address of the transaction
  * WSTRB(write strobe) must reflect appropriate valid bytes for AXI write beats
  * Only Increment burst type is supported
  * AXI lock, memory type, protection type, Quality of service and Region identifier are not supported
  * Transactions from the Shell to CL must complete within the timeout period to avoid transaction termination by the Shell
  * DMA transactions from the Shell to CL must complete within the timeout period to avoid transaction termination and invalid data returned for the DMA transaction
  * PCIM and DMA-PCIS AXI-4 interfaces do not support AxSIZE other than 3'b110 (64B)

* AFI must be re-loaded after an instance re-boot.

## Unsupported Features (Planned for future releases)
* FPGA to FPGA communication over PCIe for F1.16xl
* FPGA to FPGA over serial ring links for F1.16xl
* Aurora and Reliable Aurora modules for the FPGA-to-FPGA 
* Preserving the DRAM content between different AFI loads (by the same running instance)
* Cadence Xcelium simulations tools

## Known Bugs/Issues
* **sh_cl_ddr_is_ready[2:0]** outputs of sh_ddr.sv are not synchronized to clk_main_a0.  Developers should synchronize these signals to clk_main_a0.


