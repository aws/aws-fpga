# AWS EC2 FPGA HDK+SDK Release Notes

## Small Shell F1.S.1.0 Release 1.6.0
* Added AWS Small Shell F1.S.1.0 (v04182104) which is 30% smaller in size than the F1.X.1.4 Shell. Smaller physical footprint of the Shell increases the available resources to the CL.
* Small shell improves FPGA <-> Host Performance by 5-20% due to increase in Number of PCIM Outstanding Read Transactions to 64. This allows CL to issue more number of read requests over PCIM and therefore achieving higher performance. This results in ~20% increase in performance for smaller read request lengths = 0x1 and 0x3; and ~5% increase in performance for request lengths = 0x7, 0xF, 0x1F and 0x3F.
* Small Shell also reduces routing congestion and ease timing closure because of additional resources in the Bottom SLR.
* Small Shell does not include DMA capability. Customers should implement their own DMA engine in the CL, or use [SDE IP](sdk/apps/virtual-ethernet/doc/SDE_HW_Guide.md) provided in the Developer Kit.


