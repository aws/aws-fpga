
# AWS EC2 FPGA HDK+SDK Errata

## Shell v1.4 (04261818)
[Shell\_04261818_Errata](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK
* Multiple SDE instances per CL is not supported in this release.  Support planned for future release.
* DRAM Data retention is not supported for CL designs with less than 4 DDRs enabled
* Combinatorial loops in CL designs are not supported.
* [Automatic Traffic Generator (ATG)](./hdk/cl/examples/cl_dram_dma/design/cl_tst.sv) in SYNC mode does not wait for write response transaction before issuing read transactions. The fix for this issue is planned in a future release.

## SDK

## SDAccel (For additional restrictions see [SDAccel ERRATA](./SDAccel/ERRATA.md))
* Virtual Ethernet is not supported when using SDAccel
* DRAM Data retention is not supported for kernels that provision less than 4 DDRs
* Combinatorial loops in CL designs are not supported.
   
