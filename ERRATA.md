
# AWS EC2 FPGA HDK+SDK Errata

## Shell F1.S.1.0 (v04182104)
[Shell F1.S.1.0 Errata](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK
* Multiple SDE instances per CL is not supported in this release. Support is planned for a future release.
* DRAM Data retention is not supported for CL designs with less than 4 DDRs enabled
* Combinatorial loops in CL designs are not supported.  
* Connecting one of the clocks provided from the shell (clk_main_a0, clk_extra_a1, etc...) directly to a BUFG in the CL is not supported by the Xilinx tools and may result in a non-functional clock. To workaround this limitation, it is recommended to use an MMCM to feed the BUFG (clk_from_shell -> MMCM -> BUFG). Please refer to [Xilinx AR# 73360](https://www.xilinx.com/support/answers/73360.html) for further details.

## HLx/IPI Flows
* HLx and IPI based flows are currently not supported in this shell

## Vitis
* Vitis and SDAccel workflows are not supported in this shell as this shell does not have a DMA engine
