# Small Shell Migration Document


This document describes the changes required when migrating your design from XDMA F1.X.1.4 to Small Shell F1.S.1.0. It is important to understand the key differences between F1.S.1.0 and shell F1.X.1.4  before migration.

| Small Shell -  F1.S.1.0	                                        |                                   XDMA Shell  F1.X.1.4
|-----------------------------------------------------------|------------------------------------------------------------------------------------|
|Customers implement DMA in CL (if required) or can also use [SDE](../cl/examples/cl_sde/README.md) or peek and poke to achieve data transfer between host and FPGA                         | DMA is part of the shell                                                         |
|Supports only vivado 2020.2	                              | Supports a variety of tool versions as mentioned in [README](../../README.md) page of aws-fpga repo |
|Occupies 14 Clock Regions	                              | Occupies 20 Clock Regions                                              |
|Supports 64 Outstanding Transactions on PCIM Reads, resulting in 5-20% improvement in FPGA<->Host performance |	Supports only 16 Outstanding Transactions on PCIM Reads |
|Supports 32 outstanding transactions on PCIM writes        | Supports 8 outstanding transactions on PCIM writes |
|Only interrupts of XDMA are supported                      | Full XDMA support (including DMA) |
|Vitis/SDAccel not supported                                | SDAccel/Vitis flows supported |
#### Table 1 Comparison of features between shells F1.S.1.0 and F1.X.1.4


Migration from shell F1.X.1.4 to small shell F1.S.1.0 should consider design changes as well as work flow changes that might be required. Migration from shell F1.X.1.4 to small shell F1.S.1.0 is not recommended to customers using Vitis/SDAccel since small shell F1.S.1.0 does not support Vitis/SDAccel. Migration to small shell F1.S.1.0 requires design changes and work flow changes and are described in detail in corresponding sections.

## Design Changes
There are differences in design features between small shell F1.S.1.0 and shell F1.X.1.4 as listed in Table 1. One of the primary differences that might significantly impact shell F1.X.1.4 customers is that small shell does not have in buit DMA engine and customers are required to implement DMA in CL region of the design. If the existing design uses DMA feature of shell F1.X.1.4, migration to small shell would involve customers either implementing their own DMA engine in CL or utilizing [SDE](../cl/examples/cl_sde/README.md) or peek and poke to achieve data transfer between host and FPGA, and therefore might be a non trivial update to their existing design(s) and have to carefully analyze the benefits from small shell Vs added cost of custom DMA implementation.

Small shell has smaller footprint in bottom SLR compared to shell F1.X.1.4. Customers need to update their Place & Route constraints to reclaim the extra area available to CL from the bottom SLR (from reduced small shell size). Please refer to cl_dram_dma [xdc](../cl/examples/cl_dram_dma/build/constraints/cl_pnr_user.xdc) #L64 example for reference on updating the constraint.
For customers who follow manual placement of the blocks for optimal performance/routing congestion, we recommend to use Table2, showing placement changes, to update CL pblock constraints to optimize your design

| INTERFACE | F1.S.1.0 SLR | F1.X.1.4 SLR |
|-----------|---------------|---------------|
| CL_SH_DDR |MID SLR  | MID SLR |
| BAR1 | MID SLR  | MID SLR |
| PCIM | BOTTOM SLR  | MID SLR |
| PCIS | MID SLR | BOTTOM SLR |
| OCL | MID SLR | BOTTOM SLR |
| DDR STAT3 | MID/BOTTOM SLR  | BOTTOM SLR |
| DDR STAT0  | MID/BOTTOM SLR | MID/BOTTOM SLR |
| DDR STAT1 | MID/BOTTOM SLR | MID/BOTTOM SLR |
| SDA | MID SLR  | MID/BOTTOM SLR|
#### Table2 Interface placement changes between shell F1.X.1.4 and shell F1.S.1.0


## Work flow changes
Small shell is released under small_shell branch and therefore customers are required to clone the small_shell branch for their workflow using
```git clone -b small_shell https://github.com/aws/aws-fpga.git```

The HDK build scripts in small_shell branch are implemented to reflect small_shell floorplan and newer Vivado tools. It’s strongly recommended users use these scripts. Users who have already customized shell F1.X.1.4 scripts should diff or compare those with the small_shell scripts and be sure to incorporate the changes into their scripts

1. Upgrade Vivado Tools to version 2020.2. Developer AMI based workflow requires [FPGA DEVELOPER AMI 1.10.0 or later](../../README.md#fpga-developer-ami)

2. Except for the addition of DDR-C awuser/aruser ports, the Shell-CL interface definition did not change between Small Shell and F1.X.1.4 Shell. Customers need to tie off these ports to zero and are not currently used (These are for future use)
3. AWS recommends customers to place their DMA Engine in Bottom SLR because the PCIM interface between Shell<->CL is now moved to Bottom SLR
4. All Xilinx IP in your CL must to be upgraded to 2020.2 or later version.
5. [ILA cores](../common/shell_v04182104/design/ip/cl_debug_bridge) need to be upgraded to 2020.2 or later
     Please refer to the [cl_dram_dma](../cl/examples/cl_dram_dma/design/cl_dram_dma.sv) example for ILA hookup on PCIS interface.
