
# AWS EC2 FPGA HDK+SDK Errata

## Shell v1.4 (04261818)
[Shell\_04261818_Errata](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK
* Multiple SDE instances per CL is not supported in this release. Support is planned for a future release.
* DRAM Data retention is not supported for CL designs with less than 4 DDRs enabled
* Combinatorial loops in CL designs are not supported.  
* Connecting one of the clocks provided from the shell (clk_main_a0, clk_extra_a1, etc...) directly to a BUFG in the CL is not supported by the Xilinx tools and may result in a non-functional clock. To workaround this limitation, it is recommended to use an MMCM to feed the BUFG (clk_from_shell -> MMCM -> BUFG).

### 2019.1 
* Vivado `compile_simlib` command fails to generate the following verilog IP libraries for the following simulators.

| Library(verilog) | Simulator |
|---|---|
| `sync_ip` | Cadence IES |
| `hdmi_gt_controller_v1_0_0` | Synopsys VCS |
* We are working with Xilinx to provide a fix for these.

## SDK

## SDAccel (For additional restrictions see [SDAccel ERRATA](./SDAccel/ERRATA.md))
* Virtual Ethernet is not supported when using SDAccel
* DRAM Data retention is not supported for kernels that provision less than 4 DDRs
* Combinatorial loops in CL designs are not supported.
   
