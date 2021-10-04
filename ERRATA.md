
# AWS EC2 FPGA HDK+SDK Errata

## Shell Errata
Shell errata is [documented here](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK
* Multiple SDE instances per CL is not supported in this release. Support is planned for a future release.
* DRAM Data retention is not supported for CL designs with less than 4 DDRs enabled
* Combinatorial loops in CL designs are not supported.
  * We will display a `UNKNOWN_BITSTREAM_GENERATE_ERROR` on detection of a combinatorial loop in the CL design and an AFI will not be generated.
* Connecting one of the clocks provided from the shell (clk_main_a0, clk_extra_a1, etc...) directly to a BUFG in the CL is not supported by the Xilinx tools and may result in a non-functional clock. To workaround this limitation, it is recommended to use an MMCM to feed the BUFG (clk_from_shell -> MMCM -> BUFG). Please refer to [Xilinx AR# 73360](https://support.xilinx.com/s/article/73360?language=en_US) for further details.

### flop_ccf.sv bug

We have identified a bug in the `flop_ccf.sv` module that can potentially impact timing closure of designs. 
The module is instantiated in `sh_ddr.sv` and inadvertently introduces a timing path on the reset logic. 
Although there is no functional impact, it may increase Vivado tool’s effort in timing closure of design. 
There should be no functional impact from this bug if your design has already met timing. 
This bug is fixed in aws-fpga release v1.4.19

Q: Which designs does this bug affect?
A: This bug only affects designs that instantiate the sh_ddr module.

Q: How do I fix my design if I am affected by this bug?
A: Pull aws-fpga release v1.4.19 or later from the aws-fpga github and rebuild your cl design. 
The flop_ccf.sv files from the latest release that contain the fix are: [sh_ddr/synth/flop_ccf.sv](https://github.com/aws/aws-fpga/blob/master/hdk/common/shell_v04261818/design/sh_ddr/synth/flop_ccf.sv) & 
[sh_ddr/sim/flop_ccf.sv](https://github.com/aws/aws-fpga/blob/master/hdk/common/shell_v04261818/design/sh_ddr/sim/flop_ccf.sv)

### Xilinx Design Advisory for UltraScale/UltraScale+ DDR4/DDR3 IP - Memory IP Timing Exceptions (AR# 73068)
AWS EC2 F1 customers using the DDR4 IP in customer logic (HDK or SDAccel/Vitis designs) may be impacted by a recent design advisory from Xilinx.

AWS customers may experience hardware failures including: post calibration data errors and DQS gate tracking issues. The error condition is build dependent and errors would need to be detected on the first write/read access after a successful calibration to prevent further data corruption.

To detect if your build is impacted by this bug, AWS recommends all EC2 F1 customers utilizing the DDR4 IP in their designs should run a TCL script on the design checkpoint point (DCP) to check to determine if the design is susceptible to this issue. If the check passes, your design is safe to use as the hardware will function properly. 
If the check fails, the design is susceptible to the issue and will need to be regenerated using the same tool version with the AR 73068 patch. 
For designs under development, we recommend applying the patch to your on-premises tools or update to developer kit v1.4.15. 
For additional details, please refer to the [Xilinx Answer Record #73068](https://support.xilinx.com/s/article/73068?language=en_US)

We recommend using [Developer Kit Release v1.4.15a](https://github.com/aws/aws-fpga/releases/tag/v1.4.15a) or newer to allow for patching and fixing the DDR4 IP timing exception by re-generating the IP.

### 2019.1 
* Vivado `compile_simlib` command fails to generate the following verilog IP libraries for the following simulators.
* Please refer to the Xilinx Answer record for details.

| Library(verilog) | Simulator | Xilinx Answer Record | 
|---|---|---|
| `sync_ip` | Cadence IES | [AR72795](https://support.xilinx.com/s/article/72795?language=en_US) |
| `hdmi_gt_controller_v1_0_0` | Synopsys VCS | [AR72601](https://support.xilinx.com/s/article/72601?language=en_US) |

## SDK

## SDAccel (For additional restrictions see [SDAccel ERRATA](./SDAccel/ERRATA.md))
* Virtual Ethernet is not supported when using SDAccel
* DRAM Data retention is not supported for kernels that provision less than 4 DDRs
* Combinatorial loops in CL designs are not supported. 
