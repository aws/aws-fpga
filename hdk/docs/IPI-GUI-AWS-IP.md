# AWS FPGA IP for IP Integrator Overview

## Table of Contents

- [AWS FPGA IP for IP Integrator Overview](#aws-fpga-ip-for-ip-integrator-overview)
  - [Table of Contents](#table-of-contents)
  - [AWS IP Overview](#aws-ip-overview)
  - [Enable IP Interfaces](#enable-ip-interfaces)
  - [Clock Signals](#clock-signals)
  - [CL Partition ID](#cl-partition-id)
  - [Advanced](#advanced)

## AWS IP Overview

The AWS IP serves as a central component in the IP Integrator (IPI) designs, providing essential AXI interfaces (OCL, PCIS and PCIM) for Host-FPGA communication, configurable clock management through predefined recipes, and auxiliary signal ports like VLED/VDIP. It enables seamless integration between CL designs and the F2 Shell.

To configure the AWS IP, double-click the AWS IP block in the 'Block Diagram'. The 'Re-customize IP' GUI displays four configuration categories.

## Enable IP Interfaces

Select the box to enable desired interfaces. The block diagram updates automatically to show enabled interfaces, ports, and clocks

For details about the shell interface, see [AWS Shell Interface Specification](./AWS_Shell_Interface_Specification.md).

![Diagram](./../../docs-rtd/source/_static/hlx_images/aws_ip_interfaces.png)

## Clock Signals

Review the [Clock Recipes User Guide](./Clock_Recipes_User_Guide.md) to determine the number of clocks needed for Groups A, B, and C, and select appropriate clock recipes for all CL clocks.

![Diagram](./../../docs-rtd/source/_static/hlx_images/aws_ip_clocks.png)

***NOTE***: `clk_main_a0_out` is a required clock and cannot be disabled.

***NOTE***: You must select 'Enable Ports for HBM in CL' in the 'Enable IP Interfaces' tab to see HBM AXI clock recipe options.

## CL Partition ID

The PCIe Vendor ID, Device ID, Subsystem Vendor ID and Subsystem ID can be configured. For now these default values typically match AWS examples and shouldn't be modified at this time.

![Diagram](./../../docs-rtd/source/_static/hlx_images/aws_ip_ids.png)

## Advanced

Pipeline stages configuration:

- Range: 1-4 pipeline stages
- Applies to the `sh_cl_ddr_stat_` interface for DDR in the CL
- Selection depends on design size and complexity
