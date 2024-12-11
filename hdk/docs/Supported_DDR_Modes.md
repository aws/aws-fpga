# Supported DDR configurations in [sh_ddr.sv](./../common/shell_stable/design/sh_ddr/sh_ddr.stub.sv)

## Table of Content

- [Supported DDR configurations in sh\_ddr.sv](#supported-ddr-configurations-in-sh_ddrsv)
  - [Table of Content](#table-of-content)
  - [Overview](#overview)
  - [Required RTL Modifications](#required-rtl-modifications)
  - [Required Verification Modifications](#required-verification-modifications)
  - [Required Build Script Modifications](#required-build-script-modifications)

## Overview

The [sh_ddr.sv](./../common/shell_stable/design/sh_ddr/sh_ddr.stub.sv) now supports following configurations for DDR Controller IPs:

- DDR Core for 64 GB DIMM.
- DDR Core for 64 GB DIMM with user-controlled Auto-Precharge mode. This feature allows user designs to issue DDR Auto-Precharge command by asserting `cl_sh_ddr_axi_awuser=1` or `cl_sh_ddr_axi_aruser=1` alongside their corresponding valid control signals. Please refer to [PG150-User Guide](https://www.xilinx.com/content/dam/xilinx/support/documents/ip_documentation/ultrascale_memory_ip/v1_4/pg150-ultrascale-memory-ip.pdf) for details on user-controlled (app_autoprecharge) Auto-Precharge mode.
- If DDR core is not required in the CL design, then users still have to instantiate `sh_ddr.sv` in top level CL, with parameter tied off to `.DDR_PRESENT(0)`. Failing to do so may result in errors during synthesis/implementation.

## Required RTL Modifications

[sh_ddr.sv](./../common/shell_stable/design/sh_ddr/sh_ddr.stub.sv) defaults to using 64 GB DDR core along with 64 GB DIMM model, and without user-controlled Auto-Precharge mode. Users are allowed to define one of the following macros in the top level of CL where `sh_ddr.sv` is instantiated. This will automatically pick up the desired DDR controller inside `sh_ddr.sv`. Supported macros are shown below:

- ``` `define USE_64GB_DDR_DIMM``` : This is 64GB DDR controller
- ``` `define USE_AP_64GB_DDR_DIMM``` : This is 64GB DDR controller with user-controlled Auto Precharge

For example, please refer to [cl_mem_perf](./../cl/examples/cl_mem_perf/design/cl_mem_perf.sv) which has ``` `define USE_AP_64GB_DDR_DIMM ``` macro to override sh_ddr.sv to use 64GB DDR core with user controlled Auto-Precharge mode.

## Required Verification Modifications

Users must pass the **same** macro as they defined in top level CL to simulate with a corresponding DIMM model.

```bash
export TEST_NAME=test_ddr

# To Run simulations with a 64 GB DDR DIMM
make TEST=${TEST_NAME} USE_64GB_DDR_DIMM=1

# To Run simulations with a 64 GB DDR DIMM and DDR core with user controlled auto-precharge mode
make TEST=${TEST_NAME} USE_AP_64GB_DDR_DIMM=1
```

:warning: The macros passed during sims must match with what is defined in the top level CL RTL file. Otherwise, users may risk running sims on unintended DIMM models, yielding inconsistent results.

## Required Build Script Modifications

AWS provides following DDR Core IPs as part of Vivado [cl_ip.xpr](./../common/ip/cl_ip/cl_ip.xpr) project. Users are required to enlist one of the following XCI files in the synthesis scripts, depending on the desired DDR configuration and macros defined:

| Macro definition in top level CL | Description                                                        | DDR XCI file to read in synthesis script |
|----------------------------------|--------------------------------------------------------------------|------------------------------------------|
| `define USE_64GB_DDR_DIMM        | 64 GB DDR core without user-controlled Auto-Precharge mode.         | `cl_ddr4.xci`                            |
| `define USE_AP_64GB_DDR_DIMM     | 64 GB DDR core with user-controlled Auto-Precharge mode.            | `cl_ddr4_64g_ap.xci`                     |

Alternately, users may choose to enlist all four DDR XCI files in their synthesis script. The Vivado tool automatically elaborates the correct DDR core based on the macro defined in top level CL file. For example, [CL_MEM_PERF synthesis script](./../cl/examples/cl_mem_perf/build/scripts/synth_cl_mem_perf.tcl) reads in all four XCI files but elaborates the desired DDR core at the time of synthesis based on macro defined in [cl_mem_perf.sv](./../cl/examples/cl_mem_perf/design/cl_mem_perf.sv)
