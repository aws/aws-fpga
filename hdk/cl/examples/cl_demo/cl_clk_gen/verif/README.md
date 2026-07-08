# CL_CLK_GEN Simulation

## Overview

This readme provides information about the simulation environment for the `cl_clk_gen` example. For more details about the overall HDK simulation environment refer to the [RTL Simulation Guide for HDK Design Flow](https://github.com/aws/aws-fpga/blob/f2/hdk/docs/RTL_Simulation_Guide_for_HDK_Design_Flow.md).

Simulations can be run from `$CL_DIR/verif/scripts/`:

```bash
make test_null                    # Runs with XSIM by default
make test_clk_adder

make test_clk_adder VCS=1         # Run with VCS
make test_clk_adder QUESTA=1      # Run with Questa
```

## SystemVerilog Tests

| Test | Description |
|------|-------------|
| `test_null` | Powers up with Clock Recipe A2, de-asserts aws_clk_gen resets, verifies MMCM locks |
| `test_clk_adder` | Programs Clock Recipe A2, then performs adder operations across the clock domain crossing (clk_main_a0 to clk_extra_a1) |

Both tests use helper tasks from `aws_clk_gen_utils.svh` for MMCM reset management.
