# F2 Clock Recipes User Guide

## Table of Content

- [F2 Clock Recipes User Guide](#f2-clock-recipes-user-guide)
  - [Table of Content](#table-of-content)
  - [Introduction](#introduction)
  - [F2 Clock Recipe Table](#f2-clock-recipe-table)
  - [How to Specify Clock Recipe During Build Time](#how-to-specify-clock-recipe-during-build-time)
  - [How to Dynamically Configure Clocks during Runtime](#how-to-dynamically-configure-clocks-during-runtime)
  - [Clock Consideration When Porting CL Designs from F1 into F2](#clock-consideration-when-porting-cl-designs-from-f1-into-f2)
  - [References](#references)

## Introduction

F2 Shell offers two clocks - `clk_main_a0` and `clk_hbm_ref` to the CL. This is different from F1 Shell, which offers total of 8 clocks from Shell to the CL as described in [F1 Shell Interface Spec](https://github.com/aws/aws-fpga/blob/master/hdk/docs/AWS_Shell_Interface_Specification.md#clocks). Offering fewer clocks from the Shell to CL is beneficial because it does not lock up the routing resources for customers who do not require all the clocks from Shell.

The `clk_main_a0` defaults to 250MHz. Dynamic reconfiguration of the frequency for `clk_main_a0` is currently NOT supported. However, this will be supported in future.

The `clk_hbm_ref` is a fixed frequency 100MHz clock required for the HBM IP to clock the APB interface.

F2 Developer Kit provides a clocking IP [AWS_CLK_GEN](./AWS_CLK_GEN_spec.md) for customers who desire to have same clocks and clock recipe support as F1. [Table](./Clock_Recipes_User_Guide.md#f2-clock-recipe-table) shows the clock recipes supported in F2.

## F2 Clock Recipe Table

| **Clock Group A**         |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
|---------------------------|------------------|------------------|------------------|------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| **Recipe Number**         | **clk_main_a0**  | **clk_extra_a1** | **clk_extra_a2** | **clk_extra_a3** | **Notes**                                                                                                                                                                                                                         |
| A0                        |              250 |             62.5 |            187.5 |              250 | AWS_CLK_GEN is not required in the CL design for clk_main_a0 recipes. clk_extra_a0/a1/a2 clocks require AWS_CLK_GEN block instantiated in CL design.                                                                              |
| A1                        |              250 |              125 |              375 |              500 |                                                                                                                                                                                                                                   |
| A2                        |              250 |           15.625 |              125 |             62.5 |                                                                                                                                                                                                                                   |
|                           |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Clock Group B**         |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Recipe Number**         | **clk_extra_b0** | **clk_extra_b1** |                  |                  | **Notes**                                                                                                                                                                                                                         |
| B0                        |              250 |              125 |                  |                  | clk_extra_b0/b1 require AWS_CLK_GEN block instantiated in the CL design.                                                                                                                                                          |
| B1                        |              125 |             62.5 |                  |                  |                                                                                                                                                                                                                                   |
| B2                        |              450 |              225 |                  |                  |                                                                                                                                                                                                                                   |
| B3                        |              250 |             62.5 |                  |                  |                                                                                                                                                                                                                                   |
| B4                        |              300 |               75 |                  |                  |                                                                                                                                                                                                                                   |
| B5                        |              400 |              100 |                  |                  |                                                                                                                                                                                                                                   |
|                           |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Clock Group C**         |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Recipe Number**         | **clk_extra_c0** | **clk_extra_c1** |                  |                  | **Notes**                                                                                                                                                                                                                         |
| C0                        |              300 |              400 |                  |                  | clk_extra_c0/c1 require AWS_CLK_GEN block instantiated in the CL design.                                                                                                                                                          |
| C1                        |              150 |              200 |                  |                  |                                                                                                                                                                                                                                   |
| C2                        |               75 |              100 |                  |                  |                                                                                                                                                                                                                                   |
| C3                        |              200 |          266.667 |                  |                  |                                                                                                                                                                                                                                   |
|                           |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Clock Group HBM**       |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Recipe Number**         | **clk_hbm_axi**  |                  |                  |                  | **NOTES**                                                                                                                                                                                                                         |
| H0                        |              250 |                  |                  |                  | clk_hbm_axi requires AWS_CLK_GEN block instantiated in the CL design. The clk_hbm_axi is used to clock the AXI interface of HBM IP. This clock is not available in F1.                                                            |
| H1                        |              125 |                  |                  |                  |                                                                                                                                                                                                                                   |
| H2                        |              450 |                  |                  |                  |                                                                                                                                                                                                                                   |
| H3                        |              300 |                  |                  |                  |                                                                                                                                                                                                                                   |
| H4                        |              400 |                  |                  |                  |                                                                                                                                                                                                                                   |
|                           |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Reference Clock Group** |                  |                  |                  |                  |                                                                                                                                                                                                                                   |
| **Recipe Number**         | **clk_hbm_ref**  |                  |                  |                  | **Notes**                                                                                                                                                                                                                         |
| -                         |              100 |                  |                  |                  | Fixed frequency 100MHz reference clock from Shell for HBM.                                                                                                                                                                        |

**NOTE:** `clk_main_a0` supports A0, A1 and A2 clock recipes without requiring AWS_CLK_GEN IP instantiated in the CL design. All other clocks and their respective clock recipes require AWS_CLK_GEN IP instantiated in the CL design and interfaced to the SDA interface from the Shell. [CL_MEM_PERF](./../cl/examples/cl_mem_perf/design/cl_mem_perf.sv) demonstrates how [AWS_CLK_GEN](./../common/lib/aws_clk_gen.sv) is integrated into CL design.

## How to Specify Clock Recipe During Build Time

Developers who wish to build CL design for a specific clock frequency defined in the [F2 Clock Recipe Table](./Clock_Recipes_User_Guide.md#f2-clock-recipe-table) can do so by passing the following arguments at the time of CL builds. Specifying clock recipe at the time of build, automatically adjusts the design clock constraints enabling the Vivado tool to close timing of CL based on chosen clock frequency.

For example, command below shows CL_MEM_PERF built using user specified clock recipes:

```bash
cd $CL_DIR/build/scripts/
./aws_build_dcp_from_cl.py --cl=cl_mem_perf --clock_recipe_a=A0 --clock_recipe_b=B3 --clock_recipe_c=C3 --clock_recipe_hbm=H4
```

When the clock_recipe switch is not explicitly specified, `aws_build_dcp_from_cl.py` defaults to `--clock_recipe_a=A1 --clock_recipe_b=B2 --clock_recipe_c=C0 --clock_recipe_hbm=H2`

**NOTE:** If AWS_CLK_GEN IP is not instantiated in the CL design, the recipes for AWS_CLK_GEN clocks will be ignored. Users may see CRITICAL WARNING related to missing AWS_CLK_GEN block during builds.

## How to Dynamically Configure Clocks during Runtime

Support for SW API to do clock frequency dynamic configuration is available using the `fpga-load-clkgen-dynamic` and `fpga-load-clkgen-recipe` command line interfaces detailed in [Amazon FPGA Image (AFI) Management Tools](../../sdk/userspace/fpga_mgmt_tools/README.md).

## Clock Consideration When Porting CL Designs from F1 into F2

1. The `clk_main_a0` is now fixed at 250MHz. It does not support clock recipes or dynamic frequecny reconfiguration. However, the will be supported in future.

2. F1 designs that relied on additional clocks such as `clk_extra_*` will now have two options in F2:

    a. Customers can instantiate required number of MMCMs in their CL design to meet the clocking requirement.

    b. Alternately, customers can instantiate [AWS_CLK_GEN](./../common/lib/aws_clk_gen.sv) IP in their CL which offers same set of clocks from F1, in addition to `clk_hbm_axi` for HBM clocking. AWS provides [SW APIs](./../../sdk/userspace/fpga_libs/fpga_clkgen/fpga_clkgen_utils.c) to simplify clock configuration for the user application.

3. F2 supports same clock recipe build switches as F1 to simplify porting of F1 designs into F2.

## References

[F1 Dynamic Clock Configuration](https://github.com/aws/aws-fpga/blob/master/hdk/docs/dynamic_clock_config.md)
