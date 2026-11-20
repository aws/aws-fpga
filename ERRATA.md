
# F2 Developer Kit Errata

## Shell Errata

Shell errata is [documented here](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK

1. Address Aliasing Bug in AMD HBM IP with Custom Address Mapping in Vivado versions prior to 2025.1

   * Refer to [AMD Knowledge Article 000037624](https://adaptivesupport.amd.com/s/article/000037624?language=en_US) for details

   * For designs implementing HBM IP with Custom Address Mapping, Vivado 2025.1 or a newer version is required

2. CL simulation might show the following "error" message if the [CL clock generator](./hdk/docs/AWS_CLK_GEN_spec.md) is contained in the design. By default, the generator blocks all output clocks (except for `o_clk_main_a0`) and asserts all output resets. This behavior violates the built-in reset check in the [AXI SmartConnect IP](https://www.xilinx.com/products/intellectual-property/smartconnect.html#overview). This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # ** Error: [SmartConnect 500-33] s_sc_aresetn should be asserted for at least 16 cycles of m_sc_aclk. tb.card.fpga.CL.CL_HBM.HBM_PRESENT_EQ_1.AXI_CONVERTER_AXI4_AXI3.cl_axi_sc_1x1_i.smartconnect_0.inst.s00_nodes.s00_aw_node.inst.<protected>.<protected>
    ```

3. CL simulation might show the following "error" message. This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # Initializing memory from data in 'ddr4_ddr_10.mem'.
    #   Reading data in x8 and bl:8 mode (Change with 'config <4,8,16> <4,8>' in this file).
    #   'ddr4_ddr_10.mem' set write data width to x4.
    #   ERROR: Failed to write data burst length to 16. Only <4,8> are valid.
    ```

4. XSIM simulator does not support a cycle-accurate simulation model for the HBM IP. We’re observing significantly longer simulation times compared to VCS and Questa simulators. This is caused by the HBM BFM used in XSIM. Therefore, running HBM simulation using VCS or Questa is strongly recommended.

5. Simulation of the [HBM monitor interface](./hdk/docs/AWS_Shell_Interface_Specification.md#hbm-monitor-interface) is not supported in this release. The HBM IP always passes initialization and remains in an operating state for all tests. Simulation support for the HBM monitor will be added in a future release.

6. HBM simulation using XSIM requires a fix described in this [AMD Answer Record](https://adaptivesupport.amd.com/s/article/000035639?language=en_US).

7. Vivado 2025.1 introduces a `set_property DONT_TOUCH` to the HBM model that makes meeting
timing difficult in the implementation stage. AMD has responded to this issue on their AR, stating that it will be fixed in a future version of Vivado. [See here for more details](https://adaptivesupport.amd.com/s/article/000038502?language=en_US&t=1754923887312). All HDK CL examples have been updated to address this issue. Customers should follow this AR when creating their own designs.

8. The `cl_dram_hbm_dma` example has a known setup timing failure when built against XDMA Shell `0x10052623` with Vivado 2024.1. Use Vivado 2024.2 or later to build this example with the XDMA Shell.

## HLx

1. When executing the `aws::make_ipi` command in Vivado to set up the HLx IPI environment, the AWS IP instance may default to the name `f1_inst`. This is a known Vivado behavior and can be safely ignored. Users can rename this instance according to their preference.

## SDK

1. The following fpga_mgmt flags are not supported for F2:
   * `FPGA_CMD_FORCE_SHELL_RELOAD`
   * `FPGA_CMD_DRAM_DATA_RETENTION`
   * `FPGA_CMD_EXTENDED_METRICS_SIZE`

   These flags will cause a run-time error if passed to:
   * `fpga_mgmt_describe_local_image`
   * `fpga_mgmt_load_local_image_flags`
   * `fpga_mgmt_load_local_image_with_options`
   * `fpga_mgmt_load_local_image_sync_flags`
   * `fpga_mgmt_load_local_image_sync_with_options`

   If your application passes these flags, you have two options:
   1. Edit your application to no longer pass these flags
   2. If your application links against `libfpga_mgmt.so`, you can uncomment the following line from the `Makefile` in the `<SDK>/userspace/fpga_libs/fpga_mgmt` directory:

   ```makefile
   #IGNORE_DEPRECATION=-DUNSUPPORTED_OPTIONS_ACKNOWLEDGED
   ```

   After editing the Makefile, run `source sdk_setup.sh` in the root of this repository. Rebuild your application as normal and the options will be ignored. Alternatively, passing `-DUNSUPPORTED_OPTIONS_ACKNOWLEDGED` to the compiler when compiling the `fpga_mgmt.c` source file will also ignore the options.

2. The `-F` flag is not supported when passed to the `fpga-load-local-image` CLI. The CLI will not error, but it will print a message indicating that the option is not supported and will be ignored.

## Software defined Accelerator Development (Vitis)

1. Support for Vitis software emulation has been deprecated by AMD and is no longer supported.

## Amazon DCV

1. Amazon DCV does not support Rocky Linux 8.10 at this time.
