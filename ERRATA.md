
# F2 Developer Kit Errata

## Shell Errata

Shell errata is [documented here](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK

1. Address Aliasing Bug in AMD HBM IP with Customer Address Mapping

   * An address aliasing bug has been identified in AMD HBM IP when the IP's "Customer Address Map" option is enabled for a 16GB HBM implementation. The bug allows a single memory entry to be accessed via two different addresses, which might lead to data corruption. More information about this bug will be published by AMD in the Ultrascale+ product errata.

   * For now, customers using 16GB HBM implementation should disable the "Customer Address Map" option in the IP until a fix is released by AMD.

2. Support for the XDMA Shell in the HDK design flow is not available at this time. CL builds using the XDMA Shell will result in a build failure.

3. CL simulation might show the following "error" message if the [CL clock generator](./hdk/docs/AWS_CLK_GEN_spec.md) is contained in the design. By default, the generator blocks all output clocks (except for `o_clk_main_a0`) and asserts all output resets. This behavior violates the built-in reset check in the [AXI SmartConnect IP](https://www.xilinx.com/products/intellectual-property/smartconnect.html#overview). This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # ** Error: [SmartConnect 500-33] s_sc_aresetn should be asserted for at least 16 cycles of m_sc_aclk. tb.card.fpga.CL.CL_HBM.HBM_PRESENT_EQ_1.AXI_CONVERTER_AXI4_AXI3.cl_axi_sc_1x1_i.smartconnect_0.inst.s00_nodes.s00_aw_node.inst.<protected>.<protected>
    ```

4. CL simulation might show the following "error" message. This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # Initializing memory from data in 'ddr4_ddr_10.mem'.
    #   Reading data in x8 and bl:8 mode (Change with 'config <4,8,16> <4,8>' in this file).
    #   'ddr4_ddr_10.mem' set write data width to x4.
    #   ERROR: Failed to write data burst length to 16. Only <4,8> are valid.
    ```

5. XSIM simulator does not support a cycle-accurate simulation model for the HBM IP. We’re observing significantly longer simulation times compared to VCS and Questa simulators. This is caused by the HBM BFM used in XSIM. Therefore, running HBM simulation using VCS or Questa is strongly recommended.

6. Simulation of the [HBM monitor interface](./hdk/docs/AWS_Shell_Interface_Specification.md/#hbm-monitor-interface) is not supported in this release. The HBM IP always passes initialization and remains in an operating state for all tests. Simulation support for the HBM monitor will be added in a future release.

7. AFIs created based on HDK XDMA shell or Vitis are not supported on F2 instances at this time.

8. HBM simulation using XSIM requires a fix described in this [AMD Answer Record](https://adaptivesupport.amd.com/s/article/000035639?language=en_US).

9. Vivado 2025.1 introduces a `set_property DONT_TOUCH` to the HBM model that makes meeting
timing difficult in the implementation stage. AMD has responded to this issue on their AR, stating that it will be fixed in a future version of Vivado. [See here for more details](https://adaptivesupport.amd.com/s/article/000038502?language=en_US&t=1754923887312). All HDK CL examples have been updated to address this issue. Customers should follow this AR when creating their own designs.

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

1. Only hardware emulation via Vitis 2024.1 and 2024.2 is currently supported.

2. Support for Vitis 2024.1 and 2024.2 accelerator binary creation and AFI creation is not supported, but will be released at a later time.

3. Support for Vitis software emulation has been deprecated by AMD, therefore, no longer supported.
