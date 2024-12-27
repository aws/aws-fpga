
# F2 Developer Kit Errata

## Shell Errata

Shell errata is [documented here](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK

1. Support for the XDMA Shell in the HDK design flow is not available at this time. CL builds using the XDMA Shell will result in a build failure.

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

5. The following HDK tests are currently not supported in XSIM and will report not supported warning if ran:

   - cl_mem_perf:
     - test_dram_dma_4k_crossing
     - test_dram_dma
     - test_dram_dma_align_addr_4k
     - test_dram_dma_single_beat_4k
     - test_dram_dma_rnd

   - cl_dram_hbm_dma:
     - test_dram_dma_4k_crossing

6. Simulation of the [HBM monitor interface](./hdk/docs/AWS_Shell_Interface_Specification.md/#hbm-monitor-interface) is not supported in this release. The HBM IP always passes initialization and remains in an operating state for all tests. Simulation support for the HBM monitor will be added in a future release.

7. AFIs created based on HDK XDMA shell or Vitis are not supported on F2
   instances at this time.

8. The following ddr simulation backdoor test is not working with 64GB memory:
   - test_ddr_peek_bdr_walking_ones

## SDK

## Software defined Accelerator Development (Vitis)

1. Only hardware emulation via Vitis 2024.1 is currently supported.

2. Support for Vitis 2024.1 accelerator binary creation and AFI creation is not supported, but will be released at a later time.

3. Support for Vitis software emulation has been deprecated by AMD, therefore, no longer supported.
