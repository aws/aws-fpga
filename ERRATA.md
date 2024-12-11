
# F2 Developer Kit Errata

## Shell Errata

Shell errata is [documented here](./hdk/docs/AWS_Shell_ERRATA.md)

## HDK

1. CL simulation might show the following "error" message if the [CL clock generator](./hdk/docs/AWS_CLK_GEN_spec.md) is contained in the design. By default, the generator blocks all output clocks (except for `o_clk_main_a0`) and asserts all output resets. This behavior violates the built-in reset check in the [AXI SmartConnect IP](https://www.xilinx.com/products/intellectual-property/smartconnect.html#overview). This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # ** Error: [SmartConnect 500-33] s_sc_aresetn should be asserted for at least 16 cycles of m_sc_aclk. tb.card.fpga.CL.CL_HBM.HBM_PRESENT_EQ_1.AXI_CONVERTER_AXI4_AXI3.cl_axi_sc_1x1_i.smartconnect_0.inst.s00_nodes.s00_aw_node.inst.<protected>.<protected>
    ```

2. CL simulation might show the following "error" message. This message can be safely ignored. A Fix for this issue is in progress.

    ```bash
    # Initializing memory from data in 'ddr4_ddr_10.mem'.
    #   Reading data in x8 and bl:8 mode (Change with 'config <4,8,16> <4,8>' in this file).
    #   'ddr4_ddr_10.mem' set write data width to x4.
    #   ERROR: Failed to write data burst length to 16. Only <4,8> are valid.
    ```

3. XSIM simulator does not support a cycle-accurate simulation model for the HBM IP. We’re observing significantly longer simulation times compared to VCS and Questa simulators. This is caused by the HBM BFM used in XSIM. Therefore, running HBM simulation using VCS or Questa is strongly recommended.

4. XDMA driver interrupt mode doesn't work currently on instances. Runtime examples have temporarily switched to use the polling mode and the interrupt mode test has been temporarily removed. Refer to the [XDMA driver installation guide](./hdk/docs/XDMA_Install.md) for instructions on how to load XDMA driver using the polling mode.

5. The following hdk tests are not supported in XSIM currently and will report not supported warning if ran:

   - cl_mem_perf:
     - test_dram_dma_4k_crossing
     - test_dram_dma
     - test_dram_dma_align_addr_4k
     - test_dram_dma_single_beat_4k
     - test_dram_dma_rnd

   - cl_dram_hbm_dma:
     - test_dram_dma_4k_crossing

6. Simulation of the [HBM monitor interface](./hdk/docs/AWS_Shell_Interface_Specification.md/#hbm-monitor-interface) is not supported in this release. The HBM IP always passes initialization and remains in an operating state for all tests. Simulation support for the HBM monitor will be added in a future release.

7. AFIs created based on HDK XDMA shell or Vitis are not supported on F2 instances at this time.

## SDK

## Software defined Accelerator Development (Vitis)

- Support for 2024.1 and hardware emulation only. Software emulation and F2 instance support is not supported at this time.
