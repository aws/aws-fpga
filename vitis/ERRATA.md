# Vitis Errata

## General

Simultaneous builds of more than one Vitis example at a time is not supported by AMD.

## Examples

The following examples are not currently supported by AMD:

* `host_xrt/host_memory_copy_buffer_xrt`
* `host_xrt/host_memory_copy_kernel_xrt`
* `host_xrt/host_memory_simple_xrt`
* `host_xrt/multiple_cus_asymmetrical_xrt`
* `host_xrt/p2p_fpga2fpga_xrt`
* `host_xrt/p2p_simple_xrt`
* `performance/host_global_bandwidth`
* `performance/host_memory_bandwidth`
* `performance/host_memory_bandwidth_xrt`
* `performance/kernel_global_bandwidth`
* `sys_opt/multiple_devices`

The following examples are currently under development by AMD:

* `host_py/hello_world_py`
* `rtl_kernels/rtl_vadd_mixed_c`

## Hardware Emulation

The following examples do not support Hardware Emulation.

* `host_xrt/kernel_chain`
* `host_xrt/mailbox_auto_restart_xrt`
* `host_xrt/mult_compute_units_xrt`
* `performance/axi_burst_performance`
* `performance/hbm_bandwidth`
* `performance/hbm_bandwidth_pseudo_random`
* `rtl_kernels/rtl_streaming_free_running_k2k`
* `rtl_kernels/rtl_streaming_k2k_mm`
* `rtl_kernels/rtl_vadd_hw_debug`
* `rtl_kernels/rtl_vadd_mixed_c_vadd`
* `sys_opt/kernel_swap`
* `sys_opt/multiple_process`

## Hardware

The following examples do not support Hardware.

* `host_xrt/asynchronous_xrt`
* `host_xrt/data_transfer_xrt`
* `rtl_kernels/rtl_adder_streams`

## Vitis 2024.2

The following examples do not support Hardware with this tool version.

* `sys_opt/multiple_process`

## Vitis 2025.1

The following examples do not support Hardware with this tool version.

* `performance/axi_burst_performance`
* `rtl_kernels/rtl_vadd_2clks`
* `sys_opt/multiple_process`
