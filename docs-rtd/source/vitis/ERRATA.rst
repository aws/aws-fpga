Vitis Errata
============

General
-------

Simultaneous builds of more than one Vitis example at a time is not supported by AMD.

Examples
--------

The following examples are not currently supported by AMD:

- ``host_xrt/host_memory_copy_buffer_xrt``
- ``host_xrt/host_memory_copy_kernel_xrt``
- ``host_xrt/host_memory_simple_xrt``
- ``host_xrt/multiple_cus_asymmetrical_xrt``
- ``host_xrt/p2p_fpga2fpga_xrt``
- ``host_xrt/p2p_simple_xrt``
- ``performance/host_global_bandwidth``
- ``performance/host_memory_bandwidth``
- ``performance/host_memory_bandwidth_xrt``
- ``performance/kernel_global_bandwidth``
- ``sys_opt/multiple_devices``

The following examples are currently under development by AMD:

- ``hello_world``

  - Warnings emitted at beginning of Hardware Emulation can be safely ignored

- ``rtl_kernels/rtl_streaming_free_running_k2k``
- ``rtl_kernels/rtl_streaming_k2k_mm``
- ``rtl_kernels/rtl_vadd_hw_debug``

- ``sys_opt/kernel_swap``

Hardware Emulation
------------------

The following examples do not support Hardware Emulation.

- ``rtl_kernels/rtl_vadd_hw_debug``
- ``host_xrt/kernel_chain``
- ``sys_opt/multiple_processes``

Vitis 2024.2
------------

Only Hardware Emulation is available for Vitis 2024.2. Hardware builds and AFI creation are not supported at this time.

``performance/axi_burst_performance`` does not support Hardware Emulation on Vitis 2024.2 at this time.

.. _vitis-20241:

Vitis 2024.1
------------

For this tool version, the following designs do not meet timing and have
reduced HBM clock speeds:

- ``host_xrt/copy_buffer_xrt``

  - Actual: 425MHz
  - Expected: 450MHz

- ``performance/iops_test_xrt``

  - Actual: 437MHz
  - Expected: 450MHz
